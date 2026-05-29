#!/usr/bin/env bash
set -euo pipefail

BASE_REMOTE="${BASE_REMOTE:-upstream}"
BASE_BRANCH="${BASE_BRANCH:-main}"
PUSH_REMOTE="${PUSH_REMOTE:-}"
AENEAS_REPO="${AENEAS_REPO:-AeneasVerif/aeneas}"
CHARON_REPO="${CHARON_REPO:-AeneasVerif/charon}"
BRANCH_PREFIX="${BRANCH_PREFIX:-update-charon}"
COMMIT_TITLE="Update charon"
MERGE_QUEUE_POLL_SECONDS="${MERGE_QUEUE_POLL_SECONDS:-30}"
MERGE_QUEUE_WAIT_TIMEOUT_SECONDS="${MERGE_QUEUE_WAIT_TIMEOUT_SECONDS:-3600}"

die() {
    echo "error: $*" >&2
    exit 1
}

require_cmd() {
    command -v "$1" >/dev/null 2>&1 || die "command '$1' not found"
}

head_is_update_charon_commit() {
    [[ "$(git log -1 --pretty=%s 2>/dev/null || true)" == "$COMMIT_TITLE" ]]
}

github_repo_from_remote() {
    local repo_dir="$1"
    local remote="$2"
    local url repo

    url="$(git -C "$repo_dir" remote get-url "$remote")" || return 1

    if repo="$(gh repo view "$url" --json nameWithOwner --jq .nameWithOwner 2>/dev/null)" &&
        [[ -n "$repo" ]]; then
        printf '%s\n' "$repo"
        return 0
    fi
    return 1
}

github_owner_from_remote() {
    local repo_dir="$1"
    local remote="$2"
    local repo

    repo="$(github_repo_from_remote "$repo_dir" "$remote")" || return 1
    printf '%s\n' "${repo%%/*}"
}

branch_push_remote() {
    local repo_dir="$1"
    local branch="$2"
    local remote

    remote="$(git -C "$repo_dir" config --get "branch.$branch.pushRemote" || true)"
    if [[ -z "$remote" ]]; then
        remote="$(git -C "$repo_dir" config --get remote.pushDefault || true)"
    fi
    if [[ -z "$remote" ]]; then
        remote="$(git -C "$repo_dir" config --get "branch.$branch.remote" || true)"
    fi
    printf '%s\n' "${remote:-origin}"
}

branch_exists_locally() {
    git show-ref --verify --quiet "refs/heads/$1"
}

branch_exists_on_push_remote() {
    git ls-remote --exit-code --heads "$PUSH_REMOTE" "$1" >/dev/null 2>&1
}

pick_update_branch() {
    local candidate="$BRANCH_PREFIX"
    local n=2

    while branch_exists_locally "$candidate" || branch_exists_on_push_remote "$candidate"; do
        candidate="${BRANCH_PREFIX}${n}"
        n=$((n + 1))
    done

    printf '%s\n' "$candidate"
}

find_pr_for_head() {
    local repo="$1"
    local owner="$2"
    local branch="$3"
    local state="${4:-open}"

    gh pr list \
        --repo "$repo" \
        --state "$state" \
        --limit 100 \
        --json number,headRefName,headRepositoryOwner,updatedAt \
        --jq "." |
        jq -r --arg owner "$owner" --arg branch "$branch" '
            [.[] | select(.headRefName == $branch and .headRepositoryOwner.login == $owner)]
            | sort_by(.updatedAt)
            | last
            | .number // empty
        '
}

pr_is_merged() {
    local repo="$1"
    local pr="$2"
    local merged

    merged="$(gh pr view "$pr" --repo "$repo" --json mergedAt --jq '.mergedAt != null')" ||
        die "could not inspect merge status for $repo PR #$pr"
    [[ "$merged" == "true" ]]
}

pr_is_in_merge_queue() {
    local repo="$1"
    local pr="$2"
    local owner="${repo%%/*}"
    local name="${repo#*/}"
    local in_queue merge_state

    in_queue="$(
        gh api graphql \
            -F owner="$owner" \
            -F name="$name" \
            -F number="$pr" \
            -f query='
                query($owner: String!, $name: String!, $number: Int!) {
                    repository(owner: $owner, name: $name) {
                        pullRequest(number: $number) {
                            isInMergeQueue
                        }
                    }
                }
            ' \
            --jq '.data.repository.pullRequest.isInMergeQueue // false' \
            2>/dev/null || true
    )"

    if [[ "$in_queue" == "true" ]]; then
        return 0
    fi

    merge_state="$(
        gh pr view "$pr" --repo "$repo" --json mergeStateStatus --jq '.mergeStateStatus // ""' \
            2>/dev/null || true
    )"
    [[ "$merge_state" == "QUEUED" ]]
}

wait_for_pr_merged() {
    local repo="$1"
    local pr="$2"
    local require_merge_queue="${3:-true}"
    local waited=0
    local seen_merge_queue=false

    while true; do
        if pr_is_merged "$repo" "$pr"; then
            echo "$repo PR #$pr is merged"
            return 0
        fi

        if pr_is_in_merge_queue "$repo" "$pr"; then
            seen_merge_queue=true
        elif [[ "$require_merge_queue" == "true" || "$seen_merge_queue" == "true" ]]; then
            die "$repo PR #$pr left the merge queue before merging"
        fi

        if (( waited >= MERGE_QUEUE_WAIT_TIMEOUT_SECONDS )); then
            die "timed out waiting for $repo PR #$pr to merge"
        fi

        if [[ "$seen_merge_queue" == "true" ]]; then
            echo "Waiting for $repo PR #$pr to merge from the merge queue"
        else
            echo "Waiting for $repo PR #$pr to enter the merge queue and merge"
        fi
        sleep "$MERGE_QUEUE_POLL_SECONDS"
        waited=$((waited + MERGE_QUEUE_POLL_SECONDS))
    done
}

ensure_charon_pr_mentions_aeneas_pr() {
    local charon_pr="$1"
    local aeneas_pr="$2"
    local ci_line="ci: use https://github.com/AeneasVerif/aeneas/pull/$aeneas_pr"
    local charon_body updated_body

    charon_body="$(gh pr view "$charon_pr" --repo "$CHARON_REPO" --json body --jq '.body // ""')"

    if [[ "$charon_body" == *"$ci_line"* ]]; then
        echo "Charon PR #$charon_pr already mentions aeneas PR #$aeneas_pr"
        return 0
    fi

    if [[ -n "$charon_body" ]]; then
        updated_body="${charon_body}"$'\n\n'"${ci_line}"
    else
        updated_body="$ci_line"
    fi

    echo "Adding aeneas PR #$aeneas_pr to charon PR #$charon_pr"
    gh pr edit "$charon_pr" --repo "$CHARON_REPO" --body "$updated_body"
}

job_id_from_run() {
    local repo="$1"
    local run_id="$2"
    local job_name="$3"

    gh run view "$run_id" --repo "$repo" --json jobs |
        jq -r --arg job "$job_name" '
            [.jobs[] | select(.name == $job)]
            | .[0].databaseId // empty
        '
}

run_id_from_pr_check() {
    local repo="$1"
    local pr="$2"
    local job_name="$3"
    local checks_json check_link

    checks_json="$(gh pr checks "$pr" --repo "$repo" --json name,link 2>/dev/null || true)"
    [[ -n "$checks_json" ]] || return 0

    check_link="$(
        jq -r --arg job "$job_name" '
            [.[] | select(.name == $job and .link != null)]
            | .[0].link // empty
        ' <<<"$checks_json"
    )"

    if [[ "$check_link" =~ /actions/runs/([0-9]+) ]]; then
        printf '%s\n' "${BASH_REMATCH[1]}"
    fi
}

rerun_pr_job() {
    local repo="$1"
    local pr="$2"
    local job_name="$3"
    local run_id job_id head_sha
    local -a run_ids

    run_id="$(run_id_from_pr_check "$repo" "$pr" "$job_name")"
    if [[ -n "$run_id" ]]; then
        job_id="$(job_id_from_run "$repo" "$run_id" "$job_name")"
        if [[ -n "$job_id" ]]; then
            echo "Rerunning $repo job '$job_name' from run $run_id"
            gh run rerun "$run_id" --repo "$repo" --job "$job_id"
            return 0
        fi
    fi

    head_sha="$(gh pr view "$pr" --repo "$repo" --json headRefOid --jq .headRefOid)"
    [[ -n "$head_sha" ]] ||
        die "could not determine head SHA for $repo PR #$pr"

    mapfile -t run_ids < <(
        gh run list --repo "$repo" --commit "$head_sha" --limit 50 --json databaseId,createdAt |
            jq -r 'sort_by(.createdAt) | reverse | .[].databaseId'
    )

    for run_id in "${run_ids[@]}"; do
        job_id="$(job_id_from_run "$repo" "$run_id" "$job_name")"
        if [[ -n "$job_id" ]]; then
            echo "Rerunning $repo job '$job_name' from run $run_id"
            gh run rerun "$run_id" --repo "$repo" --job "$job_id"
            return 0
        fi
    done

    die "could not find $repo job '$job_name' on PR #$pr"
}

require_cmd git
require_cmd gh
require_cmd jq
require_cmd make

echo "Updating charon pin"
make update-charon-pin

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

git remote get-url "$BASE_REMOTE" >/dev/null 2>&1 ||
    die "base remote '$BASE_REMOTE' does not exist; set BASE_REMOTE=..."

if [[ -z "$PUSH_REMOTE" ]]; then
    PUSH_REMOTE="$(git config --get remote.pushDefault || true)"
fi
PUSH_REMOTE="${PUSH_REMOTE:-origin}"
git remote get-url "$PUSH_REMOTE" >/dev/null 2>&1 ||
    die "push remote '$PUSH_REMOTE' does not exist; set PUSH_REMOTE=..."

[[ -d charon ]] || die "./charon does not exist"
git -C charon rev-parse --is-inside-work-tree >/dev/null 2>&1 ||
    die "./charon is not a git worktree"

current_branch="$(git branch --show-current)"
[[ -n "$current_branch" ]] || die "aeneas is in detached HEAD state"

echo "Fetching $BASE_REMOTE/$BASE_BRANCH"
git fetch "$BASE_REMOTE" "$BASE_BRANCH"

if [[ "$current_branch" == "$BASE_BRANCH" ]]; then
    echo "Fast-forwarding $BASE_BRANCH from $BASE_REMOTE/$BASE_BRANCH"
    git pull --ff-only "$BASE_REMOTE" "$BASE_BRANCH"

    new_branch="$(pick_update_branch)"
    echo "Creating branch $new_branch"
    git switch -c "$new_branch"
    current_branch="$new_branch"
else
    echo "Continuing on existing branch $current_branch"
fi

charon_branch="$(git -C charon branch --show-current)"
[[ -n "$charon_branch" ]] || die "./charon is in detached HEAD state; cannot infer a PR branch"

charon_remote="$(branch_push_remote charon "$charon_branch")"
charon_owner="$(github_owner_from_remote charon "$charon_remote")" ||
    die "could not infer GitHub owner from ./charon remote '$charon_remote'"

echo "Looking for charon PR for $charon_owner:$charon_branch"
charon_pr="$(find_pr_for_head "$CHARON_REPO" "$charon_owner" "$charon_branch" open)"
if [[ -z "$charon_pr" ]]; then
    charon_pr="$(find_pr_for_head "$CHARON_REPO" "$charon_owner" "$charon_branch" all)"
fi
[[ -n "$charon_pr" ]] ||
    die "no charon PR found for $charon_owner:$charon_branch in $CHARON_REPO"

pr_body="Companion PR to https://github.com/AeneasVerif/charon/pull/$charon_pr"

echo "Committing changes"
git add --all
if git diff --cached --quiet; then
    if head_is_update_charon_commit; then
        echo "No staged changes; reusing existing '$COMMIT_TITLE' commit"
    else
        die "no changes to commit and HEAD is not already '$COMMIT_TITLE'"
    fi
else
    if head_is_update_charon_commit; then
        echo "Amending existing '$COMMIT_TITLE' commit"
        git commit --amend --no-edit
    else
        echo "Creating new '$COMMIT_TITLE' commit"
        git commit -m "$COMMIT_TITLE"
    fi
fi

aeneas_owner="$(github_owner_from_remote . "$PUSH_REMOTE")" ||
    die "could not infer GitHub owner from remote '$PUSH_REMOTE'"

echo "Pushing $current_branch to $PUSH_REMOTE"
git fetch "$PUSH_REMOTE" "+refs/heads/$current_branch:refs/remotes/$PUSH_REMOTE/$current_branch" \
    >/dev/null 2>&1 || true
git push --force-with-lease -u "$PUSH_REMOTE" "$current_branch"

echo "Looking for existing aeneas PR for $aeneas_owner:$current_branch"
aeneas_pr="$(find_pr_for_head "$AENEAS_REPO" "$aeneas_owner" "$current_branch" open)"
if [[ -n "$aeneas_pr" ]]; then
    gh pr edit "$aeneas_pr" \
        --repo "$AENEAS_REPO" \
        --title "$COMMIT_TITLE" \
        --body "$pr_body"
    gh pr view "$aeneas_pr" --repo "$AENEAS_REPO" --json url --jq .url
else
    gh pr create \
        --repo "$AENEAS_REPO" \
        --base "$BASE_BRANCH" \
        --head "$aeneas_owner:$current_branch" \
        --title "$COMMIT_TITLE" \
        --body "$pr_body"
    aeneas_pr="$(find_pr_for_head "$AENEAS_REPO" "$aeneas_owner" "$current_branch" open)"
    [[ -n "$aeneas_pr" ]] ||
        die "created aeneas PR, but could not find it for $aeneas_owner:$current_branch"
fi

if pr_is_merged "$CHARON_REPO" "$charon_pr"; then
    echo "Charon PR #$charon_pr is merged; rerunning aeneas job 'charon-pin-is-merged'"
    rerun_pr_job "$AENEAS_REPO" "$aeneas_pr" "charon-pin-is-merged"
elif pr_is_in_merge_queue "$CHARON_REPO" "$charon_pr"; then
    echo "Charon PR #$charon_pr is in the merge queue"
    wait_for_pr_merged "$CHARON_REPO" "$charon_pr"
    rerun_pr_job "$AENEAS_REPO" "$aeneas_pr" "charon-pin-is-merged"
else
    ensure_charon_pr_mentions_aeneas_pr "$charon_pr" "$aeneas_pr"
    rerun_pr_job "$CHARON_REPO" "$charon_pr" "select-dep-versions"
    wait_for_pr_merged "$CHARON_REPO" "$charon_pr" false
    rerun_pr_job "$AENEAS_REPO" "$aeneas_pr" "charon-pin-is-merged"
fi
