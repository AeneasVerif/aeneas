#!/usr/bin/env python3
"""Check the fork's patch ledger: `Fork-Patch:` trailers and description files.

The cryspen/aeneas fork carries its changes to upstream Aeneas as *patches*.
Every commit of the fork carries exactly one trailer

    Fork-Patch: <patch-name>

and every patch has a prose description file `fork/patches/<patch-name>.md`.
The rebase of the fork onto upstream relies on this ledger. This script checks
it, either for a pull request (`pr`) or for a whole fork stack (`stack`).

Usage:

    check-ledger.py pr --upstream upstream/main --base origin/dev --head HEAD \\
        --title "<PR title>" --body-file <file with the PR description>
    check-ledger.py pr --upstream upstream/main --base origin/dev \\
        --message-file <file with the squash commit message>
    check-ledger.py stack --upstream upstream/main [--head origin/dev] [--adjacent]

Exit status: 0 if the ledger is valid, 1 if it has violations, 2 on a usage or
git error.

Rules (each violation names its rule in brackets):

[trailer]
    A commit (or, for Squash and merge, the squash message: the PR title, a
    blank line and the PR description) has exactly one `Fork-Patch:` trailer.
    Trailers are read with git's own parser, so the trailer must be in the
    last paragraph of the message. A `---` line in a PR description is text,
    not the end of the message.

[patch-name]
    A patch name is kebab-case: `^[a-z0-9]+(-[a-z0-9]+)*$`.

[description-exists]
    Every patch named by a trailer has `fork/patches/<patch-name>.md` at the
    head commit.

[description-lint]
    A description file starts with the line `# <patch-name>` and has a
    `## Summary` section. Other sections are free-form.

[ledger-changes]  (pr mode)
    A pull request either creates a patch (adds its description file) or
    extends patches (changes their description files, at least the History or
    Rebase notes). So every patch the PR names has its description file added
    or changed by the PR, and every description file the PR adds, changes or
    deletes belongs to a patch it names. For Rebase and merge this holds per
    commit: a commit only changes the description file of its own patch, and
    some commit naming a patch changes that patch's description file.

[merge-commit]
    Fork commits are not merges. Merge commits in a pull request make Rebase
    and merge invalid.

[stale-base]  (pr mode)
    The pull request is based on `dev` from before the last rebase of the
    fork: its merge base with the base branch is an upstream commit, or one of
    its commits is on an old `dev-YYYY-MM-DD` branch. Rebase only your own
    commits onto the new `dev`:

        git rebase --onto origin/dev <old-base>

    (where `origin` is cryspen/aeneas; fetch it first), with `<old-base>` the
    last commit of your branch that came from the old `dev`. A plain
    `git rebase origin/dev` would replay old commits of the fork.

[orphan-description]  (stack mode)
    Every description file is named by at least one commit of the stack.

[adjacent]  (stack mode with --adjacent)
    The commits of each patch are adjacent, as they are right after a rebase.

In pr mode, a pull request passes if its ledger is valid for Squash and merge
or for Rebase and merge; the report says which of the two are valid.

When `GITHUB_ACTIONS` is set, violations are also emitted as workflow
annotations, and when `GITHUB_STEP_SUMMARY` is set, the report is appended to
that file.
"""

import argparse
import os
import re
import subprocess
import sys

PATCHES_DIR = "fork/patches"
PATCH_NAME = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")
OLD_DEV = re.compile(r"^dev-[0-9]{4}-[0-9]{2}-[0-9]{2}$")
TRAILER_KEY = "fork-patch"


class GitError(Exception):
    pass


def git(*args, input=None, check=True):
    """Run git and return its standard output."""
    proc = subprocess.run(
        ["git", *args],
        input=input,
        capture_output=True,
        text=True,
    )
    if check and proc.returncode != 0:
        raise GitError(f"git {' '.join(args)} failed:\n{proc.stderr.strip()}")
    return proc


def out(*args, input=None):
    return git(*args, input=input).stdout


def rev(r):
    return out("rev-parse", "--verify", "--quiet", f"{r}^{{commit}}").strip()


def merge_base(a, b):
    return out("merge-base", a, b).strip()


def is_ancestor(a, b):
    proc = git("merge-base", "--is-ancestor", a, b, check=False)
    if proc.returncode not in (0, 1):
        raise GitError(f"git merge-base --is-ancestor failed:\n{proc.stderr.strip()}")
    return proc.returncode == 0


def short(c):
    return c[:9]


def subject(c):
    return out("log", "-1", "--format=%s", c).strip()


def describe(c):
    return f"{short(c)} ({subject(c)})"


def commit_trailers(c):
    """The `Fork-Patch:` values of a commit, as git's trailer parser sees them."""
    text = out("log", "-1", "--format=%(trailers:key=Fork-Patch,valueonly)", c)
    return [line for line in text.split("\n") if line.strip()]


def message_trailers(message):
    """The `Fork-Patch:` values of a commit message that isn't committed yet."""
    text = out("interpret-trailers", "--parse", "--no-divider", input=message)
    values = []
    for line in text.split("\n"):
        key, sep, value = line.partition(":")
        if sep and key.strip().lower() == TRAILER_KEY:
            values.append(value.strip())
    return values


def description_path(patch):
    return f"{PATCHES_DIR}/{patch}.md"


def patch_of_path(path):
    """The patch whose description file is `path`, or None for other files."""
    rest = path[len(PATCHES_DIR) + 1 :]
    if "/" in rest or not rest.endswith(".md"):
        return None
    return rest[: -len(".md")]


def file_at(commit, path):
    proc = git("show", f"{commit}:{path}", check=False)
    return proc.stdout if proc.returncode == 0 else None


class Report:
    def __init__(self):
        self.violations = []

    def add(self, rule, message):
        self.violations.append((rule, message))

    def __bool__(self):
        return bool(self.violations)

    def lines(self):
        return [f"[{rule}] {message}" for rule, message in self.violations]


def check_name(report, patch, where):
    if not PATCH_NAME.match(patch):
        report.add(
            "patch-name",
            f"{where}: patch name {patch!r} is not kebab-case "
            "(`^[a-z0-9]+(-[a-z0-9]+)*$`)",
        )
        return False
    return True


def check_trailer_count(report, values, where):
    """Check for exactly one trailer; return the patch name if there is one."""
    if not values:
        report.add("trailer", f"{where} has no `Fork-Patch:` trailer in its last paragraph")
        return None
    if len(values) > 1:
        report.add(
            "trailer",
            f"{where} has {len(values)} `Fork-Patch:` trailers "
            f"({', '.join(values)}); it must have exactly one",
        )
        return None
    return values[0] if check_name(report, values[0], where) else None


def check_description(report, head, patch):
    path = description_path(patch)
    text = file_at(head, path)
    if text is None:
        report.add("description-exists", f"patch {patch!r} has no description file `{path}`")
        return
    lint_description(report, path, patch, text)


def lint_description(report, path, patch, text):
    lines = [line.rstrip() for line in text.split("\n")]
    if not lines or lines[0] != f"# {patch}":
        report.add("description-lint", f"`{path}` must start with the line `# {patch}`")
    if "## Summary" not in lines:
        report.add("description-lint", f"`{path}` has no `## Summary` section")


def changed_paths(a, b):
    text = out("diff", "--name-only", "--no-renames", a, b, "--", PATCHES_DIR)
    return [p for p in text.split("\n") if p]


def commit_changed_paths(c):
    text = out(
        "diff-tree", "--no-commit-id", "--name-only", "--no-renames", "-r", c, "--", PATCHES_DIR
    )
    return [p for p in text.split("\n") if p]


def check_changed_paths(report, paths, allowed, where):
    """Check that `paths` only change description files of patches in `allowed`."""
    changed = set()
    for path in paths:
        patch = patch_of_path(path)
        if patch is None:
            report.add(
                "ledger-changes",
                f"{where} changes `{path}`, which is not a description file "
                f"(`{PATCHES_DIR}/<patch-name>.md`)",
            )
            continue
        changed.add(patch)
        if patch not in allowed:
            report.add(
                "ledger-changes",
                f"{where} changes `{path}` but doesn't name patch {patch!r}; "
                "description changes belong to the commits of their own patch",
            )
    return changed


def old_dev_refs():
    """Refs of old `dev` branches kept by rebases (`dev-YYYY-MM-DD`)."""
    refs = []
    for ref in out("for-each-ref", "--format=%(refname)", "refs/heads", "refs/remotes").split():
        if ref.startswith("refs/heads/"):
            name = ref[len("refs/heads/") :]
        else:
            parts = ref.split("/", 3)
            if len(parts) < 4:
                continue
            name = parts[3]
        if OLD_DEV.match(name):
            refs.append(ref)
    return refs


def stale_base(upstream, base, head, mb):
    """Return (stale, old_base): whether the PR is based on a pre-rebase `dev`."""
    stale = is_ancestor(mb, merge_base(upstream, base))
    candidates = set()
    for ref in old_dev_refs():
        proc = git("merge-base", "--all", head, ref, check=False)
        for c in proc.stdout.split():
            if not is_ancestor(c, mb):
                candidates.add(c)
    if candidates:
        stale = True
    old_base = None
    for c in candidates:
        if all(is_ancestor(o, c) for o in candidates):
            old_base = c
            break
    return stale, old_base


def check_squash(report, head, mb, message):
    patch = check_trailer_count(report, message_trailers(message), "the squash message")
    named = {patch} if patch else set()
    changed = check_changed_paths(report, changed_paths(mb, head), named, "the pull request")
    if patch:
        check_description(report, head, patch)
        if patch not in changed:
            report.add(
                "ledger-changes",
                f"the pull request names patch {patch!r} but doesn't add or change "
                f"`{description_path(patch)}`; update at least its History or Rebase notes",
            )
    return changed


def check_rebase(report, head, mb, commits):
    for c in out("rev-list", "--merges", f"{mb}..{head}").split():
        report.add("merge-commit", f"commit {describe(c)} is a merge commit")
    changed_by = {}
    for c in commits:
        where = f"commit {describe(c)}"
        patch = check_trailer_count(report, commit_trailers(c), where)
        allowed = {patch} if patch else set()
        changed = check_changed_paths(report, commit_changed_paths(c), allowed, where)
        if patch:
            changed_by.setdefault(patch, set()).update(changed)
    for patch in sorted(changed_by):
        check_description(report, head, patch)
        if patch not in changed_by[patch]:
            report.add(
                "ledger-changes",
                f"no commit naming patch {patch!r} adds or changes "
                f"`{description_path(patch)}`; update at least its History or Rebase notes",
            )


def run_pr(args):
    head = rev(args.head)
    base = rev(args.base)
    upstream = rev(args.upstream)
    for name, value in (("head", head), ("base", base), ("upstream", upstream)):
        if not value:
            raise GitError(f"--{name} does not name a commit")
    if args.message_file is not None:
        with open(args.message_file, encoding="utf-8", newline="") as f:
            message = f.read()
    else:
        body = ""
        if args.body_file is not None:
            with open(args.body_file, encoding="utf-8", newline="") as f:
                body = f.read()
        message = args.title + ("\n\n" + body if body.strip() else "\n")
    message = message.replace("\r\n", "\n")
    if not message.endswith("\n"):
        message += "\n"

    mb = merge_base(base, head)
    stale, old_base = stale_base(upstream, base, head, mb)
    if stale:
        report = Report()
        message = (
            "branch is based on `dev` from before the last rebase; rebase only your own "
            "commits onto `dev`: "
            f"`git rebase --onto origin/dev {short(old_base) if old_base else '<old-base>'}` "
            "(where `origin` is cryspen/aeneas; fetch it first)"
        )
        if not old_base:
            message += ", with `<old-base>` the last commit of your branch that came from the old `dev`"
        report.add("stale-base", message)
        emit([("Pull request", report)], ok=False)
        return 1

    commits = out("rev-list", "--reverse", "--no-merges", f"{mb}..{head}").split()
    squash, rebase = Report(), Report()
    if not commits:
        for report in (squash, rebase):
            report.add("trailer", "the pull request has no commits")
    else:
        check_squash(squash, head, mb, message)
        check_rebase(rebase, head, mb, commits)
    ok = not squash or not rebase
    emit([("Squash and merge", squash), ("Rebase and merge", rebase)], ok=ok, methods=True)
    return 0 if ok else 1


def run_stack(args):
    head = rev(args.head)
    upstream = rev(args.upstream)
    if not head or not upstream:
        raise GitError("--head and --upstream must name commits")
    base = merge_base(upstream, head)
    report = Report()
    for c in out("rev-list", "--merges", f"{base}..{head}").split():
        report.add("merge-commit", f"commit {describe(c)} is a merge commit")
    commits = out("rev-list", "--reverse", "--no-merges", f"{base}..{head}").split()
    sequence = []
    named = set()
    for c in commits:
        patch = check_trailer_count(report, commit_trailers(c), f"commit {describe(c)}")
        sequence.append(patch)
        if patch:
            named.add(patch)
    for patch in sorted(named):
        check_description(report, head, patch)
    listing = out("ls-tree", "--name-only", head, f"{PATCHES_DIR}/")
    for path in listing.split("\n"):
        patch = patch_of_path(path) if path else None
        if patch is None or patch in named:
            continue
        report.add(
            "orphan-description",
            f"`{path}` describes patch {patch!r}, but no commit of the stack names it",
        )
        lint_description(report, path, patch, file_at(head, path) or "")
    if args.adjacent:
        seen, previous = set(), None
        for c, patch in zip(commits, sequence):
            if patch is None:
                previous = None
                continue
            if patch != previous and patch in seen:
                report.add(
                    "adjacent",
                    f"commit {describe(c)} of patch {patch!r} is not adjacent to the "
                    "patch's earlier commits",
                )
            seen.add(patch)
            previous = patch
    summary = f"Checked {len(commits)} commits of `{short(base)}..{short(head)}`."
    emit([("Stack", report)], ok=not report, preface=summary)
    return 1 if report else 0


def emit(sections, ok, methods=False, preface=None):
    """Print the report, annotate it on GitHub and append it to the job summary."""
    in_actions = os.environ.get("GITHUB_ACTIONS") == "true"
    md = ["## Fork ledger check", ""]
    if preface:
        md += [preface, ""]
    if methods:
        md += ["| Merge method | Ledger |", "|---|---|"]
        for title, report in sections:
            md.append(f"| {title} | {'invalid' if report else 'valid'} |")
        md.append("")
    for title, report in sections:
        if not report:
            if not methods:
                md += [f"### {title}: valid", ""]
            continue
        md += [f"### {title}: violations", ""]
        md += [f"- {line}" for line in report.lines()] + [""]
    md.append("Result: **" + ("pass" if ok else "fail") + "**")
    text = "\n".join(md) + "\n"

    sys.stdout.write(text)
    if in_actions:
        level = "error" if not ok else "warning"
        for title, report in sections:
            for line in report.lines():
                print(f"::{level} title=Fork ledger ({title})::{escape(line)}")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as f:
            f.write(text)


def escape(s):
    return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def main():
    parser = argparse.ArgumentParser(
        description="Check the fork's `Fork-Patch:` trailers and `fork/patches/` description files.",
        epilog="The module docstring lists the rules.",
    )
    sub = parser.add_subparsers(dest="mode", required=True)
    pr = sub.add_parser("pr", help="check a pull request")
    pr.add_argument("--upstream", required=True, help="upstream `main`")
    pr.add_argument("--base", required=True, help="the branch the PR targets (`dev`)")
    pr.add_argument("--head", default="HEAD", help="the PR's head commit")
    msg = pr.add_mutually_exclusive_group(required=True)
    msg.add_argument("--message-file", help="the squash commit message")
    msg.add_argument("--title", help="the PR title")
    pr.add_argument("--body-file", help="the PR description (with --title)")
    stack = sub.add_parser("stack", help="check a whole fork stack")
    stack.add_argument("--upstream", required=True, help="upstream `main`")
    stack.add_argument("--head", default="HEAD", help="the tip of the stack")
    stack.add_argument(
        "--adjacent", action="store_true", help="require each patch's commits to be adjacent"
    )
    args = parser.parse_args()
    if args.mode == "pr" and args.body_file is not None and args.title is None:
        parser.error("--body-file needs --title")
    try:
        return run_pr(args) if args.mode == "pr" else run_stack(args)
    except (GitError, OSError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
