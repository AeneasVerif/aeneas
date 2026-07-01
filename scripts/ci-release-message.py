#!/usr/bin/env python3
import json
import os
import re
import sys
import urllib.error
import urllib.request


def env(name, default=""):
    return os.environ.get(name, default)


def status_icon(result):
    return {
        "success": "✅",
        "failure": "❌",
    }.get(result, "❔")


def github_api(path):
    request = urllib.request.Request(
        f"{env('GITHUB_API_URL', 'https://api.github.com')}{path}",
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {env('GITHUB_TOKEN')}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request) as response:
        return json.load(response)


def build_results():
    repo = env("GITHUB_REPOSITORY")
    run_id = env("GITHUB_RUN_ID")
    if not repo or not run_id or not env("GITHUB_TOKEN"):
        return []

    jobs = []
    page = 1
    while True:
        data = github_api(f"/repos/{repo}/actions/runs/{run_id}/jobs?per_page=100&page={page}")
        page_jobs = data.get("jobs", [])
        jobs.extend(page_jobs)
        if len(page_jobs) < 100:
            break
        page += 1

    results = []
    build_job_re = re.compile(r"^Build \((.*)\)$")
    for job in jobs:
        match = build_job_re.match(job.get("name", ""))
        if match:
            results.append((match.group(1), job.get("conclusion") or job.get("status") or "unknown"))
    return sorted(results)


def main():
    try:
        builds = build_results()
    except (json.JSONDecodeError, urllib.error.URLError) as error:
        print(f"failed to fetch workflow jobs: {error}", file=sys.stderr)
        builds = []

    success = env("PREPARE_RESULT") == "success" and env("BUILD_RESULT") == "success"

    lines = [
        f"## Aeneas release: {env('TAG_NAME', 'unknown')}",
    ]

    if env("TAG_NAME"):
        lines.append(
            f"tag: {env('GITHUB_SERVER_URL')}/{env('GITHUB_REPOSITORY')}/releases/tag/{env('TAG_NAME')}"
        )
    lines.extend(
        [
            f"run: {env('GITHUB_SERVER_URL')}/{env('GITHUB_REPOSITORY')}/actions/runs/{env('GITHUB_RUN_ID')}",
            "",
            "*Statuses:*",
        ]
    )

    if builds:
        for artifact_name, result in builds:
            lines.append(f"{status_icon(result)} {artifact_name}")
    else:
        lines.append(f"{status_icon(env('BUILD_RESULT', 'missing'))} builds ({env('BUILD_RESULT', 'missing')})")

    print("MSG<<EOF")
    print("\n".join(lines))
    print("EOF")
    print(f"SUCCESS={1 if success else 0}")


if __name__ == "__main__":
    main()
