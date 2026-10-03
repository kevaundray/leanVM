"""Posts on a PR, as one comment, what a run comparing the PR with its base found.

    pr_comment.py counts HEAD_SHA counts.json    (counts.yml's artifact `counts`)
    pr_comment.py bench HEAD_SHA ab.json...      (bench.yml's artifacts `ab-*`)

The comment is created, edited on every run, and deleted once nothing is shown. `--dry-run`
prints it instead and calls nothing.

counts-comment.yml and bench-comment.yml run this from the default branch with a write token,
on artifacts a PR's run wrote, a fork's included, so nothing in them is trusted: the PR number
is taken from them only to ask GitHub whether that PR's head is HEAD_SHA, the commit the run
measured, and every name and number is checked before it reaches the comment. Never run it from
a checkout of the PR's code.
"""

import argparse
import itertools
import json
import math
import os
import re
import statistics
import subprocess
import sys
from dataclasses import dataclass, field

NAME = re.compile(r"[A-Za-z0-9_.-]+")
TEXT = re.compile(r"[A-Za-z0-9 ()@.,_-]*")
COMMIT = re.compile(r"[0-9a-f]{40}")

# A time is shown when every round moved it the same way and its median ratio is this far from one.
THRESHOLD = 0.01

# Bench measures, in the order the comment groups them, and what it calls them.
MEASURES = {"latency": "Proving time", "verify": "Verifying time", "proof-size": "Proof size"}


class Bad(Exception):
    """An artifact that does not say what a run of ours would."""


def checked(pattern, value, what):
    if isinstance(value, str) and pattern.fullmatch(value):
        return value
    raise Bad(f"not {what}: {value!r}")


def number(value):
    if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value) and value >= 0:
        return value
    raise Bad(f"not a value: {value!r}")


def pr_number(value):
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return value
    raise Bad(f"not a PR number: {value!r}")


def metrics(report):
    """Bencher Metric Format, `{benchmark: {measure: {"value": v, ...}}}`, as `{(benchmark, measure): v}`."""
    if not isinstance(report, dict):
        raise Bad("not a report")
    out = {}
    for benchmark, measures in report.items():
        if not isinstance(measures, dict):
            raise Bad(f"not measures: {benchmark!r}")
        for measure, metric in measures.items():
            if not isinstance(metric, dict):
                raise Bad(f"not a metric: {measure!r}")
            out[checked(NAME, benchmark, "a name"), checked(NAME, measure, "a name")] = number(metric.get("value"))
    return out


def signed(n):
    return f"+{n:,}" if n > 0 else f"{n:,}"


def percent(fraction):
    return f"{fraction:+.2%}"


def seconds(ns):
    for unit, scale in (("s", 1e9), ("ms", 1e6)):
        if ns >= scale:
            return f"{ns / scale:.2f} {unit}"
    return f"{ns / 1e3:.2f} µs"


def bold(text, on):
    return f"**{text}**" if on else text


def counts(doc, head):
    """The counts that changed, in the order the PR reports them."""
    base = checked(COMMIT, doc.get("base"), "a commit")
    sides = doc.get("counts")
    if not isinstance(sides, dict):
        raise Bad("no counts")
    old, new = metrics(sides.get("base")), metrics(sides.get("head"))
    rows = []
    for program, measure in [*new, *(key for key in old if key not in new)]:
        a, b = old.get((program, measure)), new.get((program, measure))
        if a == b:
            continue
        if a is None or b is None:
            change = "new" if a is None else "removed"
        else:
            change = bold(signed(b - a) + (f" ({percent((b - a) / a)})" if a > 0 else ""), b > a)
        cells = ["none" if v is None else f"{v:,}" for v in (a, b)]
        rows.append(f"| {program} | {measure} | {cells[0]} | {cells[1]} | {change} |")
    if not rows:
        return ""
    return "\n".join(
        [
            "### Exact counts",
            "",
            (
                f"`cargo leanvm bench --cycles-only`, the counts that changed: {head} merged into its base, against the base {base}. "
                "Any increase fails the Counts check."
            ),
            "",
            "| program | measure | base | this PR | change |",
            "|---|---|---:|---:|---:|",
            *rows,
        ]
    )


@dataclass(order=True)
class Row:
    rank: int
    measure: str
    benchmark: str
    testbed: str
    cpu: str = field(compare=False)
    shown: bool = field(compare=False)
    base: str = field(compare=False)
    pr: str = field(compare=False)
    change: str = field(compare=False)


def tables(rows, cpu):
    """One table per measure, in `MEASURES` order, the rows sorted by benchmark and runner."""
    lines = []
    for measure, group in itertools.groupby(sorted(rows), key=lambda row: row.measure):
        lines += [f"#### {MEASURES.get(measure, measure)}", ""]
        if cpu:
            lines += ["| benchmark | runner | CPU | base | this PR | change |", "|---|---|---|---:|---:|---:|"]
            lines += [f"| {r.benchmark} | {r.testbed} | {r.cpu} | {r.base} | {r.pr} | {r.change} |" for r in group]
        else:
            lines += ["| benchmark | runner | base | this PR | change |", "|---|---|---:|---:|---:|"]
            lines += [f"| {r.benchmark} | {r.testbed} | {r.base} | {r.pr} | {r.change} |" for r in group]
        lines.append("")
    return lines


def cell(measure, by_round):
    if not by_round:
        return "none"
    values = sorted(set(by_round.values()))
    if measure == "proof-size":
        return " or ".join(f"{v:,} B" for v in values)
    return seconds(statistics.median(by_round.values()))


def compare(measure, base, head):
    """Whether a measure's row is shown, and its change, from its values by round on each side."""
    if not base or not head:
        return True, "new" if not base else "removed"
    if measure == "proof-size":
        a, b = set(base.values()), set(head.values())
        if len(a) > 1 or len(b) > 1:
            return True, "varies between rounds"
        (a,), (b,) = a, b
        return b != a, bold(f"{signed(b - a)} B ({percent((b - a) / a)})", b > a)
    ratios = [head[r] / base[r] for r in base if r in head and base[r] > 0]
    median = statistics.median(ratios)
    shown = (min(ratios) > 1 or max(ratios) < 1) and abs(median - 1) >= THRESHOLD
    return shown, bold(f"{percent(median - 1)} ({percent(min(ratios) - 1)} to {percent(max(ratios) - 1)})", shown and median > 1)


def bench(docs, head):
    """Each benchmark's base and PR, proven in turns on one runner: the rows that moved, and every row collapsed."""
    bases = {checked(COMMIT, doc.get("base"), "a commit") for doc in docs}
    if len(bases) != 1:
        raise Bad(f"not one base commit: {bases}")
    rows, rounds = [], 0
    for doc in docs:
        testbed, cpu = checked(NAME, doc.get("testbed"), "a name"), checked(TEXT, doc.get("cpu"), "plain text")
        runs = doc.get("runs")
        if not isinstance(runs, list) or not runs:
            raise Bad("no runs")
        sides = {"base": {}, "head": {}}
        for run in runs:
            if not isinstance(run, dict):
                raise Bad("not a run")
            r, side = run.get("round"), run.get("side")
            if not isinstance(r, int) or isinstance(r, bool) or side not in sides:
                raise Bad(f"not a run: round {r!r}, side {side!r}")
            rounds = max(rounds, r)
            for key, value in metrics(run.get("results")).items():
                sides[side].setdefault(key, {})[r] = value
        for benchmark, measure in sides["base"].keys() | sides["head"].keys():
            base, pr = sides["base"].get((benchmark, measure), {}), sides["head"].get((benchmark, measure), {})
            shown, change = compare(measure, base, pr)
            rank = list(MEASURES).index(measure) if measure in MEASURES else len(MEASURES)
            rows.append(Row(rank, measure, benchmark, testbed, cpu, shown, cell(measure, base), cell(measure, pr), change))
    if not any(row.shown for row in rows):
        return ""
    (base,) = bases
    return "\n".join(
        [
            "### Proving: base against this PR, on one runner",
            "",
            (
                f"{head} merged into its base, against the base {base}: each benchmark proven in turns on one runner, "
                f"base and PR {rounds} times each. A size is shown when it changed; a time when it moved the same way in every round "
                f"and its median by at least {THRESHOLD:.0%} (the change is the median ratio, with the rounds' range)."
            ),
            "",
            *tables([row for row in rows if row.shown], cpu=False),
            "<details><summary>Every result</summary>",
            "",
            *tables(rows, cpu=True),
            "</details>",
        ]
    )


def gh(*args):
    return subprocess.run(["gh", "api", *args], check=True, capture_output=True, text=True).stdout


def post(repo, pr, head, marker, body):
    """Create, edit or delete the PR's comment that starts with `marker`."""
    if gh(f"repos/{repo}/pulls/{pr}", "--jq", ".head.sha").strip() != head:
        print(f"::warning::PR #{pr}'s head is not {head}, the commit this run measured: nothing posted")
        return
    mine = f'.[] | select(.user.login == "github-actions[bot]" and (.body | startswith("{marker}"))) | .id'
    ids = gh("--paginate", f"repos/{repo}/issues/{pr}/comments", "--jq", mine).split()
    if not body:
        if ids:
            gh("-X", "DELETE", f"repos/{repo}/issues/comments/{ids[0]}")
    elif ids:
        gh("-X", "PATCH", f"repos/{repo}/issues/comments/{ids[0]}", "-f", f"body={marker}\n{body}")
    else:
        gh(f"repos/{repo}/issues/{pr}/comments", "-f", f"body={marker}\n{body}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("kind", choices=["counts", "bench"])
    parser.add_argument("head", help="the PR's head commit, the one the run measured")
    parser.add_argument("files", nargs="+")
    parser.add_argument("--dry-run", action="store_true", help="print the comment, call nothing")
    args = parser.parse_args()
    head = checked(COMMIT, args.head, "a commit")
    docs = []
    for path in args.files:
        with open(path) as f:
            doc = json.load(f)
        if not isinstance(doc, dict):
            raise Bad(f"not a run's artifact: {path}")
        docs.append(doc)
    prs = {pr_number(doc.get("pr")) for doc in docs}
    if len(prs) != 1 or (args.kind == "counts" and len(docs) != 1):
        raise Bad(f"not one PR's run: {prs}")
    (pr,) = prs
    body = counts(docs[0], head) if args.kind == "counts" else bench(docs, head)
    if args.dry_run:
        print(body)
    else:
        post(os.environ["REPO"], pr, head, f"<!-- leanvm-{args.kind} -->", body)


if __name__ == "__main__":
    try:
        main()
    except Bad as e:
        sys.exit(f"pr_comment.py: {e}")
