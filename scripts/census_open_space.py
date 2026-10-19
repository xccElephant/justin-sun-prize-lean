"""Count catalogue records and PR-title coverage; do not infer proof validity.

Reproduce using a live main response, a complete earlier PR index, an overlapping
updated-PR page, and the live total. Reads catalogue blobs at the verified commit.
"""

import argparse
import collections
import csv
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--head", required=True, type=Path)
    ap.add_argument("--delta", required=True, type=Path)
    ap.add_argument("--total", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    head = json.loads(args.head.read_text())
    sha = head["sha"]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)

    def git(*parts):
        return subprocess.check_output(
            ["git", "-C", str(root / "reference/awards"), *parts], text=True
        )

    def read(path):
        return git("show", f"{sha}:{path}")

    index = read("problems/README.md")
    indexed = {}
    for line in index.splitlines():
        if re.match(r"^\| JSP-\d+", line):
            cells = [c.strip() for c in line.strip("|").split("|")]
            jsp, title, status, lean, eligible, solver, lean_claim = cells
            assert jsp not in indexed
            indexed[jsp] = dict(status=status, lean=lean, eligible=eligible,
                                solver_claim=solver, lean_claim=lean_claim)

    details = {}
    manifests = []
    files = git("ls-tree", "-r", "--name-only", sha, "problems").splitlines()
    for path in files:
        if not re.fullmatch(r"problems/catalog-\d+-\d+\.md", path):
            continue
        txt = read(path)
        manifests.append(dict(path=path, sha256=hashlib.sha256(txt.encode()).hexdigest()))
        for m in re.finditer(r"^## (JSP-\d+) · (.*)\n([\s\S]*?)(?=^## JSP-|\Z)", txt, re.M):
            fields = {}
            for line in m[3].splitlines():
                if line.startswith("| "):
                    parts = line.strip().strip("|").split("|", 1)
                    if len(parts) == 2:
                        fields[parts[0].strip()] = parts[1].strip()
            assert m[1] not in details
            details[m[1]] = dict(title=m[2], path=path, fields=fields)
    assert indexed.keys() == details.keys()
    assert set(indexed) == {f"JSP-{i:06}" for i in range(1, len(indexed) + 1)}

    baseline = root / "reports/discovery-2026-10-19/pr-index/all-pr-metadata.json"
    prs = {p["number"]: p for p in json.loads(baseline.read_text())}
    delta = json.loads(args.delta.read_text())
    # The live updated page must overlap the date of the complete baseline.
    assert min(p["updated_at"] for p in delta) < "2026-10-19T00:00:00Z"
    for p in delta:
        prs[p["number"]] = dict(
            number=p["number"], title=p["title"],
            state="MERGED" if p["merged_at"] else p["state"].upper(),
            isDraft=p["draft"], createdAt=p["created_at"],
            updatedAt=p["updated_at"], url=p["html_url"])
    total = json.loads(args.total.read_text())["data"]["repository"]["pullRequests"]["totalCount"]
    assert len(prs) == total
    hits = collections.defaultdict(list)
    for p in prs.values():
        for n in set(re.findall(r"\bJSP[- _]?(\d{1,6})(?!\d)", p["title"], re.I)):
            hits[f"JSP-{int(n):06}"].append(p)
    ledger = {r["jsp"]: r for r in json.loads(
        (root / "verification/2026-10-19-discovery/CANDIDATE_LEDGER.json").read_text())}
    rows = []
    for jsp, idx in indexed.items():
        det = details[jsp]
        assert det["fields"]["Current status"].split("<br>")[0] == idx["status"]
        entry = ledger.get(jsp, {})
        # Reading a publisher scope note is not a substantive proof review.
        reviewed = bool(entry.get("review"))
        record = dict(jsp=jsp, title=det["title"], **idx,
                      area=det["fields"].get("Mathematical area", ""),
                      detail_lean=det["fields"].get("Lean proof", ""),
                      status_detail=det["fields"]["Current status"],
                      catalog_path=det["path"],
                      substantive_review=reviewed,
                      assessment=entry.get("assessment", "unreviewed_beyond_metadata"),
                      approved_for_implementation=bool(entry.get("approved_for_implementation")),
                      prs=sorted(hits[jsp], key=lambda p: p["number"], reverse=True))
        record["pr_title_hits"] = len(record["prs"])
        record["open_pr_title_hits"] = sum(p["state"] == "OPEN" for p in record["prs"])
        rows.append(record)

    opened = [r for r in rows if r["status"] == "Open"]
    solved = [r for r in rows if r["status"] == "Solved"]
    pool = [r for r in solved if r["lean"].startswith("No")]
    lean_yes = [r for r in solved if r["lean"] == "Yes"]
    assert len(opened) + len(pool) + len(lean_yes) == len(rows)

    def coverage(items):
        return dict(records=len(items), with_pr_title_hit=sum(bool(r["prs"]) for r in items),
                    without_pr_title_hit=sum(not r["prs"] for r in items),
                    with_open_pr_title_hit=sum(bool(r["open_pr_title_hits"]) for r in items))

    counts = dict(
        checked_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        official_main=sha, official_main_committed_at=head["commit"]["committer"]["date"],
        catalog_total=len(rows), catalog_open=len(opened), catalog_solved=len(solved),
        solved_lean_recorded=len(lean_yes), solved_lean_not_recorded=len(pool),
        solved_independent_math_review_pending=sum(
            "independent mathematical review pending" in r["status_detail"].lower()
            for r in solved),
        pool_substantively_reviewed=sum(r["substantive_review"] for r in pool),
        pool_without_substantive_review=sum(not r["substantive_review"] for r in pool),
        pool_approved_for_implementation=sum(r["approved_for_implementation"] for r in pool),
        pr_index_count=len(prs), pr_live_total=total, delta_rows=len(delta),
        delta_oldest_updated_at=min(p["updated_at"] for p in delta),
        open_coverage=coverage(opened), pool_coverage=coverage(pool),
        pool_missed_by_detail_no_prefix=[r["jsp"] for r in pool
                                        if not r["detail_lean"].startswith("No")],
        source_manifests=manifests,
        limitations=[
            "Open/Solved/Lean are official catalogue metadata, not a fresh mathematical audit.",
            "PR matches use JSP IDs in titles only; no hit is not proof of no submission.",
            "A title hit is not a complete proof, accepted claim, or established priority.",
            "37 existing reviews have differing evidence depth; not 37 full independent builds.",
            "No implementable or award-eligible vacancy is established by this census."])

    for name, value in [("COUNTS.json", counts), ("CATALOG.json", rows),
                        ("OPEN.json", opened), ("LEAN_CANDIDATES.json", pool),
                        ("PR_METADATA.json", sorted(prs.values(), key=lambda p:p["number"]))]:
        (out / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    for path, name in [(args.head,"official-head.json"), (args.delta,"pr-delta.json"),
                       (args.total,"pr-live-total.json")]:
        (out / name).write_bytes(path.read_bytes())
    (out / "official-index.md").write_text(index)
    (out / "official-award-process.md").write_text(read("docs/award-process.md"))
    with (out / "CATALOG.csv").open("w", newline="", encoding="utf-8-sig") as file:
        cols = ["jsp","title","area","status","lean","pr_title_hits",
                "open_pr_title_hits","substantive_review","eligible","catalog_path"]
        writer = csv.DictWriter(file, fieldnames=cols, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({k:v for k,v in counts.items() if k not in ["source_manifests","limitations"]},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
