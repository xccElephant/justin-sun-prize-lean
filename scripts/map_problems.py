import glob, re

# 1. Read all Erdos files in lean-proofs/src/latest/ErdosProblems and formal-conjectures
fc_files = glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean")
lp_files = glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/*.lean")

print(f"formal-conjectures Erdos files: {len(fc_files)}, lean-proofs Erdos files: {len(lp_files)}")

# Check how JSP problems map to Erdos problem numbers using commit 7be685c or current catalog
import subprocess
catalog_files = sorted(glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/awards/problems/catalog-*.md"))

# Parse current catalog
jsp_items = []
for cf in catalog_files:
    text = open(cf, encoding="utf-8").read()
    blocks = re.split(r"\n## (JSP-\d+) · ", text)
    for i in range(1, len(blocks), 2):
        pid = blocks[i].strip()
        body = blocks[i+1]
        title = body.splitlines()[0].strip()
        fields = {}
        for line in body.splitlines():
            if line.startswith("| ") and " | " in line:
                parts = [p.strip() for p in line.strip("|").split("|", 1)]
                if len(parts) == 2 and parts[0] not in ("Field", "---"):
                    fields[parts[0]] = parts[1]
        jsp_items.append({"id": pid, "title": title, "fields": fields, "raw": body})

# Check Solved + Lean=Yes entries to see how JSP IDs correlate with Erdos IDs!
mapping_anchors = []
for item in jsp_items:
    raw = item["raw"]
    m_e = re.search(r"(?:erdosproblems\.com/(?:forum/thread/)?|ErdosProblem|Erdos|problems/)(\d+)", raw)
    if m_e:
        mapping_anchors.append((item["id"], int(m_e.group(1)), item["title"][:50]))

print(f"Found {len(mapping_anchors)} direct Erdos number anchors in catalog:")
for jid, eid, t in mapping_anchors[:25]:
    print(f"  {jid} -> Erdos #{eid}: {t}")
