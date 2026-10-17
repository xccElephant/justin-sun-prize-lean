import glob, re, subprocess, json

# Read all catalog entries from commit cada53b (which had all 1,027 problems before consolidation) and current HEAD
catalog_files = sorted(glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/awards/problems/catalog-*.md"))

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
        jsp_items.append({"id": pid, "num": int(pid.split("-")[1]), "title": title, "fields": fields, "raw": body})

# Also read problems.yaml from teorth/erdosproblems
import yaml
erdos_probs = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
print(f"Loaded {len(erdos_probs)} Erdos problems from problems.yaml")

# Read sources.yaml from plby/lean-proofs
lp_sources = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/data/sources.yaml", encoding="utf-8"))
lp_by_erdos = {}
for s in lp_sources:
    k = s.get("key", "")
    if k.startswith("ErdosProblems.Erdos"):
        num = k.replace("ErdosProblems.Erdos", "")
        lp_by_erdos[num] = s
print(f"Loaded {len(lp_by_erdos)} Erdos entries in lean-proofs/data/sources.yaml")

# Check FormalConjectures files to see what references or docstrings they have
fc_by_erdos = {}
for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean"):
    m = re.search(r"/(\d+)\.lean$", p)
    if m:
        num = int(m.group(1))
        fc_by_erdos[num] = open(p, encoding="utf-8").read()

# Find anchors where JSP entry explicitly contains Erdos number
anchors = {}
for item in jsp_items:
    raw = item["raw"]
    # Look for erdosproblems.com/N or ErdosProblemN or ErdosN or Erdős Problem #N
    for pat in [
        r"erdosproblems\.com/(?:forum/thread/)?(\d+)",
        r"ErdosProblem(\d+)\.lean",
        r"ErdosProblems/Erdos(\d+)\.lean",
        r"problems/(\d+)/Erdos\1\.lean",
        r"Erdős Problem #(\d+)",
        r"erdos-problem-(\d+)",
        r"Erdos(\d+)"
    ]:
        m = re.search(pat, raw)
        if m:
            anchors[item["num"]] = int(m.group(1))
            break

print("Explicit anchors count:", len(anchors))
for jnum, enum in sorted(anchors.items()):
    print(f"  JSP-{jnum:06d} == Erdos #{enum}")
