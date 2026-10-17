import json, glob, re, yaml, urllib.request

jsp_erdos_map = {int(k): int(v) for k, v in json.load(open("/Users/xcc/Project/justin-sun-prize-lean/jsp_erdos_map.json")).items()}
erdos_list = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
erdos_by_num = {int(p["number"]): p for p in erdos_list if str(p.get("number", "")).isdigit()}

lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}
fc_files = {int(re.search(r"/(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean") if re.search(r"/(\d+)\.lean$", p)}

catalog_files = sorted(glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/awards/problems/catalog-*.md"))
jsp_items = {}
for cf in catalog_files:
    text = open(cf, encoding="utf-8").read()
    blocks = re.split(r"\n## (JSP-\d+) · ", text)
    for i in range(1, len(blocks), 2):
        pid = blocks[i].strip()
        jnum = int(pid.split("-")[1])
        body = blocks[i+1]
        title = body.splitlines()[0].strip()
        fields = {}
        for line in body.splitlines():
            if line.startswith("| ") and " | " in line:
                parts = [p.strip() for p in line.strip("|").split("|", 1)]
                if len(parts) == 2 and parts[0] not in ("Field", "---"):
                    fields[parts[0]] = parts[1]
        jsp_items[jnum] = {"id": pid, "jnum": jnum, "title": title, "fields": fields, "raw": body}

# Check our top Solved+Lean=No candidates and verify whether they are in lp_files (Boris Alexeev's repo)
candidates = [
    266, 267, 288, 314, 346, 383, 388, 402, 434, 465, 490,
    506, 598, 704, 711, 715, 746, 747, 788, 799, 817, 819,
    837, 854, 906, 1000, 1007, 1022
]

print("=== Checking Top Solved + Lean=No Candidates ===")
for jnum in candidates:
    it = jsp_items.get(jnum)
    if not it: continue
    enum = jsp_erdos_map.get(jnum)
    ep = erdos_by_num.get(enum, {}) if enum else {}
    in_lp = enum in lp_files if enum else False
    in_fc = enum in fc_files if enum else False
    st = it["fields"].get("Current status", "")
    pub = it["fields"].get("Publication details", "")
    print(f"JSP-{jnum:06d} (est. Erdos #{enum}) | in_plby={in_lp} | in_FC={in_fc} | ep_formal={ep.get('formal_status',{}).get('state')}")
    print(f"   Title: {it['title'][:85]}")
    print(f"   Status: {st[:100]}")
    if "overleaf" in pub or "arxiv" in pub or "openai" in pub:
        print(f"   Pub: {pub[:120]}")
