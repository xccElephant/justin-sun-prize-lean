import json, glob, re, yaml

if __package__:
    from .problem_mapping import load_problem_mapping
else:
    from problem_mapping import load_problem_mapping

jsp_erdos_map = load_problem_mapping()
# Unknown mappings are skipped below; numerical offsets are not evidence.

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

# Category 1: Solved in JSP (or solved in problems.yaml) AND NOT in plby/lean-proofs AND NOT formal_status == Lean!
unformalized_solved = []
for jnum, it in sorted(jsp_items.items()):
    if jnum < 43 or jnum > 1022: continue
    enum = jsp_erdos_map.get(jnum)
    if not enum: continue
    ep = erdos_by_num.get(enum, {})
    in_lp = enum in lp_files
    in_fc = enum in fc_files
    ep_formal = ep.get("formal_status", {}).get("state", "")
    ep_informal = ep.get("informal_status", {}).get("state", "")
    jsp_st = it["fields"].get("Current status", "")
    jsp_lean = it["fields"].get("Lean proof", "")
    if jsp_lean.startswith("No") and not in_lp and ep_formal != "Lean":
        if jsp_st.startswith("Solved") or ep_informal in ("proved", "disproved", "solved"):
            unformalized_solved.append((jnum, enum, it, ep, in_fc))

unknown_mappings = [j for j in jsp_items if 43 <= j <= 1022 and j not in jsp_erdos_map]
print(f"Metadata-only candidates: {len(unformalized_solved)}; full-proof availability unverified")
print(f"Entries skipped for unresolved mapping: {len(unknown_mappings)}")

# Highlight those where:
# (a) JSP status is Open, but erdosproblems.com informal_status is proved/disproved! (Newly solved!)
# (b) JSP status has Proof contributors or recent 2024-2026 papers or disproofs!
print("\n=== JSP Open / external solved metadata leads; verify mapping and existing proofs ===")
for jnum, enum, it, ep, in_fc in unformalized_solved:
    if it["fields"].get("Current status") == "Open":
        print(f"  JSP-{jnum:06d} (Erdos #{enum}) | FC_stmt={in_fc} | ep_status={ep.get('status',{}).get('state')} ({ep.get('status',{}).get('last_update')}) | prize={ep.get('prize')}")
        print(f"     Title: {it['title'][:85]}")

print("\n=== JSP Solved / Lean-No metadata leads with named contributors or recent sources ===")
for jnum, enum, it, ep, in_fc in unformalized_solved:
    st = it["fields"].get("Current status", "")
    pub = it["fields"].get("Publication details", "")
    if "Proof contributors" in st or "2025" in pub or "2026" in pub or "2024" in pub or "disproved" in str(ep.get("informal_status",{}).get("state","")):
        print(f"  JSP-{jnum:06d} (Erdos #{enum}) | FC_stmt={in_fc} | ep_inf={ep.get('informal_status',{}).get('state')} | prize={ep.get('prize')}")
        print(f"     Title: {it['title'][:85]}")
        if "Proof contributors" in st:
            print(f"     Solver: {st[:100]}")
        if pub and "No publication" not in pub:
            print(f"     Pub: {pub[:110]}")

print("\n=== All metadata leads; no proof-vacancy or prize-eligibility conclusion ===")
for jnum, enum, it, ep, in_fc in unformalized_solved:
    st = it["fields"].get("Current status", "")
    pub = it["fields"].get("Publication details", "")
    area = it["fields"].get("Mathematical area", "")
    print(f"--------------------------------------------------")
    print(f"JSP-{jnum:06d} (Erdos #{enum}) [{area}] | FC_stmt={in_fc} | ep_inf={ep.get('informal_status',{}).get('state')} | prize={ep.get('prize')}")
    print(f"  Title: {it['title']}")
    print(f"  JSP Status: {st}")
    print(f"  Pub: {pub}")
