import glob, re, json, yaml

fc_files = glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean")
lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}
erdos_list = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
erdos_by_num = {int(p["number"]): p for p in erdos_list if str(p.get("number", "")).isdigit()}

only_solved = []
mixed_open_solved = []

for p in sorted(fc_files):
    m = re.search(r"/(\d+)\.lean$", p)
    if not m: continue
    enum = int(m.group(1))
    txt = open(p, encoding="utf-8").read()
    if "category research solved" in txt and "formal_proof" not in txt and enum not in lp_files:
        ep = erdos_by_num.get(enum, {})
        has_open = "category research open" in txt
        if not has_open:
            only_solved.append((enum, p, ep))
        else:
            mixed_open_solved.append((enum, p, ep))

print(f"Of 176: Purely solved (no 'category research open' in file): {len(only_solved)}, Mixed (has both open and solved variants): {len(mixed_open_solved)}")
for enum, p, ep in only_solved:
    print(f"  Purely solved Erdos #{enum}: ep_inf={ep.get('informal_status',{}).get('state')}, ep_form={ep.get('formal_status',{}).get('state')}, tags={ep.get('tags')}")
