import yaml, glob, re, json, urllib.request

erdos_list = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
erdos_by_num = {int(p["number"]): p for p in erdos_list if str(p.get("number", "")).isdigit()}
lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}
fc_files = {int(re.search(r"/(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean") if re.search(r"/(\d+)\.lean$", p)}

print("=== 1. Inspecting Erdos #[216, 504, 575, 625, 1219] ===")
for num in [216, 504, 575, 625, 1219]:
    print(f"\n--- Erdos #{num} ---")
    print("problems.yaml:", erdos_by_num.get(num))
    if num in fc_files:
        print("FormalConjectures file exists:", fc_files[num])
        print(open(fc_files[num]).read()[:600])

# Also check if there are any other Erdos problems in problems.yaml with status NOT open and NOT in lp_files!
print("\n=== 2. All Erdos problems NOT in plby/lean-proofs where informal_status != 'open' ===")
for p in erdos_list:
    num_s = str(p.get("number", ""))
    if not num_s.isdigit(): continue
    num = int(num_s)
    inf = p.get("informal_status", {}).get("state", "")
    if inf != "open" and num not in lp_files:
        print(f"  Erdos #{num}: informal={inf} ({p.get('informal_status',{}).get('last_update')}), formal={p.get('formal_status',{}).get('state')}, in_FC={num in fc_files}, tags={p.get('tags')}")
