import glob, re, json, yaml

fc_files = glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean")
lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}

fc_solved_no_proof_url = []
fc_solved_with_proof_url = []

for p in sorted(fc_files):
    m = re.search(r"/(\d+)\.lean$", p)
    if not m: continue
    enum = int(m.group(1))
    txt = open(p, encoding="utf-8").read()
    if "category research solved" in txt:
        has_fp = "formal_proof" in txt
        in_lp = enum in lp_files
        if not has_fp and not in_lp:
            fc_solved_no_proof_url.append((enum, p))
        else:
            fc_solved_with_proof_url.append((enum, has_fp, in_lp))

print(f"In FormalConjectures: category research solved count = {len(fc_solved_no_proof_url) + len(fc_solved_with_proof_url)}")
print(f"  With formal_proof or in plby/lean-proofs: {len(fc_solved_with_proof_url)}")
print(f"  WITHOUT formal_proof AND NOT in plby/lean-proofs: {len(fc_solved_no_proof_url)}")
for enum, p in fc_solved_no_proof_url:
    print(f"    Erdos #{enum}: {p}")
