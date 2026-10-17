import glob, re, json, yaml

erdos_list = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
erdos_by_num = {int(p["number"]): p for p in erdos_list if str(p.get("number", "")).isdigit()}
lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}
fc_files = {int(re.search(r"/(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean") if re.search(r"/(\d+)\.lean$", p)}

# Read FormalConjectures docstrings/titles and bib keys
fc_data = {}
for enum, path in fc_files.items():
    txt = open(path, encoding="utf-8").read()
    bibs = set(re.findall(r"\[([A-Za-z0-9]{3,10})\]", txt))
    fc_data[enum] = {"text": txt, "bibs": bibs}

# Read lean-proofs md files
lp_md = {}
for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/ErdosProblems/Erdos*.md"):
    m = re.search(r"Erdos(\d+)\.md$", p)
    if m:
        lp_md[int(m.group(1))] = open(p, encoding="utf-8").read()

# Let's check how many problems in problems.yaml are solved/disproved vs open
print("In problems.yaml (1,221 problems):")
from collections import Counter
c = Counter((p.get("informal_status", {}).get("state", ""), p.get("formal_status", {}).get("state", "")) for p in erdos_list)
for k, v in c.most_common():
    print(f"  {v:4d} | informal={k[0]} | formal={k[1]}")

# Find all Erdos problems where informal_status is proved/disproved/solved, formal_status is unformalized, AND NOT in lp_files!
truly_unformalized_erdos = []
for p in erdos_list:
    num_s = str(p.get("number", ""))
    if not num_s.isdigit(): continue
    num = int(num_s)
    inf = p.get("informal_status", {}).get("state", "")
    form = p.get("formal_status", {}).get("state", "")
    if inf in ("proved", "disproved", "solved") and form == "unformalized" and num not in lp_files:
        truly_unformalized_erdos.append(num)

print(f"\nErdos problems in problems.yaml that are proved/disproved, unformalized, and NOT in plby/lean-proofs: {len(truly_unformalized_erdos)}")
print("Numbers:", truly_unformalized_erdos)
