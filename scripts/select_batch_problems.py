import glob, re, json, yaml

jsp_erdos = {int(v): int(k) for k, v in json.load(open("/Users/xcc/Project/justin-sun-prize-lean/jsp_erdos_map.json")).items()}
for j in range(1003, 1023):
    jsp_erdos[1197 + (j - 1002)] = j

erdos_list = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
erdos_by_num = {int(p["number"]): p for p in erdos_list if str(p.get("number", "")).isdigit()}
lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}
fc_files = {int(re.search(r"/(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean") if re.search(r"/(\d+)\.lean$", p)}

catalog_files = sorted(glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/awards/problems/catalog-*.md"))
all_catalog = "\n".join(open(f, encoding="utf-8").read() for f in catalog_files)

# Let's inspect all falsifiable / verifiable / decidable Erdos problems in FormalConjectures that are NOT in plby/lean-proofs
print("=== Track B: Falsifiable / Verifiable / Decidable Open Problems in FormalConjectures ===")
for enum in [7, 23, 64, 97, 107, 114, 128, 242, 287, 307, 364, 366, 375, 398, 458, 488, 583, 617, 628, 647, 672, 699, 723, 743, 779, 835, 982, 1020, 1041, 1082]:
    ep = erdos_by_num.get(enum, {})
    fc_path = fc_files.get(enum)
    if not fc_path: continue
    txt = open(fc_path, encoding="utf-8").read()
    # Extract main theorem signature
    m_thm = re.search(r"(/--[\s\S]*?-/\s*)?@\[category research open[^\]]*\]\s*theorem\s+erdos_" + str(enum) + r"\b([\s\S]*?:=\s*by\s*sorry)", txt)
    if m_thm:
        doc = " ".join((m_thm.group(1) or "").splitlines())
        sig = " ".join(m_thm.group(2).splitlines())
        print(f"Erdos #{enum:<4d} [{ep.get('informal_status',{}).get('state')}] tags={ep.get('tags')} prize={ep.get('prize')}")
        print(f"  Doc: {doc[-220:]}")
        print(f"  Sig: theorem erdos_{enum} {sig[:180]}")
