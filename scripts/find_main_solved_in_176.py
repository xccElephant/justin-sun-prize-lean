import glob, re, json

fc_files = glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean")
lp_files = {int(re.search(r"Erdos(\d+)\.lean$", p).group(1)): p for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean") if re.search(r"Erdos(\d+)\.lean$", p)}

main_solved = []
for p in sorted(fc_files):
    m = re.search(r"/(\d+)\.lean$", p)
    if not m: continue
    enum = int(m.group(1))
    if enum in lp_files: continue
    txt = open(p, encoding="utf-8").read()
    # Find all blocks of @[category research solved... ] theorem name
    for m_thm in re.finditer(r"(/--[\s\S]*?-/\s*)?@\[category research solved([^\]]*)\]\s*theorem\s+([A-Za-z0-9_.]+)", txt):
        doc = (m_thm.group(1) or "").strip()
        attrs = m_thm.group(2)
        tname = m_thm.group(3)
        if "formal_proof" in attrs:
            continue
        # Check if it's a main theorem (e.g. erdos_N) or has 2024/2025/2026 in doc or is a disproof/counterexample
        is_main = (tname == f"erdos_{enum}")
        has_recent = any(y in doc for y in ["2024", "2025", "2026", "disproved", "counterexample", "false", "negative"])
        if is_main or has_recent:
            main_solved.append((enum, tname, is_main, doc[-300:] if doc else ""))

print(f"Found {len(main_solved)} main/recent solved theorems in FormalConjectures with NO formal_proof and NOT in plby:")
for enum, tname, is_main, doc in main_solved:
    tag = "[MAIN]" if is_main else "[VAR]"
    clean_doc = " ".join(doc.splitlines())
    print(f"  Erdos #{enum:<4d} {tag} {tname}: {clean_doc[:110]}")
