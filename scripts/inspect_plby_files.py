import glob, re

lp_files = glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean")
print("Total Erdos*.lean in plby/src/latest/ErdosProblems:", len(lp_files))

has_sorry = []
has_axiom = []
imports_sub = []
clean_standalone = []

for p in sorted(lp_files):
    m = re.search(r"Erdos(\d+)\.lean$", p)
    if not m: continue
    num = int(m.group(1))
    txt = open(p, encoding="utf-8").read()
    # remove comments
    no_comm = re.sub(r"/-.*?-\/", "", txt, flags=re.S)
    no_comm = re.sub(r"--.*", "", no_comm)
    if re.search(r"\bsorry\b|\badmit\b", no_comm):
        has_sorry.append((num, p))
    elif re.search(r"\baxiom\b", no_comm):
        has_axiom.append((num, p))
    elif re.search(r"import\s+ErdosProblems\.", no_comm):
        imports_sub.append((num, p))
    else:
        clean_standalone.append((num, p))

print(f"  has_sorry: {len(has_sorry)}, has_axiom: {len(has_axiom)}, imports_sub: {len(imports_sub)}, clean_standalone: {len(clean_standalone)}")

# Also check if the imported subdirectories have sorry/axiom!
sub_sorry = []
sub_axiom = []
for num, p in imports_sub:
    sub_dir = p.replace(".lean", "")
    sub_files = glob.glob(f"{sub_dir}/**/*.lean", recursive=True)
    full_sub = "\n".join(open(sf, encoding="utf-8").read() for sf in sub_files)
    nc = re.sub(r"/-.*?-\/", "", full_sub, flags=re.S)
    nc = re.sub(r"--.*", "", nc)
    if re.search(r"\bsorry\b|\badmit\b", nc):
        sub_sorry.append(num)
    if re.search(r"\baxiom\b", nc):
        sub_axiom.append(num)

print(f"  In imports_sub ({len(imports_sub)}): sub_sorry={len(sub_sorry)} ({sub_sorry}), sub_axiom={len(sub_axiom)} ({sub_axiom})")
if has_sorry:
    print("  has_sorry nums:", [x[0] for x in has_sorry])
if has_axiom:
    print("  has_axiom nums:", [x[0] for x in has_axiom[:30]])
