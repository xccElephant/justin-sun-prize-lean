import glob, re, json

fc_dir = "/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems"

for enum in [7, 23, 64, 97, 107, 114, 128, 238, 242, 287, 307, 364, 365, 366, 371, 375, 398, 458, 488, 583, 617, 628, 647, 672, 699, 723, 743, 779, 835, 940, 959, 982, 1020, 1041, 1082, 1154, 1176, 1219]:
    p = f"{fc_dir}/{enum}.lean"
    try:
        txt = open(p, encoding="utf-8").read()
        lines = txt.splitlines()
        # remove license header
        body = "\n".join(lines[15:])
        print(f"================ Erdos #{enum} ({len(lines)} lines) ================")
        print(body[:1200])
    except Exception as e:
        pass
