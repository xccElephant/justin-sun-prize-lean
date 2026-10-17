import glob, re, yaml, json

# 1. Load problems.yaml from teorth/erdosproblems
erdos_list = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems/data/problems.yaml", encoding="utf-8"))
erdos_by_num = {int(p["number"]): p for p in erdos_list if str(p.get("number", "")).isdigit()}

# 2. Load plby/lean-proofs sources.yaml
lp_sources = yaml.safe_load(open("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/data/sources.yaml", encoding="utf-8"))
lp_by_num = {}
for s in lp_sources:
    k = s.get("key", "")
    m = re.match(r"ErdosProblems\.Erdos(\d+)$", k)
    if m:
        lp_by_num[int(m.group(1))] = s

# Also check actual .lean files in lean-proofs/src/latest/ErdosProblems/
lp_files = {}
for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/src/latest/ErdosProblems/Erdos*.lean"):
    m = re.search(r"Erdos(\d+)\.lean$", p)
    if m:
        lp_files[int(m.group(1))] = p

# Also check FormalConjectures files
fc_files = {}
for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/*.lean"):
    m = re.search(r"/(\d+)\.lean$", p)
    if m:
        fc_files[int(m.group(1))] = p

# 3. Parse JSP catalog (JSP-000043 to JSP-001022 are Erdos problems in strictly increasing Erdos number order!)
catalog_files = sorted(glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/awards/problems/catalog-*.md"))
jsp_items = []
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
        # Extract bib keys like &#91;Er75&#93; or [Er75]
        bibs = re.findall(r"(?:&#91;|\[)([A-Za-z0-9]{3,10})(?:&#93;|\])", fields.get("Publication details", ""))
        # Extract explicit Erdos anchor if any
        anchor = None
        for pat in [
            r"erdosproblems\.com/(?:forum/thread/)?(\d+)",
            r"ErdosProblem(\d+)\.lean",
            r"ErdosProblems/Erdos(\d+)\.lean",
            r"problems/(\d+)/Erdos\1\.lean",
            r"Erdős Problem #(\d+)",
            r"erdos-problem-(\d+)",
        ]:
            m = re.search(pat, body)
            if m and jnum >= 43 and jnum <= 1022:
                val = int(m.group(1))
                # JSP-000995 had a ref to Erdos 202 in text, filter out out-of-order noise
                if abs(val - (jnum * 1.2)) < 250:
                    anchor = val
                    break
        jsp_items.append({
            "id": pid,
            "jnum": jnum,
            "title": title,
            "fields": fields,
            "bibs": bibs,
            "anchor": anchor,
            "raw": body
        })

print("Total JSP items:", len(jsp_items))

# Check what references exist in FormalConjectures files
fc_bibs = {}
for enum, path in fc_files.items():
    txt = open(path, encoding="utf-8").read()
    bs = re.findall(r"\[([A-Za-z0-9]{3,10})\]", txt)
    fc_bibs[enum] = set(bs)

# Also check ErdosProblems/*.md in plby/lean-proofs
lp_md_files = {}
for p in glob.glob("/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs/ErdosProblems/Erdos*.md"):
    m = re.search(r"Erdos(\d+)\.md$", p)
    if m:
        lp_md_files[int(m.group(1))] = open(p, encoding="utf-8").read()

# Map JSP 43..1022 monotonically using anchors + bib overlap + prize + tags
anchor_pairs = [(43, 1)] + [(it["jnum"], it["anchor"]) for it in jsp_items if it["anchor"] and 43 < it["jnum"] <= 1022]
# Ensure strictly increasing
clean_anchors = []
for jn, en in anchor_pairs:
    if not clean_anchors or (jn > clean_anchors[-1][0] and en > clean_anchors[-1][1]):
        clean_anchors.append((jn, en))

print(f"Clean monotonic anchors: {len(clean_anchors)} from JSP-{clean_anchors[0][0]} (Erdos #{clean_anchors[0][1]}) to JSP-{clean_anchors[-1][0]} (Erdos #{clean_anchors[-1][1]})")

# For any specific JSP item in a segment between two anchors (j1, e1) and (j2, e2),
# let's score candidate Erdos numbers e in (e1, e2) by bib match, prize match, tag match!
item_by_jnum = {it["jnum"]: it for it in jsp_items}

def score_match(it, enum):
    sc = 0
    ep = erdos_by_num.get(enum, {})
    # Prize match
    hb = it["fields"].get("Historical bounty", "").replace("&#36;", "$").strip()
    ep_prize = str(ep.get("prize", "no")).strip()
    if hb.startswith("$") and ep_prize.startswith("$"):
        if hb == ep_prize:
            sc += 50
        else:
            sc -= 50
    elif hb.startswith("$") != ep_prize.startswith("$"):
        sc -= 30
    # Bib match with FormalConjectures
    jb = set(it["bibs"])
    fb = fc_bibs.get(enum, set())
    if jb and fb:
        overlap = len(jb & fb)
        sc += overlap * 25
    # Area / tag match
    area = it["fields"].get("Mathematical area", "").lower()
    tags = [t.lower() for t in ep.get("tags", [])]
    for t in tags:
        if t in area:
            sc += 10
    return sc

# DP alignment within each anchor interval
jsp_to_erdos = {}
for idx in range(len(clean_anchors) - 1):
    j1, e1 = clean_anchors[idx]
    j2, e2 = clean_anchors[idx + 1]
    jsp_to_erdos[j1] = e1
    jsp_to_erdos[j2] = e2
    js = list(range(j1 + 1, j2))
    es = list(range(e1 + 1, e2))
    if not js:
        continue
    # DP to find strictly increasing assignment of js -> subseq of es maximizing score
    n, m = len(js), len(es)
    dp = [[-10**9] * (m + 1) for _ in range(n + 1)]
    parent = [[0] * (m + 1) for _ in range(n + 1)]
    for j in range(m + 1):
        dp[0][j] = 0
    for i in range(1, n + 1):
        it = item_by_jnum[js[i - 1]]
        for j in range(i, m - (n - i) + 1):
            # option 1: skip es[j-1]
            if dp[i][j - 1] > dp[i][j]:
                dp[i][j] = dp[i][j - 1]
                parent[i][j] = 0
            # option 2: match js[i-1] with es[j-1]
            val = dp[i - 1][j - 1] + score_match(it, es[j - 1])
            if val > dp[i][j]:
                dp[i][j] = val
                parent[i][j] = 1
    # Backtrack
    ci, cj = n, m
    while ci > 0 and cj > 0:
        if parent[ci][cj] == 1:
            jsp_to_erdos[js[ci - 1]] = es[cj - 1]
            ci -= 1
            cj -= 1
        else:
            cj -= 1

print("Mapped JSP entries:", len(jsp_to_erdos))
with open("/Users/xcc/Project/justin-sun-prize-lean/jsp_erdos_map.json", "w") as f:
    json.dump(jsp_to_erdos, f, indent=2)
