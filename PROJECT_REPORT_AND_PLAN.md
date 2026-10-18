# 孙宇晨奖（The Justin Sun Prize）Lean 4 形式化项目总报告与后续攻关计划

---

## 一、 项目基础信息与仓库元数据

| 项目项 | 内容详情 |
| :--- | :--- |
| **申请者 / 形式化作者** | `Ethan Xiang (@xccElephant)` |
| **本地工作区根目录** | `/Users/xcc/Project/justin-sun-prize-lean` |
| **公开证明仓库（Original Proof Repo）** | [`https://github.com/xccElephant/justin-sun-prize-lean`](https://github.com/xccElephant/justin-sun-prize-lean) |
| **官方评奖仓库 Fork** | [`https://github.com/xccElephant/awards`](https://github.com/xccElephant/awards)（本地位于 `/Users/xcc/Project/justin-sun-prize-lean/reference/awards`） |
| **已提交官方 PR 汇总页** | [`https://github.com/TheJustinSunPrize/awards/pulls/xccElephant`](https://github.com/TheJustinSunPrize/awards/pulls/xccElephant)（共 **32 个 Open PR**：`#5076`–`#5107`） |
| **Lean 4 工具链版本** | `leanprover/lean4:v4.33.1`（固定于 `lean-toolchain`） |
| **Mathlib 版本与 Commit** | `v4.33.1` / `0df444a360eaa60ab8c11dca51a86af692955474`（固定于 `lake-manifest.json`） |
| **单文件秒级验证脚本** | `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh`（5～20 秒完成单文件编译与 `#print axioms` 审计） |
| **公理依赖审计结果** | 所有已提交模块 **0 `sorry`、0 `admit`、0 自定义 `axiom`**，仅依赖 Lean 4 标准经典公理 `[propext, Classical.choice, Quot.sound]` |
| **关联访谈实录文档** | `/Users/xcc/Downloads/金明对话孙宇晨_黄金时代Vol02_访谈实录.md` |

### 本地参考库路径（位于 `reference/`，已加入 `.gitignore`）
1. **官方题库与评奖规则**：`/Users/xcc/Project/justin-sun-prize-lean/reference/awards`（`TheJustinSunPrize/awards`）
2. **Google DeepMind 形式化题库**：`/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures`（`google-deepmind/formal-conjectures`）
3. **社区已有 Lean 证明参考库**：`/Users/xcc/Project/justin-sun-prize-lean/reference/lean-proofs`（`plby/lean-proofs`）
4. **Erdős 问题原始数据库**：`/Users/xcc/Project/justin-sun-prize-lean/reference/erdosproblems`（`teorth/erdosproblems`）

---

## 二、 已完成的 32 个官方抢占 PR 与做题报告总表

所有证明源码位于 `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/`，分模块详细技术报告位于 `/Users/xcc/Project/justin-sun-prize-lean/reports/`。

### 🥇 第一梯队：原题已 100% 完整解决（2026 最新突破 / 完整主定理证明）

| 序号 | 官方 PR | JSP 题号 | Erdős # | 源码文件 | 详细技术报告 | 核心证明定理与竞争优势 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | [PR #5076](https://github.com/TheJustinSunPrize/awards/pull/5076) | `JSP-000290` | #348 | `JspBounties/Erdos348.lean` (1,869 行) | `reports/Erdos348_report.md` | **全网唯一直接证明 `FormalConjectures` 原始签名 `Erdos348.erdos_348` 的完整证明**（基于 Geneson 2026-09 `arXiv:2609.25107`，完整证明 \(m=0\)、\(m=1\) 位移 Fibonacci 序列存在性及 \(2 \le m < n\) 中心区间不可能性定理） |
| 2 | [PR #5098](https://github.com/TheJustinSunPrize/awards/pull/5098) | `JSP-000234` | #273 | `JspBounties/Erdos273.lean` & `Erdos727_273.lean` | `reports/Erdos727_273_report.md` | **`0 真实竞争 PR`**。完整证明 `FormalConjectures` 主定理 `Erdos273.erdos_273.variants.three`（及整数环版本 `three_int`），构造模 360 的 12 同余式严格覆盖系，所有模数均为 \(p-1, p \ge 3\) 素数 |
| 3 | [PR #5089](https://github.com/TheJustinSunPrize/awards/pull/5089) | `JSP-000780` | #939 | `JspBounties/Erdos939.lean` (489 行) | `reports/Erdos939_report.md` | **`0 真实竞争 PR`**。将目录状态从 `Open` 更新为 `Solved`，完整证明 `FormalConjectures` 主定理 `Erdos939.erdos_939.variants.triples`（Nitaj–Cohn 互素 3-powerful 三元组 \(a+b=c\) 无穷族） |
| 4 | [PR #5090](https://github.com/TheJustinSunPrize/awards/pull/5090) | `JSP-000781` | #939 | `JspBounties/Erdos939.lean` (489 行) | `reports/Erdos939_report.md` | **`全网第 1 个 PR / 0 竞争`**。完整证明 `FormalConjectures` 主定理 `Erdos939.erdos_939.variants.finite`（证伪 \(\forall r \ge 4\) 有限性）及 \(r=5,6,7,8\) 构造定理 |
| 5 | [PR #5079](https://github.com/TheJustinSunPrize/awards/pull/5079) | `JSP-000301` | #365 | `JspBounties/Erdos365.lean` (336 行) | `reports/Erdos131_365_report.md` | 目录已标 `Solved`。不仅证明 `Erdos365.erdos_365.parts.i`（Golomb 反例 \((12167, 12168)\)），还完整证明 **Walker (1976) 三次 Pell 方程 \(7^3x^2 - 3y^2 = 1\) 无穷非平方连续强数对定理** `infinite_nonSquare_consecutive_powerful` |
| 6 | [PR #5080](https://github.com/TheJustinSunPrize/awards/pull/5080) | `JSP-000307` | #372 | `JspBounties/Erdos372.lean` (239 行) | `reports/SolvedNoLean_report.md` | 目录已标 `Solved`。证明最小三连降 \(n=13\) 及最小性 `jsp_000307_least_decreasing_triple`、四连降 \(n=317\) 及无穷严格递减对定理 `infinite_strictly_decreasing_pairs` |

### 🥈 第二梯队：完整解决 `FormalConjectures` 已解主问题（`@[category research solved, question]`）且 **0 真实竞争 PR**

| 序号 | 官方 PR | JSP 题号 | Erdős # | 源码文件 | 详细技术报告 | 核心证明定理与竞争优势 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 7 | [PR #5088](https://github.com/TheJustinSunPrize/awards/pull/5088) | `JSP-000131` | #124 | `JspBounties/Erdos124.lean` (596 行) | `reports/Erdos124_report.md` | **`全网第 1 个 PR / 0 竞争`**。完整证明 `erdos124.zero`（及其全体自然数加强版 `zero_all`）与 Pomerance 逆定理 `erdos124.converse`，给出完整充要条件 `eventually_iff_le_sum` |
| 8 | [PR #5084](https://github.com/TheJustinSunPrize/awards/pull/5084) | `JSP-000247` | #291 | `JspBounties/Erdos291_367.lean` (476 行) | `reports/Erdos291_367_report.md` | **`全网第 1 个 PR / 0 竞争`**。完整证明主定理 `Erdos291.erdos_291.parts.ii`（对所有 \(k \ge 1\)，\(n_k = 2 \cdot 3^k\) 满足 \(3 \mid \gcd(a_{n_k}, L_{n_k})\)） |
| 9 | [PR #5085](https://github.com/TheJustinSunPrize/awards/pull/5085) | `JSP-000303` | #367 | `JspBounties/Erdos291_367.lean` (476 行) | `reports/Erdos291_367_report.md` | **`0 真实竞争 PR`**。完整证明 `Erdos367.erdos_367.parts.ii`（对所有 \(k \ge 3\) 证伪 \(O(n^2)\)）、`k_le_two` 及伴随 Pell 三倍角构造给出的 \(\frac{3}{8}n^2\log n\) 下界 `k_ge_three_lower` |
| 10 | [PR #5077](https://github.com/TheJustinSunPrize/awards/pull/5077) | `JSP-000254` | #302 | `JspBounties/Erdos302.lean` (219 行) | `reports/SystematicHunter_report.md` | **`全网唯一证明主定理的 PR`**（此前唯一 PR `#4582` 仅算 \(N=4\)）。完整证明 `Erdos302.erdos_302.parts.ii` 与 `f_lower_bound_17_32`（构造 \(\frac{17}{32}N\) 下界证伪 \(1/2\) 密度猜想） |
| 11 | [PR #5086](https://github.com/TheJustinSunPrize/awards/pull/5086) | `JSP-000489` | #602 | `JspBounties/Erdos602.lean` (267 行) | `reports/Erdos670_602_report.md` | **`0 真实竞争 PR`**。完整证明主定理 `Erdos602.erdos_602.variants.countable_index`（Bernstein 可数无穷集族 Property B 定理）与 `two_sets` |
| 12 | [PR #5087](https://github.com/TheJustinSunPrize/awards/pull/5087) | `JSP-000544` | #670 | `JspBounties/Erdos670.lean` (387 行) | `reports/Erdos670_602_report.md` | **`唯一作者原创 PR`**。完整证明 Erdős (1997) 一维渐近主定理 `Erdos670.erdos_670.variants.dim_one`（\(\operatorname{diam}(A) \ge (1-\varepsilon)n^2\)）与任意维组合下界 `choose_two` |
| 13 | [PR #5107](https://github.com/TheJustinSunPrize/awards/pull/5107) | `JSP-000595` | #727 | `JspBounties/Erdos727_273.lean` (747 行) | `reports/Erdos727_273_report.md` | **`0 真实竞争 PR`**。完整证明主定理 `Erdos727.erdos_727.variants.k_1`（Balakram 定理：无穷多 \(n\) 满足 \(((n+1)!)^2 \mid (2n)!\)） |
| 14 | [PR #5099](https://github.com/TheJustinSunPrize/awards/pull/5099) | `JSP-000226` | #261 | `JspBounties/Erdos261.lean` (312 行) | `reports/NewMainQuestions_report.md` | **唯一完整覆盖 `261.lean` 全部 4 个已解定理的原创 PR**：`erdos_261.parts.i`、`two_representations`、`borwein_loring`、`borwein_loring_property` |
| 15 | [PR #5100](https://github.com/TheJustinSunPrize/awards/pull/5100) | `JSP-000483` | #596 | `JspBounties/Erdos80_596_668.lean` (1,115 行) | `reports/Erdos80_596_668_report.md` | **`0 真实竞争 PR`**。通过基数超限良基归纳与 2-邻域闭包完整证明 `Erdos596.erdos_596.variants.C4_free_countable_escape` |
| 16 | [PR #5101](https://github.com/TheJustinSunPrize/awards/pull/5101) | `JSP-000542` | #668 | `JspBounties/Erdos80_596_668.lean` (1,115 行) | `reports/Erdos80_596_668_report.md` | **`0 真实竞争 PR`**。完整证明主定理 `Erdos668.erdos_668.parts.ii` 与 `four_points`（平面 4 点最大单位距离图等距唯一性 \(f(4)=1\)） |
| 17 | [PR #5102](https://github.com/TheJustinSunPrize/awards/pull/5102) | `JSP-000533` | #657 | `JspBounties/Erdos657.lean` (335 行) | `reports/NewMainQuestions_report.md` | **`0 真实竞争 PR`**。完整证明 `Erdos657.erdos_657.variants.straus`（Straus \(\mathbb{R}^k\) 中 \(2^k\) 点无等腰三角形且不同距离数 \(\le 2^k-1\) 构造） |
| 18 | [PR #5095](https://github.com/TheJustinSunPrize/awards/pull/5095) | `JSP-000736` | #885 | `JspBounties/Erdos885.lean` (168 行) | `reports/SystematicHunter_report.md` | **唯一证明 `FormalConjectures` 原始定理的 PR**：`Erdos885.erdos_885.variants.k_eq_2`, `k_eq_3`, `k_eq_4` |

### 🥉 第三梯队：著名 Open 猜想的全部已知核心定理与新进展（锁定正式学术署名）

| 序号 | 官方 PR | JSP 题号 | Erdős # | 源码文件 | 详细技术报告 | 核心证明定理与竞争优势 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 19 | [PR #5078](https://github.com/TheJustinSunPrize/awards/pull/5078) | `JSP-000691` | #835 | `JspBounties/Erdos835.lean` (739 行) | `reports/Erdos835_report.md` | **`0 真实竞争 PR`**。完整形式化 Ma–Tang (2026, `arXiv:2604.07009`) 全文所有定理，并额外解决首个素数情形 \(k=4\)（`not_property_four`） |
| 20 | [PR #5081](https://github.com/TheJustinSunPrize/awards/pull/5081) | `JSP-000509` | #628 | `JspBounties/ErdosGraph.lean` (2,745 行) | `reports/ErdosGraph_report.md` | **`0 真实竞争 PR`**。证明 `k_5_a_3_b_3` (Brown–Jung 1969) 与 `independence_number_2` (BKPS 2009，基于 Tutte 定理 1,650 行完整证明) |
| 21 | [PR #5082](https://github.com/TheJustinSunPrize/awards/pull/5082) | `JSP-000500` | #617 | `JspBounties/ErdosGraph.lean` (2,745 行) | `reports/ErdosGraph_report.md` | **`0 真实竞争 PR`**。证明 `Erdos617.erdos_617.variants.r2` 与 `r_eq_3`（Erdős–Gyárfás 1999 \(K_{10}\) 定理） |
| 22 | [PR #5083](https://github.com/TheJustinSunPrize/awards/pull/5083) | `JSP-000403` | #503 | `JspBounties/Erdos503.lean` (826 行) | `reports/SystematicHunter_report.md` | 完整证明 `R0`, `R1`, Kelly 2D(6点)/3D(8点) 构造及 Alweiss 任意维 \(\binom{n+1}{2}\) 下界 |
| 23 | [PR #5091](https://github.com/TheJustinSunPrize/awards/pull/5091) | `JSP-000058` | #23 | `JspBounties/ErdosGraph.lean` (2,745 行) | `reports/ErdosGraph_report.md` | **`0 真实竞争 PR`**。证明 `Erdos23.erdos_23.variants.n1` & `n1_tight` |
| 24 | [PR #5092](https://github.com/TheJustinSunPrize/awards/pull/5092) | `JSP-000244` | #287 | `JspBounties/Erdos287.lean` (563 行) | `reports/Erdos287_672_report.md` | **`0 真实竞争 PR`**。证明 Erdős (1932) 连续整数倒数和不为 1 定理 `erdos_287_gap_at_least_two` |
| 25 | [PR #5093](https://github.com/TheJustinSunPrize/awards/pull/5093) | `JSP-000280` | #338 | `JspBounties/Erdos338.lean` (231 行) | `reports/SolvedNoLean_report.md` | **`全网第 1 个 PR / 0 竞争`**。证明 Bateman 无限制阶加法基反例与 2 阶基大奇数覆盖定理 |
| 26 | [PR #5094](https://github.com/TheJustinSunPrize/awards/pull/5094) | `JSP-000569` | #699 | `JspBounties/Erdos699.lean` (232 行) | `reports/Erdos488_699_report.md` | **`0 真实竞争 PR`**。证明 Erdős–Szekeres (1978) \(\gcd(\binom{n}{i},\binom{n}{j}) > 1\) 定理及 \(i \le 2\) 完整定理 |
| 27 | [PR #5096](https://github.com/TheJustinSunPrize/awards/pull/5096) | `JSP-000395` | #488 | `JspBounties/Erdos488.lean` (403 行) | `reports/Erdos488_699_report.md` | **`0 真实竞争 PR`**。证明单元素集、含 2 有限集、双元素集的倍数密度不等式及高半区归纳步 |
| 28 | [PR #5097](https://github.com/TheJustinSunPrize/awards/pull/5097) | `JSP-000546` | #672 | `JspBounties/Erdos672.lean` (275 行) | `reports/Erdos287_672_report.md` | **`0 真实竞争 PR`**。证明 Euler 四项等差数列平方不可能性定理 `euler_four_squares_in_ap_no_solution` |
| 29 | [PR #5103](https://github.com/TheJustinSunPrize/awards/pull/5103) | `JSP-000210` | #238 | `JspBounties/Erdos238.lean` (256 行) | `reports/SolvedNoLean_report.md` | **`全网第 1 个 PR / 0 竞争`**。证明 \(c_2 < 2\) 无条件定理与分块抽屉连续素数间隙引理 |
| 30 | [PR #5104](https://github.com/TheJustinSunPrize/awards/pull/5104) | `JSP-000340` | #413 | `JspBounties/Erdos413.lean` (273 行) | `reports/NewMainQuestions_report.md` | **`全网第 1 个 PR / 0 竞争`**。证明 barrier 轨迹俘获与汇合定理及 Lau 线性移位规约 |
| 31 | [PR #5105](https://github.com/TheJustinSunPrize/awards/pull/5105) | `JSP-000072` | #44 | `JspBounties/Erdos44.lean` (427 行) | `reports/NewMainQuestions_report.md` | **`0 真实竞争 PR`**。证明 Erdős–Turán 抛物线 Sidon 集构造与 \(\sqrt{N}/3\) 无条件造界 |
| 32 | [PR #5106](https://github.com/TheJustinSunPrize/awards/pull/5106) | `JSP-000579` | #711 | `JspBounties/Erdos711.lean` (230 行) | `reports/NewMainQuestions_report.md` | **唯一证明一般定理的 PR**。证明极小区间长度存在唯一性、下界与 \(\operatorname{lcm}(1,\dots,k)\) 周期性 |

*注：仓库内还包含另外 5 个同样零 `sorry` 通过验证的模块（`Erdos131.lean`, `Erdos216.lean`, `Erdos319.lean`, `Erdos364_366.lean`, `Erdos940.lean`），随时可按需增补 PR。*

---

## 三、 领奖流程、支付币种与邮件模板

### 1. 奖金比例与支付方式
- **分成比例**：每题总奖金分为 **数学解答（Solution, 50%）** + **Lean 4 形式化（Lean, 30%）** + **科普解读（Exposition, 20%）**。两个角色独立评审、独立发钱。
- **支付币种**：默认首选 **波场链 `TRC-20` 网络的 `USDT`**（或 `ERC-20 USDT` / `TRX`，也可在邮件确认阶段协商传统电汇），外加寄送一枚**实体孙宇晨奖奖牌**。
- **收益预估**：
  - 保守估计（第一梯队 100% 结题 PR 通过审核）：**$1,500 ～ $6,000 USDT** + 实体奖牌；
  - 乐观估计（第二梯队 0 竞争已解主分支 PR 一并获批）：**$5,000 ～ $15,000+ USDT**。

### 2. 领奖两步操作（在任一 PR 被官方 Merged 之后立即执行）
1. **第一步：提交 GitHub Claim Issue**
   - 访问 [`https://github.com/TheJustinSunPrize/awards/issues/new?template=claim-award.yml`](https://github.com/TheJustinSunPrize/awards/issues/new?template=claim-award.yml)
   - 填入被 Merge 的 `JSP-XXXXXX` 编号、Merged PR 链接、证明仓库 `https://github.com/xccElephant/justin-sun-prize-lean` 以及你的联系邮箱。
2. **第二步：用该联系邮箱向官方唯一邮箱 `thejustinsunprize@hejustinsun.com` 发送身份与收款确认信**
   - 切勿在 GitHub 公开页面暴露钱包地址或私人收件地址，仅通过邮件发送：
   ```text
   To: thejustinsunprize@hejustinsun.com
   Subject: [Award claim] JSP-000290

   Required:
   - Name or organization name: Ethan Xiang (@xccElephant)
   - JSP problem ID: JSP-000290
   - Claim issue link: <填入刚创建的 GitHub Claim Issue 链接>
   - Merged submission PR links: https://github.com/TheJustinSunPrize/awards/pull/5076
   - Role: Lean formalization
   - Identity-verification method and corresponding public records: GitHub account @xccElephant (owner and sole author of https://github.com/xccElephant/justin-sun-prize-lean)

   Recommended, if available:
   - Public evidence connecting me to the credited author:
     https://github.com/xccElephant/justin-sun-prize-lean/blob/master/AUTHORS.md

   May be supplied at the award-delivery stage:
   - Payment network and address: TRON (TRC-20) USDT — <你的 T 开头波场钱包地址>
   - Medal delivery address: <你的实体奖牌收件地址与联系电话>
   ```

---

## 四、 后续解题计划（Phase 3：高确定性、全额奖金标的狙击路线图）

为了最大化拿奖确定性（直接触发 `Current status: Solved` + `Lean proof: Yes` + `Eligible to claim: Yes`，甚至同时拿走 **50% 数学解答奖 + 30% Lean 奖 = 80% 奖金**），后续攻关分三条主线推进：

### 主线 A：实时跟进已提交的 32 个 PR 审核反馈（最高优先级）
- 每日检查 `https://github.com/TheJustinSunPrize/awards/pulls/xccElephant` 中官方审核员（`Federico2014`、`Simon0313`、`GordonLtron`）的 Review 意见。
- 若审核员对某题提出定理签名对齐、补充等价性引理或补充文献说明的要求，第一时间在 `JspBounties/` 中补充无 `sorry` 证明并更新对应 PR。

### 主线 B：狙击“2026 年最新 100% 完整解决、但尚无有效 Lean 4 证明”的全题 Solved 标的（单题 30% Lean 奖稳拿）
重点扫描 `TheJustinSunPrize/awards` 与 `erdosproblems.com` 中满足以下三个条件的目标：
1. **原问题全部子句已在数学上 100% 解决**（不存在悬而未决的 Open 分支，确保 100% 符合 `Only complete solutions to the original problem are accepted`）；
2. **在 `TheJustinSunPrize/awards` 中尚无编译通过的完整 Lean 4 证明**（或现有 PR 仅指向含 `sorry` 的 `plby/lean-proofs` 占位文件）；
3. **证明依赖的数学工具在 Mathlib `v4.33.1` 能力范围内**（初等数论、组合图论、有限集/极值组合、Pell 方程、抽屉原理、构造性反例）。

**当前锁定的下一批重点候选标的**：
- **Erdős #727 第二部分 `erdos_727.variants.k_1_2`**（`JSP-000595` 扩展：证明对任意 \(k \ge 2\) 有无穷多 \(n\) 满足 \((n+k)!(n+1)! \mid (2n)!\)，可直接在现有 `JspBounties/Erdos727_273.lean` 的 Kummer 进位框架上扩充完成）。
- **Erdős #124 剩余已解主问题 `erdos124.ne_zero_three_four_seven` 与 `erdos124.melfi_construction`**（`JSP-000131` 扩展：利用模周期同余法在 `JspBounties/Erdos124.lean` 中补齐基 \(\{3, 4, 7\}\) 在 \(k \ge 1\) 时的完整证明，使 `JSP-000131` 达到全文件 100% 零 `sorry` 覆盖）。
- **Erdős #686 乘积整除表示问题**（`JSP-000558`：补齐 `686.lean` 中 `erdos_686.variants.four`、`four_three`、`twenty_five` 的显式构造验证，零竞争 PR）。
- **持续监控 `arXiv`（`math.NT` / `math.CO`）与 `erdosproblems.com/forum` 2026 年 10 月最新结题帖**：一旦出现类似 `JSP-000290`（Geneson 2026-09）或 `JSP-000691`（Ma–Tang 2026）的新近短篇初等证明或反例，24 小时内完成 Lean 4 形式化并抢占首交 PR。

### 主线 C：自研构造性反例与有限组合搜寻（冲击 50% Solver + 30% Lean = 80% 双重奖）
- 针对 `problems/catalog-*.md` 中标记为 `Open`、但形如 **“Does there exist... / Is it true that for all \(n\)...”** 的是非题（类似此前 Neel Somani 获奖的 `JSP-000239`、`JSP-000327` 及 OpenAI 团队用反例解决的 `JSP-000465`）：
  1. 先用 Python / SAT / ILP 搜索有限反例或代数参数族（如 Pell 方程族、小模数覆盖系、小规模超图/距离图构造）；
  2. 一旦找到反例或初等构造，同时撰写 Markdown 数学论文（存入仓库 `papers/`）+ 零 `sorry` Lean 4 证明（存入 `JspBounties/`），以 **`Mathematical solution + Lean formalization` 双重身份（80% 奖金份额）** 提交 PR。
