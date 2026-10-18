/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 711 (`FormalConjectures/ErdosProblems/711.lean`): Distinct Multiples in Short Intervals

*References:*
- [erdosproblems.com/711](https://www.erdosproblems.com/711)
- [ErPo80] Erdős, P. and Pomerance, C., *Matching the natural numbers up to $n$ with distinct
  multiples in another interval*. Indag. Math. 83 (1980), 147–161.
- [vD26] van Doorn, W., *On the length of an interval that contains distinct multiples of the
  first $n$ positive integers*. [arXiv:2601.16972](https://arxiv.org/abs/2601.16972), Integers 26 (2026), #A7.

This file formalizes the following zero-`sorry` results for `FormalConjectures/ErdosProblems/711.lean`:
1. **Universal Existence and Uniqueness of Minimal Interval Length $f(n, m)$
   (`exists_isMinimalIntervalLength`, `isMinimalIntervalLength_unique`)**:
   For every $n, m \in \mathbb{N}$, proves via an explicit strictly increasing multiple construction
   $a_i = (m + i + 1)(i + 1)$ and well-ordering (`Nat.find`) that there exists a unique $L$
   satisfying `IsMinimalIntervalLength n m L`.
2. **Exact Evaluation at $m = 0$ (`isMinimalIntervalLength_zero`) and General Lower Bound
   (`n_add_one_le_of_isMinimalIntervalLength`)**:
   Proves by pigeonhole injection into `Finset.Ioo m (m + L)` that $f(n, m) \ge n + 1$ for all
   $n \ge 1$ and all $m$, with equality $f(n, 0) = n + 1$ at $m = 0$.
3. **Common-Multiple Periodicity of $f(n, m)$ (`isMinimalIntervalLength_add_of_common_multiple`)**:
   If $M$ is divisible by every $k \in \{1, \ldots, n\}$, then shifting the interval by $M$
   preserves valid tuples (`HasDivisibleDistinctTuple n (m + M) L ↔ HasDivisibleDistinctTuple n m L`)
   and hence $f(n, m + M) = f(n, m)$.
4. **Unconditional solution of `erdos_711.parts.ii` (`erdos_711_parts_ii`)**:
   A kernel-checked finite Hall obstruction at n = 5000, restriction to divisible indices,
   and van Doorn's splice prove that the gap diverges, with the explicit witness m = 4n.
   The old conditional wrapper is retained for API compatibility. Part i is not proved here.

-/

open Filter Finset

namespace Erdos711

/-- There are distinct $a_1,\ldots,a_n$ in the open interval $(m,m+L)$ such that
$i \mid a_i$ for every $1 \leq i \leq n$. -/
def HasDivisibleDistinctTuple (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
      ∀ i : Fin n, m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

/-- $L$ is the minimal interval length for the parameters $(n,m)$. -/
def IsMinimalIntervalLength (n m L : ℕ) : Prop :=
  HasDivisibleDistinctTuple n m L ∧
    ∀ L', HasDivisibleDistinctTuple n m L' → L ≤ L'

/-!
## Part 1: Existence and Uniqueness of the Minimal Interval Length $f(n, m)$
-/

/-- Explicit upper bound witness: for every $n, m \in \mathbb{N}$, setting
$a_i = (m + i + 1)(i + 1)$ gives a valid tuple in $(m, m + L)$ for $L = (m + n + 1)(n + 1) + 1$. -/
lemma exists_hasDivisibleDistinctTuple (n m : ℕ) :
    ∃ L : ℕ, HasDivisibleDistinctTuple n m L := by
  refine ⟨(m + n + 1) * (n + 1) + 1, fun i : Fin n => (m + i.1 + 1) * (i.1 + 1), ?_, ?_⟩
  · intro i j hij
    dsimp at hij
    ext
    nlinarith
  · intro i
    have hi : i.1 < n := i.2
    refine ⟨by nlinarith, ?_, dvd_mul_left (i.1 + 1) (m + i.1 + 1)⟩
    calc
      (m + i.1 + 1) * (i.1 + 1) ≤ (m + n + 1) * (n + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ < m + ((m + n + 1) * (n + 1) + 1) := by omega

/-- **Existence of Minimal Interval Length (`exists_isMinimalIntervalLength`)**:
For every $n, m \in \mathbb{N}$, there exists $L \in \mathbb{N}$ satisfying
`IsMinimalIntervalLength n m L`. -/
theorem exists_isMinimalIntervalLength (n m : ℕ) :
    ∃ L : ℕ, IsMinimalIntervalLength n m L := by
  classical
  have hex := exists_hasDivisibleDistinctTuple n m
  exact ⟨Nat.find hex, Nat.find_spec hex, fun L' hL' => Nat.find_min' hex hL'⟩

/-- **Uniqueness of Minimal Interval Length (`isMinimalIntervalLength_unique`)**:
If $L_1$ and $L_2$ both satisfy `IsMinimalIntervalLength n m`, then $L_1 = L_2$. -/
theorem isMinimalIntervalLength_unique {n m L₁ L₂ : ℕ}
    (h₁ : IsMinimalIntervalLength n m L₁) (h₂ : IsMinimalIntervalLength n m L₂) :
    L₁ = L₂ :=
  le_antisymm (h₁.2 L₂ h₂.1) (h₂.2 L₁ h₁.1)

/-!
## Part 2: General Lower Bound $f(n, m) \ge n + 1$ and Exact Evaluation $f(n, 0) = n + 1$
-/

/-- **General Pigeonhole Lower Bound (`n_add_one_le_of_hasDivisibleDistinctTuple`)**:
For any $n \ge 1$ and any $m, L \in \mathbb{N}$, if `HasDivisibleDistinctTuple n m L` holds, then
$n + 1 \le L$. -/
theorem n_add_one_le_of_hasDivisibleDistinctTuple {n m L : ℕ} (hn : 1 ≤ n)
    (h : HasDivisibleDistinctTuple n m L) : n + 1 ≤ L := by
  obtain ⟨a, hinj, ha⟩ := h
  have hsub : Finset.univ.image a ⊆ Finset.Ioo m (m + L) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ioo.mpr ⟨(ha i).1, (ha i).2.1⟩
  have hcard : n ≤ L - 1 := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = (Finset.univ.image a).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.Ioo m (m + L)).card := Finset.card_le_card hsub
      _ = L - 1 := by simp
  have hL_pos : 1 ≤ L := by
    have i0 : Fin n := ⟨0, hn⟩
    have := (ha i0).1
    have := (ha i0).2.1
    omega
  omega

/-- **Exact Value at $m = 0$ (`isMinimalIntervalLength_zero`)**:
For every $n \ge 1$, the minimal interval length for $(n, 0)$ is $n + 1$. -/
theorem isMinimalIntervalLength_zero {n : ℕ} (hn : 1 ≤ n) :
    IsMinimalIntervalLength n 0 (n + 1) := by
  refine ⟨⟨fun i : Fin n => i.1 + 1, ?_, ?_⟩, fun L' hL' =>
    n_add_one_le_of_hasDivisibleDistinctTuple hn hL'⟩
  · intro i j hij
    dsimp at hij
    ext
    omega
  · intro i
    have hi : i.1 < n := i.2
    dsimp
    exact ⟨by omega, by omega, dvd_refl (i.1 + 1)⟩

/-!
## Part 3: Common-Multiple Periodicity of $f(n, m)$
-/

/-- Shifting $m$ by a common multiple $M$ of $1, \ldots, n$ preserves `HasDivisibleDistinctTuple`. -/
theorem hasDivisibleDistinctTuple_add_iff_of_dvd {n m M L : ℕ}
    (hM : ∀ i : Fin n, (i.1 + 1) ∣ M) :
    HasDivisibleDistinctTuple n (m + M) L ↔ HasDivisibleDistinctTuple n m L := by
  constructor
  · rintro ⟨a, hinj, ha⟩
    refine ⟨fun i => a i - M, ?_, ?_⟩
    · intro i j hij
      dsimp at hij
      have hi : M < a i := by have := (ha i).1; omega
      have hj : M < a j := by have := (ha j).1; omega
      exact hinj (by omega)
    · intro i
      obtain ⟨h1, h2, hdvd⟩ := ha i
      dsimp
      refine ⟨by omega, by omega, ?_⟩
      exact Nat.dvd_sub hdvd (hM i)
  · rintro ⟨a, hinj, ha⟩
    refine ⟨fun i => a i + M, ?_, ?_⟩
    · intro i j hij
      dsimp at hij
      exact hinj (by omega)
    · intro i
      obtain ⟨h1, h2, hdvd⟩ := ha i
      dsimp
      exact ⟨by omega, by omega, Nat.dvd_add hdvd (hM i)⟩

/-- Shifting $m$ by a common multiple $M$ of $1, \ldots, n$ preserves `IsMinimalIntervalLength`. -/
theorem isMinimalIntervalLength_add_iff_of_dvd {n m M L : ℕ}
    (hM : ∀ i : Fin n, (i.1 + 1) ∣ M) :
    IsMinimalIntervalLength n (m + M) L ↔ IsMinimalIntervalLength n m L := by
  simp only [IsMinimalIntervalLength, hasDivisibleDistinctTuple_add_iff_of_dvd hM]

/-!
## Part 4: A finite Hall obstruction and scaling

The splice construction is due to Wouter van Doorn [vD26, Lemma 2].
The finite certificate and the qualitative scaling proof below are independently constructed.
-/

/-- Independently formalized from Wouter van Doorn, arXiv:2601.16972, Lemma 2.
The intervals here are open, as in the project definition. -/
theorem hasDivisibleDistinctTuple_splice {k n L : ℕ} (hk : 1 ≤ k)
    (h : HasDivisibleDistinctTuple n (k * k * n) L) :
    HasDivisibleDistinctTuple (k * n) (k * n) ((k * k * n - k * n) + L) := by
  classical
  obtain ⟨a, ha, hb⟩ := h
  have hbase : k * n ≤ k * k * n := by
    calc
      k * n = 1 * (k * n) := by ring
      _ ≤ k * (k * n) := Nat.mul_le_mul_right _ hk
      _ = k * k * n := by ring
  let b : Fin (k * n) → ℕ := fun i =>
    if hi : i.val < n then a ⟨i.val, hi⟩ else k * (i.val + 1)
  refine ⟨b, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val < n <;> by_cases hj : j.val < n
    · have he : a ⟨i.val, hi⟩ = a ⟨j.val, hj⟩ := by simpa [b, hi, hj] using hij
      have he' := congrArg Fin.val (ha he)
      exact Fin.ext he'
    · have hia := (hb ⟨i.val, hi⟩).1
      have hjn : j.val < k * n := j.isLt
      have he : a ⟨i.val, hi⟩ = k * (j.val + 1) := by simpa [b, hi, hj] using hij
      nlinarith
    · have hja := (hb ⟨j.val, hj⟩).1
      have hin : i.val < k * n := i.isLt
      have he : k * (i.val + 1) = a ⟨j.val, hj⟩ := by simpa [b, hi, hj] using hij
      nlinarith
    · have he : k * (i.val + 1) = k * (j.val + 1) := by simpa [b, hi, hj] using hij
      apply Fin.ext
      nlinarith
  · intro i
    by_cases hi : i.val < n
    · obtain ⟨hlo, hup, hd⟩ := hb ⟨i.val, hi⟩
      simpa only [b, dif_pos hi] using
        (show k * n < a ⟨i.val, hi⟩ ∧
          a ⟨i.val, hi⟩ < k * n + (k * k * n - k * n + L) ∧
          (i.val + 1) ∣ a ⟨i.val, hi⟩ from ⟨by omega, by omega, hd⟩)
    · have hin : i.val < k * n := i.isLt
      have hL : 0 < L := by
        have hn : 0 < n := by nlinarith
        have hh := hb ⟨0, hn⟩
        omega
      simp only [b, dif_neg hi]
      refine ⟨?_, ?_, dvd_mul_left _ _⟩
      · nlinarith
      · have hu : k * (i.val + 1) ≤ k * k * n := by nlinarith
        omega


theorem hasDivisibleDistinctTuple_restrict {q N n L : ℕ} (hq : 0 < q) (hN : q * N ≤ n)
    (h : HasDivisibleDistinctTuple n n L) :
    HasDivisibleDistinctTuple N N ((n + L - 1) / q - N + 1) := by
  obtain ⟨a, ha, hb⟩ := h
  let idx : Fin N → Fin n := fun i => ⟨q * (i.val + 1) - 1, by
    have hi := i.isLt
    have : q * (i.val + 1) ≤ q * N := Nat.mul_le_mul_left _ (by omega)
    have : 0 < q * (i.val + 1) := Nat.mul_pos hq (by omega)
    omega⟩
  have hidx (i : Fin N) : (idx i).val + 1 = q * (i.val + 1) := by
    dsimp [idx]
    have : 0 < q * (i.val + 1) := Nat.mul_pos hq (by omega)
    omega
  have hd (i : Fin N) : q ∣ a (idx i) := by
    have hh := (hb (idx i)).2.2
    rw [hidx] at hh
    exact dvd_trans (dvd_mul_right _ _) hh
  have he (i : Fin N) : q * (a (idx i) / q) = a (idx i) :=
    Nat.mul_div_cancel' (hd i)
  refine ⟨fun i => a (idx i) / q, ?_, ?_⟩
  · intro i j hij
    dsimp at hij
    have hij' : a (idx i) = a (idx j) := by rw [← he i, ← he j, hij]
    have hh := congrArg Fin.val (ha hij')
    have hi := hidx i
    have hj := hidx j
    apply Fin.ext
    nlinarith
  · intro i
    obtain ⟨hlo, hup, hdiv⟩ := hb (idx i)
    have hi := he i
    have hlow : N < a (idx i) / q := by
      by_contra hh
      have : q * (a (idx i) / q) ≤ q * N := Nat.mul_le_mul_left _ (by omega)
      omega
    have hu : a (idx i) / q ≤ (n + L - 1) / q :=
      Nat.div_le_div_right (by omega)
    dsimp only
    refine ⟨hlow, by omega, ?_⟩
    rw [hidx] at hdiv
    obtain ⟨t, ht⟩ := hdiv
    have ht' : a (idx i) / q = (i.val + 1) * t := by
      apply Nat.eq_of_mul_eq_mul_left hq
      rw [he i, ht]
      ring
    exact ⟨t, ht'⟩



theorem scale_lower {q N n L A : ℕ} (hq : 0 < q) (hNN : 0 < N)
    (hN : q * N ≤ n) (hA : IsMinimalIntervalLength N N A)
    (h : HasDivisibleDistinctTuple n n L) :
    q * (N + A - 1) < n + L := by
  have hh := hA.2 _ (hasDivisibleDistinctTuple_restrict hq hN h)
  have hp := n_add_one_le_of_hasDivisibleDistinctTuple hNN (hasDivisibleDistinctTuple_restrict hq hN h)
  have htuple := (hasDivisibleDistinctTuple_restrict hq hN h).choose_spec.2 ⟨0, hNN⟩
  have hh' : N + A - 1 ≤ (n + L - 1) / q := by omega
  have hmul := Nat.mul_le_mul_left q hh'
  have hdiv := Nat.div_mul_le_self (n + L - 1) q
  have hL := n_add_one_le_of_hasDivisibleDistinctTuple (by nlinarith) h
  have hhbound : q * (N + A - 1) ≤ n + L - 1 := by
    exact hmul.trans (by simpa [Nat.mul_comm] using hdiv)
  omega

namespace FiniteObstruction

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option cbv.maxSteps 100000000

private def increasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => (a < b) && increasing (b :: xs)

private theorem increasing_sound (xs : List ℕ) (h : increasing xs = true) :
    xs.IsChain (· < ·) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    cases xs with
    | nil => exact .singleton a
    | cons b xs =>
      have hh : a < b ∧ increasing (b :: xs) = true := by
        simpa [increasing, Bool.and_eq_true] using h
      exact List.isChain_cons_cons.mpr ⟨hh.1, ih hh.2⟩

def s : List ℕ := [520,528,540,560,567,576,588,594,600,616,624,630,640,648,660,672,675,700,702,704,720,728,729,750,756,768,780,784,792,800,810,840,864,880,882,891,896,900,912,918,920,924,936,945,952,960,972,980,990,1000,1008,1020,1024,1026,1040,1050,1053,1056,1064,1080,1088,1092,1100,1104,1120,1125,1134,1140,1152,1170,1176,1188,1200,1215,1216,1224,1232,1242,1248,1250,1260,1280,1296,1300,1320,1323,1344,1350,1360,1368,1372,1377,1380,1386,1400,1404,1408,1428,1440,1452,1456,1458,1470,1485,1496,1500,1512,1520,1530,1536,1539,1540,1560,1568,1575,1584,1596,1600,1620,1632,1638,1650,1656,1664,1672,1680,1700,1701,1710,1716,1728,1750,1755,1760,1764,1768,1782,1792,1800,1820,1824,1836,1840,1848,1872,1875,1890,1900,1904,1920,1932,1936,1944,1950,1960,1976,1980,2000,2016,2024,2025,2028,2040,2048,2052,2058,2070,2079,2080,2100,2106,2112,2128,2142,2156,2160,2176,2178,2184,2187,2200,2205,2208,2240,2244,2250,2268,2280,2288,2295,2304,2310,2340,2352,2376,2380,2394,2400,2420,2430,2432,2448,2450,2457,2464,2475,2484,2496,2500,2508,2520,2548,2550,2560,2565,2574,2592,2600,2625,2640,2646,2652,2660,2673,2688,2700,2720,2730,2736,2744,2750,2754,2760,2772,2800,2808,2816,2835,2850,2856,2860,2880,2898,2904,2912,2916,2925,2940,2964,2970,2992,3000,3024,3036,3040,3042,3060,3072,3078,3080,3087,3120,3125,3136,3150,3159,3168,3192,3200,3213,3220,3234,3240,3250,3264,3267,3276,3300,3312,3328,3332,3344,3360,3366,3375,3380,3388,3400,3402,3420,3430,3432,3450,3456,3465,3500,3510,3520,3528,3536,3564,3570,3584,3591,3600,3630,3640,3645,3648,3672,3675,3680,3696,3724,3726,3740,3744,3750,3762,3780,3800,3808,3822,3825,3840,3850,3861,3864,3872,3888,3900,3920,3952,3960,3969,3978,3990,4000,4004,4032,4048,4050,4056,4080,4095,4096,4104,4116,4125,4131,4140,4158,4160,4180,4200,4212,4224,4250,4256,4275,4284,4290,4312,4320,4347,4352,4356,4368,4374,4375,4400,4410,4416,4420,4446,4455,4480,4488,4500,4536,4550,4554,4560,4563,4576,4590,4600,4608,4617,4620,4680,4704,4725,4732,4750,4752,4760,4788,4800,4802,4830,4840,4851,4860,4864,4875,4896,4900,4914,4928,4940,4950,4968,4992,4998,5000]
private theorem s_check : increasing s = true := by decide +kernel
def S : Finset ℕ := ⟨s, (List.isChain_iff_pairwise.mp (increasing_sound _ s_check)).nodup⟩
def t : List ℕ := [5016,5040,5096,5100,5103,5120,5130,5148,5184,5200,5250,5265,5280,5292,5304,5320,5346,5376,5400,5440,5460,5472,5488,5500,5508,5520,5544,5600,5616,5625,5632,5670,5700,5712,5720,5760,5796,5808,5824,5832,5850,5880,5928,5940,5984,6000,6048,6072,6075,6080,6084,6120,6144,6156,6160,6174,6210,6237,6240,6250,6272,6300,6318,6336,6384,6400,6426,6440,6468,6480,6500,6528,6534,6552,6561,6600,6615,6624,6656,6664,6688,6720,6732,6750,6760,6776,6800,6804,6840,6860,6864,6885,6900,6912,6930,7000,7020,7040,7056,7072,7128,7140,7168,7182,7200,7260,7280,7290,7296,7344,7350,7360,7371,7392,7425,7448,7452,7480,7488,7500,7524,7560,7600,7616,7644,7650,7680,7695,7700,7722,7728,7744,7776,7800,7840,7875,7904,7920,7938,7956,7980,8000,8008,8019,8064,8096,8100,8112,8160,8190,8192,8208,8232,8250,8262,8280,8316,8320,8360,8400,8424,8448,8500,8505,8512,8550,8568,8580,8624,8640,8694,8704,8712,8736,8748,8750,8775,8800,8820,8832,8840,8892,8910,8960,8976,9000,9072,9100,9108,9120,9126,9152,9180,9200,9216,9234,9240,9261,9360,9375,9408,9450,9464,9477,9500,9504,9520,9576,9600,9604,9639,9660,9680,9702,9720,9728,9750,9792,9800,9801,9828,9856,9880,9900,9936,9984,9996,10000,10032,10080,10098,10120,10125,10140,10164,10192,10200,10206,10240,10260,10290,10296,10350,10368,10395,10400,10472,10500,10530,10560,10584,10608,10640,10692,10710,10752,10773,10780,10800,10880,10890,10920,10935,10944,10976,11000,11016,11025,11040,11088,11172,11178,11200,11220,11232,11250,11264,11286,11340,11400,11424,11440,11466,11475,11520,11550,11583,11592,11616,11648,11664,11700,11704,11760,11856,11880,11900,11907,11934,11960,11968,11970,12000,12012,12096,12100,12144,12150,12160,12168,12240,12250,12285,12288,12312,12320,12348,12375,12376,12393,12420,12474,12480,12500,12540,12544,12600,12636,12672,12740,12750,12768,12800,12825,12852,12870,12880,12936,12960,13000,13041,13056,13068,13104,13122,13125,13200,13230,13248,13260,13300,13312,13328,13338,13365,13376,13440,13464,13500,13520,13524,13552,13600,13608,13650,13662,13680,13689,13720,13728,13750,13770,13800,13824,13832,13851,13860,14000,14040,14080,14112,14144,14168,14175,14196,14250,14256,14280,14300,14336,14352,14364,14400,14406,14490,14520,14553,14560,14580,14592,14625,14688,14700,14720,14742,14784,14820,14850,14896,14904,14960,14976,14994,15000]
private theorem t_check : increasing t = true := by decide +kernel
def T : Finset ℕ := ⟨t, (List.isChain_iff_pairwise.mp (increasing_sound _ t_check)).nodup⟩
theorem cards : T.card < S.card := by decide +kernel
#print axioms cards

private theorem bounds_check : s.all (fun i => decide (0 < i ∧ i ≤ 5000)) = true := by
  decide +kernel

theorem bounds : ∀ i ∈ S, 0 < i ∧ i ≤ 5000 := by
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp bounds_check i hi)
#print axioms bounds

private theorem closure_check : s.all (fun i =>
    (List.range (15000 / i + 1)).all (fun k =>
      (!(decide (5000 < i * k))) || t.contains (i * k))) = true := by
  decide +kernel

theorem closure : ∀ i ∈ S, ∀ k ∈ Finset.range (15000 / i + 1),
    5000 < i * k → i * k ∈ T := by
  intro i hi k hk hlo
  have h1 := List.all_eq_true.mp closure_check i hi
  have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr (Finset.mem_range.mp hk))
  have hc : t.contains (i * k) = true := by simpa [hlo] using h2
  exact List.contains_iff_mem.mp hc
#print axioms closure

theorem obstruction : ¬ HasDivisibleDistinctTuple 5000 5000 10001 := by
  rintro ⟨a, ha, hb⟩
  let f : ℕ → ℕ := fun i => if hi : 0 < i ∧ i ≤ 5000 then a ⟨i - 1, by omega⟩ else 0
  have maps : Set.MapsTo f S T := by
    intro i hi
    obtain ⟨hip, hin⟩ := bounds i hi
    have hh := hb ⟨i - 1, by omega⟩
    have hdiv : i ∣ a ⟨i - 1, by omega⟩ := by simpa [Nat.sub_add_cancel hip] using hh.2.2
    obtain ⟨t, ht⟩ := hdiv
    have hmem : t ∈ Finset.range (15000 / i + 1) := by
      apply Finset.mem_range.mpr
      have hu : i * t ≤ 15000 := by omega
      have := (Nat.le_div_iff_mul_le hip).mpr (by simpa [Nat.mul_comm] using hu)
      omega
    have hc := closure i hi t hmem (by omega)
    simpa [f, hip, hin, ht] using hc
  have inj : Set.InjOn f S := by
    intro i hi j hj hij
    obtain ⟨hip, hin⟩ := bounds i hi
    obtain ⟨hjp, hjn⟩ := bounds j hj
    have hh : a ⟨i - 1, by omega⟩ = a ⟨j - 1, by omega⟩ := by
      simpa [f, hip, hin, hjp, hjn] using hij
    have := congrArg Fin.val (ha hh)
    dsimp at this
    omega
  exact (Nat.not_le_of_gt cards) (Finset.card_le_card_of_injOn f maps inj)

#print axioms obstruction

end FiniteObstruction

/-- The finite Hall obstruction forces a strict linear surplus at one scale. -/
theorem finite_diagonal_lower {A : ℕ} (hA : IsMinimalIntervalLength 5000 5000 A) :
    10002 ≤ A := by
  by_contra hh
  obtain ⟨a, ha, hb⟩ := hA.1
  apply FiniteObstruction.obstruction
  refine ⟨a, ha, ?_⟩
  intro i
  obtain ⟨hlo, hup, hd⟩ := hb i
  exact ⟨hlo, by omega, hd⟩

/-- Restriction to even indices, combined with van Doorn's splice, produces
an actual gap for the same n and the explicit offset 4n. -/
theorem gap_from_diagonal {n Ln Lm : ℕ} (hn : 0 < n)
    (hLn : IsMinimalIntervalLength n n Ln)
    (hLm : IsMinimalIntervalLength n (4 * n) Lm) :
    Ln - 2 * n - 1 ≤ Lm - Ln := by
  obtain ⟨A, hA⟩ := exists_isMinimalIntervalLength (2 * n) (2 * n)
  have hs := scale_lower (q := 2) (by omega) hn (by omega) hLn hA.1
  have hm : HasDivisibleDistinctTuple n (2 * 2 * n) Lm := by
    simpa using hLm.1
  have hu := hA.2 _ (hasDivisibleDistinctTuple_splice (by omega) hm)
  have hp := n_add_one_le_of_hasDivisibleDistinctTuple hn hLn.1
  have hu' : A ≤ 2 * n + Lm := by
    have he : 2 * 2 * n - 2 * n = 2 * n := by omega
    simpa only [he] using hu
  by_cases ht : Ln ≤ 2 * n + 1
  · omega
  · omega

/-- Unconditional solution of Erdős 711 parts.ii, using a finite Hall
obstruction and scaling. The witness offset is always 4n. -/
theorem erdos_711_parts_ii : ∀ B : ℕ, ∀ᶠ n in atTop,
    ∃ m Lm Ln : ℕ, IsMinimalIntervalLength n m Lm ∧
      IsMinimalIntervalLength n n Ln ∧ B ≤ Lm - Ln := by
  intro B
  filter_upwards [eventually_ge_atTop (5000 * (B + 15001))] with n hn
  obtain ⟨A, hA⟩ := exists_isMinimalIntervalLength 5000 5000
  obtain ⟨Ln, hLn⟩ := exists_isMinimalIntervalLength n n
  obtain ⟨Lm, hLm⟩ := exists_isMinimalIntervalLength n (4 * n)
  have hapos := finite_diagonal_lower hA
  have hnpos : 0 < n := by omega
  have hq : 0 < n / 5000 := by omega
  have hscale := scale_lower hq (by omega) (Nat.div_mul_le_self n 5000) hA hLn.1
  have hrem := Nat.mod_lt n (by omega : 0 < 5000)
  have hdecomp := Nat.div_add_mod n 5000
  have hprod : (n / 5000) * 15001 ≤ (n / 5000) * (5000 + A - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hsurplus : B ≤ Ln - 2 * n - 1 := by omega
  exact ⟨4 * n, Lm, Ln, hLm, hLn,
    hsurplus.trans (gap_from_diagonal hnpos hLn hLm)⟩

/-- **Deduction of `erdos_711.parts.ii` from van Doorn's Lower Bound (`[vD26]`)**:
Combining `exists_isMinimalIntervalLength` with van Doorn's theorem [vD26] that for every $B$ and
all sufficiently large $n$, there exists $m$ whose minimal interval length exceeds $f(n, n)$ by at
least $B$, yields the exact statement of `erdos_711.parts.ii`. -/
theorem erdos_711_parts_ii_of_van_doorn
    (hvd : ∀ B : ℕ, ∀ᶠ n in atTop, ∃ m : ℕ,
      ∀ Lm Ln : ℕ, HasDivisibleDistinctTuple n m Lm →
        IsMinimalIntervalLength n n Ln → B ≤ Lm - Ln) :
    ∀ B : ℕ, ∀ᶠ n in atTop,
      ∃ m Lm Ln : ℕ, IsMinimalIntervalLength n m Lm ∧
        IsMinimalIntervalLength n n Ln ∧ B ≤ Lm - Ln := by
  intro B
  filter_upwards [hvd B] with n ⟨m, hm⟩
  obtain ⟨Lm, hLm⟩ := exists_isMinimalIntervalLength n m
  obtain ⟨Ln, hLn⟩ := exists_isMinimalIntervalLength n n
  exact ⟨m, Lm, Ln, hLm, hLn, hm Lm Ln hLm.1 hLn⟩

/-- FC-compatible name for the unconditional parts.ii statement. -/
theorem erdos_711.parts.ii : ∀ B : ℕ, ∀ᶠ n in atTop,
    ∃ m Lm Ln : ℕ, IsMinimalIntervalLength n m Lm ∧
      IsMinimalIntervalLength n n Ln ∧ B ≤ Lm - Ln :=
  erdos_711_parts_ii

end Erdos711

#print axioms Erdos711.exists_isMinimalIntervalLength
#print axioms Erdos711.isMinimalIntervalLength_unique
#print axioms Erdos711.n_add_one_le_of_hasDivisibleDistinctTuple
#print axioms Erdos711.isMinimalIntervalLength_zero
#print axioms Erdos711.isMinimalIntervalLength_add_iff_of_dvd
#print axioms Erdos711.hasDivisibleDistinctTuple_splice
#print axioms Erdos711.hasDivisibleDistinctTuple_restrict
#print axioms Erdos711.scale_lower
#print axioms Erdos711.finite_diagonal_lower
#print axioms Erdos711.gap_from_diagonal
#print axioms Erdos711.erdos_711_parts_ii
#print axioms Erdos711.erdos_711_parts_ii_of_van_doorn

#print axioms Erdos711.erdos_711.parts.ii
