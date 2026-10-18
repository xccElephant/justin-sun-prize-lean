/-
Repository: https://github.com/xccElephant/justin-sun-prize-lean
Formalization author: xccElephant (Ethan Xiang)
Toolchain: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 131 (JSP-000137): Non-Dividing Sets in $\{1, \dots, N\}$

*Problem Statement (Erdős Problem 131 / JSP-000137):*
Let $F(N)$ be the maximal size of a subset $A \subseteq \{1, \dots, N\}$ such that no $a \in A$
divides the sum of any nonempty subset of $A \setminus \{a\}$ (such a set $A$ is called
*non-dividing*). Is it true that $F(N) > N^{1/2 - o(1)}$?

*Mathematical Background & Resolution:*
- **Erdős, Lev, Rauzy, Sándor, and Sárközy [ELRSS99]** introduced Property P (no $a \in A$ divides
  a nonempty sum of larger elements of $A$) and Property Q (non-dividing sets), proving
  $F(N) \le P(N) < 3\sqrt{N} + 1$ and $F(N) \gg N^{1/5}$ (combining Straus's transfer theorem with
  Bosznay's [Bo89] non-averaging set construction).
- Every non-dividing set is **non-averaging**: if $a \in A$ were the average of a nonempty subset
  $S \subseteq A \setminus \{a\}$, then $\sum_{x \in S} x = |S| \cdot a$, so $a$ would divide
  $\sum_{x \in S} x$.
- **Pham and Zakharov [PhZa24]** proved that every non-averaging subset of $\{1, \dots, N\}$ has
  size at most $N^{1/4 + o(1)}$, which implies $F(N) \le N^{1/4 + o(1)}$ and refutes
  $F(N) > N^{1/2 - o(1)}$.
- The exact asymptotic exponent of $F(N)$ between $N^{1/5}$ and $N^{1/4 + o(1)}$ remains open
  (hence `JSP-000137` is listed as Open in the catalog).

*What This File Proves (Zero `sorry`):*
1. **Core Definitions & Extremal API**: `NonDividing`, decidability, `F(N)`, attainment of `F(N)`,
   monotonicity `F_mono`, basic bounds `1 ≤ F(N) ≤ N`, and exact values for small $N$
   ($F(0)=0, F(1)=1, F(2)=1, F(3)=2, F(4)=2, F(5)=2, F(6)=2, F(7)=3$).
2. **Primitive Set Property**: Every non-dividing set is primitive ($a \nmid b$ for distinct
   $a, b \in A$).
3. **Reduction to Non-Averaging Sets**: Every non-dividing set is non-averaging
   (`NonDividing.nonAveraging`), yielding $F(N) \le H_{\text{nonavg}}(N)$ (`F_le_H_nonavg`).
4. **Unconditional Pigeonhole Bound**: Using prefix sums modulo $a$ and the Pigeonhole Principle,
   every positive element $a$ of a non-dividing set $A$ satisfies $|A| \le a$
   (`card_le_of_mem_nonDividing`). Consequently, $2 F(N) \le N + 1$, i.e.,
   $F(N) \le (N + 1) / 2$ for all $N \ge 1$ (`two_mul_F_le`, `F_le_half`).
5. **ELRSS Property P & Lower Bound Construction**: Every non-dividing set satisfies Property P
   (`NonDividing.propertyP`), so $F(N) \le P(N)$ (`F_le_P`), and for $k(k-1) < N$ the top interval
   $[N - k + 1, N]$ satisfies Property P (`propertyP_Icc_top`), giving $k \le P(N)$.
6. **Asymptotic Disproof of $F(N) > N^{1/2 - o(1)}$**: Any sub-square-root bound
   $F(N) \le N^{\alpha + o(1)}$ with $\alpha < 1/2$ (and in particular the Pham–Zakharov bound
   $\alpha = 1/4$) implies `erdos_131` (`erdos_131_of_subSqrtBound`, `erdos_131_of_pham_zakharov`).
-/

open Filter Topology
open scoped BigOperators

namespace Erdos131

/-! ## Section 1: Definitions and Basic API -/

/-- A finite set $A$ of naturals is *non-dividing* if no $a \in A$ divides the sum of the
elements of any nonempty subset $S \subseteq A \setminus \{a\}$. -/
def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S.Nonempty → ¬ a ∣ ∑ x ∈ S, x

instance (A : Finset ℕ) : Decidable (NonDividing A) := by
  unfold NonDividing; infer_instance

/-- $F(N)$ is the maximal size of a non-dividing subset of $\{1, \dots, N\}$. -/
def F (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonDividing).sup Finset.card

/-- $F(N)$ is attained: some non-dividing $A \subseteq \{1, \dots, N\}$ has exactly $F(N)$
elements. -/
theorem exists_card_eq_F (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, NonDividing A ∧ A.card = F N := by
  obtain ⟨A, hA, h⟩ := Finset.exists_mem_eq_sup
    (((Finset.Icc 1 N).powerset).filter NonDividing)
    ⟨∅, by simp [NonDividing]⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, h.symm⟩

/-- Every non-dividing $A \subseteq \{1, \dots, N\}$ has at most $F(N)$ elements. -/
theorem card_le_F {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hnd : NonDividing A) :
    A.card ≤ F N :=
  Finset.le_sup (f := Finset.card) (by simp [hA, hnd])

/-- Subsets of non-dividing sets are non-dividing. -/
theorem NonDividing.mono {A B : Finset ℕ} (hAB : A ⊆ B) (hB : NonDividing B) :
    NonDividing A := by
  intro a ha S hS hne
  exact hB a (hAB ha) S (hS.trans (Finset.erase_subset_erase a hAB)) hne

/-- Trivial upper bound: $F(N) \le N$. -/
theorem F_le (N : ℕ) : F N ≤ N := by
  obtain ⟨A, hA, -, h⟩ := exists_card_eq_F N
  simpa [← h] using Finset.card_le_card hA

/-- $F$ is monotone. -/
theorem F_mono : Monotone F := fun _ _ hMN =>
  let ⟨_, hA, hnd, h⟩ := exists_card_eq_F _
  h ▸ card_le_F (hA.trans (Finset.Icc_subset_Icc_right hMN)) hnd

/-- Trivial lower bound: for $N \ge 1$, the singleton $\{N\}$ is non-dividing, so
$1 \le F(N)$. -/
theorem one_le_F {N : ℕ} (hN : 1 ≤ N) : 1 ≤ F N := by
  have h := card_le_F (N := N) (A := {N}) (by simp [hN]) (by
    intro a ha S hS hne
    have : S = ∅ := by simpa [Finset.mem_singleton.1 ha] using hS
    simp [this] at hne)
  simpa using h

/-- Exact values of $F(N)$ for $0 \le N \le 7$. -/
theorem F_small_values :
    F 0 = 0 ∧ F 1 = 1 ∧ F 2 = 1 ∧ F 3 = 2 ∧ F 4 = 2 ∧ F 5 = 2 ∧ F 6 = 2 ∧ F 7 = 3 := by
  decide

/-! ## Section 2: Primitivity and Relation to Non-Averaging Sets -/

/-- Every non-dividing set is primitive: no element divides any other distinct element. -/
theorem NonDividing.not_dvd_of_ne {A : Finset ℕ} (hnd : NonDividing A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) : ¬ a ∣ b := by
  have hS : ({b} : Finset ℕ) ⊆ A.erase a := by
    simp [Finset.singleton_subset_iff, hb, hne.symm]
  have h := hnd a ha {b} hS (Finset.singleton_nonempty b)
  simpa using h

/-- A finite set $A$ of naturals is *non-averaging* if no $a \in A$ is the arithmetic mean of
any nonempty subset $S \subseteq A \setminus \{a\}$. -/
def NonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S.Nonempty → ∑ x ∈ S, x ≠ S.card * a

instance (A : Finset ℕ) : Decidable (NonAveraging A) := by
  unfold NonAveraging; infer_instance

/-- $H_{\text{nonavg}}(N)$ is the maximal size of a non-averaging subset of $\{1, \dots, N\}$. -/
def H_nonavg (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonAveraging).sup Finset.card

/-- Every non-dividing set is non-averaging. -/
theorem NonDividing.nonAveraging {A : Finset ℕ} (hnd : NonDividing A) : NonAveraging A := by
  intro a ha S hS hne hsum
  apply hnd a ha S hS hne
  exact ⟨S.card, by linarith⟩

/-- For every $N$, the maximum non-dividing set size $F(N)$ is at most the maximum non-averaging
set size $H_{\text{nonavg}}(N)$. -/
theorem F_le_H_nonavg (N : ℕ) : F N ≤ H_nonavg N := by
  obtain ⟨A, hA, hnd, hcard⟩ := exists_card_eq_F N
  rw [← hcard]
  exact Finset.le_sup (f := Finset.card) (by simp [hA, hnd.nonAveraging])

/-! ## Section 3: Unconditional Pigeonhole Bound ($|A| \le \min A$ and $F(N) \le (N+1)/2$) -/

/-- Given a finite set $B$ and $m \le |B|$, there is a nested chain of subsets
$T_0 \subseteq T_1 \subseteq \dots \subseteq T_m \subseteq B$ with $|T_i| = i$. -/
theorem exists_nested_chain_of_le_card {B : Finset ℕ} :
    ∀ m ≤ B.card, ∃ T : ℕ → Finset ℕ,
      (∀ i ≤ m, T i ⊆ B ∧ (T i).card = i) ∧
      (∀ i < m, T i ⊆ T (i + 1)) := by
  intro m hm
  induction m with
  | zero =>
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      simp
    · intro i hi
      omega
  | succ m ih =>
    obtain ⟨T, hTB, hmono⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨hTm_sub, hTm_card⟩ := hTB m (le_refl m)
    obtain ⟨x, hxB, hxTm⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (by omega : (T m).card < B.card)
    let T' : ℕ → Finset ℕ := fun i => if i ≤ m then T i else insert x (T m)
    refine ⟨T', ?_, ?_⟩
    · intro i hi
      rcases Nat.of_le_succ hi with him | rfl
      · dsimp [T']
        rw [if_pos him]
        exact hTB i him
      · dsimp [T']
        rw [if_neg (by omega)]
        refine ⟨Finset.insert_subset hxB hTm_sub, ?_⟩
        rw [Finset.card_insert_of_notMem hxTm, hTm_card]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with him | rfl
      · dsimp [T']
        rw [if_pos (Nat.le_of_lt him), if_pos (Nat.succ_le_of_lt him)]
        exact hmono i him
      · dsimp [T']
        rw [if_pos (le_refl i), if_neg (by omega)]
        exact Finset.subset_insert x (T i)

/-- Monotonicity of a step-monotone chain of finsets. -/
theorem chain_subset_of_le {T : ℕ → Finset ℕ} {m : ℕ}
    (hmono : ∀ i < m, T i ⊆ T (i + 1)) {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) :
    T i ⊆ T j := by
  induction j with
  | zero =>
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hij
    subst hi0
    exact Finset.Subset.refl _
  | succ j ih =>
    rcases Nat.of_le_succ hij with hij' | rfl
    · exact (ih hij' (Nat.le_of_succ_le hjm)).trans (hmono j (Nat.lt_of_succ_le hjm))
    · exact Finset.Subset.refl _

/-- **Pigeonhole Bound for Non-Dividing Sets**:
For any non-dividing set $A$ and any positive element $a \in A$, we have $|A| \le a$.
Proof: If $|A \setminus \{a\}| \ge a$, a nested chain $T_0 \subset T_1 \subset \dots \subset T_a$
of subsets of $A \setminus \{a\}$ produces $a + 1$ prefix sums. By the Pigeonhole Principle modulo
$a$, two sums $T_i \subset T_j$ have the same residue mod $a$, so $T_j \setminus T_i$ is a nonempty
subset of $A \setminus \{a\}$ whose sum is divisible by $a$. -/
theorem card_le_of_mem_nonDividing {A : Finset ℕ} (hnd : NonDividing A)
    {a : ℕ} (ha : a ∈ A) (ha_pos : 0 < a) : A.card ≤ a := by
  by_contra hlt
  have hB_card : a ≤ (A.erase a).card := by
    have hcard_erase := Finset.card_erase_add_one ha
    omega
  obtain ⟨T, hTB, hmono⟩ := exists_nested_chain_of_le_card a hB_card
  let f : Fin (a + 1) → Fin a := fun i =>
    ⟨(∑ x ∈ T i.val, x) % a, Nat.mod_lt _ ha_pos⟩
  have hcard_lt : Fintype.card (Fin a) < Fintype.card (Fin (a + 1)) := by
    simp
  obtain ⟨i, j, hij_ne, hf_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard_lt
  have hmod_eq : (∑ x ∈ T i.val, x) % a = (∑ x ∈ T j.val, x) % a :=
    congrArg Fin.val hf_eq
  suffices ∀ u v : Fin (a + 1), u < v →
      (∑ x ∈ T u.val, x) % a = (∑ x ∈ T v.val, x) % a → False by
    rcases lt_or_gt_of_ne hij_ne with hlt_ij | hgt_ij
    · exact this i j hlt_ij hmod_eq
    · exact this j i hgt_ij hmod_eq.symm
  intro u v huv hmod
  have huv_le : u.val ≤ v.val := Nat.le_of_lt huv
  have hv_le : v.val ≤ a := Nat.le_of_lt_succ v.isLt
  have hu_le : u.val ≤ a := huv_le.trans hv_le
  have hsub : T u.val ⊆ T v.val := chain_subset_of_le hmono huv_le hv_le
  let S := T v.val \ T u.val
  have hSB : S ⊆ A.erase a := Finset.sdiff_subset.trans (hTB v.val hv_le).1
  have hS_card : S.card = v.val - u.val := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, (hTB v.val hv_le).2, (hTB u.val hu_le).2]
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsum_add : ∑ x ∈ S, x + ∑ x ∈ T u.val, x = ∑ x ∈ T v.val, x :=
    Finset.sum_sdiff hsub
  have hdiv_eq :
      ∑ x ∈ S, x + a * ((∑ x ∈ T u.val, x) / a) = a * ((∑ x ∈ T v.val, x) / a) := by
    have hU := Nat.div_add_mod (∑ x ∈ T u.val, x) a
    have hV := Nat.div_add_mod (∑ x ∈ T v.val, x) a
    linarith
  have hdvd_S : a ∣ ∑ x ∈ S, x := by
    refine ⟨(∑ x ∈ T v.val, x) / a - (∑ x ∈ T u.val, x) / a, ?_⟩
    rw [Nat.mul_sub]
    omega
  exact hnd a ha S hSB hS_ne hdvd_S

/-- Unconditional upper bound: for every $N \ge 1$, $2 F(N) \le N + 1$. -/
theorem two_mul_F_le {N : ℕ} (hN : 1 ≤ N) : 2 * F N ≤ N + 1 := by
  obtain ⟨A, hA, hnd, hcard⟩ := exists_card_eq_F N
  have hF_pos : 1 ≤ F N := one_le_F hN
  have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
  let a := A.min' hA_ne
  have ha_mem : a ∈ A := Finset.min'_mem A hA_ne
  have ha_Icc : a ∈ Finset.Icc 1 N := hA ha_mem
  have ha_pos : 0 < a := by
    simp only [Finset.mem_Icc] at ha_Icc
    omega
  have hcard_le_a : A.card ≤ a := card_le_of_mem_nonDividing hnd ha_mem ha_pos
  have hA_sub_aN : A ⊆ Finset.Icc a N := by
    intro x hx
    simp only [Finset.mem_Icc]
    exact ⟨Finset.min'_le A x hx, (Finset.mem_Icc.mp (hA hx)).2⟩
  have hcard_le_Icc : A.card ≤ N + 1 - a := by
    have := Finset.card_le_card hA_sub_aN
    simpa [Nat.card_Icc] using this
  have ha_le_N : a ≤ N := (Finset.mem_Icc.mp ha_Icc).2
  omega

/-- For every $N \ge 1$, $F(N) \le (N + 1) / 2$. -/
theorem F_le_half {N : ℕ} (hN : 1 ≤ N) : F N ≤ (N + 1) / 2 := by
  have := two_mul_F_le hN
  omega

/-! ## Section 4: ELRSS Property P and Explicit Lower Bound Construction -/

/-- A set $A \subseteq \mathbb{N}$ satisfies *Property P* (Erdős–Lev–Rauzy–Sándor–Sárközy [ELRSS99])
if no $a \in A$ divides the sum of any nonempty subset of elements of $A$ strictly greater than
$a$. -/
def PropertyP (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.filter (a < ·), S.Nonempty → ¬ a ∣ ∑ x ∈ S, x

instance (A : Finset ℕ) : Decidable (PropertyP A) := by
  unfold PropertyP; infer_instance

/-- $P(N)$ is the maximal size of a subset of $\{1, \dots, N\}$ with Property P. -/
def P (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter PropertyP).sup Finset.card

/-- Every non-dividing set satisfies Property P. -/
theorem NonDividing.propertyP {A : Finset ℕ} (hnd : NonDividing A) : PropertyP A := by
  intro a ha S hS hne
  have hS_erase : S ⊆ A.erase a := by
    intro x hx
    have hx' := hS hx
    simp only [Finset.mem_filter] at hx'
    exact Finset.mem_erase.mpr ⟨ne_of_gt hx'.2, hx'.1⟩
  exact hnd a ha S hS_erase hne

/-- For every $N$, $F(N) \le P(N)$. -/
theorem F_le_P (N : ℕ) : F N ≤ P N := by
  obtain ⟨A, hA, hnd, hcard⟩ := exists_card_eq_F N
  rw [← hcard]
  exact Finset.le_sup (f := Finset.card) (by simp [hA, hnd.propertyP])

/-- **ELRSS Theorem 2 Lower Bound Construction**:
If $1 \le k \le N$ and $k(k - 1) < N$, then the top interval $\{N - k + 1, \dots, N\}$ satisfies
Property P, because for any $a \in [N - k + 1, N]$ and any nonempty subset $S$ of larger elements in
$[N - k + 1, N]$ of size $l \le k - 1$, its sum lies strictly between $l a$ and $(l + 1) a$. -/
theorem propertyP_Icc_top {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hk2 : k * (k - 1) < N) :
    PropertyP (Finset.Icc (N - k + 1) N) := by
  intro a ha S hS hne hdvd
  simp only [Finset.mem_Icc] at ha
  have hS_Icc : S ⊆ Finset.Icc (N - k + 2) N := by
    intro x hx
    have hx' := hS hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx' ⊢
    omega
  have hl_pos : 1 ≤ S.card := Finset.card_pos.mpr hne
  have hl_le : S.card ≤ k - 1 := by
    have := Finset.card_le_card hS_Icc
    rw [Nat.card_Icc] at this
    omega
  have hsum_gt : S.card * a < ∑ x ∈ S, x := by
    have hsum_ge : ∑ _x ∈ S, (a + 1) ≤ ∑ x ∈ S, x :=
      Finset.sum_le_sum (fun x hx => by
        have hx' := Finset.mem_filter.mp (hS hx)
        omega)
    simp only [Finset.sum_const, smul_eq_mul] at hsum_ge
    nlinarith
  have hsum_lt : ∑ x ∈ S, x < (S.card + 1) * a := by
    have hsum_le : ∑ x ∈ S, x ≤ ∑ _x ∈ S, N :=
      Finset.sum_le_sum (fun x hx => by
        have hx' := Finset.mem_Icc.mp (Finset.mem_filter.mp (hS hx)).1
        exact hx'.2)
    simp only [Finset.sum_const, smul_eq_mul] at hsum_le
    have hprod : (S.card + 1) * (k - 1) ≤ k * (k - 1) :=
      Nat.mul_le_mul_right (k - 1) (by omega)
    have ha_add : N + 1 ≤ a + k := by omega
    have hk_eq : (k - 1) + 1 = k := by omega
    nlinarith
  obtain ⟨m, hm⟩ := hdvd
  have hlt1 : S.card * a < a * m := by linarith
  have hlt2 : a * m < (S.card + 1) * a := by linarith
  have hm_gt : S.card < m := by nlinarith
  have hm_lt : m < S.card + 1 := by nlinarith
  omega

/-- Whenever $1 \le k \le N$ and $k(k - 1) < N$, we have $k \le P(N)$. -/
theorem le_P_of_mul_pred_lt {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hk2 : k * (k - 1) < N) :
    k ≤ P N := by
  have hsub : Finset.Icc (N - k + 1) N ⊆ Finset.Icc 1 N :=
    Finset.Icc_subset_Icc (by omega) (le_refl N)
  have hcard : (Finset.Icc (N - k + 1) N).card = k := by
    rw [Nat.card_Icc]
    omega
  rw [← hcard]
  exact Finset.le_sup (f := Finset.card) (by simp [hsub, propertyP_Icc_top hk1 hkN hk2])

/-! ## Section 5: Disproof of $F(N) > N^{1/2 - o(1)}$ (`erdos_131`) -/

/-- The general sub-square-root upper bound hypothesis $F(N) \le N^{\alpha + o(1)}$. -/
def SubSqrtBound (α : ℝ) : Prop :=
  ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
    ∀ᶠ N : ℕ in atTop, (F N : ℝ) ≤ (N : ℝ) ^ (α + f N)

/-- Pham and Zakharov's (2024) theorem (`SubSqrtBound (1 / 4)`):
every non-averaging (and hence every non-dividing) subset of $\{1, \dots, N\}$ has size at most
$N^{1/4 + o(1)}$. -/
def PhamZakharovBound : Prop := SubSqrtBound ((1 : ℝ) / 4)

/-- Any upper bound $F(N) \le N^{\alpha + o(1)}$ with $\alpha < 1/2$ refutes the conjecture
$F(N) > N^{1/2 - o(1)}$. -/
theorem erdos_131_of_subSqrtBound {α : ℝ} (hα : α < 1 / 2) (hbound : SubSqrtBound α) :
    ¬ ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 - f N) < (F N : ℝ) := by
  rintro ⟨f, hf, hlow⟩
  obtain ⟨g, hg, hup⟩ := hbound
  let ε : ℝ := (1 / 2 - α) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hf' : ∀ᶠ N : ℕ in atTop, f N < ε := hf.eventually (gt_mem_nhds hε)
  have hg' : ∀ᶠ N : ℕ in atTop, g N < ε := hg.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN1, h1, h2, h3, h4⟩ :=
    ((eventually_ge_atTop 1).and (hlow.and (hup.and (hf'.and hg')))).exists
  have hle : (N : ℝ) ^ (α + g N) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - f N) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by dsimp [ε] at h3 h4; linarith)
  linarith

/-- **Erdős Problem 131 (from Pham–Zakharov [PhZa24])**:
The Pham–Zakharov bound $F(N) \le N^{1/4 + o(1)}$ implies that $F(N) > N^{1/2 - o(1)}$ does not
hold. -/
theorem erdos_131_of_pham_zakharov (hpz : PhamZakharovBound) :
    ¬ ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 - f N) < (F N : ℝ) :=
  erdos_131_of_subSqrtBound (by norm_num) hpz

#print axioms exists_card_eq_F
#print axioms F_small_values
#print axioms NonDividing.nonAveraging
#print axioms F_le_H_nonavg
#print axioms card_le_of_mem_nonDividing
#print axioms two_mul_F_le
#print axioms F_le_half
#print axioms propertyP_Icc_top
#print axioms le_P_of_mul_pred_lt
#print axioms erdos_131_of_subSqrtBound
#print axioms erdos_131_of_pham_zakharov

end Erdos131
