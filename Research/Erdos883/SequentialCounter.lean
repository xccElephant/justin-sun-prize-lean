import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Lean.Elab.Tactic.Omega

/-!
# Prefix counts for sequential at-most counters

`i` is the number of processed inputs, so the prefix consists of indices strictly
below `i`. `aux P i j` uses zero-based threshold indices: it means that at least
`j + 1` inputs in that prefix are true. `atLeast P i t` exposes the corresponding
one-based threshold convention (and also permits the vacuous threshold `t = 0`).

These are generic counting and auxiliary-assignment lemmas for checking clauses
of a Sinz at-most encoding. They do not define a CNF or prove correctness of a
complete encoding.
-/

namespace Erdos883Research.SequentialCounter

variable (P : ℕ → Prop) [DecidablePred P]

/-- Number of true inputs among indices `0, ..., i - 1`. -/
def prefixTrueCount (i : ℕ) : ℕ := ((Finset.range i).filter P).card

@[simp] theorem prefixTrueCount_zero : prefixTrueCount P 0 = 0 := by
  simp [prefixTrueCount]

/-- Processing input `i` adds exactly its truth indicator. -/
theorem prefixTrueCount_step (i : ℕ) :
    prefixTrueCount P (i + 1) = prefixTrueCount P i + if P i then 1 else 0 := by
  by_cases hi : P i
  · simp [prefixTrueCount, Finset.range_add_one, Finset.filter_insert, hi,
      Finset.card_insert_of_notMem]
  · simp [prefixTrueCount, Finset.range_add_one, Finset.filter_insert, hi]

theorem prefixTrueCount_step_of_true {i : ℕ} (hi : P i) :
    prefixTrueCount P (i + 1) = prefixTrueCount P i + 1 := by
  simp [prefixTrueCount_step, hi]

theorem prefixTrueCount_step_of_false {i : ℕ} (hi : ¬ P i) :
    prefixTrueCount P (i + 1) = prefixTrueCount P i := by
  simp [prefixTrueCount_step, hi]

@[simp] theorem prefixTrueCount_one :
    prefixTrueCount P 1 = if P 0 then 1 else 0 := by
  simpa using prefixTrueCount_step P 0

theorem prefixTrueCount_one_of_true (h : P 0) : prefixTrueCount P 1 = 1 := by
  simp [h]

theorem prefixTrueCount_one_of_false (h : ¬ P 0) : prefixTrueCount P 1 = 0 := by
  simp [h]

theorem prefixTrueCount_mono : Monotone (prefixTrueCount P) := by
  intro i n hin
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha, hPa⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨Finset.range_mono hin ha, hPa⟩

theorem prefixTrueCount_le_total {i n : ℕ} (hin : i ≤ n) :
    prefixTrueCount P i ≤ prefixTrueCount P n :=
  prefixTrueCount_mono P hin

theorem prefixTrueCount_le_length (i : ℕ) : prefixTrueCount P i ≤ i := by
  simpa [prefixTrueCount] using Finset.card_filter_le (Finset.range i) P

theorem prefixTrueCount_le_succ (i : ℕ) :
    prefixTrueCount P i ≤ prefixTrueCount P (i + 1) :=
  prefixTrueCount_mono P (Nat.le_succ i)

theorem prefixTrueCount_pos_of_true {i : ℕ} (hi : P i) :
    1 ≤ prefixTrueCount P (i + 1) := by
  have hstep := prefixTrueCount_step_of_true P hi
  omega

/-- The arithmetic form of the input-and-counter increment clause. -/
theorem prefixTrueCount_increment {i t : ℕ} (hi : P i)
    (ht : t ≤ prefixTrueCount P i) : t + 1 ≤ prefixTrueCount P (i + 1) := by
  have hstep := prefixTrueCount_step_of_true P hi
  omega

/-- A true next input leaves strictly fewer than `k` true inputs before it,
provided the total prefix of length `n` contains at most `k` true inputs. -/
theorem prefixTrueCount_lt_of_true_of_total_le {i n k : ℕ}
    (htotal : prefixTrueCount P n ≤ k) (hin : i < n) (hi : P i) :
    prefixTrueCount P i < k := by
  have hstep := prefixTrueCount_step_of_true P hi
  have hle := prefixTrueCount_le_total P (show i + 1 ≤ n by omega)
  omega

/-- Threshold-indexed assignment; threshold `1` means at least one true input. -/
def atLeast (i t : ℕ) : Prop := t ≤ prefixTrueCount P i

/-- Zero-based auxiliary assignment: column `j` means at least `j + 1`. -/
def aux (i j : ℕ) : Prop := j + 1 ≤ prefixTrueCount P i

theorem aux_iff_atLeast (i j : ℕ) : aux P i j ↔ atLeast P i (j + 1) :=
  Iff.rfl

@[simp] theorem aux_zero (j : ℕ) : ¬ aux P 0 j := by
  simp [aux]

@[simp] theorem aux_one_zero : aux P 1 0 ↔ P 0 := by
  by_cases h : P 0 <;> simp [aux, h]

/-- The initial singleton row has no true higher columns. -/
theorem aux_one_higher {j : ℕ} (hj : 1 ≤ j) : ¬ aux P 1 j := by
  have hle := prefixTrueCount_le_length P 1
  unfold aux
  omega

/-- A true input forces the first zero-based auxiliary column. -/
theorem aux_of_true {i : ℕ} (hi : P i) : aux P (i + 1) 0 :=
  prefixTrueCount_pos_of_true P hi

theorem aux_increment {i j : ℕ} (hi : P i) (hs : aux P i j) :
    aux P (i + 1) (j + 1) :=
  prefixTrueCount_increment P hi hs

theorem aux_propagate {i j : ℕ} (hs : aux P i j) : aux P (i + 1) j :=
  Nat.le_trans hs (prefixTrueCount_le_succ P i)

theorem aux_mono {i n j : ℕ} (hin : i ≤ n) (hs : aux P i j) : aux P n j :=
  Nat.le_trans hs (prefixTrueCount_le_total P hin)

/-- Standard overflow prohibition, stated with the actual threshold `k`. -/
theorem atLeast_no_overflow {i n k : ℕ}
    (htotal : prefixTrueCount P n ≤ k) (hin : i < n) (hi : P i) :
    ¬ atLeast P i k := by
  have hlt := prefixTrueCount_lt_of_true_of_total_le P htotal hin hi
  unfold atLeast
  omega

/-- Zero-based version of the overflow clause: column `j` has threshold `j + 1`. -/
theorem aux_no_overflow {i n j : ℕ}
    (htotal : prefixTrueCount P n ≤ j + 1) (hin : i < n) (hi : P i) :
    ¬ aux P i j :=
  atLeast_no_overflow P htotal hin hi

/-- In particular, a total bound `k` rules out zero-based column `k` before a
true input. `aux_no_overflow` also handles the stronger column `k - 1` for `k > 0`. -/
theorem aux_not_at_bound {i n k : ℕ}
    (htotal : prefixTrueCount P n ≤ k) (hin : i < n) (hi : P i) :
    ¬ aux P i k := by
  apply aux_no_overflow P (n := n) (hin := hin) (hi := hi)
  omega

/-- A true input forces threshold `1` in the one-based convention. -/
theorem atLeast_of_true {i : ℕ} (hi : P i) : atLeast P (i + 1) 1 :=
  prefixTrueCount_pos_of_true P hi

theorem atLeast_increment {i t : ℕ} (hi : P i) (hs : atLeast P i t) :
    atLeast P (i + 1) (t + 1) :=
  prefixTrueCount_increment P hi hs

theorem atLeast_propagate {i t : ℕ} (hs : atLeast P i t) :
    atLeast P (i + 1) t :=
  Nat.le_trans hs (prefixTrueCount_le_succ P i)

end Erdos883Research.SequentialCounter
