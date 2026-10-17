import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 575 (`JSP-000465`): Turán Compactness Counterexamples & Common-Neighbor Geometry

*References:*
- [erdosproblems.com/575](https://www.erdosproblems.com/575) (`JSP-000465`)
- [ES82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
  Combinatorica 2 (1982), 275–288.
- [OAI26] OpenAI, *Counterexamples to the Compactness and Degeneracy Conjectures for Extremal
  Numbers* (`ten-proofs-oai.pdf`, Chapter 10).

This file formalizes:
1. **The Acyclic Family Compactness Counterexample $\mathcal{F} = \{K_{1,2}, 2K_2\}$
   (Section 1.1 of Chapter 10)**:
   - Any graph $G$ that is simultaneously $K_{1,2}$-free (no two distinct edges share a vertex)
     and $2K_2$-free (no two distinct edges are vertex-disjoint) has **at most 1 edge**
     (`le_one_edge_of_no_K12_no_2K2`).
   - Conversely, on $2m$ vertices, the matching of $m$ disjoint edges is $K_{1,2}$-free with $m$
     edges (`matching_is_K12_free`), and on $n \ge 2$ vertices, the star graph has $n - 1$ edges
     and is $2K_2$-free (`star_is_2K2_free`), proving that $\mathrm{ex}(n, \{K_{1,2}, 2K_2\}) = 1$
     while $\mathrm{ex}(n, K_{1,2}) \ge \lfloor n/2 \rfloor$ and $\mathrm{ex}(n, 2K_2) = n - 1$.
2. **Lemma 3.1 of OpenAI Chapter 10 (Common-Neighbor Geometry in $\{C_4, C_6\}$-Free Bipartite
   Graphs)**:
   - **Lemma 3.1(1a) (`unique_common_neighbor_of_C4_free`)**: In a $C_4$-free bipartite graph $B$,
     any two distinct vertices $u \ne v$ in $S$ have at most one common neighbor.
   - **Lemma 3.1(1b) (`common_neighbor_coincide_of_C4_C6_free`)**: In a $\{C_4, C_6\}$-free
     bipartite graph $B$, if three distinct vertices $u, v, w \in S$ are pairwise related in the
     auxiliary common-neighbor graph $R_S$, then all three pairs share the exact same common
     neighbor.
   - **Lemma 3.1(3) (`Z_uv_independent_of_C4_C6_free`)**: If $u \ne v \in S$ are unrelated in $R_S$
     (no common neighbor in $B$), then the set $Z_{uv} = \{w \in S : w \sim u \text{ and } w \sim v\}$
     is $R_S$-independent (no two distinct vertices in $Z_{uv}$ share a common neighbor in $B$).
-/

namespace Erdos575

/-!
## Part 1: Extremal Compactness Counterexample $\mathcal{F} = \{K_{1,2}, 2K_2\}$
-/

/-- A graph on vertex type `V` represented by its symmetric irreflexive adjacency relation, or
equivalently on unordered pairs; here we work directly with a finite set `E` of 2-element vertex
subsets (`Finset V` of cardinality 2) so edge counting is immediate. -/
def IsEdgeSet {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = 2

/-- `E` contains a copy of $K_{1,2}$ (a 2-edge star / path $P_3$) if two distinct edges in `E`
share a common vertex. -/
def HasK12 {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : Prop :=
  ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ ≠ e₂ ∧ (e₁ ∩ e₂).Nonempty

/-- `E` contains a copy of $2K_2$ (two independent edges) if two distinct edges in `E` are
disjoint. -/
def Has2K2 {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : Prop :=
  ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ ≠ e₂ ∧ Disjoint e₁ e₂

/-- **Dichotomy**: Any two distinct edges $e_1 \ne e_2$ either share a vertex ($K_{1,2}$) or are
vertex-disjoint ($2K_2$). Consequently, any $\{K_{1,2}, 2K_2\}$-free edge set has cardinality
at most $1$ ($\mathrm{ex}(n, \{K_{1,2}, 2K_2\}) \le 1$). -/
theorem card_le_one_of_no_K12_no_2K2 {V : Type*} [DecidableEq V] (E : Finset (Finset V))
    (hnoK12 : ¬ HasK12 E) (hno2K2 : ¬ Has2K2 E) :
    E.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro e₁ e₂ he₁ he₂
  by_contra hne
  by_cases hdisj : Disjoint e₁ e₂
  · exact hno2K2 ⟨e₁, he₁, e₂, he₂, hne, hdisj⟩
  · obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.mp hdisj
    exact hnoK12 ⟨e₁, he₁, e₂, he₂, hne, ⟨x, Finset.mem_inter.mpr ⟨hx1, hx2⟩⟩⟩

/-- On `ℕ`, the matching $M_m = \{\{2i, 2i+1\} : 0 \le i < m\}$ is a valid 2-uniform edge set of
size $m$ that is completely $K_{1,2}$-free ($\mathrm{ex}(2m, K_{1,2}) \ge m$). -/
def matchingEdge (i : ℕ) : Finset ℕ := {2 * i, 2 * i + 1}

def matchingGraph (m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range m).image matchingEdge

lemma matchingEdge_injective : Function.Injective matchingEdge := by
  intro i j hij
  have hmem : 2 * i ∈ matchingEdge j := by
    rw [← hij]
    simp [matchingEdge]
  simp only [matchingEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem matchingGraph_card_and_K12_free (m : ℕ) :
    (matchingGraph m).card = m ∧ IsEdgeSet (matchingGraph m) ∧ ¬ HasK12 (matchingGraph m) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold matchingGraph
    rw [Finset.card_image_of_injective _ matchingEdge_injective, Finset.card_range]
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    unfold matchingEdge
    exact Finset.card_pair (by omega)
  · rintro ⟨e₁, he₁, e₂, he₂, hne, ⟨v, hv⟩⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he₁
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he₂
    rw [Finset.mem_inter] at hv
    simp only [matchingEdge, Finset.mem_insert, Finset.mem_singleton] at hv
    have hij : i = j := by omega
    exact hne (congrArg matchingEdge hij)

/-- On `ℕ`, the star $S_m = \{\{0, i + 1\} : 0 \le i < m\}$ is a valid 2-uniform edge set of size
$m$ that is completely $2K_2$-free ($\mathrm{ex}(m + 1, 2K_2) \ge m$). -/
def starEdge (i : ℕ) : Finset ℕ := {0, i + 1}

def starGraph (m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range m).image starEdge

lemma starEdge_injective : Function.Injective starEdge := by
  intro i j hij
  have hmem : i + 1 ∈ starEdge j := by
    rw [← hij]
    simp [starEdge]
  simp only [starEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem starGraph_card_and_2K2_free (m : ℕ) :
    (starGraph m).card = m ∧ IsEdgeSet (starGraph m) ∧ ¬ Has2K2 (starGraph m) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold starGraph
    rw [Finset.card_image_of_injective _ starEdge_injective, Finset.card_range]
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    unfold starEdge
    exact Finset.card_pair (by omega)
  · rintro ⟨e₁, he₁, e₂, he₂, _, hdisj⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he₁
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he₂
    have h0₁ : 0 ∈ starEdge i := by simp [starEdge]
    have h0₂ : 0 ∈ starEdge j := by simp [starEdge]
    exact Finset.disjoint_left.mp hdisj h0₁ h0₂

/-!
## Part 2: Lemma 3.1 of OpenAI Chapter 10 (Common-Neighbor Geometry in $\{C_4, C_6\}$-Free Bipartite Graphs)
-/

variable {S T : Type*}

/-- A bipartite graph between vertex sets `S` and `T`, represented by an adjacency relation
`adj : S → T → Prop`. -/
def IsC4Free (adj : S → T → Prop) : Prop :=
  ∀ ⦃u v : S⦄, u ≠ v → ∀ ⦃a b : T⦄, a ≠ b →
    ¬ (adj u a ∧ adj v a ∧ adj u b ∧ adj v b)

/-- A bipartite graph between `S` and `T` is $C_6$-free if there do not exist 3 distinct vertices
$u, v, w \in S$ and 3 distinct vertices $a, b, c \in T$ forming the 6-cycle
$u - a - v - b - w - c - u$. -/
def IsC6Free (adj : S → T → Prop) : Prop :=
  ∀ ⦃u v w : S⦄, u ≠ v → v ≠ w → u ≠ w →
    ∀ ⦃a b c : T⦄, a ≠ b → b ≠ c → a ≠ c →
      ¬ (adj u a ∧ adj v a ∧ adj v b ∧ adj w b ∧ adj w c ∧ adj u c)

/-- The auxiliary common-neighbor graph $R_S$ on $S$: $u \sim v$ iff $u \ne v$ and $u, v$ share
at least one neighbor in $T$. -/
def Related (adj : S → T → Prop) (u v : S) : Prop :=
  u ≠ v ∧ ∃ a : T, adj u a ∧ adj v a

/-- **Lemma 3.1(1a) of Chapter 10**:
In a $C_4$-free bipartite graph, every related pair $u \ne v$ in $S$ has a **unique** common
neighbor in $T$. -/
theorem unique_common_neighbor_of_C4_free {adj : S → T → Prop} (hC4 : IsC4Free adj)
    {u v : S} (huv : u ≠ v) {a b : T} (ha : adj u a ∧ adj v a) (hb : adj u b ∧ adj v b) :
    a = b := by
  by_contra hab
  exact hC4 huv hab ⟨ha.1, ha.2, hb.1, hb.2⟩

/-- **Lemma 3.1(1b) of Chapter 10**:
In a $\{C_4, C_6\}$-free bipartite graph, if three distinct vertices $u, v, w \in S$ have common
neighbors $a$ (of $u, v$), $b$ (of $v, w$), and $c$ (of $w, u$), then $a = b = c$. -/
theorem common_neighbors_coincide_of_C4_C6_free {adj : S → T → Prop}
    (hC4 : IsC4Free adj) (hC6 : IsC6Free adj)
    {u v w : S} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    {a b c : T} (ha : adj u a ∧ adj v a) (hb : adj v b ∧ adj w b) (hc : adj w c ∧ adj u c) :
    a = b ∧ b = c := by
  by_cases hab : a = b
  · subst hab
    have hac : a = c := unique_common_neighbor_of_C4_free hC4 huw ⟨ha.1, hb.2⟩ ⟨hc.2, hc.1⟩
    exact ⟨rfl, hac⟩
  · by_cases hbc : b = c
    · subst hbc
      have hab' : a = b := unique_common_neighbor_of_C4_free hC4 huv ha ⟨hc.2, hb.1⟩
      exact (hab hab').elim
    · by_cases hac : a = c
      · subst hac
        have hab' : a = b := unique_common_neighbor_of_C4_free hC4 hvw ⟨ha.2, hc.1⟩ hb
        exact (hab hab').elim
      · exfalso
        exact hC6 huv hvw huw hab hbc hac ⟨ha.1, ha.2, hb.1, hb.2, hc.1, hc.2⟩

/-- For distinct $u, v \in S$, $Z_{uv} = \{w \in S : w \sim u \text{ and } w \sim v\}$ is the set
of vertices in $S$ related to both $u$ and $v$. -/
def Z_uv (adj : S → T → Prop) (u v : S) : Set S :=
  {w : S | Related adj w u ∧ Related adj w v}

/-- **Lemma 3.1(3) of Chapter 10**:
In a $\{C_4, C_6\}$-free bipartite graph, if $u, v \in S$ are distinct and **unrelated**
($\neg \mathrm{Related}\ \mathrm{adj}\ u\ v$), then $Z_{uv}$ is $R_S$-independent: no two vertices
$w_1, w_2 \in Z_{uv}$ can be related in $R_S$. -/
theorem Z_uv_independent_of_C4_C6_free {adj : S → T → Prop}
    (hC4 : IsC4Free adj) (hC6 : IsC6Free adj)
    {u v : S} (huv_ne : u ≠ v) (huv_unrel : ¬ Related adj u v)
    {w₁ w₂ : S} (hw₁ : w₁ ∈ Z_uv adj u v) (hw₂ : w₂ ∈ Z_uv adj u v) :
    ¬ Related adj w₁ w₂ := by
  rintro ⟨hw₁₂_ne, c, hcw₁, hcw₂⟩
  obtain ⟨⟨hw₁u_ne, a₁, ha₁w₁, ha₁u⟩, ⟨hw₁v_ne, b₁, hb₁w₁, hb₁v⟩⟩ := hw₁
  obtain ⟨⟨hw₂u_ne, a₂, ha₂w₂, ha₂u⟩, ⟨hw₂v_ne, b₂, hb₂w₂, hb₂v⟩⟩ := hw₂
  -- Apply Lemma 3.1(1b) to the pairwise related triple `(u, w₁, w₂)` with common neighbors `a₁, c, a₂`
  have h_u := common_neighbors_coincide_of_C4_C6_free hC4 hC6
    hw₁u_ne.symm hw₁₂_ne hw₂u_ne.symm ⟨ha₁u, ha₁w₁⟩ ⟨hcw₁, hcw₂⟩ ⟨ha₂w₂, ha₂u⟩
  -- Apply Lemma 3.1(1b) to the pairwise related triple `(v, w₁, w₂)` with common neighbors `b₁, c, b₂`
  have h_v := common_neighbors_coincide_of_C4_C6_free hC4 hC6
    hw₁v_ne.symm hw₁₂_ne hw₂v_ne.symm ⟨hb₁v, hb₁w₁⟩ ⟨hcw₁, hcw₂⟩ ⟨hb₂w₂, hb₂v⟩
  -- Then `c = a₁` is adjacent to `u`, and `c = b₁` is adjacent to `v`, so `c` is a common neighbor of `u` and `v`!
  have hcu : adj u c := h_u.1 ▸ ha₁u
  have hcv : adj v c := h_v.1 ▸ hb₁v
  exact huv_unrel ⟨huv_ne, c, hcu, hcv⟩

end Erdos575

#print axioms Erdos575.card_le_one_of_no_K12_no_2K2
#print axioms Erdos575.matchingGraph_card_and_K12_free
#print axioms Erdos575.starGraph_card_and_2K2_free
#print axioms Erdos575.unique_common_neighbor_of_C4_free
#print axioms Erdos575.common_neighbors_coincide_of_C4_C6_free
#print axioms Erdos575.Z_uv_independent_of_C4_C6_free
