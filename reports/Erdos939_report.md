# Erdős Problem 939 (`JSP-000780` & `JSP-000781`) Formalization Report

## 1. Overview

- **Lean 4 File**: `/Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos939.lean`
- **Reference Source**: `/Users/xcc/Project/justin-sun-prize-lean/reference/formal-conjectures/FormalConjectures/ErdosProblems/939.lean`
- **Catalog Entries**: `JSP-000780` & `JSP-000781` ([erdosproblems.com/939](https://www.erdosproblems.com/939))
- **Toolchain**: `leanprover/lean4:v4.33.1` (Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`)
- **Verification Status**: Compiles cleanly with **0 errors**, **0 warnings**, **0 `sorry`**, **0 `admit`**, and **0 custom axioms** via `/Users/xcc/Project/justin-sun-prize-lean/check_lean.sh /Users/xcc/Project/justin-sun-prize-lean/JspBounties/Erdos939.lean`.
- **Axiom Footprint**: Every theorem depends exclusively on the standard axioms `[propext, Classical.choice, Quot.sound]`.

---

## 2. Main Theorems Formalized in `JspBounties/Erdos939.lean`

| Declaration | Mathematical Statement | Status |
| :--- | :--- | :--- |
| `Erdos939.erdos_939.variants.triples` | **Main Question (`JSP-000780`)**: There are infinitely many triples $(a, b, c)$ of coprime positive $3$-powerful numbers such that $a + b = c$. | Proven (`0 sorry`) |
| `Erdos939.erdos_939.variants.finite` | **Main Question (`JSP-000781`)**: Disproves `∀ r ≥ 4, (Erdos939Sums r).Finite` by proving `(Erdos939Sums 6).Infinite`. | Proven (`0 sorry`) |
| `Erdos939.erdos_939_five_nonempty` | `(Erdos939Sums 5).Nonempty`, witnessed by $2^5 \cdot 17^6 + 7^{11} + 2^5 \cdot 3^6 \cdot 7^8 = 3^7 \cdot 13^7$. | Proven (`0 sorry`) |
| `Erdos939.erdos_939_six_infinite` | `(Erdos939Sums 6).Infinite` via an infinite parametric family of $4$-element coprime $6$-powerful sets with $6$-powerful sums. | Proven (`0 sorry`) |
| `Erdos939.erdos_939_seven_infinite` | `(Erdos939Sums 7).Infinite` via an infinite parametric family of $5$-element coprime $7$-powerful sets with $7$-powerful sums. | Proven (`0 sorry`) |
| `Erdos939.erdos_939.variants.seven` | `(Erdos939Sums 7).Nonempty` (immediate corollary of `erdos_939_seven_infinite`). | Proven (`0 sorry`) |
| `Erdos939.erdos_939_eight_infinite` | `(Erdos939Sums 8).Infinite` via an infinite parametric family of $6$-element coprime $8$-powerful sets with $8$-powerful sums. | Proven (`0 sorry`) |
| `Erdos939.erdos_939.variants.eight` | `(Erdos939Sums 8).Nonempty` (immediate corollary of `erdos_939_eight_infinite`). | Proven (`0 sorry`) |
| `Erdos939.erdos_939.variants.examples` | `∃ r ≥ 4, (Erdos939Sums r).Nonempty`. | Proven (`0 sorry`) |
| `Erdos939.erdos_939.variants.euler` | Lander–Parkin counterexample $27^5 + 84^5 + 110^5 + 133^5 = 144^5$ to Euler's sum of powers conjecture. | Proven (`0 sorry`) |

---

## 3. Proof Architecture & Key Insights

### 3.1 Eliminating the Factor of $3$ in Cohn's Recurrence (`erdos_939.variants.triples`, `JSP-000780`)
To construct infinitely many coprime $3$-powerful triples $a + b = c$, Cohn (1998) used the cubic secant-tangent map on $a X^3 + b Y^3 = c Z^3$, which in positive integers corresponds to the polynomial identity (for $a + b = c$ and $a < b$):
$$a(b + c)^3 + c(b - a)^3 = b(a + c)^3.$$
In general, when $\gcd(a, b) = 1$ and $a + b = c$, any common divisor $g = \gcd(b + c, a + c) = \gcd(a + 2b, 2a + b)$ divides $3a$ and $3b$, so $g \in \{1, 3\}$. In Cohn's paper, one must divide out by $3^3$ whenever $3 \mid (a - b)$.

We observed a key structural invariant (`ValidTriple`):
- If **at least one of $a, b, c$ is divisible by $3$** (`3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c`), then since $\gcd(a, b) = 1$ and $a + b = c$, **exactly one** of $a, b, c$ is divisible by $3$, so $3 \nmid (b + c)$ and $3 \nmid (a + c)$.
- Consequently, $\gcd(b + c, a + c) = 1$ holds **unconditionally** (`coprime_add_of_valid`), and the new triple $(a', b', c') = (a(b + c)^3, c(b - a)^3, b(a + c)^3)$ automatically preserves:
  1. Coprimality $\gcd(a', b') = 1$,
  2. The $3$-divisibility invariant `3 ∣ a' ∨ 3 ∣ b' ∨ 3 ∣ c'`,
  3. $3$-powerfulness (`Full.mul` and `Full.pow_of_le`), and
  4. Strict growth $c < c'$.
- Starting from Nitaj's seed $a_0 = 271^3$, $b_0 = 2^3 \cdot 3^5 \cdot 73^3$, $c_0 = 919^3$ (where $3 \mid b_0$), iterating `nextTriple` produces an injective sequence `tripleSeq : ℕ → ℕ × ℕ × ℕ` of coprime $3$-powerful triples without ever dividing out common factors.

### 3.2 Prime-Free Parametric Families for $r = 6, 7, 8$ (`erdos_939.variants.finite`, `JSP-000781`)
The discussion on `erdosproblems.com/939` expands $(X + Y)^r - (X - Y)^r$ and sets $X = q^r, Y = B^r$ for primes $q > B$ with $q \nmid B$. We simplified this construction in two ways:
1. **No primes needed in the parameter $X$**:
   Any $r$-th power $M^r$ is $r$-powerful (`Full.pow_of_le`), whether $M$ is prime or composite. Setting $M = B(m + 4) + 1$ for arbitrary $m \in \mathbb{N}$ gives $\gcd(M, B) = 1$ and $M \ge 4B$ for all $m \in \mathbb{N}$ without invoking Euclid's theorem on infinitely many primes.
2. **Factoring-free proof of $r$-powerfulness (`Full.mul_pow_of_dvd` & `full_monomial_term`)**:
   Whenever $c \mid B$, every prime factor of $c \cdot B^r$ divides $B$, so $p^r \mid B^r \mid c \cdot B^r$. Writing each binomial term as
   $$c \cdot (M^r)^a \cdot (B^r)^{b+1} = (c \cdot B^r) \cdot (M^a)^r \cdot (B^b)^r$$
   proves `(r).Full` for every summand in 5 lines without prime factorization (`Nat.primeFactors`) of large integers:
   - **$r = 6$ ($B = 120$, $4$ summands)**: $(X + Y)^6 = 12 X Y^5 + 40 X^3 Y^3 + 12 X^5 Y + (X - Y)^6$.
   - **$r = 7$ ($B = 210$, $5$ summands)**: $(X + Y)^7 = 2 Y^7 + 42 X^2 Y^5 + 70 X^4 Y^3 + 14 X^6 Y + (X - Y)^7$.
   - **$r = 8$ ($B = 1120$, $6$ summands)**: $(X + Y)^8 = 16 X Y^7 + 112 X^3 Y^5 + 32 X^5 Y^3 + 80 X^5 Y^3 + 16 X^7 Y + (X - Y)^8$.
