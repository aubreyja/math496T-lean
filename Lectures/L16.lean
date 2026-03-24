import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Ring.Parity

/- # Lecture 16: Cantor's Diagonal Argument — Countable and Uncountable Sets

New tactic: `native_decide`
Recall: **intro, use, obtain, simp, constructor, rw, omega, linarith, exact?**

`native_decide` solves a goal when the goal is **decidable** and Lean can
compute the answer directly.  It is especially useful for concrete examples
like checking the value of a function on a specific input.

## Overview

So far, we have studied functions between sets: injections, surjections, and
bijections.  Today we use bijections to compare the **sizes** of infinite sets.
Moral: not all infinities are equal.

The key results:
  1. ℤ has the same cardinality as ℕ (it is **countably infinite**).
  2. **Cantor's theorem**: the power set 𝒫(S) is always strictly larger than S.
  3. The set of infinite binary sequences (ℕ → Bool) or
     real numbers between 0 and 1 in  bicimal (binary decimal) form is **uncountable**.

The proofs use a single powerful technique — the **diagonal argument**.

### An Interesting Fact

In 1891 Georg Cantor proved that there is no bijection between a set and
its power set, thus there are **different sizes of infinity**.
The result shocked the mathematical community and led Cantor's colleague
Leopold Kronecker to call him a "corrupter of youth."
Cantor's ideas are at the foundation of modern set theory,
and David Hilbert declared:
"No one shall expel us from the paradise that Cantor has created."
-/


-- ============================================================================
-- ## Key Definitions
-- ============================================================================

/-
**Equinumerous** (same cardinality):  Two types α and β have the same
cardinality if there exists a bijection f : α → β.

**Countably infinite**: A type α is countably infinite if there exists a
bijection f : ℕ → α.  Its cardinality is denoted ℵ₀ (aleph-nought).

**Countable**: A type is countable if it is finite or countably infinite.

**Uncountable**: A type that is not countable.

In Lean/Mathlib, `Set.Countable S` means S is countable, and
`Cardinal` provides the full cardinality API.  For this lecture, we work
mostly with raw bijections and injections/surjections.
-/

-- Recall the key definitions from Lectures 14–15:
#check @Function.Injective   -- ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
#check @Function.Surjective  -- ∀ b, ∃ a, f a = b
#check @Function.Bijective   -- Injective f ∧ Surjective f


-- recall a set is really a predicate on a type:
theorem predicate_set_bijective {α : Type*} {f : (α → Prop) → Set α} (h : f=fun P => {x | P x}) : Function.Bijective f := by
  rw [h]
  constructor
  . -- injectivity
    intro P Q h
    ext x
    simp [Set.ext_iff] at h
    exact h x
  . -- surjectivity
    intro S
    simp
    use fun x => (x ∈ S)
    simp


-- ============================================================================
-- ## Part 1: Equinumerous Sets and Cardinality
-- ============================================================================

/-
Two types α and β are **equinumerous** (have the same cardinality,
written |α| = |β|) if there exists a bijection between them.

This is an equivalence relation on types:
  • Reflexive: id is a bijection α → α.
  • Symmetric: if f : α → β is a bijection, then f⁻¹ : β → α is too.
  • Transitive: composition of bijections is a bijection (Lecture 14).

A type is **countably infinite** if it is equinumerous with ℕ.  Its
cardinality is called ℵ₀ (aleph-nought, the first infinite cardinal).

Galileo observed in 1638 that ℕ and the even numbers are equinumerous
(via n ↦ 2n), even though the even numbers are a proper subset.
Dedekind later used this as a *definition*:
__a set is infinite iff it is equinumerous with its proper subset__.
-/

-- The even-numbers bijection from Lecture 14:
def double : ℕ → ℕ := fun n => 2 * n

-- Recall: we proved this is injective but NOT surjective (as ℕ → ℕ).
-- But as a function ℕ → {n : ℕ | 2 ∣ n}, it would be bijective.
-- This shows that ℕ and the even numbers have the same cardinality!

-- Reflexivity: id is a bijection.
example : Function.Bijective (id : α → α) := by
  constructor
  · intro a b h; exact h
  · intro a; use a; rfl

-- Exercises (Part 1)

-- (a) Prove that the successor function is injective on ℕ:
example : Function.Injective (fun n : ℕ => n + 1) := by
  sorry

-- (b) Prove that n ↦ n + 1 is NOT surjective on ℕ (0 has no preimage):
example : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  sorry

/- Dedekind's definition:
A set is infinite if it is in bijection with its proper subset.-/

-- (c) Dedekind's criterion: ℕ is infinite because n ↦ n + 1 is a
-- bijection from ℕ to the positive naturals {n : ℕ | 0 < n}.
-- Prove the injection part:
example : Function.Injective (fun n : ℕ => n + 1) ∧
    ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  sorry


-- ============================================================================
-- ## Part 2: ℤ is Countably Infinite
-- ============================================================================

/-
We construct an explicit bijection ℕ → ℤ using the **zigzag** pattern:

  n:  0   1   2   3   4   5   6  ...
  ↓   ↓   ↓   ↓   ↓   ↓   ↓   ↓
  z:  0  −1   1  −2   2  −3   3  ...

The formula:
  • If n is even: f(n) = n / 2
  • If n is odd:  f(n) = −(n / 2) - 1

In Lean, we work with integer division on ℕ.  This function and its inverse
give a bijection ℕ ↔ ℤ, proving that ℤ is countably infinite.
-/

#check Nat.even_or_odd

-- The zigzag function:
def zigzag : ℕ → ℤ := fun n =>
  if n % 2 = 0 then (n / 2 : ℤ)
            else -(n / 2 : ℤ) - 1



-- Let's verify on small values:
#eval zigzag 0   -- 0
#eval zigzag 1   -- -1
#eval zigzag 2   -- 1
#eval zigzag 3   -- -2
#eval zigzag 4   -- 2
#eval zigzag 5   -- -3

-- The inverse function: ℤ → ℕ
-- Nonnegative integers go to even naturals, and negative integers go to odd ones.
def zagzig : ℤ → ℕ
  | Int.ofNat n => 2 * n
  | Int.negSucc n => 2 * n + 1

#eval zagzig 0    -- 0
#eval zagzig (-1)  -- 1
#eval zagzig 1    -- 2
#eval zagzig (-2)  -- 3
#eval zagzig 2    -- 4

#print Even -- ∃ r, a = r + r
example (n:ℕ) : Even n ∨ Odd n := by exact Nat.even_or_odd n
example (n : ℕ) : ¬ (Even n) ↔ Odd n := Nat.not_even_iff_odd

-- We prove zagzig is a left inverse of zigzag (zagzig ∘ zigzag = id).
-- This establishes injectivity of zigzag.
theorem zagzig_zigzag : ∀ n:ℕ, zagzig (zigzag n) = n := by
  intro n
  rcases Nat.even_or_odd n with heven | hodd
  · -- n is even: zigzag n lands in the nonnegative branch of zagzig.
    obtain ⟨k, hk⟩ := heven
    rw [← two_mul] at hk
    simp [hk,zigzag]
    simp [zagzig]
  · -- n is odd: zigzag n lands in the negative branch of zagzig.
    obtain ⟨k, hk⟩ := hodd
    simp [hk,zigzag]
    have hh : (2 * (k:ℤ) + 1) / 2 = k := by omega
    rw [hh]
    simp [zagzig]
    have : - (k : ℤ) - 1 = Int.negSucc k := by omega
    simp [this]

-- We prove zigzag is a left inverse of zagzig (zigzag ∘ zagzig = id).
-- This establishes surjectivity of zigzag.
theorem zigzag_zagzig : ∀ z, zigzag (zagzig z) = z := by
  intro z
  simp [zagzig]
  rcases z with n | n
  . -- z = n is nonnegative: zigzag lands in the even branch.
    simp [zigzag]
  . -- z = - n - 1 is negative: zigzag lands in the odd branch.
    simp [zigzag]
    have hh : (2 * (n:ℤ) + 1) / 2 = n := by omega
    simp [hh]
    omega


-- **Theorem**: zigzag is a bijection, so |ℕ| = |ℤ|.
theorem zigzag_bijective : Function.Bijective zigzag := by
  constructor
  · -- Injective: if zigzag m = zigzag n, then m = n.
    intro m n h
    have hm := zagzig_zigzag m
    have hn := zagzig_zigzag n
    rw [h] at hm; linarith
  · -- Surjective: for any z : ℤ, there exists n with zigzag n = z.
    intro z
    use zagzig z
    exact zigzag_zagzig z


-- Exercises (Part 2)

-- `native_decide` is a convenient way to close concrete, computable goals.
-- It reduces the proposition by computation, using Lean's native evaluator,
-- so it works best on closed examples rather than symbolic goals.

-- (a) Verify: zigzag 6 = 3:
example : zigzag 6 = 3 := by native_decide

-- (b) Verify: zagzig (-5) = 9:
example : zagzig (-5) = 9 := by native_decide

-- (c) Prove that zagzig is also a bijection (since it is the inverse of
-- a bijection — use the theorems above):
theorem zagzig_bijective : Function.Bijective zagzig := by
  sorry

-- (d) Prove: the function n ↦ n + 1 is a bijection ℤ → ℤ.
-- (This is easy on ℤ, unlike ℕ!)
example : Function.Bijective (fun n : ℤ => n + 1) := by
  sorry


-- ============================================================================
-- ## Part 3: Cantor's Theorem
-- ============================================================================

/-
**Cantor's Theorem (1891)**: For any type `α`, there is no surjection
from `α` to `Set α`.
(Recall that Set α is the type of subsets of α, which is α → Prop).

Here `Set α` is Lean's version of the power set `𝒫(α)`: a function
`S : α → Prop` is the characteristic function of a subset (`S x` is true
iff `x ∈ S`).

**Proof**: Suppose `f : α → Set α` is surjective.  Define the
**diagonal set**:

  `D = { x : α | ¬ f(x)(x) }`

In words: `D` is the set of all `x` such that `x` is NOT in `f(x)`.

Since `f` is surjective, `D = f(a)` for some `a : α`.  But then:
  • If `a ∈ D`, then by definition of `D`, `a ∉ f(a) = D`.  Contradiction!
  • If `a ∉ D`, then by definition of `D`, `a ∈ f(a) = D`.  Contradiction!

So `f` cannot be surjective.  ∎

This is the **diagonal argument**: we construct an object that differs
from every entry on the "diagonal" f(x)(x).
-/

example {x : α} {P : α → Prop} : x ∈ {y | P y} ↔ P x := by exact Set.mem_setOf

-- **Cantor's Theorem** (no surjection α → Set α):
theorem cantor (f : α → Set α) : ¬ Function.Surjective f := by
  intro h
  -- h : ∀ S : Set α, ∃ a, f a = S
  -- Define the diagonal set D:
  let D : Set α := {x | ¬ (x ∈ f x)}
  -- Since f is surjective, D = f a for some a:
  obtain ⟨a, ha⟩ := h D
  -- Two cases: either a ∈ D or a ∉ D.
--, i.e. ¬ f a a.
  -- rcases a ∈ D with hD | notD
  -- done
  by_cases hD : a ∈ D
  .   -- Case 1: suppose a ∈ D
      -- then by definition of `D`, `a ∉ f(a)`.
    have notD : a ∉ f a := Set.mem_setOf.mp hD
      -- but, since D = f a, we have a ∈ f a.  Contradiction.
    rw [← ha] at hD
    exact notD hD
  .   -- Case 2: suppose `a ∉ D`, then `a ∉ f a`
     have notD : a ∉ f a := by rw [ha]; exact hD
      -- then by definition of `D`, `a ∈ D`.
     have hinD : a ∈ D := Set.mem_setOf.mpr notD
     exact hD hinD


/-
**Corollary**: |α| < |𝒫(α)| for every type α.

More precisely: there is an injection α → Set α
(sending each element to its singleton set), but no surjection.
So the power set is strictly larger.
-/

-- The injection α → Set α: each a maps to the singleton {a}.
-- This is the function a ↦ (fun x => x = a).
theorem singleton_injective : Function.Injective (fun a : α => (fun x : α => x = a)) := by
  intro a b h
  -- h : (fun x => x = a) = (fun x => x = b)
  have : (fun x : α => x = a) a = (fun x : α => x = b) a := by
    exact congrFun h a
  simp at this
  exact this

-- Combining: there is an injection but no surjection from α to Set α.
-- This is the precise meaning of |α| < |𝒫(α)|.

-- For finite sets, this is clear: if |α| = n, then |𝒫(α)| = 2ⁿ > n.
-- Cantor's theorem tells us this holds for INFINITE sets too!


-- Exercises (Part 3)

-- (a) Prove Cantor's theorem for α → Bool instead of α → Prop.
-- (This is closer to the "binary sequence" formulation.)
theorem cantor_bool (f : α → (α → Bool)) : ¬ Function.Surjective f := by
  sorry

-- (b) Complete the proof of the singleton injection in a different style:
-- send a to the "membership predicate" (fun x => a = x) instead.
example : Function.Injective (fun a : α => (fun x : α => a = x)) := by
  sorry

-- (c) Show that there is no injection (α → Prop) → α.
-- (Hint: an injection from a larger set to a smaller one would give a
-- surjection the other way, contradicting Cantor's theorem.)
-- We'll just prove this using the core idea:
theorem no_injection_powerset (f : (α → Prop) → α) :
    ¬ Function.Injective f := by
  sorry


-- ============================================================================
-- ## Part 4: Infinite Binary Sequences Are Uncountable
-- ============================================================================

/-
Consider the type `ℕ → Bool` of infinite binary sequences.
An element is a function that assigns to each n ∈ ℕ a value
`true` or `false`.  We can think of these as "binary fractions":
infinite strings of 0s and 1s after a binary point.

  Example: (true, false, true, true, false, ...) represents 0.10110...₂

**Claim**: There is no surjection ℕ → (ℕ → Bool).

This is a DIRECT instance of Cantor's theorem with α = ℕ!
The power set 𝒫(ℕ) can be identified with ℕ → Bool (or ℕ → Prop):
a subset S ⊆ ℕ corresponds to its characteristic function χ_S.

**Connection to the real numbers** (a preview of Stage 9):
Every real number in [0,1] can be written in binary as 0.b₁b₂b₃...
This gives a close relationship between ℕ → Bool and the interval
[0,1] ⊂ ℝ.  When we introduce ℝ in Stage 9, we will prove formally
that |ℝ| = |ℕ → Bool| = |𝒫(ℕ)|.  For now, the uncountability of
ℕ → Bool is a precise stand-in for the uncountability of the reals.

**The classical "list" argument** (human-language version):

Suppose for contradiction that we could list ALL binary sequences:

  s₀ = b₀₀ b₀₁ b₀₂ b₀₃ ...
  s₁ = b₁₀ b₁₁ b₁₂ b₁₃ ...
  s₂ = b₂₀ b₂₁ b₂₂ b₂₃ ...
  s₃ = b₃₀ b₃₁ b₃₂ b₃₃ ...
    ⋮

Construct a new sequence d by flipping the diagonal:
  d(n) = NOT bₙₙ

Then d differs from sₙ at position n, for every n.
So d is not in the list — contradiction!  ∎
-/

-- The diagonal argument, specialized to ℕ → Bool:
-- (This is just `cantor_bool` with α := ℕ, but let's write it out
-- explicitly to see the diagonal construction.)

theorem binary_sequences_uncountable :
    ¬ ∃ f : ℕ → (ℕ → Bool), Function.Surjective f := by
  intro ⟨f, hf⟩
  -- Construct the diagonal sequence:
  -- d(n) = !f(n)(n)  (flip the diagonal)
  let d : ℕ → Bool := fun n => !f n n
  -- By surjectivity, d = f(a) for some a:
  obtain ⟨a, ha⟩ := hf d
  -- Ask: what is d(a)?
  -- On one hand, d(a) = !f(a)(a)  (by definition of d).
  -- On the other hand, d(a) = f(a)(a)  (since d = f(a)).
  have h1 : d a = !f a a := rfl
  have h2 : d a = f a a := by rw [ha]
  -- So f(a)(a) = !f(a)(a), which is impossible for booleans.
  rw [h2] at h1
  -- h1 : f a a = !f a a
  cases hb : f a a <;> simp_all

-- Alternative phrasing: no surjection ℕ → (ℕ → Bool).
-- This follows from cantor_bool directly:
example : ∀ f : ℕ → (ℕ → Bool), ¬ Function.Surjective f :=
  fun f => cantor_bool f


-- Exercises (Part 4)

-- (a) The "flip" function that negates every bit of a binary sequence
-- is a bijection (ℕ → Bool) → (ℕ → Bool).  Prove it's injective:
def flipAll : (ℕ → Bool) → (ℕ → Bool) := fun s n => !s n

example : Function.Injective flipAll := by
  sorry

-- (b) Prove that there is no surjection ℕ → (ℕ → ℕ).
-- (Hint: if there were, we could restrict to Bool-valued functions.)
-- Actually, this follows directly from Cantor's theorem!
theorem no_surj_nat_to_nat_nat :
    ∀ f : ℕ → (ℕ → ℕ), ¬ Function.Surjective f := by
  sorry

-- (c) Show there is an injection ℕ → (ℕ → Bool).
-- (This combined with the non-surjectivity establishes |ℕ| < |ℕ → Bool|.)
-- Hint: send n to the sequence that is `true` at position n and `false`
-- everywhere else.
theorem nat_injects_into_binary_seq :
    Function.Injective (fun n : ℕ => (fun m : ℕ => n = m)) := by
  sorry


-- ============================================================================
-- ## Part 5: No Largest Cardinality
-- ============================================================================

/-
Cantor's theorem has a remarkable consequence: there is no largest
cardinality.

Given ANY type α, we can form 𝒫(α) = Set α, which is strictly
larger.  Then 𝒫(𝒫(α)) is strictly larger still.  And so on, forever.

  |ℕ| < |𝒫(ℕ)| < |𝒫(𝒫(ℕ))| < |𝒫(𝒫(𝒫(ℕ)))| < ⋯

This gives an infinite ascending chain of cardinalities.

**Russell's Paradox (1901)**: What about the "set of all sets"?
If such a set U existed, then 𝒫(U) ⊆ U (since 𝒫(U) is a set), giving
|𝒫(U)| ≤ |U|.  But Cantor's theorem says |U| < |𝒫(U)|.  Contradiction!

This paradox — together with similar ones by Burali-Forti and Cantor
himself — showed that "naive" set theory (where any collection is a set)
is inconsistent, and motivated the development of **axiomatic set theory**
(Zermelo–Fraenkel, 1908–1922).

In Lean, this paradox is avoided by the **universe hierarchy**: there is
no `Type` that contains all types.  Instead, `Type 0 : Type 1 : Type 2 : ...`
-/

-- The chain of power sets: each is strictly larger than the last.
-- We just restate Cantor's theorem in a slightly different form.

-- There is an injection α → Set α but no surjection.
-- Hence |α| < |Set α|.
-- Applying this to Set α gives |Set α| < |Set (Set α)|.
-- And so on.

-- We already proved this!  But let's package it neatly.

/-- Cantor's theorem: for any type α, there is an injection α → Set α
    but no surjection α → Set α. -/
theorem cantor_strict :
    (∃ i : α → Set α, Function.Injective i) ∧
    (∀ f : α → Set α, ¬ Function.Surjective f) :=
  ⟨⟨fun a x => x = a, singleton_injective⟩, cantor⟩




-- Exercises (Part 5)

-- (a) Prove: there is no surjection Bool → (Bool → Prop).
-- (Even with just two elements, the power set {∅, {tt}, {ff}, {tt,ff}}
-- has four elements — strictly more.)
example : ∀ f : Bool → (Bool → Prop), ¬ Function.Surjective f := by
  sorry

-- (b) Prove: there IS a surjection (α → Prop) → α → Prop (the identity!):
example : Function.Surjective (id : (α → Prop) → (α → Prop)) := by
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Verify zigzag 7 = -4:
example : zigzag 7 = -4 := by native_decide

-- (2) Verify zagzig 5 = 10:
example : zagzig 5 = 10 := by native_decide

-- (3) Prove that the constant function ℕ → (ℕ → Bool) sending every n
-- to the all-true sequence is NOT surjective:
example : ¬ Function.Surjective (fun _ : ℕ => (fun _ : ℕ => true)) := by sorry

-- (4) Prove there is no surjection ℕ → (ℕ → Prop):
example : ∀ f : ℕ → (ℕ → Prop), ¬ Function.Surjective f := by sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (5) Define an injection ℤ → ℕ (i.e. the inverse direction of zigzag).
-- We already have zagzig; prove it's injective directly.
theorem zagzig_injective : Function.Injective zagzig := by sorry

-- (6) Prove that if there is a bijection α ↔ β and a bijection β ↔ γ,
-- then there is a bijection α ↔ γ.  (Transitivity of equinumerosity.)
-- Use composition of bijections from Lecture 14.
theorem equinum_trans {f : α → β} {g : β → γ}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f) := by sorry

-- (7) Prove Cantor's theorem in yet another form: there is no bijection
-- between α and α → Bool.
theorem cantor_no_bijection : ∀ f : α → (α → Bool), ¬ Function.Bijective f := by sorry

-- (8) Show that |ℕ| ≠ |ℕ → Bool|, i.e. there is no bijection ℕ ↔ (ℕ → Bool).
example : ∀ f : ℕ → (ℕ → Bool), ¬ Function.Bijective f := by sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (9) The diagonal argument can also show: there is no surjection ℕ → (ℕ → ℕ).
-- Prove this by a direct diagonal construction (without using cantor).
-- Hint: given f : ℕ → (ℕ → ℕ), define d(n) = f(n)(n) + 1.
theorem cantor_nat_nat_direct :
    ∀ f : ℕ → (ℕ → ℕ), ¬ Function.Surjective f := by sorry

-- (10) CHALLENGE: Prove that for any injection g : (ℕ → Bool) → ℕ,
-- g is not surjective.
-- (There is NO bijection ℕ ↔ (ℕ → Bool), and there IS an injection
-- ℕ → (ℕ → Bool), so any injection the other way cannot be surjective.)
-- Hint: if g were bijective, its inverse would be a surjection ℕ → (ℕ → Bool).
-- This is actually not so easy to prove directly — feel free to use `cantor_bool`.
theorem injection_bool_seq_not_surj (g : (ℕ → Bool) → ℕ)
    (hg : Function.Injective g) : ¬ Function.Surjective g := by sorry

-- (11) CHALLENGE: A "self-referential" variant.
-- Define the Russell set: R = { x | x ∉ f(x) }.
-- Prove that R ≠ f(a) for any a.  This is the core of Cantor's argument,
-- stated for a specific a rather than using surjectivity.
theorem russell_diag (f : α → (α → Prop)) (a : α) :
    (fun x => ¬ f x x) ≠ f a := by sorry
