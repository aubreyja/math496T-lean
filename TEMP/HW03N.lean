
/-
  # Homework 3 Submission

  *Name*: Nicholas Schlabach
-/

-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod

/-! # Homework 3: Sets and Set Operations
Based on Lectures 10–11. Prove properties of sets using
extensionality, indexed families, cartesian products, and power sets.
-/

section

variable {α ι : Type*}
variable (A : ι → Set α)
variable (S T U : Set α)

-- Symmetric difference: elements in exactly one of S and T.
-- Use `ext`, `constructor`, and careful case analysis.
@[autogradedProof 10]
theorem problem1 : (S \ T) ∪ (T \ S) = (S ∪ T) \ (S ∩ T) := by
  ext x
  constructor
  . rintro (⟨x_in_s, x_not_in_t⟩ | ⟨x_in_t, x_not_in_s⟩)
    . constructor
      . left
        exact x_in_s
      . rintro ⟨h_in_s,h_n_t⟩
        contradiction
    . constructor
      . right
        exact x_in_t
      . rintro ⟨_,_⟩ -- don't seem to need to name these things
        contradiction
  . rintro ⟨(x_in_s | x_in_t), x_not_in_intersection⟩
    . left
      constructor
      . exact x_in_s
      . intro x_in_t
        have : x ∈ (S ∩ T) := ⟨x_in_s, x_in_t⟩
        contradiction
    . right
      constructor
      . exact x_in_t
      . intro x_in_s
        have : x ∈ (S ∩ T) := ⟨ x_in_s,x_in_t⟩
        contradiction

-- Complement of a union with an indexed union.
-- Combine De Morgan for indexed unions with De Morgan for binary union.
@[autogradedProof 10]
theorem problem2 : (S ∪ ⋃ i, A i)ᶜ = Sᶜ ∩ ⋂ i, (A i)ᶜ := by
  ext x
  constructor
  . intro h
    simp [Set.mem_compl_iff] at h
    obtain ⟨x_not_in_s, h2⟩ := h
    constructor
    . exact x_not_in_s
    . rw [Set.mem_iInter]
      exact h2
  . rintro ⟨ x_in_comp_s,x_in_iInter_a⟩
    simp [Set.mem_compl_iff]
    constructor
    . exact x_in_comp_s
    . simp [Set.mem_iInter] at x_in_iInter_a
      exact x_in_iInter_a


-- Power set of an intersection equals the intersection of power sets.
-- Unfold `𝒫` using `Set.mem_powerset_iff` and use the fact that
-- `X ⊆ S ∩ T ↔ X ⊆ S ∧ X ⊆ T`.
@[autogradedProof 10]
theorem problem3 : 𝒫 (S ∩ T) = 𝒫 S ∩ 𝒫 T := by
  ext x
  constructor
  . rw [Set.mem_powerset_iff]
    intro h
    constructor
    . rw [Set.mem_powerset_iff]
      rw [Set.subset_inter_iff] at h
      obtain ⟨ x_subset_s,_⟩  := h
      exact x_subset_s
    . rw [Set.mem_powerset_iff]
      rw [Set.subset_inter_iff] at h
      obtain ⟨_,x_subset_t⟩  := h
      exact x_subset_t
  . intro h
    rw [Set.mem_powerset_iff]
    rw [Set.mem_inter_iff] at h
    obtain ⟨x_in_power_s, x_in_power_t⟩  := h
    rw [Set.subset_inter_iff]
    constructor
    . rw [Set.mem_powerset_iff] at x_in_power_s
      exact x_in_power_s
    . rw [Set.mem_powerset_iff] at x_in_power_t
      exact x_in_power_t

-- Turns out I didn't need this for problem 4
theorem comp_subset (h : S ⊆ T) : Tᶜ ⊆ Sᶜ := by
    intro x
    rw [Set.mem_compl_iff]
    intro x_not_in_t
    intro x_in_s
    have x_in_t : x ∈ T := by
      apply h
      exact x_in_s
    contradiction

-- Subset and complement interaction.
-- If S ⊆ T, then the complement of T is contained in the complement of S.
-- This is the contrapositive for sets!
-- Then use this to show: if S ⊆ T, then S ∩ Tᶜ = ∅.
@[autogradedProof 10]
theorem problem4 (h : S ⊆ T) : S ∩ Tᶜ = ∅ := by
  -- Here is my first proof for problem 4, which didn't need comp_subset
  ext x
  constructor
  . intro h
    rw [Set.mem_inter_iff] at h
    obtain ⟨ x_in_s,x_in_comp_t⟩ := h
    have x_in_t : x ∈ T := by
      apply h
      exact x_in_s
    contradiction
  . intro x_in_emptyset
    contradiction

-- Cartesian product meets indexed intersection.
-- Prove: (⋂ i, A i) ×ˢ (⋂ i, B i) ⊆ ⋂ i, (A i ×ˢ B i)
-- Unfold using `Set.mem_prod` and `Set.mem_iInter`,
-- then specialize the hypotheses.
variable {β : Type*}
variable (B : ι → Set β)

@[autogradedProof 10]
theorem problem5 : (⋂ i, A i) ×ˢ (⋂ i, B i) ⊆ ⋂ i, (A i ×ˢ B i) := by
  rintro ⟨a,b⟩ h
  rw [Set.mem_iInter]
  intro i
  rw [Set.mem_prod] at h
  rw [Set.mem_iInter,Set.mem_iInter] at h
  obtain ⟨a_in_iA,b_in_iB⟩ := h
  show a ∈ A i ∧ b ∈ B i
  constructor
  . exact a_in_iA i
  . exact b_in_iB i

end
