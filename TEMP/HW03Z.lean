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
  . intro h
    rcases h with ⟨hS, hnT⟩ | ⟨hT, hnS⟩
    constructor
    . left
      exact hS
    . intro hc
      have ⟨ _, hT⟩ := hc
      contradiction
    constructor
    . right
      exact hT
    . intro hc
      have ⟨ hS, _⟩ := hc
      contradiction
  . intro h
    rcases h with ⟨ (hS|hT), hD⟩
    left
    constructor
    . exact hS
    . intro hT
      apply hD
      constructor
      . exact hS
      . exact hT
    right
    constructor
    . exact hT
    . intro hS
      apply hD
      constructor
      . exact hS
      . exact hT
  done

-- Complement of a union with an indexed union.
-- Combine De Morgan for indexed unions with De Morgan for binary union.
@[autogradedProof 10]
theorem problem2 : (S ∪ ⋃ i, A i)ᶜ = Sᶜ ∩ ⋂ i, (A i)ᶜ := by
  ext x
  constructor
  . intro h
    constructor
    . intro hS
      apply h
      exact Or.inl hS
    . intro Aic
      intro hAi
      rcases hAi with ⟨j, hj⟩
      simp at hj -- I want to see what it's doing because it looks ew
      rw [← hj]
      intro hAj
      apply h
      right
      exact Set.mem_iUnion.mpr ⟨j, hAj⟩

  . rintro ⟨hSc,hIntAiC⟩
    rintro (hS | hUAi)
    . contradiction
    . rcases Set.mem_iUnion.mp hUAi with ⟨j, hAj⟩
      have hxAic : x ∈ (A j)ᶜ := Set.mem_iInter.mp hIntAiC j
      contradiction
  done

-- Power set of an intersection equals the intersection of power sets.
-- Unfold `𝒫` using `Set.mem_powerset_iff` and use the fact that
-- `X ⊆ S ∩ T ↔ X ⊆ S ∧ X ⊆ T`.
@[autogradedProof 10]
theorem problem3 : 𝒫 (S ∩ T) = 𝒫 S ∩ 𝒫 T := by
  ext A
  constructor
  . intro h
    rw [Set.mem_powerset_iff] at h
    rw [Set.subset_inter_iff] at h
    have ⟨ hS, hT⟩ := h
    rw [← Set.mem_powerset_iff] at hS
    rw [← Set.mem_powerset_iff] at hT
    constructor; exact hS; exact hT

  . intro h
    rw [Set.mem_inter_iff] at h
    have ⟨ hPS, hPT⟩ := h
    rw [Set.mem_powerset_iff] at hPS
    rw [Set.mem_powerset_iff] at hPT
    have h: A ⊆ S ∩ T := by
      intro x hA
      constructor; exact hPS hA; exact hPT hA
    rw [← Set.mem_powerset_iff] at h
    exact h
  done

-- Subset and complement interaction.
-- If S ⊆ T, then the complement of T is contained in the complement of S.
-- This is the contrapositive for sets!
-- Then use this to show: if S ⊆ T, then S ∩ Tᶜ = ∅.
@[autogradedProof 10]
theorem problem4 (h : S ⊆ T) : S ∩ Tᶜ = ∅ := by
  ext x
  constructor
  . rintro ⟨ hS, hTc⟩
    have hT := h hS
    exfalso
    contradiction
  . intro hh
    exfalso
    exact False.elim hh
  done

-- Cartesian product meets indexed intersection.
-- Prove: (⋂ i, A i) ×ˢ (⋂ i, B i) ⊆ ⋂ i, (A i ×ˢ B i)
-- Unfold using `Set.mem_prod` and `Set.mem_iInter`,
-- then specialize the hypotheses.
variable {β : Type*}
variable (B : ι → Set β)

@[autogradedProof 10]
theorem problem5 : (⋂ i, A i) ×ˢ (⋂ i, B i) ⊆ ⋂ i, (A i ×ˢ B i) := by
  intro x h
  have ⟨hA, hB⟩ := Set.mem_prod.mp h
  apply Set.mem_iInter.mpr
  intro i
  apply Set.mem_prod.mpr
  constructor
  . exact Set.mem_iInter.mp hA i
  . exact Set.mem_iInter.mp hB i
  done
end
