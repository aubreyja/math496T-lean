-- import AutograderLib
import Mathlib.Tactic

/-! # Homework 1
To begin with let prove the basic properties of ∧, ∨, and ¬.
-/

section

variable (P Q R T: Prop)

-- Commutativity
@[autogradedProof 5]
theorem problem1 : P ∧ Q ↔ Q ∧ P := by
  constructor
  rintro ⟨h₁,h₂⟩
  constructor
  assumption
  assumption
  rintro ⟨h₁,h₂⟩
  constructor
  assumption
  assumption
  done

@[autogradedProof 5]
theorem problem2 : P ∨ Q ↔ Q ∨ P := by
  constructor
  · rintro (hp|hq)
    right
    assumption
    left
    assumption
  · rintro (hq|hp)
    right
    assumption
    left
    assumption
  done

 -- Associativity
@[autogradedProof 5]
theorem problem3 : (P ∧ Q) ∧ R ↔ Q ∧ (P ∧ R) := by
  constructor
  · rintro ⟨⟨hp,hq⟩,hr⟩
    constructor
    assumption
    constructor
    assumption
    assumption
  · rintro ⟨hq,⟨hp,hr⟩⟩
    constructor
    constructor
    assumption
    assumption
    assumption
  done

@[autogradedProof 5]
theorem problem4 : (P ∨ Q) ∨ R ↔ Q ∨ (P ∨ R) := by
  constructor
  · rintro ((hp|hq)|hr)
    right
    left
    assumption
    left
    assumption
    right
    right
    assumption
  · rintro (hq|(hp|hr))
    left
    right
    assumption
    left
    left
    assumption
    right
    assumption
  done

-- Distributivity of ∧ over ∨
@[autogradedProof 5]
theorem problem5 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · rintro ⟨hp,(hq|hr)⟩
    left
    constructor
    assumption
    assumption
    right
    constructor
    assumption
    assumption
  · rintro (⟨p,q⟩|⟨p,r⟩)
    constructor
    assumption
    left
    assumption
    constructor
    assumption
    right
    assumption
  done

-- Distributivity of ∨ over ∧
@[autogradedProof 5]
theorem problem6 : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · rintro (p|⟨q,r⟩)
    constructor
    left
    assumption
    left
    assumption
    constructor
    right
    assumption
    right
    assumption
  · rintro ⟨(p|q),(p|r)⟩
    left
    assumption
    constructor
    assumption
    left
    assumption
    right
    constructor
    assumption
    assumption
  done

@[autogradedProof 5]
theorem problem7 : (P ∧ ¬ Q) → ¬ (P → Q) := by
  rintro ⟨p,nq⟩
  intro h
  have q := h p
  contradiction
  done

@[autogradedProof 5]
theorem problem8 : ∀ S : Prop, ¬ P → (P → S) := by
  intro s
  intro np
  intro p
  contradiction
  done

-- This might require some logical thinking first
@[autogradedProof 5]
theorem problem9 : ∃ Q, ∀ P, P ∨ Q ↔ Q := by
  use True
  intro p
  constructor
  rintro (h₁ | h₂)
  trivial
  assumption
  intro
  right
  assumption
  done

@[autogradedProof 5]
theorem problem10 : ∃ Q, ∀ P, P ∨ Q ↔ P := by
  use False
  intro p
  constructor
  rintro (h₁ | h₂)
  assumption
  exfalso
  assumption
  intro
  left
  assumption
  done

end
