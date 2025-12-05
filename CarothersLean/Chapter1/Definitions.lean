import Mathlib.Data.Real.Basic


open Set

-- Definitions from the text
def bdd_above (A : Set ℝ) : Prop :=
  ∃ x : ℝ, ∀ a : ℝ, a ∈ A → a ≤ x
