import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Lattice



open Set

-- Your custom "bounded above" definition
def bdd_above (A : Set ℝ) : Prop :=
  ∃ X : ℝ, ∀ a : ℝ, a ∈ A → a ≤ X

def bdd_below (A : Set ℝ) : Prop :=
  ∃ x : ℝ, ∀ a : ℝ, a ∈ A → x ≤ a

-- Your completeness-style statement

import Mathlib/Data/Real/Basic
import Mathlib/Data/Set/Lattice

open Set

-- Your version of bounded above/below
def bdd_above (A : Set ℝ) :=
  ∃ M, ∀ a ∈ A, a ≤ M

def bdd_below (A : Set ℝ) :=
  ∃ m, ∀ a ∈ A, m ≤ a

def isSup (A : Set ℝ) (s : ℝ) : Prop :=
  (∀ a ∈ A, a ≤ s) ∧ (∀ M, (∀ a ∈ A, a ≤ M) → s ≤ M)


-- Axiom: every nonempty bounded above set has a supremum.
axiom completeness_sup {A : Set ℝ} :
  A.Nonempty → bdd_above A → ∃ s : ℝ, isSup A s

-- PROVE:
-- If A is a nonempty subset of R that is bdd below, show that A has a greatest lower bound. That is show that there is a number m in R satisfying

-- i) m is a lower bound for A, and
-- ii) if x is a lower bound for A, then x ≤ m.

theorem exists_glb {A : Set ℝ}
    (hA : A.Nonempty) (hb : bdd_below A) :
    ∃ m, (∀ a ∈ A, m ≤ a) ∧ (∀ x, (∀ a ∈ A, x ≤ a) → x ≤ m) := by
  classical

  -- Convert bdd beklow A to bdd above of -A
   rcases hb with (L, hL)
   have hUpper : bdd_above (-A) := by
     refine (-)
