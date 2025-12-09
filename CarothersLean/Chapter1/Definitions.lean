import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Lattice
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Order.Basic

-- Welcome to a guide on how to use Lean to formalize real analysis!
-- In this file, we will define some basic concepts related to bounded sets and supremums,
-- and prove a few fundamental theorems about them.

open Set
-- The above imports the necessary libraries for working with real numbers and sets in Lean.

def bdd_above (A : Set ℝ) :=
  ∃ M, ∀ a ∈ A, a ≤ M
-- Notice the syntax above, we are defining a property `bdd_above` that takes a set of real numbers `A`
-- and states that there exists a real number `M` such that every element `a` in `A` is less than or equal to `M`.
def bdd_below (A : Set ℝ) :=
  ∃ m, ∀ a ∈ A, m ≤ a

def isSup (A : Set ℝ) (s : ℝ) : Prop :=
  (∀ a ∈ A, a ≤ s) ∧ (∀ M, (∀ a ∈ A, a ≤ M) → s ≤ M)


-- Axiom: every nonempty bounded above set has a supremum.
axiom completeness_sup {A : Set ℝ} :
  A.Nonempty → bdd_above A → ∃ s : ℝ, isSup A s

-- EXERCISE 1, PROVE:
-- If A is a nonempty subset of R that is bdd below, show that A has a greatest lower bound. That is show that there is a number m in R satisfying

-- i) m is a lower bound for A, and
-- ii) if x is a lower bound for A, then x ≤ m.

-- Informal proof:
-- Let B = { -a | a ∈ A }. Since A is nonempty, B is nonempty. Since A is bounded below, B is bounded above. By the completeness axiom, B has a supremum, say s. Define m = -s. We will show that m is the greatest lower bound of A.
-- First, we show that m is a lower bound for A. For any a ∈ A, we have -a ∈ B, so -a ≤ s →  a ≥ -s = m.
-- Next, we show that m is the greatest lower bound. Suppose x is any lower bound for A. Then for any a ∈ A, we have x ≤ a, which implies -a ≤ -x. Thus, -x is an upper bound for B. By the definition of supremum, we have s ≤ -x. Negating this inequality gives x ≤ -s = m.
-- Therefore, m is the greatest lower bound of A.
theorem exists_glb {A : Set ℝ}
    (hA_nonempty : A.Nonempty)
    (hA_bddBelow : bdd_below A) :
    ∃ m : ℝ,
      (∀ a ∈ A, m ≤ a) ∧
      (∀ x, (∀ a ∈ A, x ≤ a) → x ≤ m) := by
  classical

  -- Define B = { -a | a ∈ A }
  let B : Set ℝ := { b | ∃ a ∈ A, b = -a }

  ------------------------------------------------------------------
  -- 1. B is nonempty
  ------------------------------------------------------------------
  have hB_nonempty : B.Nonempty := by
    rcases hA_nonempty with ⟨a₀, ha₀⟩
    exact ⟨-a₀, ⟨a₀, ha₀, rfl⟩⟩

  ------------------------------------------------------------------
  -- 2. B is bounded above
  ------------------------------------------------------------------
  have hB_bddAbove : bdd_above B := by
    rcases hA_bddBelow with ⟨lowerBound, hLowerBound⟩
    refine ⟨-lowerBound, ?_⟩
    intro b hb_in_B
    rcases hb_in_B with ⟨a, ha_in_A, rfl⟩
    have : lowerBound ≤ a := hLowerBound a ha_in_A
    simpa using (neg_le_neg this)

  ------------------------------------------------------------------
  -- 3. Let s = sup(B) using completeness
  ------------------------------------------------------------------
  rcases completeness_sup hB_nonempty hB_bddAbove with ⟨s, hs_supB⟩
  have hSupB_upper  := hs_supB.1
  have hSupB_least  := hs_supB.2

  ------------------------------------------------------------------
  -- 4. Define m = -s
  ------------------------------------------------------------------
  refine ⟨-s, ?_, ?_⟩

  ------------------------------------------------------------------
  -- (i) m is a lower bound of A:  -s ≤ a for all a ∈ A
  ------------------------------------------------------------------
  · intro a ha_in_A
    have hNegA_in_B : -a ∈ B := ⟨a, ha_in_A, rfl⟩
    have h_negA_le_s : -a ≤ s := hSupB_upper _ hNegA_in_B
    simpa using (neg_le.mpr h_negA_le_s)

  ------------------------------------------------------------------
  -- (ii) m is the greatest lower bound
  ------------------------------------------------------------------
  · intro x hx_isLower
    -- Show -x is an upper bound for B
    have hNegX_isUpper : ∀ b ∈ B, b ≤ -x := by
      intro b hb_in_B
      rcases hb_in_B with ⟨a, ha_in_A, rfl⟩
      have h_x_le_a : x ≤ a := hx_isLower a ha_in_A
      simpa using (neg_le_neg h_x_le_a)

    -- Use the "least upper bound" property: s ≤ -x
    have h_s_le_negX : s ≤ -x := hSupB_least (-x) hNegX_isUpper

    -- Negate: x ≤ -s
    simpa using (neg_le_neg h_s_le_negX)

-- Define infinum and supremum functions
def isInf (A : Set ℝ) (i : ℝ) : Prop :=
  (∀ a ∈ A, i ≤ a) ∧ (∀ m, (∀ a ∈ A, m ≤ a) → m ≤ i)
axiom completeness_inf {A : Set ℝ} :
  A.Nonempty → bdd_below A → ∃ m : ℝ, isInf A m

  /--

EXERCISE 2,
Let A be a bounded subset of ℝ containing at least two points. Prove that
(a) -infty < inf A ≤ sup A < infty.
(b) If B is a nonempty subset of A, then inf A ≤ inf B and sup B ≤ sup A.
(c) If B is the set of all upper bounds for A, then B is nonempty, bounded below, and inf B = sup A.
-/

theorem exercise2a {A : Set ℝ}
    (h_twoPoints : ∃ x₁ ∈ A, ∃ x₂ ∈ A, x₁ ≠ x₂)
    (h_bddBelow : bdd_below A)
    (h_bddAbove : bdd_above A) :
    ∃ m s : ℝ, isInf A m ∧ isSup A s ∧ m ≤ s := by
  classical

  -- extract nonempty from “two points”
  rcases h_twoPoints with ⟨x₁, hx₁A, x₂, hx₂A, _⟩
  have h_nonempty : A.Nonempty := ⟨x₁, hx₁A⟩

  -- get inf A and sup A using your axioms
  rcases completeness_inf h_nonempty h_bddBelow with ⟨m, hmInf⟩
  rcases completeness_sup h_nonempty h_bddAbove with ⟨s, hsSup⟩

  -- unpack definitions to get pointwise bounds
  have m_le_all : ∀ a ∈ A, m ≤ a := hmInf.1
  have all_le_s : ∀ a ∈ A, a ≤ s := hsSup.1

  -- pick any element of A to connect m ≤ a ≤ s
  rcases h_nonempty with ⟨a0, ha0A⟩
  have m_le_a0 : m ≤ a0 := m_le_all a0 ha0A
  have a0_le_s : a0 ≤ s := all_le_s a0 ha0A
  have m_le_s : m ≤ s := le_trans m_le_a0 a0_le_s

  exact ⟨m, s, hmInf, hsSup, m_le_s⟩
