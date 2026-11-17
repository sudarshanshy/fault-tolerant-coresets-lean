import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Arithmetic of the proxy-decoder counterexample (Appendix A.1)

This file checks the scalar calculations in the unnumbered counterexample on
pages 16–17 of the source PDF. It is deliberately not a formalization of the
full metric counterexample: the finite shortest-path metric, cluster assignments,
and uniform sensitivity bounds for all two-center queries are not constructed
here. The quantities below are the explicit formulas stated in the PDF.
-/

namespace FTC.CounterexampleArithmetic

noncomputable section

/-- The cost of the reference clustering on the corrupted summary. -/
def referenceCost (n : ℝ) : ℝ := 2 * n - 27 / 4

/-- Proxy score of the genuine singleton `p₁`. -/
def singletonProxy (n : ℝ) : ℝ := 2 + 1 / (2 * referenceCost n)

/-- Proxy score of the corruption `b`. -/
def corruptionProxy (n : ℝ) : ℝ := 2 / (n - 1) + 2 * (n - 4) / referenceCost n

/-- Upper bound on proxy scores of the other genuine entries. -/
def ordinaryProxy (n : ℝ) : ℝ := 2 / (n - 1) + 2 / referenceCost n

/-- The paper's uniform upper bound on genuine-entry sensitivities. -/
def genuineBound (n : ℝ) : ℝ := 1 / (n - 3)

/-- The sensitivity ratio of `b` witnessed by `{p₂,p₃}`. -/
def corruptionWitness (n : ℝ) : ℝ := (n - 4) / (2 * n - 7)

/-- Distortion after the proxy rule removes `p₁` and retains `b`. -/
def wrongDistortion (n : ℝ) : ℝ := 2 * (n - 4) / (n - 2)

theorem referenceCost_pos {n : ℝ} (hn : 8 ≤ n) : 0 < referenceCost n := by
  unfold referenceCost
  linarith

theorem singletonProxy_gt_two {n : ℝ} (hn : 8 ≤ n) : 2 < singletonProxy n := by
  have hd := referenceCost_pos hn
  have hp : 0 < 1 / (2 * referenceCost n) :=
    one_div_pos.mpr (by linarith)
  unfold singletonProxy
  linarith

theorem corruptionProxy_gt_one {n : ℝ} (hn : 8 ≤ n) : 1 < corruptionProxy n := by
  have hd := referenceCost_pos hn
  have hn1 : 0 < n - 1 := by linarith
  unfold corruptionProxy
  rw [div_add_div _ _ (ne_of_gt hn1) (ne_of_gt hd)]
  apply (lt_div_iff₀ (mul_pos hn1 hd)).2
  unfold referenceCost
  nlinarith

theorem corruptionProxy_lt_two {n : ℝ} (hn : 8 ≤ n) : corruptionProxy n < 2 := by
  have hd := referenceCost_pos hn
  have hfirst : 2 / (n - 1) < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  have hsecond : 2 * (n - 4) / referenceCost n < 1 := by
    apply (div_lt_one hd).2
    unfold referenceCost
    linarith
  unfold corruptionProxy
  linarith

theorem ordinaryProxy_lt_two {n : ℝ} (hn : 8 ≤ n) : ordinaryProxy n < 2 := by
  have hd := referenceCost_pos hn
  have hfirst : 2 / (n - 1) < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  have hsecond : 2 / referenceCost n < 1 := by
    apply (div_lt_one hd).2
    unfold referenceCost
    linarith
  unfold ordinaryProxy
  linarith

/-- The claimed genuine-sensitivity bound lies below the cluster-size term
of every nonsingleton proxy. -/
theorem genuineBound_le_cluster_term {n : ℝ} (hn : 8 ≤ n) :
    genuineBound n ≤ 2 / (n - 1) := by
  unfold genuineBound
  apply (div_le_div_iff₀ (by linarith : 0 < n - 3) (by linarith : 0 < n - 1)).2
  linarith

/-- The witnessed corruption sensitivity strictly exceeds the bound for all
of the genuine entries. -/
theorem genuineBound_lt_corruptionWitness {n : ℝ} (hn : 8 ≤ n) :
    genuineBound n < corruptionWitness n := by
  unfold genuineBound corruptionWitness
  apply (div_lt_div_iff₀ (by linarith : 0 < n - 3)
    (by linarith : 0 < 2 * n - 7)).2
  have hp := mul_nonneg (by linarith : 0 ≤ n - 8) (by linarith : 0 ≤ n - 1)
  nlinarith

/-- Given the paper's lower bound `n-3` on optimum cost, its reference
clustering satisfies the asserted factor-two guarantee. -/
theorem reference_two_approx {n opt : ℝ} (hopt : n - 3 ≤ opt) :
    referenceCost n ≤ 2 * opt := by
  unfold referenceCost
  linarith

/-- All strict scalar separations needed for the opposite proxy/exact choices. -/
theorem proxy_and_sensitivity_separations {n : ℝ} (hn : 8 ≤ n) :
    2 < singletonProxy n ∧
    1 < corruptionProxy n ∧ corruptionProxy n < 2 ∧
    ordinaryProxy n < 2 ∧ genuineBound n ≤ 2 / (n - 1) ∧
    genuineBound n < corruptionWitness n := by
  exact ⟨singletonProxy_gt_two hn, corruptionProxy_gt_one hn,
    corruptionProxy_lt_two hn, ordinaryProxy_lt_two hn,
    genuineBound_le_cluster_term hn, genuineBound_lt_corruptionWitness hn⟩

/-- The parameter regime of the PDF implies all the numerical size
conditions used above. -/
theorem size_ge_eight {ε n : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 10)
    (hn : 8 / ε ≤ n) : 8 ≤ n := by
  have h : 8 ≤ 8 / ε := (le_div_iff₀ hε).2 (by linarith)
  exact h.trans hn

/-- Exact distortion and clean-deletion error estimates from Appendix A.1. -/
theorem distortion_and_deletion_bounds {ε n : ℝ} (hε : 0 < ε)
    (hεsmall : ε < 1 / 10) (hn : 8 / ε ≤ n) :
    2 - ε ≤ wrongDistortion n ∧ 1 + 6 * ε < 2 - ε ∧
    1 / (n - 2) ≤ ε := by
  have hn8 := size_ge_eight hε hεsmall hn
  have hn2 : 0 < n - 2 := by linarith
  have hbudget : 8 ≤ n * ε := (div_le_iff₀ hε).1 hn
  refine ⟨?_, ?_, ?_⟩
  · unfold wrongDistortion
    apply (le_div_iff₀ hn2).2
    nlinarith
  · linarith
  · apply (div_le_iff₀ hn2).2
    nlinarith

/-- The scalar distortion formula exceeds the upper coreset tolerance. -/
theorem wrongDistortion_gt_tolerance {ε n : ℝ} (hε : 0 < ε)
    (hεsmall : ε < 1 / 10) (hn : 8 / ε ≤ n) :
    1 + 6 * ε < wrongDistortion n := by
  obtain ⟨hlarge, hgap, _⟩ := distortion_and_deletion_bounds hε hεsmall hn
  exact hgap.trans_le hlarge

/-- An elementary selection consequence: if the scalar bounds for the
metric construction hold uniformly over its entries, the two score rules have
different strict maximizers. The metric hypotheses themselves are not proved
in this file. -/
theorem opposite_strict_maximizers {I : Type*} [DecidableEq I]
    (Q : Finset I) (g b : I) (proxy exactScore : I → ℝ) {n : ℝ}
    (hn : 8 ≤ n) (hg : g ∈ Q) (hb : b ∈ Q) (hgb : g ≠ b)
    (hproxy : proxy g = singletonProxy n)
    (hotherProxy : ∀ i ∈ Q, i ≠ g → proxy i ≤ 2)
    (hexactBad : corruptionWitness n ≤ exactScore b)
    (hexactGood : ∀ i ∈ Q, i ≠ b → exactScore i ≤ genuineBound n) :
    (g ∈ Q ∧ ∀ i ∈ Q, i ≠ g → proxy i < proxy g) ∧
    (b ∈ Q ∧ ∀ i ∈ Q, i ≠ b → exactScore i < exactScore b) ∧ g ≠ b := by
  refine ⟨⟨hg, ?_⟩, ⟨hb, ?_⟩, hgb⟩
  · intro i hi hig
    rw [hproxy]
    exact (hotherProxy i hi hig).trans_lt (singletonProxy_gt_two hn)
  · intro i hi hib
    exact (hexactGood i hi hib).trans_lt
      ((genuineBound_lt_corruptionWitness hn).trans_le hexactBad)

end

end FTC.CounterexampleArithmetic
