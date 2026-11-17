import FaultTolerantCoresets.Counterexample.ProxyCore
import FaultTolerantCoresets.Counterexample.SensitivityWitnesses

/-! # A genuine factor-two reference clustering and its actual proxy scores -/

namespace FTC.Counterexample

open FTC.CounterexampleArithmetic

def assignedCenter {n : ℕ} (first j i : Fin n) : Vertex n := if i = first then a else p j

/-- The proxy clusters are exactly the fibers of the reference assignment. -/
theorem clusterMembers_eq_assignment_fiber {n : ℕ} (first j i : Fin n) :
    clusterMembers first i = Finset.univ.filter
      (fun z => assignedCenter first j z = assignedCenter first j i) := by
  ext z
  by_cases hi : i = first <;> by_cases hz : z = first <;>
    simp [clusterMembers, assignedCenter, hi, hz]

/-- Every reference assignment is the unique closest of its two centers. -/
theorem reference_assignment_nearest {n : ℕ} (M : ℝ)
    (bad first j : Fin n) (hfirst : first.val = 0) (hj : j.val ≠ 0)
    (hbad : bad.val ≠ 0) (i : Fin n) :
    if i = first then
      graphDist M (corruptedEntries bad i).point a <
        graphDist M (corruptedEntries bad i).point (p j)
    else graphDist M (corruptedEntries bad i).point (p j) <
        graphDist M (corruptedEntries bad i).point a := by
  have hfb : first ≠ bad := by intro h; exact hbad (h ▸ hfirst)
  by_cases hi : i = first
  · subst i
    simpa [corruptedEntries, hfb] using reference_first_nearest M first j hfirst hj
  · rw [if_neg hi]
    by_cases hib : i = bad
    · subst i
      simpa [corruptedEntries] using reference_b_nearest M j
    · have hi0 : i.val ≠ 0 := by
        intro h0
        apply hi
        exact Fin.ext (h0.trans hfirst.symm)
      simpa [corruptedEntries, hib] using reference_other_nearest M i j hi0

theorem reference_cost_formula {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j) :
    corruptCost M hM bad (referenceQuery j) = referenceCost (n : ℝ) := by
  rw [corruptCost_reference M hM bad first j hfirst hj hbad hbj, hM2]
  unfold referenceCost
  ring

/-- The reference centers really are a factor-two approximation on Q. -/
theorem reference_is_two_approx {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j)
    (S : Query n) : corruptCost M hM bad (referenceQuery j) ≤ 2 * corruptCost M hM bad S := by
  rw [reference_cost_formula M hM hM2 bad first j hfirst hj hbad hbj]
  exact reference_two_approx (corrupt_cost_lower_bound M hM (by omega) bad S)

theorem proxy_first_formula {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j) :
    proxy M hM bad first (referenceQuery j) first = singletonProxy (n : ℝ) := by
  have hfb : first ≠ bad := by intro h; exact hbad (h ▸ hfirst)
  rw [proxy_first, corruptContribution_apply, if_neg hfb,
    pointLoss_first_reference M hM first j hfirst hj,
    reference_cost_formula M hM hM2 bad first j hfirst hj hbad hbj]
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd := referenceCost_pos hnR
  unfold singletonProxy
  field_simp [ne_of_gt hd]
  <;> ring

theorem proxy_bad_formula {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j) :
    proxy M hM bad first (referenceQuery j) bad = corruptionProxy (n : ℝ) := by
  have hbf : bad ≠ first := by intro h; exact hbad (h.symm ▸ hfirst)
  rw [proxy_other M hM bad first bad (referenceQuery j) hbf,
    corruptContribution_apply, if_pos rfl, pointLoss_b_reference,
    reference_cost_formula M hM hM2 bad first j hfirst hj hbad hbj, hM2]
  rfl

theorem proxy_ordinary_le {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j i : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j)
    (hif : i ≠ first) (hib : i ≠ bad) :
    proxy M hM bad first (referenceQuery j) i ≤ ordinaryProxy (n : ℝ) := by
  rw [proxy_other M hM bad first i (referenceQuery j) hif,
    corruptContribution_apply, if_neg hib,
    reference_cost_formula M hM hM2 bad first j hfirst hj hbad hbj]
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd := referenceCost_pos hnR
  have hcap := pointLoss_reference_le_one M hM i j
  have hr : 2 * pointLoss M hM (p i) (referenceQuery j) / referenceCost (n : ℝ) ≤
      2 / referenceCost (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hd.le
    linarith
  unfold ordinaryProxy
  linarith

/-- The singleton uniquely maximizes the proxy, although it is genuine. -/
theorem proxy_strict_max {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j i : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j)
    (hif : i ≠ first) :
    proxy M hM bad first (referenceQuery j) i <
      proxy M hM bad first (referenceQuery j) first := by
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [proxy_first_formula M hM hn hM2 bad first j hfirst hj hbad hbj]
  by_cases hib : i = bad
  · subst i
    rw [proxy_bad_formula M hM hM2 bad first j hfirst hj hbad hbj]
    exact (corruptionProxy_lt_two hnR).trans (singletonProxy_gt_two hnR)
  · exact ((proxy_ordinary_le M hM hn hM2 bad first j i hfirst hj hbad hbj hif hib).trans_lt
      (ordinaryProxy_lt_two hnR)).trans (singletonProxy_gt_two hnR)

/-- These are valid pointwise sensitivity upper bounds on the actual Q. -/
theorem sensitivity_le_proxy {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j i : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j) :
    FTC.sensitivity (corruptContribution M hM bad) Finset.univ i ≤
      proxy M hM bad first (referenceQuery j) i := by
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases hib : i = bad
  · subst i
    rw [proxy_bad_formula M hM hM2 bad first j hfirst hj hbad hbj]
    exact (FTC.sensitivity_le_one (corruptContribution_nonneg M hM bad) _ _).trans
      (corruptionProxy_gt_one hnR).le
  · by_cases hif : i = first
    · subst i
      rw [proxy_first_formula M hM hn hM2 bad first j hfirst hj hbad hbj]
      exact (FTC.sensitivity_le_one (corruptContribution_nonneg M hM bad) _ _).trans
        (by linarith [singletonProxy_gt_two hnR])
    · have hterm := cluster_term_le_proxy M hM bad first i (referenceQuery j)
      rw [card_cluster_other first i hif] at hterm
      exact (corrupt_good_sensitivity_le M hM (by omega) bad i hib).trans
        ((genuineBound_le_cluster_term hnR).trans hterm)

end FTC.Counterexample
