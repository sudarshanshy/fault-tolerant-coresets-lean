import FaultTolerantCoresets.Counterexample.SensitivityBounds
import FaultTolerantCoresets.Counterexample.Witnesses
import FaultTolerantCoresets.CounterexampleArithmetic

/-! # Exact clean sensitivities and the corruption's witnessing query -/

namespace FTC.Counterexample

theorem exists_two_other_indices {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    ∃ j l : Fin n, j ≠ l ∧ i ≠ j ∧ i ≠ l := by
  have hc := Finset.card_erase_add_one (Finset.mem_univ i)
  have hG : 1 < ((Finset.univ : Finset (Fin n)).erase i).card := by
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨j, l, hj, hl, hjl⟩ := Finset.one_lt_card_iff.mp hG
  exact ⟨j, l, hjl, Ne.symm (Finset.mem_erase.mp hj).1,
    Ne.symm (Finset.mem_erase.mp hl).1⟩

/-- Every clean entry has exactly the sensitivity asserted in Appendix A.1. -/
theorem clean_sensitivity_eq {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 3 ≤ n) (i : Fin n) :
    FTC.sensitivity (cleanContribution M hM) Finset.univ i = 1 / ((n : ℝ) - 2) := by
  apply le_antisymm (clean_sensitivity_le M hM hn i)
  obtain ⟨j, l, hjl, hij, hil⟩ := exists_two_other_indices hn i
  have h := FTC.contribution_le_sensitivity_mul_cost (cleanContribution_nonneg M hM)
    (Finset.mem_univ i) (simplexQuery j l hjl)
  have hci : cleanContribution M hM i (simplexQuery j l hjl) = 1 := by
    rw [cleanContribution_apply, pointLoss_simplex, if_neg hij, if_neg hil]
  change _ ≤ _ * cleanCost M hM (simplexQuery j l hjl) at h
  rw [hci, cleanCost_simplex] at h
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (div_le_iff₀ (by linarith : 0 < (n : ℝ) - 2)).2
  simpa [mul_comm] using h

theorem corruption_sensitivity_lower {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 4 ≤ n) (bad j l : Fin n) (hjl : j ≠ l) (hbj : bad ≠ j) (hbl : bad ≠ l) :
    M ^ 2 / ((n : ℝ) - 3 + M ^ 2) ≤
      FTC.sensitivity (corruptContribution M hM bad) Finset.univ bad := by
  have h := FTC.contribution_le_sensitivity_mul_cost (corruptContribution_nonneg M hM bad)
    (Finset.mem_univ bad) (simplexQuery j l hjl)
  change _ ≤ _ * corruptCost M hM bad (simplexQuery j l hjl) at h
  simp only [corruptContribution_apply, if_pos rfl, pointLoss_b_simplex] at h
  rw [corruptCost_simplex M hM bad j l hjl hbj hbl] at h
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (div_le_iff₀ (by nlinarith [sq_nonneg M] : 0 < (n : ℝ) - 3 + M ^ 2)).2
  simpa [mul_comm] using h

/-- Exact sensitivity strictly prefers the corruption to every genuine entry. -/
theorem corruption_strict_sensitivity_max {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4)
    (bad j l : Fin n) (hjl : j ≠ l) (hbj : bad ≠ j) (hbl : bad ≠ l)
    (i : Fin n) (hib : i ≠ bad) :
    FTC.sensitivity (corruptContribution M hM bad) Finset.univ i <
      FTC.sensitivity (corruptContribution M hM bad) Finset.univ bad := by
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlo := corruption_sensitivity_lower M hM (by omega) bad j l hjl hbj hbl
  have hden : (n : ℝ) - 3 + M ^ 2 = 2 * (n : ℝ) - 7 := by rw [hM2]; ring
  rw [hden, hM2] at hlo
  exact (corrupt_good_sensitivity_le M hM (by omega) bad i hib).trans_lt
    ((FTC.CounterexampleArithmetic.genuineBound_lt_corruptionWitness hnR).trans_le hlo)

end FTC.Counterexample
