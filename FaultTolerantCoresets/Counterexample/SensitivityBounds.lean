import FaultTolerantCoresets.Counterexample.FlatQueries
import FaultTolerantCoresets.Sensitivity

/-! # Uniform sensitivity and clean-deletion guarantees -/

namespace FTC.Counterexample

theorem clean_entry_bound {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 3 ≤ n) (i : Fin n) (S : Query n) :
    cleanContribution M hM i S ≤ (1 / ((n : ℝ) - 2)) * cleanCost M hM S := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  have h := clean_uniform_bound M hM (by omega) i S
  calc
    cleanContribution M hM i S ≤ cleanCost M hM S / ((n : ℝ) - 2) :=
      (le_div_iff₀ hd).2 (by nlinarith [h])
    _ = (1 / ((n : ℝ) - 2)) * cleanCost M hM S := by ring

theorem clean_sensitivity_le {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 3 ≤ n) (i : Fin n) :
    FTC.sensitivity (cleanContribution M hM) Finset.univ i ≤ 1 / ((n : ℝ) - 2) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply FTC.sensitivity_le_of_contribution_le (cleanContribution_nonneg M hM)
    (Finset.mem_univ i) (div_nonneg (by norm_num) (by linarith))
  exact clean_entry_bound M hM hn i

theorem corrupt_good_entry_bound {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 4 ≤ n) (bad i : Fin n) (hib : i ≠ bad) (S : Query n) :
    corruptContribution M hM bad i S ≤
      (1 / ((n : ℝ) - 3)) * corruptCost M hM bad S := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 3 := by linarith
  have h := corrupt_uniform_good_bound M hM (by omega) bad i hib S
  calc
    corruptContribution M hM bad i S ≤ corruptCost M hM bad S / ((n : ℝ) - 3) :=
      (le_div_iff₀ hd).2 (by nlinarith [h])
    _ = (1 / ((n : ℝ) - 3)) * corruptCost M hM bad S := by ring

theorem corrupt_good_sensitivity_le {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 4 ≤ n) (bad i : Fin n) (hib : i ≠ bad) :
    FTC.sensitivity (corruptContribution M hM bad) Finset.univ i ≤
      1 / ((n : ℝ) - 3) := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply FTC.sensitivity_le_of_contribution_le (corruptContribution_nonneg M hM bad)
    (Finset.mem_univ i) (div_nonneg (by norm_num) (by linarith))
  exact corrupt_good_entry_bound M hM hn bad i hib

/-- Removing the corruption yields an ε-coreset: only the one original clean
copy at its former location is missing. -/
theorem exact_deletion_isCoreset {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 3 ≤ n) (bad : Fin n) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : 1 / ((n : ℝ) - 2) ≤ ε) :
    FTC.IsCoreset ε (cleanCost M hM)
      (FTC.cost (corruptContribution M hM bad) (Finset.univ.erase bad)) := by
  intro S
  have heq := cost_good_eq_clean M hM bad (Finset.univ.erase bad) (by simp) S
  rw [heq]
  have hc : 0 ≤ cleanCost M hM S := FTC.cost_nonneg (cleanContribution_nonneg M hM) _ _
  have hci : 0 ≤ cleanContribution M hM bad S := cleanContribution_nonneg M hM bad S
  have hentry := clean_entry_bound M hM hn bad S
  have hbudget := mul_le_mul_of_nonneg_right hsmall hc
  have herase := FTC.cost_erase_add (cleanContribution M hM) (Finset.mem_univ bad) S
  change FTC.cost (cleanContribution M hM) (Finset.univ.erase bad) S +
    cleanContribution M hM bad S = cleanCost M hM S at herase
  constructor <;> nlinarith

end FTC.Counterexample
