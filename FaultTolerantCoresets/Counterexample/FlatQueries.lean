import FaultTolerantCoresets.Counterexample.Queries
import FaultTolerantCoresets.Counterexample.FlatBounds

/-! # Uniform cost bounds for every actual two-center query -/

open scoped BigOperators

namespace FTC.Counterexample

noncomputable def commonLevel {n : ℕ} (M : ℝ) (S : Query n) : ℝ :=
  S.centers.inf' S.nonempty (fun v => baseline M v ^ 2)

/-- Union of the at-most-one original-point exceptions of the two centers. -/
def queryExceptions {n : ℕ} (S : Query n) : Finset (Fin n) :=
  S.centers.biUnion exceptional

theorem queryExceptions_card_le_two {n : ℕ} (S : Query n) :
    (queryExceptions S).card ≤ 2 :=
  card_biUnion_le_two S.centers exceptional S.card_eq exceptional_card_le_one

theorem one_le_commonLevel {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (S : Query n) :
    1 ≤ commonLevel M S := by
  apply Finset.le_inf'
  intro v _
  have hv := one_le_baseline M hM v
  nlinarith

theorem commonLevel_nonneg {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (S : Query n) :
    0 ≤ commonLevel M S := le_trans (by norm_num) (one_le_commonLevel M hM S)

theorem pointLoss_le_commonLevel {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i : Fin n) (S : Query n) : pointLoss M hM (p i) S ≤ commonLevel M S := by
  apply Finset.le_inf'
  intro v hv
  have hpoint : pointLoss M hM (p i) S ≤ graphDist M (p i) v ^ 2 := by
    rw [pointLoss_eq_inf]
    exact Finset.inf'_le _ hv
  have hcap : graphDist M (p i) v ^ 2 ≤ baseline M v ^ 2 := by
    exact (sq_le_sq₀ (graphDist_nonneg M hM _ _) (baseline_nonneg M hM v)).2
      (graphDist_le_baseline M i v)
  exact hpoint.trans hcap

/-- Every original point outside at most two exceptions has the common loss. -/
theorem pointLoss_eq_commonLevel_of_notMem {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i : Fin n) (S : Query n) (hi : i ∉ queryExceptions S) :
    pointLoss M hM (p i) S = commonLevel M S := by
  apply le_antisymm (pointLoss_le_commonLevel M hM i S)
  rw [pointLoss_eq_inf]
  apply Finset.le_inf'
  intro v hv
  have hinot : i ∉ exceptional v := by
    intro h
    exact hi (Finset.mem_biUnion.mpr ⟨v, hv, h⟩)
  rw [graphDist_eq_baseline_of_notMem M i v hinot]
  exact Finset.inf'_le _ hv

theorem commonLevel_mul_card_sub_two_le_cost {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (G : Finset (Fin n)) (S : Query n) :
    ((G.card : ℝ) - 2) * commonLevel M S ≤ FTC.cost (cleanContribution M hM) G S := by
  have he : ((queryExceptions S).card : ℝ) ≤ 2 := by
    exact_mod_cast queryExceptions_card_le_two S
  calc
    ((G.card : ℝ) - 2) * commonLevel M S ≤
        ((G.card : ℝ) - ((queryExceptions S).card : ℝ)) * commonLevel M S :=
      mul_le_mul_of_nonneg_right (by linarith) (commonLevel_nonneg M hM S)
    _ ≤ ∑ i ∈ G, cleanContribution M hM i S := by
      apply sum_lower_bound_of_flat G (queryExceptions S)
        (fun i => cleanContribution M hM i S) (commonLevel M S)
        (fun i => cleanContribution_nonneg M hM i S) (commonLevel_nonneg M hM S)
      intro i hi
      simp only [cleanContribution_apply]
      exact pointLoss_eq_commonLevel_of_notMem M hM i S (Finset.mem_sdiff.mp hi).2
    _ = FTC.cost (cleanContribution M hM) G S := rfl

theorem pointLoss_mul_card_sub_two_le_cost {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (G : Finset (Fin n)) (hG : 2 ≤ G.card) (i : Fin n) (S : Query n) :
    ((G.card : ℝ) - 2) * pointLoss M hM (p i) S ≤
      FTC.cost (cleanContribution M hM) G S := by
  have hcoef : 0 ≤ (G.card : ℝ) - 2 := by
    have h : (2 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hG
    linarith
  exact (mul_le_mul_of_nonneg_left (pointLoss_le_commonLevel M hM i S) hcoef).trans
    (commonLevel_mul_card_sub_two_le_cost M hM G S)

theorem card_sub_two_le_cost {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (G : Finset (Fin n)) (hG : 2 ≤ G.card) (S : Query n) :
    (G.card : ℝ) - 2 ≤ FTC.cost (cleanContribution M hM) G S := by
  have hcoef : 0 ≤ (G.card : ℝ) - 2 := by
    have h : (2 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hG
    linarith
  calc
    (G.card : ℝ) - 2 = ((G.card : ℝ) - 2) * 1 := by ring
    _ ≤ ((G.card : ℝ) - 2) * commonLevel M S :=
      mul_le_mul_of_nonneg_left (one_le_commonLevel M hM S) hcoef
    _ ≤ FTC.cost (cleanContribution M hM) G S :=
      commonLevel_mul_card_sub_two_le_cost M hM G S

theorem cost_good_eq_clean {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad : Fin n) (G : Finset (Fin n)) (hG : bad ∉ G) (S : Query n) :
    FTC.cost (corruptContribution M hM bad) G S = FTC.cost (cleanContribution M hM) G S := by
  apply FTC.cost_congr
  intro i hi T
  have hib : i ≠ bad := by intro h; subst i; exact hG hi
  simp [corruptContribution_apply, hib]

theorem clean_uniform_bound {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 2 ≤ n) (i : Fin n) (S : Query n) :
    ((n : ℝ) - 2) * cleanContribution M hM i S ≤ cleanCost M hM S := by
  simpa [cleanCost] using pointLoss_mul_card_sub_two_le_cost M hM
    (Finset.univ : Finset (Fin n)) (by simpa) i S

theorem corrupt_uniform_good_bound {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 3 ≤ n) (bad i : Fin n) (hib : i ≠ bad) (S : Query n) :
    ((n : ℝ) - 3) * corruptContribution M hM bad i S ≤ corruptCost M hM bad S := by
  let G := (Finset.univ : Finset (Fin n)).erase bad
  have hcard := Finset.card_erase_add_one (Finset.mem_univ bad)
  have hcardR : (G.card : ℝ) + 1 = (n : ℝ) := by
    have hcN : G.card + 1 = n := by simpa [G] using hcard
    exact_mod_cast hcN
  have hG : 2 ≤ G.card := by
    have hc : G.card + 1 = n := by simpa [G] using hcard
    omega
  have hflat := pointLoss_mul_card_sub_two_le_cost M hM G hG i S
  have heq := cost_good_eq_clean M hM bad G (by simp [G]) S
  have hmono := FTC.cost_mono (corruptContribution_nonneg M hM bad)
    (Finset.erase_subset bad Finset.univ) S
  change FTC.cost (corruptContribution M hM bad) G S ≤ _ at hmono
  rw [heq] at hmono
  have hci : corruptContribution M hM bad i S = pointLoss M hM (p i) S := by simp [hib]
  rw [hci]
  have hcoef : (G.card : ℝ) - 2 = (n : ℝ) - 3 := by linarith
  rw [hcoef] at hflat
  exact hflat.trans hmono

theorem corrupt_cost_lower_bound {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 3 ≤ n) (bad : Fin n) (S : Query n) :
    (n : ℝ) - 3 ≤ corruptCost M hM bad S := by
  let G := (Finset.univ : Finset (Fin n)).erase bad
  have hcard := Finset.card_erase_add_one (Finset.mem_univ bad)
  have hcardR : (G.card : ℝ) + 1 = (n : ℝ) := by
    have hcN : G.card + 1 = n := by simpa [G] using hcard
    exact_mod_cast hcN
  have hG : 2 ≤ G.card := by
    have hc : G.card + 1 = n := by simpa [G] using hcard
    omega
  have hlo := card_sub_two_le_cost M hM G hG S
  have heq := cost_good_eq_clean M hM bad G (by simp [G]) S
  have hmono := FTC.cost_mono (corruptContribution_nonneg M hM bad)
    (Finset.erase_subset bad Finset.univ) S
  change FTC.cost (corruptContribution M hM bad) G S ≤ _ at hmono
  rw [heq] at hmono
  change (n : ℝ) - 3 ≤ FTC.cost (corruptContribution M hM bad) Finset.univ S
  linarith

end FTC.Counterexample
