import FaultTolerantCoresets.Hardness.MetricExtension

/-!
# The exact optimum-to-sensitivity identity in Appendix B

The optimum is attained by an actual finite k-center set. Queries containing
the added point have zero numerator; all other queries are lifted original
queries. Consequently the genuine sensitivity supremum is
`D² / (D² + L * OPT)`, including the case `OPT = 0`.
-/

namespace FTC.Hardness

open FTC.FiniteMetric

variable {X : Type*} [DecidableEq X] [Fintype X] [MetricSpace X] {k : ℕ}

instance finiteCenterSet : Finite (CenterSet X k) :=
  Finite.of_injective CenterSet.centers (fun _ _ h => centerSet_ext h)

theorem centerSet_nonempty (hk : 0 < k) (hkX : k ≤ Fintype.card X) :
    Nonempty (CenterSet X k) := by
  obtain ⟨C, _, hC⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset X).card by simpa using hkX)
  exact ⟨⟨C, hC, Finset.card_pos.mp (hC ▸ hk)⟩⟩

theorem exists_optimalCenters (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X) :
    ∃ C : CenterSet X k, ∀ E : CenterSet X k, cost kmeansLoss P C ≤ cost kmeansLoss P E := by
  classical
  letI : Fintype (CenterSet X k) := Fintype.ofFinite _
  letI : Nonempty (CenterSet X k) := centerSet_nonempty hk hkX
  obtain ⟨C, _, hC⟩ := Finset.exists_min_image
    (Finset.univ : Finset (CenterSet X k)) (cost kmeansLoss P) Finset.univ_nonempty
  exact ⟨C, fun E => hC E (Finset.mem_univ E)⟩

noncomputable def optimalCenters (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X) :
    CenterSet X k := (exists_optimalCenters P hk hkX).choose

noncomputable def optimum (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X) : ℝ :=
  cost kmeansLoss P (optimalCenters P hk hkX)

theorem optimum_nonneg (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X) :
    0 ≤ optimum P hk hkX := cost_nonneg kmeansLoss_nonneg _ _

theorem optimum_le (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X)
    (C : CenterSet X k) : optimum P hk hkX ≤ cost kmeansLoss P C :=
  (exists_optimalCenters P hk hkX).choose_spec C

/-- Exact identity, first stated with an arbitrary globally optimal center set. -/
theorem sensitivity_eq_of_optimal (P : Finset X) (D : ℝ) (hD : 0 < D)
    {L : ℝ} (hL : 0 ≤ L) (Copt : CenterSet X k)
    (hopt : ∀ E : CenterSet X k, cost kmeansLoss P Copt ≤ cost kmeansLoss P E) :
    sensitivity (gadgetContribution (k := k) D L) (extendedClients P) none =
      D ^ 2 / (D ^ 2 + L * cost kmeansLoss P Copt) := by
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hc : 0 ≤ cost kmeansLoss P Copt := cost_nonneg kmeansLoss_nonneg _ _
  have hden : 0 < D ^ 2 + L * cost kmeansLoss P Copt :=
    add_pos_of_pos_of_nonneg hD2 (mul_nonneg hL hc)
  have hr : 0 ≤ D ^ 2 / (D ^ 2 + L * cost kmeansLoss P Copt) :=
    div_nonneg hD2.le hden.le
  apply le_antisymm
  · apply sensitivity_le_of_contribution_le (gadgetContribution_nonneg D hL)
      (none_mem_extendedClients P) hr
    intro C
    by_cases hnew : none ∈ C.centers
    · simp only [gadgetContribution, extensionLoss_new_of_mem D C hnew]
      exact mul_nonneg hr (cost_nonneg (gadgetContribution_nonneg D hL) _ _)
    · rw [← lift_lowerCenters C hnew]
      simp only [gadgetContribution, extensionLoss_new_lift, gadgetCost_lift]
      calc
        D ^ 2 = (D ^ 2 / (D ^ 2 + L * cost kmeansLoss P Copt)) *
            (D ^ 2 + L * cost kmeansLoss P Copt) :=
          (div_mul_cancel₀ _ hden.ne').symm
        _ ≤ (D ^ 2 / (D ^ 2 + L * cost kmeansLoss P Copt)) *
            (D ^ 2 + L * cost kmeansLoss P (lowerCenters C hnew)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add_right (mul_le_mul_of_nonneg_left (hopt _) hL) _) hr
  · apply (div_le_iff₀ hden).2
    have h := contribution_le_sensitivity_mul_cost (gadgetContribution_nonneg D hL)
      (none_mem_extendedClients P) (liftCenters Copt)
    simpa only [gadgetContribution, extensionLoss_new_lift, gadgetCost_lift] using h

/-- The exact identity claimed in the proof of Theorem 4.2. -/
theorem sensitivity_formula (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X)
    (D : ℝ) (hD : 0 < D) {L : ℝ} (hL : 0 ≤ L) :
    sensitivity (gadgetContribution (k := k) D L) (extendedClients P) none =
      D ^ 2 / (D ^ 2 + L * optimum P hk hkX) :=
  sensitivity_eq_of_optimal P D hD hL (optimalCenters P hk hkX)
    (optimum_le P hk hkX)

/-- The same identity for the project's actual weighted metric k-means API. -/
theorem weighted_sensitivity_formula (P : Finset X) (hk : 0 < k)
    (hkX : k ≤ Fintype.card X) (D : ℝ) (hD : 0 < D)
    (hdiam : ∀ x y : X, dist x y ≤ D) {L : ℝ} (hL : 0 ≤ L) :
    letI := extensionMetric D hD hdiam
    sensitivity (weightedLoss (k := k) (gadgetEntries L hL)) (extendedClients P) none =
      D ^ 2 / (D ^ 2 + L * optimum P hk hkX) := by
  rw [← gadgetContribution_eq_weightedLoss D hD hdiam hL]
  exact sensitivity_formula P hk hkX D hD hL

end FTC.Hardness
