import FaultTolerantCoresets.FiniteMetric.SensitivityReduction

/-!
# Indexed weighted form of Theorem 4.1

This version applies directly to the weighted summaries consumed by the
filtering decoder. Identical locations have separate entry indices, and an
entry of weight zero has sensitivity zero. The constrained oracle minimizes
the weighted objective over the same finite admissible-center sets.
-/

namespace FTC.FiniteMetric

variable {I X : Type*} [DecidableEq I] [Fintype X] [DecidableEq X] [MetricSpace X]
  {k : ℕ}

omit [Fintype X] [DecidableEq X] in
/-- Squaring the radius does not change the admissible-center constraint. -/
theorem admissible_dist_iff (p x : X) (C : CenterSet X k) :
    Admissible p (dist p x ^ 2) C ↔ ∀ y ∈ C.centers, dist p x ≤ dist p y := by
  constructor
  · intro h y hy
    exact (sq_le_sq₀ dist_nonneg dist_nonneg).1 (h y hy)
  · intro h y hy
    exact (sq_le_sq₀ dist_nonneg dist_nonneg).2 (h y hy)

/-- A separate weighted contribution for each stored index. -/
noncomputable def weightedLoss (entries : I → Entry X) (i : I) (C : CenterSet X k) : ℝ :=
  contribution kmeansLoss entries i C

theorem weightedLoss_nonneg (entries : I → Entry X) (i : I) (C : CenterSet X k) :
    0 ≤ weightedLoss entries i C :=
  contribution_nonneg kmeansLoss entries kmeansLoss_nonneg i C

theorem weightedSensitivity_of_weight_zero (entries : I → Entry X)
    (U : Finset I) (p : I) (hw : (entries p).weight = 0) :
    sensitivity (weightedLoss (k := k) entries) U p = 0 := by
  by_cases hp : p ∈ U
  · apply le_antisymm
    · apply sensitivity_le_of_contribution_le (weightedLoss_nonneg entries) hp le_rfl
      intro C
      simp [weightedLoss, contribution, hw]
    · exact sensitivity_nonneg (weightedLoss_nonneg entries) U p
  · exact sensitivity_of_not_mem hp

/-- Specification of the weighted constrained oracle needed for one indexed
sensitivity. Its output cost is compared with every feasible competitor. -/
structure IndexedConstrainedOracle (U : Finset I) (entries : I → Entry X)
    (p : I) (ρ : ℝ) where
  solve : ∀ x : X,
    FeasibleRadius (k := k) (entries p).point x → CenterSet X k
  admissible : ∀ x h,
    Admissible (entries p).point (dist (entries p).point x ^ 2) (solve x h)
  approximation : ∀ x h (C : CenterSet X k),
    Admissible (entries p).point (dist (entries p).point x ^ 2) C →
    cost (weightedLoss entries) U (solve x h) ≤ ρ * cost (weightedLoss entries) U C

variable {U : Finset I} {entries : I → Entry X} {p : I} {ρ : ℝ}

/-- A weighted trial score; the numerator uses the queried entry's own weight. -/
noncomputable def weightedTrialScore
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ) (x : X) : ℝ := by
  classical
  exact if h : FeasibleRadius (k := k) (entries p).point x then
    ((entries p).weight * dist (entries p).point x ^ 2) /
      cost (weightedLoss entries) U (oracle.solve x h)
  else 0

noncomputable def weightedEstimate
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ) : ℝ :=
  (Finset.univ : Finset X).sup' ⟨(entries p).point, Finset.mem_univ _⟩
    (weightedTrialScore oracle)

theorem weightedTrialScore_nonneg
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ) (x : X) :
    0 ≤ weightedTrialScore oracle x := by
  unfold weightedTrialScore
  split_ifs
  · exact div_nonneg (mul_nonneg (entries p).weight_nonneg (sq_nonneg _))
      (cost_nonneg (weightedLoss_nonneg entries) _ _)
  · exact le_rfl

omit [DecidableEq I] [DecidableEq X] in
theorem weightedTrialScore_le_estimate
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ) (x : X) :
    weightedTrialScore oracle x ≤ weightedEstimate oracle := by
  exact Finset.le_sup' (weightedTrialScore oracle) (Finset.mem_univ x)

theorem weightedEstimate_nonneg
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ) :
    0 ≤ weightedEstimate oracle :=
  (weightedTrialScore_nonneg oracle (entries p).point).trans
    (weightedTrialScore_le_estimate oracle (entries p).point)

theorem weightedTrialScore_le_sensitivity
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ)
    (hp : p ∈ U) (x : X) :
    weightedTrialScore oracle x ≤ sensitivity (weightedLoss (k := k) entries) U p := by
  unfold weightedTrialScore
  split_ifs with h
  · let C := oracle.solve x h
    change ((entries p).weight * dist (entries p).point x ^ 2) /
        cost (weightedLoss entries) U C ≤ sensitivity (weightedLoss (k := k) entries) U p
    have hr : (entries p).weight * dist (entries p).point x ^ 2 ≤ weightedLoss entries p C := by
      have hd := (admissible_iff (entries p).point _ C).1 (oracle.admissible x h)
      exact mul_le_mul_of_nonneg_left hd (entries p).weight_nonneg
    have hc : 0 ≤ cost (weightedLoss entries) U C :=
      cost_nonneg (weightedLoss_nonneg entries) U C
    by_cases hz : cost (weightedLoss entries) U C = 0
    · simpa [hz] using sensitivity_nonneg (weightedLoss_nonneg entries) U p
    · have hcpos : 0 < cost (weightedLoss entries) U C := lt_of_le_of_ne hc (Ne.symm hz)
      have hs := contribution_le_sensitivity_mul_cost (weightedLoss_nonneg entries) hp C
      exact (div_le_iff₀ hcpos).2 (hr.trans hs)
  · exact sensitivity_nonneg (weightedLoss_nonneg entries) U p

theorem weightedEstimate_le_sensitivity
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ) (hp : p ∈ U) :
    weightedEstimate oracle ≤ sensitivity (weightedLoss (k := k) entries) U p := by
  apply Finset.sup'_le
  intro x _
  exact weightedTrialScore_le_sensitivity oracle hp x

theorem weighted_contribution_le_estimate_mul_cost
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ)
    (hp : p ∈ U) (hρ : 0 < ρ) (C : CenterSet X k) :
    weightedLoss entries p C ≤
      (ρ * weightedEstimate oracle) * cost (weightedLoss entries) U C := by
  have he : 0 ≤ weightedEstimate oracle := weightedEstimate_nonneg oracle
  have hc : 0 ≤ cost (weightedLoss entries) U C :=
    cost_nonneg (weightedLoss_nonneg entries) U C
  by_cases hz : weightedLoss entries p C = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg hρ.le he) hc
  · have hlpos : 0 < weightedLoss entries p C :=
      lt_of_le_of_ne (weightedLoss_nonneg entries p C) (Ne.symm hz)
    obtain ⟨x, hx, hclosest⟩ := exists_closest_center (entries p).point C
    have hCadm : Admissible (entries p).point (dist (entries p).point x ^ 2) C := by
      rw [admissible_iff, ← hclosest]
    have hfeas : FeasibleRadius (k := k) (entries p).point x := ⟨C, hCadm⟩
    let D := oracle.solve x hfeas
    have hD : weightedLoss entries p C ≤ weightedLoss entries p D := by
      have hd := (admissible_iff (entries p).point _ D).1 (oracle.admissible x hfeas)
      rw [← hclosest] at hd
      exact mul_le_mul_of_nonneg_left hd (entries p).weight_nonneg
    have hdpos : 0 < cost (weightedLoss entries) U D :=
      lt_of_lt_of_le (hlpos.trans_le hD)
        (contribution_le_cost (weightedLoss_nonneg entries) hp D)
    have htrial : weightedTrialScore oracle x =
        weightedLoss entries p C / cost (weightedLoss entries) U D := by
      simp only [weightedTrialScore, dif_pos hfeas]
      rw [weightedLoss, contribution, hclosest]
    have hscore : weightedLoss entries p C ≤
        weightedEstimate oracle * cost (weightedLoss entries) U D := by
      apply (div_le_iff₀ hdpos).1
      rw [← htrial]
      exact weightedTrialScore_le_estimate oracle x
    have happ : cost (weightedLoss entries) U D ≤ ρ * cost (weightedLoss entries) U C :=
      oracle.approximation x hfeas C hCadm
    calc
      weightedLoss entries p C ≤
          weightedEstimate oracle * cost (weightedLoss entries) U D := hscore
      _ ≤ weightedEstimate oracle * (ρ * cost (weightedLoss entries) U C) :=
        mul_le_mul_of_nonneg_left happ he
      _ = (ρ * weightedEstimate oracle) * cost (weightedLoss entries) U C := by ring

/-- The weighted extension of Theorem 4.1, with separately indexed copies. -/
theorem weightedEstimate_approximates_sensitivity
    (oracle : IndexedConstrainedOracle (k := k) U entries p ρ)
    (hp : p ∈ U) (hρ : 0 < ρ) :
    sensitivity (weightedLoss (k := k) entries) U p / ρ ≤ weightedEstimate oracle ∧
      weightedEstimate oracle ≤ sensitivity (weightedLoss (k := k) entries) U p := by
  constructor
  · apply (div_le_iff₀ hρ).2
    have hbound : sensitivity (weightedLoss (k := k) entries) U p ≤
        ρ * weightedEstimate oracle :=
      sensitivity_le_of_contribution_le (weightedLoss_nonneg entries) hp
        (mul_nonneg hρ.le (weightedEstimate_nonneg oracle))
        (weighted_contribution_le_estimate_mul_cost oracle hp hρ)
    simpa [mul_comm] using hbound
  · exact weightedEstimate_le_sensitivity oracle hp

/-- A family of constrained weighted solvers supplies exactly the oracle API
used by the deterministic filtering theorem. -/
noncomputable def indexedApproxSensitivityOracle
    (entries : I → Entry X) (ρ : ℝ) (hρ : 0 < ρ)
    (solvers : ∀ (U : Finset I) (p : I), IndexedConstrainedOracle (k := k) U entries p ρ) :
    ApproxSensitivityOracle (weightedLoss (k := k) entries) ρ where
  score U p := weightedEstimate (solvers U p)
  lower U p hp := by
    have h := (weightedEstimate_approximates_sensitivity (solvers U p) hp hρ).1
    have h' := (div_le_iff₀ hρ).1 h
    simpa [mul_comm] using h'
  upper U p hp :=
    (weightedEstimate_approximates_sensitivity (solvers U p) hp hρ).2

omit [DecidableEq I] in
theorem weighted_oracle_calls_le_card (entries : I → Entry X) (p : I) :
    (queriedRadii (k := k) (entries p).point).card ≤ Fintype.card X :=
  oracle_calls_le_card (entries p).point

end FTC.FiniteMetric
