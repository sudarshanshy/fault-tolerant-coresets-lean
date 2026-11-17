import FaultTolerantCoresets.Sensitivity
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Theorem 4.1: constrained finite-metric k-means gives sensitivities

The oracle is called once for each feasible radius indexed by an ambient point.
Infeasible radii are skipped. Squared radii are used throughout; they induce the
same admissible center sets as the radii in the paper. Real division sets a
zero-cost ratio to zero, and the proof treats that case explicitly.
-/

namespace FTC.FiniteMetric

variable {X : Type*} [Fintype X] [DecidableEq X] [MetricSpace X] {k : ℕ}

/-- A feasible solution has exactly `k` distinct centers and is nonempty. -/
structure CenterSet (X : Type*) (k : ℕ) where
  centers : Finset X
  card_eq : centers.card = k
  nonempty : centers.Nonempty

/-- Squared distance to the closest center. -/
noncomputable def kmeansLoss (p : X) (C : CenterSet X k) : ℝ :=
  C.centers.inf' C.nonempty (fun x => dist p x ^ 2)

theorem kmeansLoss_nonneg (p : X) (C : CenterSet X k) : 0 ≤ kmeansLoss p C := by
  apply Finset.le_inf'
  intro x _
  exact sq_nonneg (dist p x)

theorem kmeansLoss_le_dist_sq (p : X) (C : CenterSet X k)
    {x : X} (hx : x ∈ C.centers) : kmeansLoss p C ≤ dist p x ^ 2 := by
  exact Finset.inf'_le _ hx

theorem exists_closest_center (p : X) (C : CenterSet X k) :
    ∃ x ∈ C.centers, kmeansLoss p C = dist p x ^ 2 := by
  exact Finset.exists_mem_eq_inf' C.nonempty (fun x => dist p x ^ 2)

/-- Every center must lie outside the open ball of squared radius `r`. -/
def Admissible (p : X) (r : ℝ) (C : CenterSet X k) : Prop :=
  ∀ x ∈ C.centers, r ≤ dist p x ^ 2

theorem admissible_iff (p : X) (r : ℝ) (C : CenterSet X k) :
    Admissible p r C ↔ r ≤ kmeansLoss p C := by
  exact (Finset.le_inf'_iff C.nonempty _).symm

/-- A trial is feasible when at least `k` admissible centers can be selected. -/
def FeasibleRadius (p x : X) : Prop :=
  ∃ C : CenterSet X k, Admissible p (dist p x ^ 2) C

/-- The finite admissible-center set; feasibility can be tested without an
optimization-oracle call by counting these centers. -/
noncomputable def admissibleCenters (p : X) (r : ℝ) : Finset X := by
  classical
  exact (Finset.univ : Finset X).filter (fun y => r ≤ dist p y ^ 2)

theorem feasibleRadius_iff_card (p x : X) :
    FeasibleRadius (k := k) p x ↔
      0 < k ∧ k ≤ (admissibleCenters p (dist p x ^ 2)).card := by
  classical
  constructor
  · rintro ⟨C, hC⟩
    constructor
    · simpa [C.card_eq] using C.nonempty.card_pos
    · have hsub : C.centers ⊆ admissibleCenters p (dist p x ^ 2) := by
        intro y hy
        simp only [admissibleCenters, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hC y hy
      simpa [C.card_eq] using Finset.card_le_card hsub
  · rintro ⟨hk, hcard⟩
    obtain ⟨Q, hQ, hQcard⟩ := Finset.exists_subset_card_eq hcard
    have hQnonempty : Q.Nonempty := Finset.card_pos.mp (by simpa [hQcard] using hk)
    refine ⟨⟨Q, hQcard, hQnonempty⟩, ?_⟩
    intro y hy
    have hmem := hQ hy
    simpa only [admissibleCenters, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- The specification of a constrained approximation oracle, restricted to the
at most `|X|` instances needed for one sensitivity estimate. The comparison
against every feasible solution is equivalent to comparison against the
optimum, and avoids choosing an optimal solution in the interface. -/
structure ConstrainedOracle (P : Finset X) (p : X) (ρ : ℝ) where
  solve : ∀ x : X, FeasibleRadius (k := k) p x → CenterSet X k
  admissible : ∀ x h, Admissible p (dist p x ^ 2) (solve x h)
  approximation : ∀ x h (C : CenterSet X k), Admissible p (dist p x ^ 2) C →
    cost kmeansLoss P (solve x h) ≤ ρ * cost kmeansLoss P C

variable {P : Finset X} {p : X} {ρ : ℝ}

/-- Score from one trial; infeasible radii contribute zero. -/
noncomputable def trialScore (oracle : ConstrainedOracle (k := k) P p ρ)
    (x : X) : ℝ := by
  classical
  exact if h : FeasibleRadius (k := k) p x then
    dist p x ^ 2 / cost kmeansLoss P (oracle.solve x h)
  else 0

/-- The largest of at most `|X|` trial scores. -/
noncomputable def estimate (oracle : ConstrainedOracle (k := k) P p ρ) : ℝ :=
  (Finset.univ : Finset X).sup' ⟨p, Finset.mem_univ p⟩ (trialScore oracle)

theorem trialScore_nonneg (oracle : ConstrainedOracle (k := k) P p ρ) (x : X) :
    0 ≤ trialScore oracle x := by
  unfold trialScore
  split_ifs
  · exact div_nonneg (sq_nonneg _) (cost_nonneg kmeansLoss_nonneg _ _)
  · exact le_rfl

theorem trialScore_le_estimate (oracle : ConstrainedOracle (k := k) P p ρ) (x : X) :
    trialScore oracle x ≤ estimate oracle := by
  exact Finset.le_sup' (trialScore oracle) (Finset.mem_univ x)

theorem estimate_nonneg (oracle : ConstrainedOracle (k := k) P p ρ) :
    0 ≤ estimate oracle :=
  (trialScore_nonneg oracle p).trans (trialScore_le_estimate oracle p)

/-- Every feasible trial provides a lower bound on exact sensitivity. -/
theorem trialScore_le_sensitivity (oracle : ConstrainedOracle (k := k) P p ρ)
    (hp : p ∈ P) (x : X) :
    trialScore oracle x ≤ sensitivity (kmeansLoss (k := k)) P p := by
  unfold trialScore
  split_ifs with h
  · let C := oracle.solve x h
    change dist p x ^ 2 / cost kmeansLoss P C ≤ sensitivity (kmeansLoss (k := k)) P p
    have hr : dist p x ^ 2 ≤ kmeansLoss p C :=
      (admissible_iff p _ C).1 (oracle.admissible x h)
    have hc : 0 ≤ cost kmeansLoss P C := cost_nonneg kmeansLoss_nonneg P C
    by_cases hz : cost kmeansLoss P C = 0
    · simpa [hz] using sensitivity_nonneg kmeansLoss_nonneg P p
    · have hcpos : 0 < cost kmeansLoss P C := lt_of_le_of_ne hc (Ne.symm hz)
      have hs := contribution_le_sensitivity_mul_cost kmeansLoss_nonneg hp C
      exact (div_le_iff₀ hcpos).2 (hr.trans hs)
  · exact sensitivity_nonneg kmeansLoss_nonneg P p

theorem estimate_le_sensitivity (oracle : ConstrainedOracle (k := k) P p ρ)
    (hp : p ∈ P) : estimate oracle ≤ sensitivity (kmeansLoss (k := k)) P p := by
  apply Finset.sup'_le
  intro x _
  exact trialScore_le_sensitivity oracle hp x

/-- For every query, the trial at its closest-center radius recovers at least
`1 / ρ` of that query's sensitivity ratio. -/
theorem contribution_le_estimate_mul_cost
    (oracle : ConstrainedOracle (k := k) P p ρ) (hp : p ∈ P) (hρ : 0 < ρ)
    (C : CenterSet X k) :
    kmeansLoss p C ≤ (ρ * estimate oracle) * cost kmeansLoss P C := by
  have he : 0 ≤ estimate oracle := estimate_nonneg oracle
  have hc : 0 ≤ cost kmeansLoss P C := cost_nonneg kmeansLoss_nonneg P C
  by_cases hz : kmeansLoss p C = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg hρ.le he) hc
  · have hlpos : 0 < kmeansLoss p C :=
      lt_of_le_of_ne (kmeansLoss_nonneg p C) (Ne.symm hz)
    obtain ⟨x, hx, hclosest⟩ := exists_closest_center p C
    have hCadm : Admissible p (dist p x ^ 2) C := by
      rw [admissible_iff, ← hclosest]
    have hfeas : FeasibleRadius (k := k) p x := ⟨C, hCadm⟩
    let D := oracle.solve x hfeas
    have hD : kmeansLoss p C ≤ kmeansLoss p D := by
      rw [hclosest]
      exact (admissible_iff p _ D).1 (oracle.admissible x hfeas)
    have hdpos : 0 < cost kmeansLoss P D :=
      lt_of_lt_of_le (hlpos.trans_le hD) (contribution_le_cost kmeansLoss_nonneg hp D)
    have htrial : trialScore oracle x = kmeansLoss p C / cost kmeansLoss P D := by
      simp only [trialScore, dif_pos hfeas]
      rw [← hclosest]
    have hscore : kmeansLoss p C ≤ estimate oracle * cost kmeansLoss P D := by
      apply (div_le_iff₀ hdpos).1
      rw [← htrial]
      exact trialScore_le_estimate oracle x
    have happ : cost kmeansLoss P D ≤ ρ * cost kmeansLoss P C :=
      oracle.approximation x hfeas C hCadm
    calc
      kmeansLoss p C ≤ estimate oracle * cost kmeansLoss P D := hscore
      _ ≤ estimate oracle * (ρ * cost kmeansLoss P C) :=
        mul_le_mul_of_nonneg_left happ he
      _ = (ρ * estimate oracle) * cost kmeansLoss P C := by ring

/-- Theorem 4.1, with all infeasible-radius and zero-cost cases explicit. -/
theorem estimate_approximates_sensitivity
    (oracle : ConstrainedOracle (k := k) P p ρ) (hp : p ∈ P) (hρ : 0 < ρ) :
    sensitivity (kmeansLoss (k := k)) P p / ρ ≤ estimate oracle ∧
      estimate oracle ≤ sensitivity (kmeansLoss (k := k)) P p := by
  constructor
  · apply (div_le_iff₀ hρ).2
    have hbound : sensitivity (kmeansLoss (k := k)) P p ≤ ρ * estimate oracle :=
      sensitivity_le_of_contribution_le kmeansLoss_nonneg hp
        (mul_nonneg hρ.le (estimate_nonneg oracle))
        (contribution_le_estimate_mul_cost oracle hp hρ)
    simpa [mul_comm] using hbound
  · exact estimate_le_sensitivity oracle hp

/-- Exactly the feasible trials are sent to the constrained oracle. -/
noncomputable def queriedRadii (p : X) : Finset X := by
  classical
  exact (Finset.univ : Finset X).filter (FeasibleRadius (k := k) p)

/-- The reduction makes at most `|X|` constrained optimization calls. -/
theorem oracle_calls_le_card (p : X) : (queriedRadii (k := k) p).card ≤ Fintype.card X := by
  classical
  simpa [queriedRadii] using
    (Finset.card_filter_le (s := (Finset.univ : Finset X)) (FeasibleRadius (k := k) p))

end FTC.FiniteMetric
