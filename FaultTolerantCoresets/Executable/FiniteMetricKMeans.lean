import FaultTolerantCoresets.Executable.FiniteMetricEnumeration
import FaultTolerantCoresets.FiniteMetric.WeightedSensitivityReduction
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Sublists

/-!
# Finite rational metrics: executable weighted k-means and sensitivity

Vertex labels have a supplied linear order, so every candidate enumeration is
computable (in particular labels can be `Fin n`). Rational distances are
interpreted as an actual real metric. All k-center subsets are enumerated;
the binomial candidate count is explicit and no polynomial optimizer is claimed.
-/

namespace FTC.Executable

open FTC.FiniteMetric

variable {I X : Type*} [DecidableEq I] [LinearOrder X] [Fintype X] {k : ℕ}

structure RationalMetric (X : Type*) where
  distance : X → X → ℚ
  self : ∀ x, distance x x = 0
  comm : ∀ x y, distance x y = distance y x
  triangle : ∀ x y z, distance x z ≤ distance x y + distance y z
  eq_of_zero : ∀ x y, distance x y = 0 → x = y

@[reducible] noncomputable def RationalMetric.toMetricSpace (d : RationalMetric X) : MetricSpace X where
  dist x y := (d.distance x y : ℝ)
  dist_self x := by simp [d.self]
  dist_comm x y := by rw [d.comm]
  dist_triangle x y z := by exact_mod_cast d.triangle x y z
  eq_of_dist_eq_zero := by
    intro x y h
    exact d.eq_of_zero x y (by exact_mod_cast h)

structure RationalEntry (X : Type*) where
  point : X
  weight : ℚ
  weight_nonneg : 0 ≤ weight

def RationalEntry.toReal (entry : RationalEntry X) : Entry X where
  point := entry.point
  weight := entry.weight
  weight_nonneg := by exact_mod_cast entry.weight_nonneg

def rationalPointLoss (d : RationalMetric X) (p : X) (C : Finset X) : ℚ :=
  if h : C.Nonempty then C.inf' h (fun x => d.distance p x ^ 2) else 0

theorem rationalPointLoss_nonneg (d : RationalMetric X) (p : X) (C : Finset X) :
    0 ≤ rationalPointLoss d p C := by
  unfold rationalPointLoss
  split_ifs
  · exact Finset.le_inf' _ _ (fun x _ => sq_nonneg _)
  · exact le_rfl

def rationalKmeansLoss (d : RationalMetric X) (entries : I → RationalEntry X)
    (i : I) (C : Finset X) : ℚ :=
  (entries i).weight * rationalPointLoss d (entries i).point C

theorem rationalKmeansLoss_nonneg (d : RationalMetric X) (entries : I → RationalEntry X) :
    ∀ i C, 0 ≤ rationalKmeansLoss d entries i C :=
  fun i C => mul_nonneg (entries i).weight_nonneg (rationalPointLoss_nonneg d _ C)

/-- All k-center subsets, in a computable canonical order. -/
def centerCandidateList (Y : Finset X) (k : ℕ) : List (Finset X) :=
  ((Y.sort).sublistsLen k).map List.toFinset

theorem mem_centerCandidateList {Y C : Finset X} :
    C ∈ centerCandidateList Y k ↔ C ⊆ Y ∧ C.card = k := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hl
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxl : x ∈ l := List.mem_toFinset.mp hx
      exact (Finset.mem_sort _).mp (hsub.subset hxl)
    · rw [List.toFinset_card_of_nodup ((Y.sort_nodup _).sublist hsub)]
      exact hlen
  · rintro ⟨hsub, hcard⟩
    apply List.mem_map.mpr
    refine ⟨C.sort, ?_, by simp⟩
    apply List.mem_sublistsLen.mpr
    refine ⟨?_, by simpa using hcard⟩
    apply List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset (C.sort_nodup _) ?_)
      (C.pairwise_sort _) (Y.pairwise_sort _)
    intro x hx
    exact (Finset.mem_sort _).mpr (hsub ((Finset.mem_sort _).mp hx))

theorem centerCandidateList_length (Y : Finset X) (k : ℕ) :
    (centerCandidateList Y k).length = Nat.choose Y.card k := by
  simp [centerCandidateList, List.length_sublistsLen]

/-- At radius r all centers must be at squared distance at least r from p. -/
def rationalAdmissible (d : RationalMetric X) (p : X) (r : ℚ) (C : Finset X) : Prop :=
  ∀ x ∈ C, r ≤ d.distance p x ^ 2

instance rationalAdmissibleDecidable (d : RationalMetric X) (p : X) (r : ℚ) :
    DecidablePred (rationalAdmissible d p r) := by
  intro C
  unfold rationalAdmissible
  infer_instance

/-- An actual exhaustive constrained weighted k-means solver. -/
def exactRationalKmeans (d : RationalMetric X) (entries : I → RationalEntry X)
    (U : Finset I) (Y : Finset X) (k : ℕ) (p : X) (r : ℚ) : Option (Finset X) :=
  constrainedFiniteSolver (rationalKmeansLoss d entries) U
    (centerCandidateList Y k) (rationalAdmissible d p r)

theorem exactRationalKmeans_spec (d : RationalMetric X) (entries : I → RationalEntry X)
    (U : Finset I) (Y : Finset X) (p : X) (r : ℚ) {C : Finset X}
    (h : exactRationalKmeans d entries U Y k p r = some C) :
    C ⊆ Y ∧ C.card = k ∧ rationalAdmissible d p r C ∧
      ∀ D ⊆ Y, D.card = k → rationalAdmissible d p r D →
        rationalCost (rationalKmeansLoss d entries) U C ≤
          rationalCost (rationalKmeansLoss d entries) U D := by
  obtain ⟨hmem, hadm, hopt⟩ := constrainedFiniteSolver_spec h
  obtain ⟨hsub, hcard⟩ := mem_centerCandidateList.mp hmem
  refine ⟨hsub, hcard, hadm, ?_⟩
  intro D hDY hDk hDa
  exact hopt D (mem_centerCandidateList.mpr ⟨hDY, hDk⟩) hDa

theorem exactRationalKmeans_none_iff (d : RationalMetric X) (entries : I → RationalEntry X)
    (U : Finset I) (Y : Finset X) (p : X) (r : ℚ) :
    exactRationalKmeans d entries U Y k p r = none ↔
      ¬ ∃ C ⊆ Y, C.card = k ∧ rationalAdmissible d p r C := by
  rw [exactRationalKmeans, constrainedFiniteSolver_none_iff]
  simp only [mem_centerCandidateList, and_assoc, exists_prop]

def exactRationalKmeansCounted (d : RationalMetric X) (entries : I → RationalEntry X)
    (U : Finset I) (Y : Finset X) (k : ℕ) (p : X) (r : ℚ) : Option (Finset X) × ℕ :=
  constrainedFiniteSolverCounted (rationalKmeansLoss d entries) U
    (centerCandidateList Y k) (rationalAdmissible d p r)

theorem exactRationalKmeansCounted_value (d : RationalMetric X) (entries : I → RationalEntry X)
    (U : Finset I) (Y : Finset X) (k : ℕ) (p : X) (r : ℚ) :
    (exactRationalKmeansCounted d entries U Y k p r).1 =
      exactRationalKmeans d entries U Y k p r :=
  constrainedFiniteSolverCounted_value _ _ _ _

/-- This counts rational-loss matrix accesses/additions and cached comparisons;
each matrix access here evaluates the point-to-center minimum. Thus this is
an explicit query/matrix-call bound, not a bit-complexity runtime assertion. -/
theorem exactRationalKmeansCounted_work_le (d : RationalMetric X) (entries : I → RationalEntry X)
    (U : Finset I) (Y : Finset X) (k : ℕ) (p : X) (r : ℚ) :
    (exactRationalKmeansCounted d entries U Y k p r).2 ≤
      (2 * U.card + 1) * Nat.choose Y.card k := by
  simpa [exactRationalKmeansCounted, centerCandidateList_length] using
    constrainedFiniteSolverCounted_work_le (rationalKmeansLoss d entries) U
      (centerCandidateList Y k) (rationalAdmissible d p r)

/-! ## Exact interpretation as the real k-means sensitivity -/

instance centerSetDecidableEq : DecidableEq (CenterSet X k) := fun C D =>
  if h : C.centers = D.centers then
    isTrue (by cases C; cases D; cases h; rfl)
  else isFalse (fun hCD => h (congrArg CenterSet.centers hCD))

/-- Finite enumeration of the actual nonempty k-center query type. -/
def centerQueries (Y : Finset X) (k : ℕ) (hk : 0 < k) : Finset (CenterSet X k) :=
  (Y.powersetCard k).attach.image (fun C =>
    ⟨C.val, (Finset.mem_powersetCard.mp C.property).2,
      Finset.card_pos.mp (by simpa [(Finset.mem_powersetCard.mp C.property).2] using hk)⟩)

theorem centerQueries_complete (hk : 0 < k) (C : CenterSet X k) :
    C ∈ centerQueries (Finset.univ : Finset X) k hk := by
  apply Finset.mem_image.mpr
  have hC : C.centers ∈ (Finset.univ : Finset X).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, C.card_eq⟩
  refine ⟨⟨C.centers, hC⟩, Finset.mem_attach _ _, ?_⟩
  cases C
  rfl

theorem centerQueries_card_le (Y : Finset X) (hk : 0 < k) :
    (centerQueries Y k hk).card ≤ Nat.choose Y.card k := by
  exact (Finset.card_image_le).trans_eq (by simp [Finset.card_powersetCard])

def rationalCenterMatrix (d : RationalMetric X) (entries : I → RationalEntry X)
    (i : I) (C : CenterSet X k) : ℚ := rationalKmeansLoss d entries i C.centers

theorem rationalPointLoss_cast (d : RationalMetric X) (p : X) (C : CenterSet X k) :
    letI : MetricSpace X := d.toMetricSpace
    (rationalPointLoss d p C.centers : ℝ) = kmeansLoss p C := by
  letI : MetricSpace X := d.toMetricSpace
  unfold rationalPointLoss
  rw [dif_pos C.nonempty]
  apply le_antisymm
  · apply Finset.le_inf'
    intro x hx
    have hq : C.centers.inf' C.nonempty (fun x => d.distance p x ^ 2) ≤ d.distance p x ^ 2 :=
      Finset.inf'_le _ hx
    change ((C.centers.inf' C.nonempty (fun x => d.distance p x ^ 2) : ℚ) : ℝ) ≤
      (d.distance p x : ℝ) ^ 2
    exact_mod_cast hq
  · obtain ⟨x, hx, hmin⟩ :=
      Finset.exists_mem_eq_inf' C.nonempty (fun x => d.distance p x ^ 2)
    rw [hmin]
    have hreal : kmeansLoss p C ≤ (d.distance p x : ℝ) ^ 2 :=
      kmeansLoss_le_dist_sq p C hx
    simpa only [Rat.cast_pow] using hreal

theorem rationalCenterMatrix_cast (d : RationalMetric X) (entries : I → RationalEntry X)
    (i : I) (C : CenterSet X k) :
    letI : MetricSpace X := d.toMetricSpace
    realContribution (rationalCenterMatrix d entries) i C =
      weightedLoss (fun j => (entries j).toReal) i C := by
  letI : MetricSpace X := d.toMetricSpace
  change (((entries i).weight * rationalPointLoss d (entries i).point C.centers : ℚ) : ℝ) = _
  push_cast
  rw [rationalPointLoss_cast]
  rfl

/-- Executable exact rational sensitivity for genuine weighted k-means. -/
def exactRationalKmeansSensitivity (d : RationalMetric X) (entries : I → RationalEntry X)
    (hk : 0 < k) (U : Finset I) (i : I) : ℚ :=
  rationalSensitivity (rationalCenterMatrix d entries)
    (centerQueries Finset.univ k hk) U i

theorem exactRationalKmeansSensitivity_cast_eq (d : RationalMetric X)
    (entries : I → RationalEntry X) (hk : 0 < k) (U : Finset I) (i : I) :
    letI : MetricSpace X := d.toMetricSpace
    (exactRationalKmeansSensitivity d entries hk U i : ℝ) =
      sensitivity (weightedLoss (k := k) (fun j => (entries j).toReal)) U i := by
  letI : MetricSpace X := d.toMetricSpace
  have hmatrix : realContribution (rationalCenterMatrix (k := k) d entries) =
      weightedLoss (k := k) (fun j => (entries j).toReal) := by
    funext j C
    exact rationalCenterMatrix_cast d entries j C
  have hc : ∀ (j : I) (C : CenterSet X k), 0 ≤ rationalCenterMatrix d entries j C :=
    fun j C => rationalKmeansLoss_nonneg d entries j C.centers
  have heq := rationalSensitivity_cast_eq
    (c := rationalCenterMatrix (k := k) d entries)
    (queries := centerQueries (Finset.univ : Finset X) k hk)
    hc (centerQueries_complete hk) U i
  rw [hmatrix] at heq
  exact heq

theorem exactRationalKmeansSensitivity_work_le (d : RationalMetric X)
    (entries : I → RationalEntry X) (hk : 0 < k) (U : Finset I) (i : I) :
    (rationalSensitivityCounted (rationalCenterMatrix d entries)
      (centerQueries Finset.univ k hk) U i).2 ≤
      Nat.choose (Fintype.card X) k * (2 * U.card + 3) := by
  rw [rationalSensitivityCounted_work]
  split_ifs
  · exact Nat.mul_le_mul_right _ (by simpa using centerQueries_card_le (Finset.univ : Finset X) hk)
  · exact Nat.zero_le _

end FTC.Executable
