import FaultTolerantCoresets.Hardness.Hardness

/-!
# Ordinary full-matrix inputs for sensitivity hardness

This module expands the compact construction into the usual distance matrix,
client mask, and individual weight list. Point zero is distinguished. The
carrier `Option (Fin n)` lists point zero followed by the n other points.
Its interpretation is independent of the star construction: every finite
nonempty rational metric with a designated client has this form after labeling.
-/

namespace FTC.Hardness.Encoding

open FTC.FiniteMetric FTC.Executable Computation Complexity

abbrev FullTy : Ty := .pair .nat
  (.pair MatrixTy (.pair (.list .bool) (.pair (.list RatTy) .nat)))
abbrev FullData := FullTy.Value

def fullMatrix (x : FullData) : MatrixData := x.2.1
def fullFlags (x : FullData) : List Bool := x.2.2.1
def fullWeights (x : FullData) : List RatData := x.2.2.2.1
@[reducible] def fullK (x : FullData) : ℕ := x.2.2.2.2

def position {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some i => i.val + 1

def fullDistance (x : FullData) (i j : Option (Fin x.1)) : ℚ :=
  rational (((fullMatrix x).getD (position i) []).getD (position j) (0, 0))

structure ValidFull (x : FullData) : Prop where
  matrix_length : (fullMatrix x).length = x.1 + 1
  square : ∀ row ∈ fullMatrix x, row.length = x.1 + 1
  flags_length : (fullFlags x).length = x.1 + 1
  weights_length : (fullWeights x).length = x.1 + 1
  self : ∀ i, fullDistance x i i = 0
  comm : ∀ i j, fullDistance x i j = fullDistance x j i
  triangle : ∀ i j z, fullDistance x i z ≤ fullDistance x i j + fullDistance x j z
  eq_of_zero : ∀ i j, fullDistance x i j = 0 → i = j
  centers_pos : 0 < fullK x
  centers_le : fullK x ≤ x.1 + 1
  query_active : (fullFlags x).getD 0 false = true

def ValidFull.metric {x : FullData} (h : ValidFull x) : RationalMetric (Option (Fin x.1)) where
  distance := fullDistance x
  self := h.self
  comm := h.comm
  triangle := h.triangle
  eq_of_zero := h.eq_of_zero

def fullClients (x : FullData) : Finset (Option (Fin x.1)) :=
  Finset.univ.filter (fun i => (fullFlags x).getD (position i) false = true)

noncomputable def fullEntries (x : FullData) (i : Option (Fin x.1)) : Entry (Option (Fin x.1)) where
  point := i
  weight := (rational ((fullWeights x).getD (position i) (0, 0)) : ℝ)
  weight_nonneg := real_weight_nonneg _

noncomputable def fullContribution (x : FullData) (h : ValidFull x) :
    Option (Fin x.1) → CenterSet (Option (Fin x.1)) (fullK x) → ℝ :=
  letI := h.metric.toMetricSpace
  weightedLoss (fullEntries x)

noncomputable def fullSensitivity (x : FullData) (h : ValidFull x) : ℝ :=
  sensitivity (fullContribution x h) (fullClients x) none

def expandedMatrix (x : TargetData) : MatrixData :=
  ((0, 0) :: x.1.1.map (fun _ => (x.2.1, 0))) ::
    x.1.1.map (fun row => (x.2.1, 0) :: row)

@[reducible] def materialize (x : TargetData) : FullData :=
  (pointCount x.1, (expandedMatrix x, (true :: x.1.2.1,
    ((1, 0) :: x.1.1.map (fun _ => x.2.2), centerCount x.1))))

theorem getD_map_inBounds {A B : Type} (f : A → B) (xs : List A) (i : ℕ)
    (hi : i < xs.length) (da : A) (db : B) :
    (xs.map f).getD i db = f (xs.getD i da) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

/-- Every entry of the materialized distance matrix has the intended value. -/
theorem materializedDistance (x : TargetData) (i j : Option (Fin (pointCount x.1))) :
    fullDistance (materialize x) i j =
      match i, j with
      | none, none => 0
      | none, some _ => (x.2.1 : ℚ)
      | some _, none => (x.2.1 : ℚ)
      | some a, some b => matrixDistance x.1.1 a b := by
  cases i with
  | none =>
    cases j with
    | none => simp [fullDistance, materialize, expandedMatrix, fullMatrix, position, rational]
    | some j =>
      simp only [fullDistance, materialize, fullMatrix, expandedMatrix, position,
        List.getD_cons_zero, List.getD_cons_succ]
      rw [getD_map_inBounds _ _ j j.isLt [] (0, 0)]
      simp [rational]
  | some i =>
    cases j with
    | none =>
      simp only [fullDistance, materialize, fullMatrix, expandedMatrix, position,
        List.getD_cons_zero, List.getD_cons_succ]
      rw [getD_map_inBounds _ _ i i.isLt [] []]
      simp [rational]
    | some j =>
      simp only [fullDistance, materialize, fullMatrix, expandedMatrix, position,
        List.getD_cons_zero, List.getD_cons_succ]
      rw [getD_map_inBounds _ _ i i.isLt [] []]
      simp only [List.getD_cons_succ, matrixDistance]

theorem materializedDistance_cast (x : TargetData) (h : ValidTarget x)
    (i j : Option (Fin (pointCount x.1))) :
    letI := h.base.metric.toMetricSpace
    (fullDistance (materialize x) i j : ℝ) = extensionDist (x.2.1 : ℝ) i j := by
  letI := h.base.metric.toMetricSpace
  rw [materializedDistance]
  cases i <;> cases j <;> simp only [extensionDist, Rat.cast_zero, Rat.cast_natCast]
  rfl

/-- Materialization produces an ordinary valid finite weighted metric instance. -/
theorem materialize_valid (x : TargetData) (h : ValidTarget x) : ValidFull (materialize x) := by
  letI := h.base.metric.toMetricSpace
  letI := extensionMetric (x.2.1 : ℝ) h.real_radius_pos h.real_radius_bound
  have hdist (i j : Option (Fin (pointCount x.1))) :
      (fullDistance (materialize x) i j : ℝ) = dist i j := materializedDistance_cast x h i j
  refine {
    matrix_length := by simp [materialize, expandedMatrix, fullMatrix, pointCount]
    square := ?_
    flags_length := ?_
    weights_length := by simp [materialize, fullWeights, pointCount]
    self := ?_
    comm := ?_
    triangle := ?_
    eq_of_zero := ?_
    centers_pos := h.base.centers_pos
    centers_le := h.base.centers_le.trans (Nat.le_succ _)
    query_active := by simp [materialize, fullFlags]
  }
  · intro row hr
    simp only [materialize, fullMatrix, expandedMatrix, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨old, hold, rfl⟩
    · simp [pointCount, materialize]
    · have := h.base.square old hold
      simpa only [List.length_cons, materialize] using congrArg Nat.succ this
  · have := h.base.clients_length
    simpa only [materialize, fullFlags, List.length_cons] using congrArg Nat.succ this
  · intro i
    have hr : (fullDistance (materialize x) i i : ℝ) = 0 := by rw [hdist, dist_self]
    exact_mod_cast hr
  · intro i j
    have hr : (fullDistance (materialize x) i j : ℝ) =
        (fullDistance (materialize x) j i : ℝ) := by rw [hdist, hdist, dist_comm]
    exact_mod_cast hr
  · intro i j z
    have hr : (fullDistance (materialize x) i z : ℝ) ≤
        (fullDistance (materialize x) i j : ℝ) + (fullDistance (materialize x) j z : ℝ) := by
      rw [hdist, hdist, hdist]
      exact dist_triangle _ _ _
    exact_mod_cast hr
  · intro i j hij
    apply dist_eq_zero.mp
    rw [← hdist, hij, Rat.cast_zero]

theorem fullClients_materialize (x : TargetData) :
    fullClients (materialize x) = extendedClients (clients x.1) := by
  ext i
  cases i <;> simp [fullClients, materialize, fullFlags, position, extendedClients,
    clients, Finset.mem_map]

theorem fullEntries_materialize_weight (x : TargetData) (i : Option (Fin (pointCount x.1))) :
    (fullEntries (materialize x) i).weight =
      match i with | none => 1 | some _ => (rational x.2.2 : ℝ) := by
  cases i with
  | none => simp [fullEntries, materialize, fullWeights, position, rational]
  | some i =>
    simp only [fullEntries, materialize, fullWeights, position, List.getD_cons_succ]
    rw [getD_map_inBounds _ _ i i.isLt [] (0, 0)]

theorem fullLoss_materialize (x : TargetData) (h : ValidTarget x)
    (p : Option (Fin (pointCount x.1)))
    (C : CenterSet (Option (Fin (pointCount x.1))) (centerCount x.1)) :
    letI := h.base.metric.toMetricSpace
    letI := (materialize_valid x h).metric.toMetricSpace
    kmeansLoss p C = extensionLoss (x.2.1 : ℝ) p C := by
  letI := h.base.metric.toMetricSpace
  letI := (materialize_valid x h).metric.toMetricSpace
  unfold kmeansLoss extensionLoss
  apply Finset.inf'_congr C.nonempty rfl
  intro q _
  change (fullDistance (materialize x) p q : ℝ) ^ 2 = extensionDist (x.2.1 : ℝ) p q ^ 2
  rw [materializedDistance_cast x h]

theorem fullContribution_materialize (x : TargetData) (h : ValidTarget x) :
    letI := h.base.metric.toMetricSpace
    fullContribution (materialize x) (materialize_valid x h) =
      gadgetContribution (k := centerCount x.1) (x.2.1 : ℝ) (rational x.2.2 : ℝ) := by
  letI := h.base.metric.toMetricSpace
  funext i C
  change (fullEntries (materialize x) i).weight *
      @kmeansLoss (Option (Fin (pointCount x.1)))
        (materialize_valid x h).metric.toMetricSpace _ i C = _
  rw [fullEntries_materialize_weight, fullLoss_materialize x h]
  cases i <;> simp only [gadgetContribution, one_mul]

theorem fullSensitivity_materialize (x : TargetData) (h : ValidTarget x) :
    fullSensitivity (materialize x) (materialize_valid x h) = targetSensitivity x h := by
  letI := h.base.metric.toMetricSpace
  unfold fullSensitivity
  rw [fullClients_materialize, fullContribution_materialize x h]
  exact (targetSensitivity_eq_gadget x h).symm

end FTC.Hardness.Encoding
