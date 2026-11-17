import FaultTolerantCoresets.Hardness.GapReduction
import FaultTolerantCoresets.Hardness.Computation
import FaultTolerantCoresets.Executable.FiniteMetricKMeans
import Mathlib.Data.List.GetD

/-!
# Binary rational input and the executable hardness gadget

A nonnegative rational is encoded as `(numerator, denominator - 1)`, so every
code has a positive denominator. A base instance stores the complete distance
matrix, a client-membership bit for each point, and k. The gap input also stores
B. The target stores the same base and the new-point radius D and common old
weight L; these explicitly describe an ordinary `(n+1)`-point weighted metric.

The target representation is restricted to the star extensions used in the
proof. It stores the common distance and weight once instead of n times; no
optimization answer or other advice occurs in the encoding.
-/

namespace FTC.Hardness.Encoding

open FTC.FiniteMetric FTC.Executable Computation

abbrev RatTy : Ty := .pair .nat .nat
abbrev MatrixTy : Ty := .list (.list RatTy)
abbrev BaseTy : Ty := .pair MatrixTy (.pair (.list .bool) .nat)
abbrev SourceTy : Ty := .pair BaseTy RatTy
abbrev TargetTy : Ty := .pair BaseTy (.pair .nat RatTy)

abbrev RatData := RatTy.Value
abbrev MatrixData := MatrixTy.Value
abbrev BaseData := BaseTy.Value
abbrev SourceData := SourceTy.Value
abbrev TargetData := TargetTy.Value

def rational (q : RatData) : ℚ := (q.1 : ℚ) / ((q.2 : ℚ) + 1)

theorem rational_nonneg (q : RatData) : 0 ≤ rational q := by
  unfold rational
  positivity

theorem rational_pos {q : RatData} (h : 0 < q.1) : 0 < rational q := by
  unfold rational
  positivity

theorem rational_le_numerator (q : RatData) : rational q ≤ (q.1 : ℚ) := by
  unfold rational
  apply (div_le_iff₀ (by positivity : 0 < (q.2 : ℚ) + 1)).mpr
  have h := mul_nonneg (show (0 : ℚ) ≤ q.1 by positivity)
    (show (0 : ℚ) ≤ q.2 by positivity)
  nlinarith

@[reducible] def pointCount (b : BaseData) : ℕ := b.1.length
@[reducible] def centerCount (b : BaseData) : ℕ := b.2.2

def matrixDistance (m : MatrixData) (x y : Fin m.length) : ℚ :=
  rational ((m.getD x []).getD y (0, 0))

/-- The finite metric and feasibility promises, stated entirely over rationals. -/
structure ValidBase (b : BaseData) : Prop where
  square : ∀ row ∈ b.1, row.length = pointCount b
  clients_length : b.2.1.length = pointCount b
  self : ∀ x, matrixDistance b.1 x x = 0
  comm : ∀ x y, matrixDistance b.1 x y = matrixDistance b.1 y x
  triangle : ∀ x y z, matrixDistance b.1 x z ≤ matrixDistance b.1 x y + matrixDistance b.1 y z
  eq_of_zero : ∀ x y, matrixDistance b.1 x y = 0 → x = y
  centers_pos : 0 < centerCount b
  centers_le : centerCount b ≤ pointCount b

def ValidBase.metric {b : BaseData} (h : ValidBase b) : RationalMetric (Fin (pointCount b)) where
  distance := matrixDistance b.1
  self := h.self
  comm := h.comm
  triangle := h.triangle
  eq_of_zero := h.eq_of_zero

def clients (b : BaseData) : Finset (Fin (pointCount b)) :=
  Finset.univ.filter (fun x => b.2.1.getD x false = true)

theorem ValidBase.centers_le_card {b : BaseData} (h : ValidBase b) :
    centerCount b ≤ Fintype.card (Fin (pointCount b)) := by simpa using h.centers_le

noncomputable def originalOptimum (b : BaseData) (h : ValidBase b) : ℝ :=
  letI := h.metric.toMetricSpace
  optimum (clients b) h.centers_pos h.centers_le_card

structure ValidSource (x : SourceData) : Prop where
  base : ValidBase x.1
  budget_pos : 0 < x.2.1

structure ValidTarget (x : TargetData) : Prop where
  base : ValidBase x.1
  radius_pos : 0 < x.2.1
  radius_bound : ∀ i j : Fin (pointCount x.1), matrixDistance x.1.1 i j ≤ (x.2.1 : ℚ)
  weight_pos : 0 < x.2.2.1

def radius (b : BaseData) : ℕ := maximum (b.1.flatten.map Prod.fst) + 1

theorem radius_pos (b : BaseData) : 0 < radius b := Nat.succ_pos _

theorem matrixDistance_le_radius {b : BaseData} (h : ValidBase b)
    (i j : Fin (pointCount b)) : matrixDistance b.1 i j ≤ (radius b : ℚ) := by
  have hrow : b.1.getD i [] ∈ b.1 := by
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem _
  have hlen := h.square _ hrow
  have hj : (j : ℕ) < (b.1.getD i []).length := hlen.symm ▸ j.isLt
  have hentry : (b.1.getD i []).getD j (0, 0) ∈ b.1.flatten := by
    apply List.mem_flatten.mpr
    refine ⟨b.1.getD i [], hrow, ?_⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hnum := le_maximum_of_mem (List.mem_map_of_mem (f := Prod.fst) hentry)
  calc
    matrixDistance b.1 i j ≤ (((b.1.getD i []).getD j (0, 0)).1 : ℚ) :=
      rational_le_numerator _
    _ ≤ (maximum (b.1.flatten.map Prod.fst) : ℚ) := by exact_mod_cast hnum
    _ ≤ (radius b : ℚ) := by unfold radius; push_cast; linarith

def weight (c D : ℕ) (B : RatData) : RatData :=
  (c * D ^ 2 * (B.2 + 1), B.1 - 1)

theorem weight_pos {c D : ℕ} (hc : 0 < c) (hD : 0 < D)
    {B : RatData} (hB : 0 < B.1) : 0 < (weight c D B).1 := by
  dsimp [weight]
  positivity

theorem weight_value (c D : ℕ) (B : RatData) (hB : 0 < B.1) :
    (rational (weight c D B) : ℝ) = amplification c (D : ℝ) (rational B : ℝ) := by
  have hsub : B.1 - 1 + 1 = B.1 := Nat.sub_add_cancel hB
  have hnum : (B.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hden : (B.2 : ℝ) + 1 ≠ 0 := by positivity
  have hsubR : ((B.1 - 1 : ℕ) : ℝ) + 1 = (B.1 : ℝ) := by exact_mod_cast hsub
  simp only [rational, weight, amplification, Rat.cast_div, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [hsubR]
  push_cast
  field_simp

/-- The complete raw transformation. It is defined even on malformed inputs;
the correctness proof uses only the source promise. -/
def reduce (c : ℕ) (x : SourceData) : TargetData :=
  (x.1, (radius x.1, weight c (radius x.1) x.2))

theorem reduce_valid {c : ℕ} (hc : 0 < c) {x : SourceData} (h : ValidSource x) :
    ValidTarget (reduce c x) where
  base := h.base
  radius_pos := radius_pos x.1
  radius_bound := matrixDistance_le_radius h.base
  weight_pos := weight_pos hc (radius_pos x.1) h.budget_pos

theorem ValidTarget.real_radius_pos {x : TargetData} (h : ValidTarget x) :
    0 < (x.2.1 : ℝ) := by exact_mod_cast h.radius_pos

theorem ValidTarget.real_radius_bound {x : TargetData} (h : ValidTarget x) :
    letI := h.base.metric.toMetricSpace
    ∀ i j : Fin (pointCount x.1), dist i j ≤ (x.2.1 : ℝ) := by
  letI := h.base.metric.toMetricSpace
  intro i j
  change (matrixDistance x.1.1 i j : ℝ) ≤ (x.2.1 : ℝ)
  exact_mod_cast h.radius_bound i j

theorem real_weight_nonneg (q : RatData) : 0 ≤ (rational q : ℝ) := by
  exact_mod_cast rational_nonneg q

/-- The target's value is the genuine weighted k-means sensitivity on its
explicit `(n+1)`-point metric, with exactly k unrestricted centers. -/
noncomputable def targetSensitivity (x : TargetData) (h : ValidTarget x) : ℝ :=
  letI := h.base.metric.toMetricSpace
  letI := extensionMetric (x.2.1 : ℝ) h.real_radius_pos h.real_radius_bound
  sensitivity (weightedLoss (k := centerCount x.1)
    (gadgetEntries (rational x.2.2 : ℝ) (real_weight_nonneg x.2.2)))
    (extendedClients (clients x.1)) none

theorem targetSensitivity_eq_gadget (x : TargetData) (h : ValidTarget x) :
    letI := h.base.metric.toMetricSpace
    targetSensitivity x h =
      sensitivity (gadgetContribution (k := centerCount x.1)
        (x.2.1 : ℝ) (rational x.2.2 : ℝ)) (extendedClients (clients x.1)) none := by
  letI := h.base.metric.toMetricSpace
  unfold targetSensitivity
  rw [← gadgetContribution_eq_weightedLoss (x.2.1 : ℝ) h.real_radius_pos
    h.real_radius_bound (real_weight_nonneg x.2.2)]

theorem reduce_sensitivity_formula {c : ℕ} (hc : 0 < c) (x : SourceData) (h : ValidSource x) :
    targetSensitivity (reduce c x) (reduce_valid hc h) =
      (rational x.2 : ℝ) / ((rational x.2 : ℝ) + (c : ℝ) * originalOptimum x.1 h.base) := by
  letI := h.base.metric.toMetricSpace
  rw [targetSensitivity_eq_gadget]
  change sensitivity (gadgetContribution (k := centerCount x.1)
    (radius x.1 : ℝ) (rational (weight c (radius x.1) x.2) : ℝ))
      (extendedClients (clients x.1)) none = _
  rw [weight_value c (radius x.1) x.2 h.budget_pos]
  exact amplified_sensitivity_formula (clients x.1) h.base.centers_pos h.base.centers_le_card
    (by exact_mod_cast radius_pos x.1) (by exact_mod_cast rational_pos h.budget_pos) hc

theorem reduce_sensitivity_eq_gadget {c : ℕ} (hc : 0 < c)
    (x : SourceData) (h : ValidSource x) :
    letI := h.base.metric.toMetricSpace
    targetSensitivity (reduce c x) (reduce_valid hc h) =
      sensitivity (gadgetContribution (k := centerCount x.1) (radius x.1 : ℝ)
        (amplification c (radius x.1 : ℝ) (rational x.2 : ℝ)))
        (extendedClients (clients x.1)) none := by
  letI := h.base.metric.toMetricSpace
  rw [targetSensitivity_eq_gadget]
  change sensitivity (gadgetContribution (k := centerCount x.1)
    (radius x.1 : ℝ) (rational (weight c (radius x.1) x.2) : ℝ))
      (extendedClients (clients x.1)) none = _
  rw [weight_value c (radius x.1) x.2 h.budget_pos]

/-! ## The actual program and its polynomial certificate -/

def radiusCode : Code BaseTy .nat :=
  .comp (.pair (.comp (.comp (.comp .fst .flatten) (.map .fst)) .maximum) (.const 1)) .add

def sourceRadiusCode : Code SourceTy .nat := .comp .fst radiusCode

def weightCode (c : ℕ) : Code SourceTy RatTy :=
  .pair
    (.comp
      (.pair
        (.comp (.pair (.const c) (.comp (.pair sourceRadiusCode sourceRadiusCode) .mul)) .mul)
        (.comp (.pair (.comp .snd .snd) (.const 1)) .add)) .mul)
    (.comp (.pair (.comp .snd .fst) (.const 1)) .sub)

def reductionCode (c : ℕ) : Code SourceTy TargetTy :=
  .pair .fst (.pair sourceRadiusCode (weightCode c))

@[simp] theorem radiusCode_eval (x : BaseData) : radiusCode.eval x = radius x := by
  simp only [radiusCode, Code.eval, radius]

@[simp] theorem reductionCode_eval (c : ℕ) (x : SourceData) :
    (reductionCode c).eval x = reduce c x := by
  simp only [reductionCode, weightCode, sourceRadiusCode, Code.eval, radiusCode_eval,
    reduce, weight, pow_two]

set_option maxHeartbeats 1000000 in
theorem reductionCode_polynomial (c : ℕ) : (reductionCode c).IsPoly := by
  unfold reductionCode weightCode sourceRadiusCode radiusCode
  repeat first
    | apply Code.IsPoly.comp
    | apply Code.IsPoly.pair
    | apply Code.IsPoly.map
    | exact Code.poly_fst
    | exact Code.poly_snd
    | exact Code.poly_const _
    | exact Code.poly_flatten
    | exact Code.poly_maximum
    | exact Code.poly_add
    | exact Code.poly_mul
    | exact Code.poly_sub

end FTC.Hardness.Encoding
