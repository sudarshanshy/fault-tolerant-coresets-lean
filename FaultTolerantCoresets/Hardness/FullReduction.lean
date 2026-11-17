import FaultTolerantCoresets.Hardness.FullMatrix

/-!
# Theorem 4.2 for explicit distance matrices and weight lists

The compact gadget is materialized by a second certified polynomial program.
Composing the programs gives a reduction into ordinary, explicitly represented
weighted finite metrics, and transfers hardness to their sensitivity gap.
-/

namespace FTC.Hardness.Encoding

open Computation Complexity

def baseMatrixCode : Code TargetTy MatrixTy := .comp .fst .fst
def targetRadiusCode : Code TargetTy RatTy := .pair (.comp .snd .fst) (.const 0)
def targetWeightCode : Code TargetTy RatTy := .comp .snd .snd
def targetCentersCode : Code TargetTy .nat := .comp (.comp .fst .snd) .snd

def firstRowCode : Code TargetTy (.list RatTy) :=
  .comp (.pair (.const (0, 0))
    (.comp (.pair targetRadiusCode baseMatrixCode) (.mapWith .fst))) .cons

def otherRowsCode : Code TargetTy MatrixTy :=
  .comp (.pair targetRadiusCode baseMatrixCode) (.mapWith .cons)

def expandedMatrixCode : Code TargetTy MatrixTy :=
  .comp (.pair firstRowCode otherRowsCode) .cons

def flagsCode : Code TargetTy (.list .bool) :=
  .comp (.pair (.const true) (.comp (.comp .fst .snd) .fst)) .cons

def weightsCode : Code TargetTy (.list RatTy) :=
  .comp (.pair (.const (1, 0))
    (.comp (.pair targetWeightCode baseMatrixCode) (.mapWith .fst))) .cons

def materializeCode : Code TargetTy FullTy :=
  .pair (.comp baseMatrixCode .length)
    (.pair expandedMatrixCode (.pair flagsCode (.pair weightsCode targetCentersCode)))

@[simp] theorem materializeCode_eval (x : TargetData) : materializeCode.eval x = materialize x := by
  simp only [materializeCode, baseMatrixCode, expandedMatrixCode, firstRowCode, otherRowsCode,
    targetRadiusCode, targetWeightCode, flagsCode, weightsCode, targetCentersCode, Code.eval,
    materialize, expandedMatrix, pointCount, centerCount]

theorem materializeCode_polynomial : materializeCode.IsPoly := by
  simp only [materializeCode, baseMatrixCode, expandedMatrixCode, firstRowCode, otherRowsCode,
    targetRadiusCode, targetWeightCode, flagsCode, weightsCode, targetCentersCode]
  repeat first
    | apply Code.IsPoly.comp
    | apply Code.IsPoly.pair
    | apply Code.IsPoly.mapWith
    | exact Code.poly_fst
    | exact Code.poly_snd
    | exact Code.poly_const _
    | exact Code.poly_cons
    | exact Code.poly_length

/-- A single executable program produces the entire explicit output instance. -/
def fullReductionCode (c : ℕ) : Code SourceTy FullTy :=
  .comp (reductionCode c) materializeCode

theorem fullReductionCode_polynomial (c : ℕ) : (fullReductionCode c).IsPoly :=
  (reductionCode_polynomial c).comp materializeCode_polynomial

@[simp] theorem fullReductionCode_eval (c : ℕ) (x : SourceData) :
    (fullReductionCode c).eval x = materialize (reduce c x) := by
  simp only [fullReductionCode, Code.eval, reductionCode_eval, materializeCode_eval]

/-- Both the bit-cost of the construction and the encoded output size have a
polynomial bound, uniformly over all raw inputs, even malformed ones. -/
theorem fullReductionCode_cost_size (c : ℕ) :
    ∃ C d : ℕ, ∀ x : SourceData,
      (fullReductionCode c).cost x + FullTy.size (materialize (reduce c x)) ≤
        bound C d (SourceTy.size x) := by
  have h := fullReductionCode_polynomial c
  unfold Code.IsPoly at h
  simpa only [fullReductionCode_eval] using h

end FTC.Hardness.Encoding

namespace FTC.Hardness

open Computation Complexity Encoding

/-- The target problem on complete distance matrices and per-entry weights. -/
def fullGapSensitivity (α : ℝ) (hα : 1 ≤ α) (t : ℚ) (ht : 0 < t) :
    PromiseProblem FullTy where
  yes x := ∃ h : ValidFull x, α * (t : ℝ) ≤ fullSensitivity x h
  no x := ∃ h : ValidFull x, fullSensitivity x h < (t : ℝ)
  disjoint x hy hn := by
    obtain ⟨hy, hyes⟩ := hy
    obtain ⟨hn, hno⟩ := hn
    have htR : 0 < (t : ℝ) := by exact_mod_cast ht
    change fullSensitivity x hy < (t : ℝ) at hno
    nlinarith

def materializeReduction (α : ℝ) (hα : 1 ≤ α) (t : ℚ) (ht : 0 < t) :
    PolyReduction (gapSensitivity α hα t ht) (fullGapSensitivity α hα t ht) where
  program := materializeCode
  polynomial := materializeCode_polynomial
  yes x hx := by
    obtain ⟨h, hyes⟩ := hx
    rw [materializeCode_eval]
    exact ⟨materialize_valid x h, by rw [fullSensitivity_materialize x h]; exact hyes⟩
  no x hx := by
    obtain ⟨h, hno⟩ := hx
    rw [materializeCode_eval]
    exact ⟨materialize_valid x h, by rw [fullSensitivity_materialize x h]; exact hno⟩

def fullGapReduction {ρ α : ℝ} (hα : 1 ≤ α) (hαρ : α < ρ)
    (params : GapParameters ρ α) :
    PolyReduction (gapKMeans ρ (lt_of_le_of_lt hα hαρ))
      (fullGapSensitivity α hα params.threshold params.threshold_pos) :=
  (gapReduction hα hαρ params).comp
    (materializeReduction α hα params.threshold params.threshold_pos)

/-- Theorem 4.2 with an ordinary explicit matrix/weight-list target encoding. -/
theorem theorem_4_2_full_matrix {ρ δ : ℝ}
    (hρ : 1 < ρ) (hδ : 0 < δ) (hδsmall : δ < ρ - 1)
    (hhard : NPHard (gapKMeans ρ hρ)) :
    ∃ params : GapParameters ρ (ρ - δ),
      NPHard (fullGapSensitivity (ρ - δ) (by linarith)
        params.threshold params.threshold_pos) := by
  obtain ⟨params⟩ := paper_gapParameters_nonempty hρ hδ hδsmall
  exact ⟨params, hhard.of_reduction (fullGapReduction (by linarith) (by linarith) params)⟩

/-- An approximation algorithm on unrestricted ordinary matrix inputs. -/
def ApproximatesFullSensitivity (α : ℝ) (algorithm : Code FullTy RatTy) : Prop :=
  ∀ x (h : ValidFull x),
    fullSensitivity x h / α ≤ (rational (algorithm.eval x) : ℝ) ∧
      (rational (algorithm.eval x) : ℝ) ≤ fullSensitivity x h

theorem approximation_on_materialized_inputs {α : ℝ} {algorithm : Code FullTy RatTy}
    (h : ApproximatesFullSensitivity α algorithm) :
    ApproximatesSensitivity α (.comp materializeCode algorithm) := by
  intro x hx
  have happrox := h (materialize x) (materialize_valid x hx)
  rw [fullSensitivity_materialize x hx] at happrox
  simpa only [Code.eval, materializeCode_eval] using happrox

theorem full_approximation_implies_np_subset_p {ρ α : ℝ}
    (hα : 1 ≤ α) (hαρ : α < ρ) (params : GapParameters ρ α)
    (hhard : NPHard (gapKMeans ρ (lt_of_le_of_lt hα hαρ)))
    {algorithm : Code FullTy RatTy} (hpoly : algorithm.IsPoly)
    (happrox : ApproximatesFullSensitivity α algorithm) :
    ∀ L : List Bool → Prop, InNP L → InP L :=
  approximation_implies_np_subset_p hα hαρ params hhard
    (materializeCode_polynomial.comp hpoly) (approximation_on_materialized_inputs happrox)

/-- The usual impossibility consequence, with NP ≠ P stated as an explicit
language witness in the same bit-cost model. -/
theorem no_polynomial_full_approximation {ρ α : ℝ}
    (hα : 1 ≤ α) (hαρ : α < ρ) (params : GapParameters ρ α)
    (hhard : NPHard (gapKMeans ρ (lt_of_le_of_lt hα hαρ)))
    (hseparation : ∃ L : List Bool → Prop, InNP L ∧ ¬ InP L) :
    ¬ ∃ algorithm : Code FullTy RatTy,
      algorithm.IsPoly ∧ ApproximatesFullSensitivity α algorithm := by
  rintro ⟨algorithm, hpoly, happrox⟩
  obtain ⟨L, hL, hnot⟩ := hseparation
  exact hnot (full_approximation_implies_np_subset_p hα hαρ params hhard hpoly happrox L hL)

/-- Any externally established open interval of gap-hardness factors transfers
to pointwise sensitivity approximation on full matrix inputs. In particular,
the paper's cited k-means hardness family can be supplied with R = 1 + 8/e. -/
theorem sensitivity_hardness_below_limit {R α : ℝ} (hα : 1 ≤ α) (hαR : α < R)
    (hbase : ∀ ρ : ℝ, ∀ hρ : 1 < ρ, ρ < R → NPHard (gapKMeans ρ hρ)) :
    ∃ (t : ℚ) (ht : 0 < t), NPHard (fullGapSensitivity α hα t ht) := by
  let ρ := (α + R) / 2
  have hαρ : α < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨params⟩ := gapParameters_nonempty hα hαρ
  exact ⟨params.threshold, params.threshold_pos,
    (hbase ρ (lt_of_le_of_lt hα hαρ) hρR).of_reduction (fullGapReduction hα hαρ params)⟩

end FTC.Hardness
