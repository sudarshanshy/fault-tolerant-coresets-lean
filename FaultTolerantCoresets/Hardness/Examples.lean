import FaultTolerantCoresets.Hardness.FullReduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Order.WithBot

/-!
# Checked YES/NO examples and the executable full-matrix bridge

The original two-point instance has optimum 1. With ρ = 3 and α = 2,
the thresholds B = 1 and B = 1/4 lie on opposite sides of the promised gap.
The same certified program produces sensitivities 1/5 and 1/17, separated by
the fixed rational threshold 1/11.
-/

namespace FTC.Hardness.Encoding

open FTC.FiniteMetric FTC.Executable

local instance {n : ℕ} : LinearOrder (Option (Fin n)) :=
  inferInstanceAs (LinearOrder (WithBot (Fin n)))

def fullRationalEntries (x : FullData) (i : Option (Fin x.1)) : RationalEntry (Option (Fin x.1)) where
  point := i
  weight := rational ((fullWeights x).getD (position i) (0, 0))
  weight_nonneg := rational_nonneg _

/-- The previously verified exhaustive numerical algorithm on the new ordinary
input format. Its use here is only a small demonstration, not a polynomial
algorithm for the hard optimization problem. -/
def exactFullSensitivity (x : FullData) (h : ValidFull x) : ℚ :=
  exactRationalKmeansSensitivity h.metric (fullRationalEntries x)
    h.centers_pos (fullClients x) none

theorem exactFullSensitivity_cast_eq (x : FullData) (h : ValidFull x) :
    (exactFullSensitivity x h : ℝ) = fullSensitivity x h := by
  unfold exactFullSensitivity
  rw [exactRationalKmeansSensitivity_cast_eq]
  rfl

end FTC.Hardness.Encoding

namespace FTC.Hardness.Examples

open FTC.FiniteMetric Encoding

def toyBase : BaseData :=
  ([[(0, 0), (1, 0)], [(1, 0), (0, 0)]], ([true, true], 1))

theorem toyBase_valid : ValidBase toyBase where
  square := by
    intro row hr
    simp only [toyBase, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  clients_length := rfl
  self := by
    intro i
    fin_cases i <;> norm_num [matrixDistance, toyBase, pointCount, rational]
  comm := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [matrixDistance, toyBase, pointCount, rational]
  triangle := by
    intro i j z
    fin_cases i <;> fin_cases j <;> fin_cases z <;>
      norm_num [matrixDistance, toyBase, pointCount, rational]
  eq_of_zero := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first | rfl | norm_num [matrixDistance, toyBase, pointCount, rational] at h
  centers_pos := by decide
  centers_le := by decide

theorem clients_toy : clients toyBase = Finset.univ := by decide

theorem toy_cost (C : CenterSet (Fin (pointCount toyBase)) (centerCount toyBase)) :
    letI := toyBase_valid.metric.toMetricSpace
    cost kmeansLoss (clients toyBase) C = 1 := by
  letI := toyBase_valid.metric.toMetricSpace
  have hcard : C.centers.card = 1 := C.card_eq
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  simp only [cost, clients_toy, kmeansLoss, hp, Finset.inf'_singleton]
  change (∑ x : Fin 2, (matrixDistance toyBase.1 x p : ℝ) ^ 2) = 1
  rw [Fin.sum_univ_two]
  fin_cases p <;> norm_num [matrixDistance, toyBase, rational]

theorem toy_optimum : originalOptimum toyBase toyBase_valid = 1 := by
  unfold originalOptimum optimum
  exact toy_cost _

def parameters : GapParameters (3 : ℝ) 2 where
  copies := 4
  copies_pos := by decide
  threshold := 1 / 11
  threshold_pos := by norm_num
  no_lt := by norm_num
  yes_le := by norm_num

def yesSource : SourceData := (toyBase, (1, 0))
def noSource : SourceData := (toyBase, (1, 3))

theorem yesSource_valid : ValidSource yesSource := ⟨toyBase_valid, by decide⟩
theorem noSource_valid : ValidSource noSource := ⟨toyBase_valid, by decide⟩

theorem yes_promised : (gapKMeans 3 (by norm_num)).yes yesSource := by
  refine ⟨yesSource_valid, ?_⟩
  norm_num [yesSource, toy_optimum, rational]

theorem no_promised : (gapKMeans 3 (by norm_num)).no noSource := by
  refine ⟨noSource_valid, ?_⟩
  norm_num [noSource, toy_optimum, rational]

def yesFull : FullData := materialize (reduce 4 yesSource)
def noFull : FullData := materialize (reduce 4 noSource)

theorem yesFull_valid : ValidFull yesFull :=
  materialize_valid _ (reduce_valid (by decide : 0 < 4) yesSource_valid)

theorem noFull_valid : ValidFull noFull :=
  materialize_valid _ (reduce_valid (by decide : 0 < 4) noSource_valid)

theorem yes_sensitivity : fullSensitivity yesFull yesFull_valid = 1 / 5 := by
  change fullSensitivity (materialize (reduce 4 yesSource))
    (materialize_valid _ (reduce_valid (by decide : 0 < 4) yesSource_valid)) = _
  rw [fullSensitivity_materialize _ (reduce_valid (by decide : 0 < 4) yesSource_valid),
    reduce_sensitivity_formula (by decide : 0 < 4) yesSource yesSource_valid]
  norm_num [yesSource, toy_optimum, rational]

theorem no_sensitivity : fullSensitivity noFull noFull_valid = 1 / 17 := by
  change fullSensitivity (materialize (reduce 4 noSource))
    (materialize_valid _ (reduce_valid (by decide : 0 < 4) noSource_valid)) = _
  rw [fullSensitivity_materialize _ (reduce_valid (by decide : 0 < 4) noSource_valid),
    reduce_sensitivity_formula (by decide : 0 < 4) noSource noSource_valid]
  norm_num [noSource, toy_optimum, rational]

theorem yes_exact_value : exactFullSensitivity yesFull yesFull_valid = 1 / 5 := by
  have h := exactFullSensitivity_cast_eq yesFull yesFull_valid
  rw [yes_sensitivity] at h
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact h

theorem no_exact_value : exactFullSensitivity noFull noFull_valid = 1 / 17 := by
  have h := exactFullSensitivity_cast_eq noFull noFull_valid
  rw [no_sensitivity] at h
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact h

end FTC.Hardness.Examples
