import FaultTolerantCoresets.SamplingWeights
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A uniform coreset certificate from the sample histogram

This certificate is simultaneous over every solution, without any assumption
that the solution type is finite. Consequently, the finite-input probability
bound proved in `FiniteIID.lean` applies to every nonnegative pointwise loss.
-/

namespace FTC.Probability

variable {J S : Type*} [Fintype J] [DecidableEq J]

/-- Real-valued indicator for one occurrence of an input index. -/
def hit (x y : J) : ℝ := if y = x then 1 else 0

/-- Number of separately indexed sampled copies of `x`, viewed as a real. -/
def histogram {m : ℕ} (sample : Fin m → J) (x : J) : ℝ :=
  ∑ i, hit x (sample i)

/-- An inverse-probability weighted sample, with individual `Fin m` indices. -/
noncomputable def inverseProbabilityContribution (a : J → S → ℝ)
    (q : J → ℝ) (m : ℕ) (sample : Fin m → J) (i : Fin m) (s : S) : ℝ :=
  (1 / ((m : ℝ) * q (sample i))) * a (sample i) s

/-- Every stored frequency is relatively accurate. The count form avoids a
division by `m` in the event and in its concentration proof. -/
def AccurateHistogram (q : J → ℝ) (ε : ℝ) {m : ℕ} (sample : Fin m → J) : Prop :=
  ∀ x, |histogram sample x - (m : ℝ) * q x| ≤ ε * ((m : ℝ) * q x)

theorem histogram_nonneg {m : ℕ} (sample : Fin m → J) (x : J) :
    0 ≤ histogram sample x := by
  apply Finset.sum_nonneg
  intro i _
  unfold hit
  split <;> norm_num

/-- Group the sample's cost by its original input index. Duplicate samples
are counted, rather than identified. -/
theorem cost_eq_histogram {a : J → S → ℝ} {q : J → ℝ} {m : ℕ}
    (sample : Fin m → J) (s : S) :
    cost (inverseProbabilityContribution a q m sample) Finset.univ s =
      ∑ x, (histogram sample x / ((m : ℝ) * q x)) * a x s := by
  unfold cost inverseProbabilityContribution
  calc
    (∑ i, (1 / ((m : ℝ) * q (sample i))) * a (sample i) s) =
        ∑ i, ∑ x, hit x (sample i) * ((1 / ((m : ℝ) * q x)) * a x s) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [hit, eq_comm]
    _ = ∑ x, ∑ i, hit x (sample i) * ((1 / ((m : ℝ) * q x)) * a x s) :=
      Finset.sum_comm
    _ = ∑ x, (histogram sample x / ((m : ℝ) * q x)) * a x s := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul]
      unfold histogram
      ring

theorem AccurateHistogram.coefficient_bounds {q : J → ℝ} {ε : ℝ} {m : ℕ}
    {sample : Fin m → J} (h : AccurateHistogram q ε sample)
    (hm : 0 < m) (hq : ∀ x, 0 < q x) (x : J) :
    1 - ε ≤ histogram sample x / ((m : ℝ) * q x) ∧
      histogram sample x / ((m : ℝ) * q x) ≤ 1 + ε := by
  have hD : 0 < (m : ℝ) * q x := mul_pos (Nat.cast_pos.mpr hm) (hq x)
  have habs := abs_le.mp (h x)
  constructor
  · apply (le_div_iff₀ hD).2
    nlinarith
  · apply (div_le_iff₀ hD).2
    nlinarith

/-- The histogram certificate gives a coreset for all solutions at once. -/
theorem AccurateHistogram.isCoreset {a : J → S → ℝ} {q : J → ℝ}
    {ε : ℝ} {m : ℕ} {sample : Fin m → J}
    (h : AccurateHistogram q ε sample) (ha : ∀ x s, 0 ≤ a x s)
    (hm : 0 < m) (hq : ∀ x, 0 < q x) :
    IsCoreset ε (cost a Finset.univ)
      (cost (inverseProbabilityContribution a q m sample) Finset.univ) := by
  intro s
  rw [cost_eq_histogram]
  have hcoeff := h.coefficient_bounds hm hq
  constructor
  · calc
      (1 - ε) * cost a Finset.univ s = ∑ x, (1 - ε) * a x s := by
        simp [cost, Finset.mul_sum]
      _ ≤ ∑ x, (histogram sample x / ((m : ℝ) * q x)) * a x s := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_right (hcoeff x).1 (ha x s)
  · calc
      (∑ x, (histogram sample x / ((m : ℝ) * q x)) * a x s) ≤
          ∑ x, (1 + ε) * a x s := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_right (hcoeff x).2 (ha x s)
      _ = (1 + ε) * cost a Finset.univ s := by simp [cost, Finset.mul_sum]

end FTC.Probability
