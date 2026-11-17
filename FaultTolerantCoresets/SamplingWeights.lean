import FaultTolerantCoresets.Sensitivity
import Mathlib.Tactic.FieldSimp

/-!
# Sensitivity sampling: the deterministic entry bound

This file proves Lemma 3.2 and the entry-bound step of Theorem A.1. A sample
is a map from a type of stored indices to input indices. No injectivity is
assumed: repeated samples retain distinct stored indices and can be corrupted
or deleted separately.

No probabilistic assumption is needed for these inequalities. The event that
the clean sample is a coreset is the only additional sampling hypothesis used
by the filtering theorem.
-/

namespace FTC

variable {I J S : Type*} [DecidableEq J]

/-- Inverse-probability weight for one copy sampled with the given score. -/
noncomputable def samplingWeight (score : J → ℝ) (T : ℝ) (m : ℕ) (x : J) : ℝ :=
  T / ((m : ℝ) * score x)

/-- A separately indexed sampled contribution; `sample` may have repetitions. -/
noncomputable def sampledContribution (a : J → S → ℝ) (sample : I → J)
    (score : J → ℝ) (T : ℝ) (m : ℕ) (i : I) (s : S) : ℝ :=
  samplingWeight score T m (sample i) * a (sample i) s

/-- Sum of scores on the input. -/
def totalScore (score : J → ℝ) (P : Finset J) : ℝ :=
  ∑ x ∈ P, score x

/-- The total sensitivity `T` appearing in Theorem 3.1. -/
noncomputable def totalSensitivity (a : J → S → ℝ) (P : Finset J) : ℝ :=
  totalScore (sensitivity a P) P

theorem totalScore_nonneg {score : J → ℝ} {P : Finset J}
    (hscore : ∀ x ∈ P, 0 ≤ score x) : 0 ≤ totalScore score P :=
  Finset.sum_nonneg hscore

theorem totalSensitivity_nonneg {a : J → S → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (P : Finset J) :
    0 ≤ totalSensitivity a P :=
  totalScore_nonneg fun x _ => sensitivity_nonneg ha P x

theorem samplingWeight_nonneg {score : J → ℝ} {T : ℝ} {m : ℕ} {x : J}
    (hT : 0 ≤ T) (hscore : 0 ≤ score x) :
    0 ≤ samplingWeight score T m x :=
  div_nonneg hT (mul_nonneg (Nat.cast_nonneg _) hscore)

theorem sampledContribution_nonneg {a : J → S → ℝ} {sample : I → J}
    {score : J → ℝ} {T : ℝ} {m : ℕ} {i : I} {s : S}
    (ha : ∀ x s, 0 ≤ a x s) (hT : 0 ≤ T) (hscore : 0 ≤ score (sample i)) :
    0 ≤ sampledContribution a sample score T m i s :=
  mul_nonneg (samplingWeight_nonneg hT hscore) (ha _ _)

/-- This identifies the weight with `1 / (m q_x)` for `q_x = score_x / T`.
The positivity hypotheses describe the support of the actual sampler. -/
theorem inverse_probability_weight {m : ℕ} {T t : ℝ}
    (hm : 0 < m) (hT : 0 < T) (ht : 0 < t) :
    1 / ((m : ℝ) * (t / T)) = T / ((m : ℝ) * t) := by
  have hm' : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  field_simp [hm', hT.ne', ht.ne']

/-- Scalar cancellation underlying both exact and proxy sampling bounds.
When a score is zero the assigned contribution is zero, so the same bound
also covers that boundary case. -/
theorem inverse_score_contribution_le {v L t T : ℝ} {m : ℕ}
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hT : 0 ≤ T) (hm : 0 < m)
    (hcontribution : v ≤ t * L) :
    (T / ((m : ℝ) * t)) * v ≤ (T / (m : ℝ)) * L := by
  by_cases ht0 : t = 0
  · simp only [ht0, mul_zero, div_zero, zero_mul]
    exact mul_nonneg (div_nonneg hT (Nat.cast_nonneg _)) hL
  · have hm' : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
    calc
      (T / ((m : ℝ) * t)) * v ≤ (T / ((m : ℝ) * t)) * (t * L) :=
        mul_le_mul_of_nonneg_left hcontribution
          (div_nonneg hT (mul_nonneg (Nat.cast_nonneg _) ht))
      _ = (T / (m : ℝ)) * L := by field_simp [hm', ht0]

/-- The generic entry bound: any score dominating the input sensitivity works. -/
theorem sampledContribution_le {a : J → S → ℝ} {sample : I → J}
    {P : Finset J} {score : J → ℝ} {T : ℝ} {m : ℕ} {i : I}
    (ha : ∀ x s, 0 ≤ a x s) (hi : sample i ∈ P)
    (hscore : sensitivity a P (sample i) ≤ score (sample i))
    (hT : 0 ≤ T) (hm : 0 < m) (s : S) :
    sampledContribution a sample score T m i s ≤
      (T / (m : ℝ)) * cost a P s := by
  have hscore0 : 0 ≤ score (sample i) :=
    (sensitivity_nonneg ha P (sample i)).trans hscore
  apply inverse_score_contribution_le (cost_nonneg ha P s) hscore0 hT hm
  exact (contribution_le_sensitivity_mul_cost ha hi s).trans
    (mul_le_mul_of_nonneg_right hscore (cost_nonneg ha P s))

/-- Lemma 3.2: every indexed copy drawn by exact sensitivity sampling has
weighted contribution at most `T / m` times the input cost. -/
theorem lemma_3_2 {a : J → S → ℝ} {sample : I → J} {P : Finset J}
    {m : ℕ} {i : I} (ha : ∀ x s, 0 ≤ a x s)
    (hm : 0 < m) (hi : sample i ∈ P) (s : S) :
    sampledContribution a sample (sensitivity a P) (totalSensitivity a P) m i s ≤
      (totalSensitivity a P / (m : ℝ)) * cost a P s :=
  sampledContribution_le ha hi le_rfl (totalSensitivity_nonneg ha P) hm s

/-- The entry-bound extension used in Theorem A.1, with total proxy score. -/
theorem proxySampling_entry_bound {a : J → S → ℝ} {sample : I → J}
    {P : Finset J} {score : J → ℝ} {m : ℕ} {i : I}
    (ha : ∀ x s, 0 ≤ a x s)
    (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hm : 0 < m) (hi : sample i ∈ P) (s : S) :
    sampledContribution a sample score (totalScore score P) m i s ≤
      (totalScore score P / (m : ℝ)) * cost a P s := by
  apply sampledContribution_le ha hi (hscore _ hi) _ hm s
  exact totalScore_nonneg fun x hx => (sensitivity_nonneg ha P x).trans (hscore x hx)

/-- The usual sample-size lower bound implies the deterministic filtering
budget `α f (T/m) ≤ ε`. -/
theorem sampling_budget {α ε T : ℝ} {f m : ℕ}
    (hε : 0 < ε) (hm : 0 < m)
    (hsize : α * (f : ℝ) * T / ε ≤ (m : ℝ)) :
    α * (f : ℝ) * (T / (m : ℝ)) ≤ ε := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hm').2
  have h := (div_le_iff₀ hε).1 hsize
  nlinarith

/-- The integer sample size corresponding to the paper's additive overhead. -/
noncomputable def faultTolerantSampleSize (m_sc f : ℕ) (α T ε : ℝ) : ℕ :=
  m_sc + ⌈α * (f : ℝ) * T / ε⌉₊

theorem faultTolerantSampleSize_lower (m_sc f : ℕ) (α T ε : ℝ) :
    α * (f : ℝ) * T / ε ≤ (faultTolerantSampleSize m_sc f α T ε : ℝ) := by
  unfold faultTolerantSampleSize
  rw [Nat.cast_add]
  exact (Nat.le_ceil _).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))

theorem faultTolerantSampleSize_pos {m_sc f : ℕ} {α T ε : ℝ}
    (hmsc : 0 < m_sc) : 0 < faultTolerantSampleSize m_sc f α T ε :=
  lt_of_lt_of_le hmsc (Nat.le_add_right _ _)

/-- Rounded sample size, in the multiplication order of the deterministic
filtering theorem's budget. -/
theorem sampling_budget_ceil {α ε T : ℝ} {f m_sc : ℕ}
    (hε : 0 < ε) (hmsc : 0 < m_sc) :
    (f : ℝ) * α * (T / (faultTolerantSampleSize m_sc f α T ε : ℝ)) ≤ ε := by
  have h := sampling_budget (α := α) (T := T) (f := f) hε
    (faultTolerantSampleSize_pos hmsc) (faultTolerantSampleSize_lower m_sc f α T ε)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

end FTC
