import FaultTolerantCoresets.Probability.FiniteIID

/-!
# Actual exact/proxy sensitivity sampling, including zero scores

Only positive-score input indices are sampled. A zero proxy score dominates
the sensitivity only when that input index has zero loss for every solution;
such indices are therefore safely omitted. The PMF is normalized from the
scores themselves, and its iid product law is used in the final theorems.

The ordinary sample count used here is the complete but loose finite-input
fallback from `FiniteIID.lean`. It is distinct from any sharper model-specific
`m_sc` supplied by the coreset literature.
-/

namespace FTC.Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {J S : Type*} [DecidableEq J]
variable [MeasurableSpace J] [DiscreteMeasurableSpace J]

/-- Positive-score support within the finite input. -/
def positiveSupport (P : Finset J) (score : J → ℝ) : Finset J := by
  classical
  exact P.filter fun x => 0 < score x

/-- A sample is drawn from this finite support; the underlying input index is
its subtype value. -/
abbrev PositiveIndex (P : Finset J) (score : J → ℝ) :=
  {x : J // x ∈ positiveSupport P score}

theorem positiveIndex_mem {P : Finset J} {score : J → ℝ}
    (x : PositiveIndex P score) : x.val ∈ P := by
  classical
  exact (Finset.mem_filter.mp x.property).1

theorem positiveIndex_score_pos {P : Finset J} {score : J → ℝ}
    (x : PositiveIndex P score) : 0 < score x.val := by
  classical
  exact (Finset.mem_filter.mp x.property).2

theorem score_nonneg_of_dominates {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x) :
    ∀ x ∈ P, 0 ≤ score x :=
  fun x hx => (sensitivity_nonneg ha P x).trans (hscore x hx)

/-- Zero sensitivity/proxy score really means zero contribution, even at
zero-cost queries. -/
theorem loss_zero_of_score_zero {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    {x : J} (hx : x ∈ P) (hzero : score x = 0) (s : S) : a x s = 0 := by
  have h := (contribution_le_sensitivity_mul_cost ha hx s).trans
    (mul_le_mul_of_nonneg_right (hscore x hx) (cost_nonneg ha P s))
  rw [hzero, zero_mul] at h
  exact le_antisymm h (ha x s)

/-- The zero-total case is a zero objective. No probability distribution on
an empty positive-score support needs to be constructed. -/
theorem cost_zero_of_totalScore_zero {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hT : totalScore score P = 0) (s : S) : cost a P s = 0 := by
  have hscore0 := score_nonneg_of_dominates ha hscore
  unfold cost
  apply Finset.sum_eq_zero
  intro x hx
  have hle : score x ≤ totalScore score P := Finset.single_le_sum hscore0 hx
  rw [hT] at hle
  have hz : score x = 0 := le_antisymm hle (hscore0 x hx)
  exact loss_zero_of_score_zero ha hscore hx hz s

/-- The degenerate zero-total input has an exact empty summary. -/
theorem empty_coreset_of_totalScore_zero {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hT : totalScore score P = 0) : IsCoreset 0 (cost a P) (cost a ∅) := by
  intro s
  rw [cost_zero_of_totalScore_zero ha hscore hT s]
  simp

theorem positiveSupport_score_sum {P : Finset J} {score : J → ℝ}
    (hscore0 : ∀ x ∈ P, 0 ≤ score x) :
    (∑ x : PositiveIndex P score, score x.val) = totalScore score P := by
  classical
  rw [Finset.sum_coe_sort]
  unfold positiveSupport totalScore
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hxnot
  have hn : ¬ 0 < score x := by
    intro hpos
    exact hxnot (Finset.mem_filter.mpr ⟨hx, hpos⟩)
  exact le_antisymm (le_of_not_gt hn) (hscore0 x hx)

/-- Restricting to positive scores does not change any reference query cost. -/
theorem positiveSupport_cost {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (s : S) :
    cost (fun (x : PositiveIndex P score) t => a x.val t) Finset.univ s = cost a P s := by
  classical
  unfold cost
  change (∑ x : PositiveIndex P score, a x.val s) = ∑ x ∈ P, a x s
  rw [Finset.sum_coe_sort (positiveSupport P score) (fun x => a x s)]
  unfold positiveSupport
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hxnot
  have hn : ¬ 0 < score x := by
    intro hpos
    exact hxnot (Finset.mem_filter.mpr ⟨hx, hpos⟩)
  have hz : score x = 0 := le_antisymm (le_of_not_gt hn)
    (score_nonneg_of_dominates ha hscore x hx)
  exact loss_zero_of_score_zero ha hscore hx hz s

/-- The actual one-draw PMF `q_x = score_x / T` on positive-score support. -/
def scoreSupportPMF (P : Finset J) (score : J → ℝ)
    (hscore0 : ∀ x ∈ P, 0 ≤ score x) (hT : 0 < totalScore score P) :
    PMF (PositiveIndex P score) :=
  pmfOfMass (fun x => score x.val / totalScore score P)
    (fun x => div_nonneg (positiveIndex_score_pos x).le hT.le)
    (by rw [← Finset.sum_div, positiveSupport_score_sum hscore0]; exact div_self hT.ne')

@[simp] theorem mass_scoreSupportPMF (P : Finset J) (score : J → ℝ)
    (hscore0 : ∀ x ∈ P, 0 ≤ score x) (hT : 0 < totalScore score P)
    (x : PositiveIndex P score) :
    mass (scoreSupportPMF P score hscore0 hT) x = score x.val / totalScore score P := by
  unfold scoreSupportPMF
  rw [mass_pmfOfMass]

theorem mass_scoreSupportPMF_pos (P : Finset J) (score : J → ℝ)
    (hscore0 : ∀ x ∈ P, 0 ≤ score x) (hT : 0 < totalScore score P)
    (x : PositiveIndex P score) : 0 < mass (scoreSupportPMF P score hscore0 hT) x := by
  rw [mass_scoreSupportPMF]
  exact div_pos (positiveIndex_score_pos x) hT

/-- The inverse-probability sample contribution is exactly the score-sampling
weight from Lemma 3.2 / Theorem A.1. -/
theorem support_sample_contribution_eq {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (hscore0 : ∀ x ∈ P, 0 ≤ score x) (hT : 0 < totalScore score P)
    {m : ℕ} (hm : 0 < m) (sample : Fin m → PositiveIndex P score) :
    inverseProbabilityContribution (fun (x : PositiveIndex P score) s => a x.val s)
        (mass (scoreSupportPMF P score hscore0 hT)) m sample =
      sampledContribution a (fun i => (sample i).val) score (totalScore score P) m := by
  funext i s
  unfold inverseProbabilityContribution sampledContribution samplingWeight
  rw [mass_scoreSupportPMF]
  rw [inverse_probability_weight hm hT (positiveIndex_score_pos (sample i))]

/-- Complete ordinary coreset guarantee for actual normalized-score iid draws,
with zero-score input indices handled by the support reduction above. -/
theorem scoreSampling_coreset_success {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hT : 0 < totalScore score P) {m : ℕ} {ε failure : ℝ}
    (hε : 0 < ε) (hfailure : 0 < failure)
    (hsize : fallbackSampleSize
      (scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT) ε failure ≤ m) :
    SucceedsWithProbabilityAtLeast
      (iidLaw (scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT) m)
      (1 - ENNReal.ofReal failure)
      (fun sample : Fin m → PositiveIndex P score =>
        IsCoreset ε (cost a P)
          (cost (sampledContribution a (fun i => (sample i).val) score (totalScore score P) m)
            Finset.univ)) := by
  let p := scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT
  have hm : 0 < m := (fallbackSampleSize_pos p ε failure).trans_le hsize
  have h := iid_coreset_success_of_sampleSize p
    (a := fun (x : PositiveIndex P score) s => a x.val s)
    (fun x s => ha x.val s) hε hfailure
    (mass_scoreSupportPMF_pos P score (score_nonneg_of_dominates ha hscore) hT) hsize
  apply h.mono
  intro sample hco
  have href : cost (fun (x : PositiveIndex P score) s => a x.val s) Finset.univ =
      cost a P := funext (positiveSupport_cost ha hscore)
  rw [href, support_sample_contribution_eq (score_nonneg_of_dominates ha hscore) hT hm sample]
    at hco
  exact hco

/-- The actual normalized-score product distribution now supplies the clean
success hypothesis of Theorem A.1; it is no longer an external assumption. -/
theorem scoreSampling_fault_tolerant {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hT : 0 < totalScore score P) {m f : ℕ} {ε failure α : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hfailure : 0 < failure) (hα : 1 ≤ α)
    (hordinary : fallbackSampleSize
      (scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT) ε failure ≤ m)
    (hfault : α * (f : ℝ) * totalScore score P / ε ≤ (m : ℝ)) :
    SucceedsWithProbabilityAtLeast
      (iidLaw (scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT) m)
      (1 - ENNReal.ofReal failure)
      (fun sample : Fin m → PositiveIndex P score =>
        FilteringSuccess ε α f (cost a P)
          (sampledContribution a (fun i => (sample i).val) score (totalScore score P) m)
          Finset.univ) := by
  let p := scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT
  have hm : 0 < m := (fallbackSampleSize_pos p ε failure).trans_le hordinary
  exact theorem_A_1_success_probability (iidLaw p m) ha
    (fun sample i => positiveIndex_mem (sample i)) hscore hm hε hεsmall hα hfault
    (scoreSampling_coreset_success ha hscore hT hε hfailure hordinary)

/-- Complete rounded additive construction for the actual iid score sampler.
It certifies the exact number of separately stored copies and its success
probability, using the explicit finite-input fallback as its ordinary count. -/
theorem scoreSampling_fault_tolerant_rounded {a : J → S → ℝ} {P : Finset J} {score : J → ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hT : 0 < totalScore score P) {f : ℕ} {ε failure α : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hfailure : 0 < failure) (hα : 1 ≤ α) :
    let p := scoreSupportPMF P score (score_nonneg_of_dominates ha hscore) hT
    let m := faultTolerantSampleSize (fallbackSampleSize p ε failure) f α (totalScore score P) ε
    (Finset.univ : Finset (Fin m)).card = m ∧
      SucceedsWithProbabilityAtLeast (iidLaw p m) (1 - ENNReal.ofReal failure)
        (fun sample : Fin m → PositiveIndex P score =>
          FilteringSuccess ε α f (cost a P)
            (sampledContribution a (fun i => (sample i).val) score (totalScore score P) m)
            Finset.univ) := by
  dsimp only
  refine ⟨by simp, ?_⟩
  apply scoreSampling_fault_tolerant ha hscore hT hε hεsmall hfailure hα
  · exact Nat.le_add_right _ _
  · exact faultTolerantSampleSize_lower _ f α (totalScore score P) ε

/-- Exact sensitivity sampling is the exact-score specialization of the fully
proved construction, including zero-sensitivity support handling. -/
theorem sensitivitySampling_fault_tolerant_rounded {a : J → S → ℝ} {P : Finset J}
    (ha : ∀ x s, 0 ≤ a x s) (hT : 0 < totalSensitivity a P)
    {f : ℕ} {ε failure α : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hfailure : 0 < failure) (hα : 1 ≤ α) :
    let p := scoreSupportPMF P (sensitivity a P) (fun x _ => sensitivity_nonneg ha P x) hT
    let m := faultTolerantSampleSize (fallbackSampleSize p ε failure) f α (totalSensitivity a P) ε
    (Finset.univ : Finset (Fin m)).card = m ∧
      SucceedsWithProbabilityAtLeast (iidLaw p m) (1 - ENNReal.ofReal failure)
        (fun sample : Fin m → PositiveIndex P (sensitivity a P) =>
          FilteringSuccess ε α f (cost a P)
            (sampledContribution a (fun i => (sample i).val) (sensitivity a P)
              (totalSensitivity a P) m) Finset.univ) := by
  exact scoreSampling_fault_tolerant_rounded ha (fun _ _ => le_rfl) hT
    hε hεsmall hfailure hα

end

end FTC.Probability
