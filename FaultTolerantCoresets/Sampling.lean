import FaultTolerantCoresets.Decoder
import FaultTolerantCoresets.SamplingWeights
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Theorem 3.1 and Theorem A.1: sampling wrappers

The substantive filtering argument is in `Decoder.lean`. This file applies it
to separately indexed exact/proxy samples and transfers the standard sampler's
success event unchanged. The sampler is parameterized by its usual coreset
success guarantee, as is the paper's quantity `m_sc(ε)`.

Probability is stated using a *measurable witness event*. The predicate that
all adversarial corruptions are decodable need not itself be measurably known:
the same measurable event certifying the clean coreset certifies the universal
adversarial guarantee. No concentration theorem or iid sampling law is assumed
to have been proved here.
-/

namespace FTC

open MeasureTheory
open scoped ENNReal

section Deterministic

variable {I S X : Type*} [DecidableEq I]

/-- The success event: a clean `ε`-coreset and simultaneous `6ε` recovery for
every nonnegative corruption affecting at most `f` individual active indices,
using any valid `α`-approximate sensitivity oracle. `peel` always returns a
subset of the active indices and inherits the corrupted contributions. -/
def FilteringSuccess (ε α : ℝ) (f : ℕ) (reference : S → ℝ)
    (c : I → S → ℝ) (U : Finset I) : Prop :=
  IsCoreset ε reference (cost c U) ∧
    ∀ (d : I → S → ℝ), (∀ i s, 0 ≤ d i s) →
      ∀ (B : Finset I), B.card ≤ f →
        (∀ i ∈ U, i ∉ B → ∀ s, d i s = c i s) →
        ∀ (oracle : ApproxSensitivityOracle d α),
          IsCoreset (6 * ε) reference (cost d (peel oracle.score f U))

/-- Package the deterministic theorem as the simultaneous success predicate. -/
theorem filtering_success_of_entry_bound {c : I → S → ℝ} {reference : S → ℝ}
    {U : Finset I} {f : ℕ} {ε δ α : ℝ}
    (hc : ∀ i s, 0 ≤ c i s) (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε reference (cost c U))
    (hentry : ∀ i ∈ U, ∀ s, c i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε) :
    FilteringSuccess ε α f reference c U := by
  refine ⟨hcoreset, ?_⟩
  intro d hd B hB hagrees oracle
  exact filtering_decoder_correct hc hd hreference hε hεsmall hδ hα
    hcoreset hB hagrees hentry hbudget oracle

/-- Bridge to Definition 2.1 for actual point/weight corruptions. Once a valid
oracle is supplied on each corrupted summary, Algorithm 1 is a filtering
decoder for a `6ε`-coreset with its inherited weights. -/
theorem FilteringSuccess.to_isFilteringFaultTolerant
    {ε α : ℝ} {f : ℕ} {reference : S → ℝ} {loss : X → S → ℝ}
    {U : Finset I} {entries : I → Entry X}
    (hsuccess : FilteringSuccess ε α f reference (contribution loss entries) U)
    (hε : 0 ≤ ε) (hreference : ∀ s, 0 ≤ reference s)
    (hloss : ∀ x s, 0 ≤ loss x s)
    (oracles : ∀ corrupted : I → Entry X,
      ApproxSensitivityOracle (contribution loss corrupted) α) :
    IsFilteringFaultTolerant (6 * ε) f reference loss U entries
      (fun corrupted => peel (oracles corrupted).score f U) := by
  constructor
  · intro s
    have hco := hsuccess.1 s
    have hεref := mul_nonneg hε (hreference s)
    constructor <;> nlinarith
  · intro corrupted hcorrupt
    obtain ⟨B, _, hB, hagrees⟩ := hcorrupt
    refine ⟨peel_subset (oracles corrupted).score f U, ?_⟩
    apply hsuccess.2 (contribution loss corrupted)
      (contribution_nonneg loss corrupted hloss) B hB ?_ (oracles corrupted)
    intro i hi hiB s
    simp only [contribution, hagrees i hi hiB]

end Deterministic

section IndexedSamples

variable {I J S : Type*} [DecidableEq I] [DecidableEq J]

/-- Exact sensitivity sampling, conditioned only on the usual clean coreset
event. There is no injectivity assumption on the indexed sample map. -/
theorem exactSampling_filtering_success {a : J → S → ℝ} {sample : I → J}
    {P : Finset J} {U : Finset I} {m f : ℕ} {ε α : ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ i, sample i ∈ P)
    (hm : 0 < m) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hsize : α * (f : ℝ) * totalSensitivity a P / ε ≤ (m : ℝ))
    (hcoreset : IsCoreset ε (cost a P)
      (cost (sampledContribution a sample (sensitivity a P) (totalSensitivity a P) m) U)) :
    FilteringSuccess ε α f (cost a P)
      (sampledContribution a sample (sensitivity a P) (totalSensitivity a P) m) U := by
  apply filtering_success_of_entry_bound
    (fun i s => sampledContribution_nonneg ha (totalSensitivity_nonneg ha P)
      (sensitivity_nonneg ha P (sample i)))
    (cost_nonneg ha P) hε.le hεsmall
    (div_nonneg (totalSensitivity_nonneg ha P) (Nat.cast_nonneg m)) hα hcoreset
    (fun i _ s => lemma_3_2 ha hm (hsample i) s)
  simpa [mul_comm, mul_left_comm, mul_assoc] using sampling_budget hε hm hsize

/-- Proxy-score sampling, conditioned on its clean coreset event (Theorem A.1). -/
theorem proxySampling_filtering_success {a : J → S → ℝ} {sample : I → J}
    {P : Finset J} {U : Finset I} {score : J → ℝ} {m f : ℕ} {ε α : ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ i, sample i ∈ P)
    (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hm : 0 < m) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hsize : α * (f : ℝ) * totalScore score P / ε ≤ (m : ℝ))
    (hcoreset : IsCoreset ε (cost a P)
      (cost (sampledContribution a sample score (totalScore score P) m) U)) :
    FilteringSuccess ε α f (cost a P)
      (sampledContribution a sample score (totalScore score P) m) U := by
  have hscore0 : ∀ x ∈ P, 0 ≤ score x :=
    fun x hx => (sensitivity_nonneg ha P x).trans (hscore x hx)
  have hT : 0 ≤ totalScore score P := totalScore_nonneg hscore0
  apply filtering_success_of_entry_bound
    (fun i s => sampledContribution_nonneg ha hT (hscore0 _ (hsample i)))
    (cost_nonneg ha P) hε.le hεsmall
    (div_nonneg hT (Nat.cast_nonneg m)) hα hcoreset
    (fun i _ s => proxySampling_entry_bound ha hscore hm (hsample i) s)
  simpa [mul_comm, mul_left_comm, mul_assoc] using sampling_budget hε hm hsize

theorem exactSampling_filtering_success_ceil {a : J → S → ℝ} {sample : I → J}
    {P : Finset J} {U : Finset I} {m_sc f : ℕ} {ε α : ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ i, sample i ∈ P)
    (hmsc : 0 < m_sc) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε (cost a P)
      (cost (sampledContribution a sample (sensitivity a P) (totalSensitivity a P)
        (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε)) U)) :
    FilteringSuccess ε α f (cost a P)
      (sampledContribution a sample (sensitivity a P) (totalSensitivity a P)
        (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε)) U :=
  exactSampling_filtering_success ha hsample (faultTolerantSampleSize_pos hmsc)
    hε hεsmall hα (faultTolerantSampleSize_lower m_sc f α (totalSensitivity a P) ε) hcoreset

theorem proxySampling_filtering_success_ceil {a : J → S → ℝ} {sample : I → J}
    {P : Finset J} {U : Finset I} {score : J → ℝ} {m_sc f : ℕ} {ε α : ℝ}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ i, sample i ∈ P)
    (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hmsc : 0 < m_sc) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε (cost a P)
      (cost (sampledContribution a sample score (totalScore score P)
        (faultTolerantSampleSize m_sc f α (totalScore score P) ε)) U)) :
    FilteringSuccess ε α f (cost a P)
      (sampledContribution a sample score (totalScore score P)
        (faultTolerantSampleSize m_sc f α (totalScore score P) ε)) U :=
  proxySampling_filtering_success ha hsample hscore (faultTolerantSampleSize_pos hmsc)
    hε hεsmall hα (faultTolerantSampleSize_lower m_sc f α (totalScore score P) ε) hcoreset

end IndexedSamples

section SuccessEvents

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable event of probability/mass at least `p` on which the predicate
holds. This avoids presupposing measurability of a predicate with universal
quantification over adversarial corruptions and sensitivity oracles. -/
def SucceedsWithProbabilityAtLeast (μ : Measure Ω) (p : ℝ≥0∞)
    (predicate : Ω → Prop) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ p ≤ μ E ∧ ∀ ω ∈ E, predicate ω

theorem SucceedsWithProbabilityAtLeast.mono {μ : Measure Ω} {p : ℝ≥0∞}
    {P Q : Ω → Prop} (hP : SucceedsWithProbabilityAtLeast μ p P)
    (hPQ : ∀ ω, P ω → Q ω) : SucceedsWithProbabilityAtLeast μ p Q := by
  obtain ⟨E, hE, hp, hP⟩ := hP
  exact ⟨E, hE, hp, fun ω hω => hPQ ω (hP ω hω)⟩

theorem SucceedsWithProbabilityAtLeast.of_measurable_event
    {μ : Measure Ω} {p : ℝ≥0∞} {predicate : Ω → Prop}
    (hE : MeasurableSet {ω | predicate ω}) (hp : p ≤ μ {ω | predicate ω}) :
    SucceedsWithProbabilityAtLeast μ p predicate :=
  ⟨{ω | predicate ω}, hE, hp, fun _ hω => hω⟩

variable {I S : Type*} [DecidableEq I]

/-- The standard clean success witness also certifies simultaneous recovery
against all admissible adversaries; the witnessing event is unchanged. -/
theorem filtering_success_probability {μ : Measure Ω} {p : ℝ≥0∞}
    {clean : Ω → I → S → ℝ} {reference : S → ℝ} {U : Finset I}
    {f : ℕ} {ε δ α : ℝ}
    (hc : ∀ ω i s, 0 ≤ clean ω i s) (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hentry : ∀ ω, ∀ i ∈ U, ∀ s, clean ω i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε)
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε reference (cost (clean ω) U))) :
    SucceedsWithProbabilityAtLeast μ p
      (fun ω => FilteringSuccess ε α f reference (clean ω) U) :=
  hstandard.mono fun ω hco => filtering_success_of_entry_bound (hc ω) hreference
    hε hεsmall hδ hα hco (hentry ω) hbudget

/-- Also, clean-event inclusion gives an outer-measure inequality for the full
predicates. The measurable-witness theorem above is the probability statement. -/
theorem outerMeasure_clean_event_le_filtering_event (μ : Measure Ω)
    {clean : Ω → I → S → ℝ} {reference : S → ℝ} {U : Finset I}
    {f : ℕ} {ε δ α : ℝ}
    (hc : ∀ ω i s, 0 ≤ clean ω i s) (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hentry : ∀ ω, ∀ i ∈ U, ∀ s, clean ω i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε) :
    μ {ω | IsCoreset ε reference (cost (clean ω) U)} ≤
      μ {ω | FilteringSuccess ε α f reference (clean ω) U} := by
  exact measure_mono fun ω hco => filtering_success_of_entry_bound (hc ω) hreference
    hε hεsmall hδ hα hco (hentry ω) hbudget

end SuccessEvents

section SampleSuccessEvents

variable {Ω I J S : Type*} [MeasurableSpace Ω] [DecidableEq I] [DecidableEq J]

/-- Theorem 3.1 for any sufficiently large integer sample count. A standard
sampler's measurable clean-success event of mass `p` yields the same mass `p`
for recovery from every `f`-fault corruption. -/
theorem theorem_3_1_success_probability (μ : Measure Ω)
    {a : J → S → ℝ} {samples : Ω → I → J} {P : Finset J} {U : Finset I}
    {m f : ℕ} {ε α : ℝ} {p : ℝ≥0∞}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ ω i, samples ω i ∈ P)
    (hm : 0 < m) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hsize : α * (f : ℝ) * totalSensitivity a P / ε ≤ (m : ℝ))
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε (cost a P)
        (cost (sampledContribution a (samples ω) (sensitivity a P) (totalSensitivity a P) m) U))) :
    SucceedsWithProbabilityAtLeast μ p
      (fun ω => FilteringSuccess ε α f (cost a P)
        (sampledContribution a (samples ω) (sensitivity a P) (totalSensitivity a P) m) U) :=
  hstandard.mono fun ω hco =>
    exactSampling_filtering_success ha (hsample ω) hm hε hεsmall hα hsize hco

/-- Theorem A.1 for sufficiently large proxy-score sample counts. -/
theorem theorem_A_1_success_probability (μ : Measure Ω)
    {a : J → S → ℝ} {samples : Ω → I → J} {P : Finset J} {U : Finset I}
    {score : J → ℝ} {m f : ℕ} {ε α : ℝ} {p : ℝ≥0∞}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ ω i, samples ω i ∈ P)
    (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hm : 0 < m) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hsize : α * (f : ℝ) * totalScore score P / ε ≤ (m : ℝ))
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε (cost a P)
        (cost (sampledContribution a (samples ω) score (totalScore score P) m) U))) :
    SucceedsWithProbabilityAtLeast μ p
      (fun ω => FilteringSuccess ε α f (cost a P)
        (sampledContribution a (samples ω) score (totalScore score P) m) U) :=
  hstandard.mono fun ω hco =>
    proxySampling_filtering_success ha (hsample ω) hscore hm hε hεsmall hα hsize hco

/-- Theorem 3.1 with the rounded additive sample size
`m_sc + ceil(α f T / ε)`. -/
theorem theorem_3_1 (μ : Measure Ω)
    {a : J → S → ℝ} {samples : Ω → I → J} {P : Finset J} {U : Finset I}
    {m_sc f : ℕ} {ε α : ℝ} {p : ℝ≥0∞}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ ω i, samples ω i ∈ P)
    (hmsc : 0 < m_sc) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε (cost a P)
        (cost (sampledContribution a (samples ω) (sensitivity a P) (totalSensitivity a P)
          (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε)) U))) :
    SucceedsWithProbabilityAtLeast μ p
      (fun ω => FilteringSuccess ε α f (cost a P)
        (sampledContribution a (samples ω) (sensitivity a P) (totalSensitivity a P)
          (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε)) U) :=
  theorem_3_1_success_probability μ ha hsample (faultTolerantSampleSize_pos hmsc)
    hε hεsmall hα (faultTolerantSampleSize_lower m_sc f α (totalSensitivity a P) ε) hstandard

/-- Theorem A.1 with the rounded additive proxy-score sample size. -/
theorem theorem_A_1 (μ : Measure Ω)
    {a : J → S → ℝ} {samples : Ω → I → J} {P : Finset J} {U : Finset I}
    {score : J → ℝ} {m_sc f : ℕ} {ε α : ℝ} {p : ℝ≥0∞}
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ ω i, samples ω i ∈ P)
    (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hmsc : 0 < m_sc) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε (cost a P)
        (cost (sampledContribution a (samples ω) score (totalScore score P)
          (faultTolerantSampleSize m_sc f α (totalScore score P) ε)) U))) :
    SucceedsWithProbabilityAtLeast μ p
      (fun ω => FilteringSuccess ε α f (cost a P)
        (sampledContribution a (samples ω) score (totalScore score P)
          (faultTolerantSampleSize m_sc f α (totalScore score P) ε)) U) :=
  theorem_A_1_success_probability μ ha hsample hscore (faultTolerantSampleSize_pos hmsc)
    hε hεsmall hα (faultTolerantSampleSize_lower m_sc f α (totalScore score P) ε) hstandard

/-- Paper-sized specialization of Theorem 3.1: the stored indices are exactly
`Fin m`, where `m = m_sc + ceil(α f T / ε)`. Its cardinality is certified
explicitly alongside the probability guarantee. Repeated sampled points still
have different stored indices. -/
theorem theorem_3_1_fin (μ : Measure Ω)
    {a : J → S → ℝ} {P : Finset J} {m_sc f : ℕ} {ε α : ℝ} {p : ℝ≥0∞}
    (samples : Ω → Fin (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε) → J)
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ ω i, samples ω i ∈ P)
    (hmsc : 0 < m_sc) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε (cost a P)
        (cost (sampledContribution a (samples ω) (sensitivity a P) (totalSensitivity a P)
          (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε)) Finset.univ))) :
    (Finset.univ : Finset (Fin (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε))).card =
        faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε ∧
      SucceedsWithProbabilityAtLeast μ p
        (fun ω => FilteringSuccess ε α f (cost a P)
          (sampledContribution a (samples ω) (sensitivity a P) (totalSensitivity a P)
            (faultTolerantSampleSize m_sc f α (totalSensitivity a P) ε)) Finset.univ) := by
  refine ⟨by simp, ?_⟩
  exact theorem_3_1 μ ha hsample hmsc hε hεsmall hα hstandard

/-- Theorem A.1 with exactly the stated rounded number of proxy-score samples. -/
theorem theorem_A_1_fin (μ : Measure Ω)
    {a : J → S → ℝ} {P : Finset J} {score : J → ℝ} {m_sc f : ℕ}
    {ε α : ℝ} {p : ℝ≥0∞}
    (samples : Ω → Fin (faultTolerantSampleSize m_sc f α (totalScore score P) ε) → J)
    (ha : ∀ x s, 0 ≤ a x s) (hsample : ∀ ω i, samples ω i ∈ P)
    (hscore : ∀ x ∈ P, sensitivity a P x ≤ score x)
    (hmsc : 0 < m_sc) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hα : 1 ≤ α)
    (hstandard : SucceedsWithProbabilityAtLeast μ p
      (fun ω => IsCoreset ε (cost a P)
        (cost (sampledContribution a (samples ω) score (totalScore score P)
          (faultTolerantSampleSize m_sc f α (totalScore score P) ε)) Finset.univ))) :
    (Finset.univ : Finset (Fin (faultTolerantSampleSize m_sc f α (totalScore score P) ε))).card =
        faultTolerantSampleSize m_sc f α (totalScore score P) ε ∧
      SucceedsWithProbabilityAtLeast μ p
        (fun ω => FilteringSuccess ε α f (cost a P)
          (sampledContribution a (samples ω) score (totalScore score P)
            (faultTolerantSampleSize m_sc f α (totalScore score P) ε)) Finset.univ) := by
  refine ⟨by simp, ?_⟩
  exact theorem_A_1 μ ha hsample hscore hmsc hε hεsmall hα hstandard

end SampleSuccessEvents

end FTC
