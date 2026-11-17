import FaultTolerantCoresets.Probability.Histogram
import FaultTolerantCoresets.Sampling
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual finite iid sampling and a complete, deliberately loose coreset bound

`iidLaw p m` is the finite product of the one-draw probability measure of `p`.
Independence, marginal laws, histogram expectations and variances are proved
for this law, rather than assumed. Chebyshev's inequality and a finite union
bound give a measurable event on which *every input frequency* is accurate.
The histogram certificate then holds simultaneously for every solution.

The resulting fallback count is roughly
`(∑ x, 1 / p(x)) / (failure * ε^2)`. This is a valid finite-input fallback,
not a claim to reproduce sharper geometry-specific sensitivity-sampling bounds.
-/

namespace FTC.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {J : Type*} [Fintype J] [DecidableEq J]
variable [MeasurableSpace J] [DiscreteMeasurableSpace J]

/-- The real mass of a single input index. -/
noncomputable def mass (p : PMF J) (x : J) : ℝ := (p x).toReal

theorem mass_nonneg (p : PMF J) (x : J) : 0 ≤ mass p x := ENNReal.toReal_nonneg

theorem mass_le_one (p : PMF J) (x : J) : mass p x ≤ 1 := by
  simpa [mass] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one x)

/-- A normalized finite probability mass function from real probabilities. -/
noncomputable def pmfOfMass (q : J → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hsum : ∑ x, q x = 1) : PMF J :=
  PMF.ofFintype (fun x => ENNReal.ofReal (q x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hq x), hsum]
    simp)

@[simp] theorem mass_pmfOfMass (q : J → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hsum : ∑ x, q x = 1) (x : J) : mass (pmfOfMass q hq hsum) x = q x := by
  simp [mass, pmfOfMass, ENNReal.toReal_ofReal (hq x)]

/-- The actual law of `m` independent draws with replacement. -/
noncomputable def iidLaw (p : PMF J) (m : ℕ) : Measure (Fin m → J) :=
  Measure.pi fun _ : Fin m => p.toMeasure

instance iidLaw_isProbabilityMeasure (p : PMF J) (m : ℕ) :
    IsProbabilityMeasure (iidLaw p m) := by
  unfold iidLaw
  infer_instance

/-- The joint mass is the product of the individual masses. -/
theorem iidLaw_singleton (p : PMF J) (m : ℕ) (sample : Fin m → J) :
    iidLaw p m {sample} = ∏ i, p (sample i) := by
  simp [iidLaw, Measure.pi_singleton, PMF.toMeasure_apply_singleton]

/-- Every coordinate has precisely the specified one-draw distribution. -/
theorem iidLaw_eval_map (p : PMF J) (m : ℕ) (i : Fin m) :
    (iidLaw p m).map (Function.eval i) = p.toMeasure := by
  exact (measurePreserving_eval (fun _ : Fin m => p.toMeasure) i).map_eq

/-- The sample coordinates are independent for the actual product law. -/
theorem iidLaw_independent (p : PMF J) (m : ℕ) :
    iIndepFun (fun i : Fin m => Function.eval i) (iidLaw p m) := by
  simpa [iidLaw] using
    (iIndepFun_pi (μ := fun _ : Fin m => p.toMeasure)
      (X := fun _ : Fin m => fun x : J => x) (fun _ => measurable_id.aemeasurable))

theorem integral_hit (p : PMF J) (x : J) :
    ∫ y, hit x y ∂p.toMeasure = mass p x := by
  simp [PMF.integral_eq_sum, hit, mass]

theorem variance_hit (p : PMF J) (x : J) :
    variance (hit x) p.toMeasure = mass p x * (1 - mass p x) := by
  rw [variance_eq_sub (MemLp.of_discrete : MemLp (hit x) 2 p.toMeasure)]
  have hsquare : (hit x) ^ 2 = hit x := by
    funext y
    simp only [Pi.pow_apply, hit]
    split <;> norm_num
  rw [hsquare, integral_hit]
  ring

theorem integral_iid_eval (p : PMF J) (m : ℕ) (i : Fin m) (f : J → ℝ) :
    ∫ sample, f (sample i) ∂iidLaw p m = ∫ x, f x ∂p.toMeasure := by
  calc
    _ = ∫ x, f x ∂((iidLaw p m).map (Function.eval i)) :=
      (integral_map (measurable_pi_apply i).aemeasurable
        (by exact AEStronglyMeasurable.of_discrete)).symm
    _ = _ := by rw [iidLaw_eval_map]

/-- The expected count is `m p(x)`. -/
theorem histogram_expectation (p : PMF J) (m : ℕ) (x : J) :
    ∫ sample, histogram sample x ∂iidLaw p m = (m : ℝ) * mass p x := by
  unfold histogram
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp [integral_iid_eval, integral_hit]

/-- The binomial variance, derived from independence of the product law. -/
theorem histogram_variance (p : PMF J) (m : ℕ) (x : J) :
    variance (fun sample : Fin m → J => histogram sample x) (iidLaw p m) =
      (m : ℝ) * (mass p x * (1 - mass p x)) := by
  have hfun : (fun sample : Fin m → J => histogram sample x) =
      ∑ i : Fin m, fun sample : Fin m → J => hit x (sample i) := by
    funext sample
    simp [histogram]
  rw [hfun, iidLaw, variance_sum_pi (fun _ =>
    (MemLp.of_discrete : MemLp (hit x) 2 p.toMeasure))]
  simp [variance_hit]

/-- Chebyshev's inequality for one input frequency, with computed moments. -/
theorem histogram_deviation_le (p : PMF J) {m : ℕ} {ε : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (x : J) (hx : 0 < mass p x) :
    iidLaw p m {sample | ε * ((m : ℝ) * mass p x) ≤
        |histogram sample x - (m : ℝ) * mass p x|} ≤
      ENNReal.ofReal ((1 / mass p x) / ((m : ℝ) * ε ^ 2)) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hthreshold : 0 < ε * ((m : ℝ) * mass p x) := mul_pos hε (mul_pos hmR hx)
  have hcheb := meas_ge_le_variance_div_sq
    (μ := iidLaw p m) (X := fun sample : Fin m → J => histogram sample x)
    (MemLp.of_discrete : MemLp (fun sample : Fin m → J => histogram sample x) 2
      (iidLaw p m)) hthreshold
  rw [histogram_expectation] at hcheb
  have hvar : variance (fun sample : Fin m → J => histogram sample x) (iidLaw p m) ≤
      (m : ℝ) * mass p x := by
    rw [histogram_variance]
    have hq := mass_nonneg p x
    have hmq : 0 ≤ (m : ℝ) * mass p x := mul_nonneg hmR.le hq
    have := mul_le_mul_of_nonneg_left (sub_le_self (1 : ℝ) hq) hmq
    nlinarith
  calc
    _ ≤ ENNReal.ofReal
        (variance (fun sample : Fin m → J => histogram sample x) (iidLaw p m) /
          (ε * ((m : ℝ) * mass p x)) ^ 2) := hcheb
    _ ≤ ENNReal.ofReal (((m : ℝ) * mass p x) /
          (ε * ((m : ℝ) * mass p x)) ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg _))
    _ = _ := by
      congr 1
      field_simp [hmR.ne', hε.ne', hx.ne']
      <;> ring

/-- At least one input index has a deviation at or above its tolerance. -/
def badHistogram (p : PMF J) (ε : ℝ) (m : ℕ) : Set (Fin m → J) :=
  {sample | ∃ x, ε * ((m : ℝ) * mass p x) ≤
    |histogram sample x - (m : ℝ) * mass p x|}

/-- The reciprocal-mass sum in the explicit finite-input fallback bound. -/
noncomputable def inverseMassSum (p : PMF J) : ℝ := ∑ x, 1 / mass p x

theorem inverseMassSum_nonneg (p : PMF J) : 0 ≤ inverseMassSum p :=
  Finset.sum_nonneg fun x _ => div_nonneg (by norm_num) (mass_nonneg p x)

/-- A finite union bound, with no assumption on the number of solutions. -/
theorem badHistogram_measure_le (p : PMF J) {m : ℕ} {ε : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hp : ∀ x, 0 < mass p x) :
    iidLaw p m (badHistogram p ε m) ≤
      ENNReal.ofReal (inverseMassSum p / ((m : ℝ) * ε ^ 2)) := by
  have hset : badHistogram p ε m = ⋃ x : J,
      {sample | ε * ((m : ℝ) * mass p x) ≤
        |histogram sample x - (m : ℝ) * mass p x|} := by
    ext sample
    simp [badHistogram]
  rw [hset]
  calc
    _ ≤ ∑ x, iidLaw p m {sample | ε * ((m : ℝ) * mass p x) ≤
        |histogram sample x - (m : ℝ) * mass p x|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ x, ENNReal.ofReal ((1 / mass p x) / ((m : ℝ) * ε ^ 2)) :=
      Finset.sum_le_sum fun x _ => histogram_deviation_le p hm hε x (hp x)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
        div_nonneg (div_nonneg (by norm_num) (mass_nonneg p x))
          (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg ε)))]
      congr 1
      simp [inverseMassSum, Finset.sum_div]

theorem accurateHistogram_of_not_bad (p : PMF J) {m : ℕ} {ε : ℝ}
    {sample : Fin m → J} (h : sample ∉ badHistogram p ε m) :
    AccurateHistogram (mass p) ε sample := by
  intro x
  have hn : ¬ ε * ((m : ℝ) * mass p x) ≤
      |histogram sample x - (m : ℝ) * mass p x| := fun hx => h ⟨x, hx⟩
  exact (not_le.mp hn).le

/-- Complete ordinary coreset guarantee for the actual iid law. The finite
histogram-complement event is a measurable witness for the probability bound. -/
theorem iid_coreset_success {S : Type*} (p : PMF J) {a : J → S → ℝ}
    {m : ℕ} {ε failure : ℝ} (ha : ∀ x s, 0 ≤ a x s)
    (hm : 0 < m) (hε : 0 < ε) (hp : ∀ x, 0 < mass p x)
    (hbound : inverseMassSum p / ((m : ℝ) * ε ^ 2) ≤ failure) :
    SucceedsWithProbabilityAtLeast (iidLaw p m) (1 - ENNReal.ofReal failure)
      (fun sample => IsCoreset ε (cost a Finset.univ)
        (cost (inverseProbabilityContribution a (mass p) m sample) Finset.univ)) := by
  have hbad : iidLaw p m (badHistogram p ε m) ≤ ENNReal.ofReal failure :=
    (badHistogram_measure_le p hm hε hp).trans (ENNReal.ofReal_le_ofReal hbound)
  refine ⟨(badHistogram p ε m)ᶜ, MeasurableSet.of_discrete, ?_, ?_⟩
  · rw [measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), measure_univ]
    exact tsub_le_tsub_left hbad 1
  · intro sample hsample
    exact (accurateHistogram_of_not_bad p hsample).isCoreset ha hm hp

/-- A loose but explicit finite-input ordinary sample count. It works for
every larger count, so it can be used as `m_sc` in the additive construction. -/
noncomputable def fallbackSampleSize (p : PMF J) (ε failure : ℝ) : ℕ :=
  ⌈inverseMassSum p / (failure * ε ^ 2)⌉₊ + 1

theorem fallbackSampleSize_pos (p : PMF J) (ε failure : ℝ) :
    0 < fallbackSampleSize p ε failure := Nat.zero_lt_succ _

theorem fallbackSampleSize_bound (p : PMF J) {m : ℕ} {ε failure : ℝ}
    (hε : 0 < ε) (hfailure : 0 < failure)
    (hsize : fallbackSampleSize p ε failure ≤ m) :
    inverseMassSum p / ((m : ℝ) * ε ^ 2) ≤ failure := by
  have hm : 0 < m := (fallbackSampleSize_pos p ε failure).trans_le hsize
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hceil : ⌈inverseMassSum p / (failure * ε ^ 2)⌉₊ ≤ m :=
    (Nat.le_succ _).trans hsize
  have hceilR : (⌈inverseMassSum p / (failure * ε ^ 2)⌉₊ : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hceil
  have hratio := (Nat.le_ceil (inverseMassSum p / (failure * ε ^ 2))).trans hceilR
  have hprod := (div_le_iff₀ (mul_pos hfailure (sq_pos_of_pos hε))).1 hratio
  apply (div_le_iff₀ (mul_pos hmR (sq_pos_of_pos hε))).2
  nlinarith

theorem iid_coreset_success_of_sampleSize {S : Type*} (p : PMF J) {a : J → S → ℝ}
    {m : ℕ} {ε failure : ℝ} (ha : ∀ x s, 0 ≤ a x s)
    (hε : 0 < ε) (hfailure : 0 < failure) (hp : ∀ x, 0 < mass p x)
    (hsize : fallbackSampleSize p ε failure ≤ m) :
    SucceedsWithProbabilityAtLeast (iidLaw p m) (1 - ENNReal.ofReal failure)
      (fun sample => IsCoreset ε (cost a Finset.univ)
        (cost (inverseProbabilityContribution a (mass p) m sample) Finset.univ)) :=
  iid_coreset_success p ha ((fallbackSampleSize_pos p ε failure).trans_le hsize) hε hp
    (fallbackSampleSize_bound p hε hfailure hsize)

end FTC.Probability
