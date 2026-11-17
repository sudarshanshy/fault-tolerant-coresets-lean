import FaultTolerantCoresets.Hardness.RationalEncoding

/-!
# Theorem 4.2: conditional NP-hardness and the approximation consequence

The source hardness premise is exactly the promised rational finite-metric
gap k-means problem. The target is a restricted family of genuine weighted
k-means sensitivity problems. Both problems use explicit binary encodings.
The reduction is an actual program in `Computation.Code`, with proved
polynomial bit-cost and output-size bounds. The NP definition and reduction
composition use that same concrete program model.

The pre-existing k-means hardness theorem is a theorem hypothesis, as it is
in the paper. There is no added hardness axiom. We do not claim a formal
equivalence between this program model and a Turing-machine model.
-/

namespace FTC.Hardness

open Computation Complexity Encoding

/-- Definition B.1 on explicit finite rational inputs. -/
def gapKMeans (ρ : ℝ) (hρ : 1 < ρ) : PromiseProblem SourceTy where
  yes x := ∃ h : ValidSource x, originalOptimum x.1 h.base ≤ (rational x.2 : ℝ)
  no x := ∃ h : ValidSource x, ρ * (rational x.2 : ℝ) < originalOptimum x.1 h.base
  disjoint x hy hn := by
    obtain ⟨hy, hyes⟩ := hy
    obtain ⟨hn, hno⟩ := hn
    have hB : 0 < (rational x.2 : ℝ) := by exact_mod_cast rational_pos hy.budget_pos
    change ρ * (rational x.2 : ℝ) < originalOptimum x.1 hy.base at hno
    nlinarith

/-- The sensitivity gap that every α-approximation can decide by comparison
with t. The metric has one distinguished point and otherwise arbitrary
rational distances; all k centers may be chosen anywhere in the metric. -/
def gapSensitivity (α : ℝ) (hα : 1 ≤ α) (t : ℚ) (ht : 0 < t) :
    PromiseProblem TargetTy where
  yes x := ∃ h : ValidTarget x, α * (t : ℝ) ≤ targetSensitivity x h
  no x := ∃ h : ValidTarget x, targetSensitivity x h < (t : ℝ)
  disjoint x hy hn := by
    obtain ⟨hy, hyes⟩ := hy
    obtain ⟨hn, hno⟩ := hn
    have htR : 0 < (t : ℝ) := by exact_mod_cast ht
    change targetSensitivity x hy < (t : ℝ) at hno
    nlinarith

/-- The executable, polynomial, promise-preserving reduction of Appendix B. -/
def gapReduction {ρ α : ℝ} (hα : 1 ≤ α) (hαρ : α < ρ)
    (params : GapParameters ρ α) :
    PolyReduction (gapKMeans ρ (lt_of_le_of_lt hα hαρ))
      (gapSensitivity α hα params.threshold params.threshold_pos) where
  program := reductionCode params.copies
  polynomial := reductionCode_polynomial params.copies
  yes x hx := by
    obtain ⟨h, hyes⟩ := hx
    rw [reductionCode_eval]
    refine ⟨reduce_valid params.copies_pos h, ?_⟩
    letI := h.base.metric.toMetricSpace
    rw [reduce_sensitivity_eq_gadget params.copies_pos x h]
    exact sensitivity_yes (clients x.1) h.base.centers_pos h.base.centers_le_card
      params hα (by exact_mod_cast radius_pos x.1)
      (by exact_mod_cast rational_pos h.budget_pos) hyes
  no x hx := by
    obtain ⟨h, hno⟩ := hx
    rw [reductionCode_eval]
    refine ⟨reduce_valid params.copies_pos h, ?_⟩
    letI := h.base.metric.toMetricSpace
    rw [reduce_sensitivity_eq_gadget params.copies_pos x h]
    exact sensitivity_no (clients x.1) h.base.centers_pos h.base.centers_le_card
      params hα hαρ (by exact_mod_cast radius_pos x.1)
      (by exact_mod_cast rational_pos h.budget_pos) hno

theorem npHard_sensitivity_of_gap {ρ α : ℝ} (hα : 1 ≤ α) (hαρ : α < ρ)
    (params : GapParameters ρ α)
    (hhard : NPHard (gapKMeans ρ (lt_of_le_of_lt hα hαρ))) :
    NPHard (gapSensitivity α hα params.threshold params.threshold_pos) :=
  hhard.of_reduction (gapReduction hα hαρ params)

/-- Theorem 4.2, with the paper's parameters and its source-hardness premise.
The rational threshold is fixed independently of the input instance. -/
theorem theorem_4_2 {ρ δ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ) (hδsmall : δ < ρ - 1)
    (hhard : NPHard (gapKMeans ρ hρ)) :
    ∃ params : GapParameters ρ (ρ - δ),
      NPHard (gapSensitivity (ρ - δ) (by linarith) params.threshold params.threshold_pos) := by
  obtain ⟨params⟩ := paper_gapParameters_nonempty hρ hδ hδsmall
  exact ⟨params, npHard_sensitivity_of_gap (by linarith) (by linarith) params hhard⟩

/-! ## Thresholding any polynomial approximation program -/

def encodeRational (t : ℚ) : RatData := (t.num.natAbs, t.den - 1)

theorem rational_encodeRational (t : ℚ) (ht : 0 ≤ t) : rational (encodeRational t) = t := by
  have hden : t.den - 1 + 1 = t.den := Nat.sub_add_cancel t.pos
  have hdenQ : ((t.den - 1 : ℕ) : ℚ) + 1 = (t.den : ℚ) := by exact_mod_cast hden
  have hnumZ : (t.num.natAbs : ℤ) = t.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ht)
  have hnumQ : (t.num.natAbs : ℚ) = (t.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hnumZ
  change (t.num.natAbs : ℚ) / (((t.den - 1 : ℕ) : ℚ) + 1) = t
  rw [hnumQ, hdenQ]
  exact t.num_div_den

theorem rational_le_iff (q r : RatData) :
    rational q ≤ rational r ↔ q.1 * (r.2 + 1) ≤ r.1 * (q.2 + 1) := by
  unfold rational
  rw [div_le_div_iff₀ (by positivity : 0 < (q.2 : ℚ) + 1)
    (by positivity : 0 < (r.2 : ℚ) + 1)]
  exact_mod_cast Iff.rfl

def thresholdCode (q : RatData) : Code RatTy .bool :=
  .comp
    (.pair
      (.comp (.pair (.const q.1) (.comp (.pair .snd (.const 1)) .add)) .mul)
      (.comp (.pair .fst (.const (q.2 + 1))) .mul)) .le

theorem thresholdCode_correct (q r : RatData) :
    (thresholdCode q).eval r = true ↔ rational q ≤ rational r := by
  simp only [thresholdCode, Code.eval, decide_eq_true_eq, rational_le_iff]

theorem thresholdCode_polynomial (q : RatData) : (thresholdCode q).IsPoly := by
  unfold thresholdCode
  repeat first
    | apply Code.IsPoly.comp
    | apply Code.IsPoly.pair
    | exact Code.poly_const _
    | exact Code.poly_fst
    | exact Code.poly_snd
    | exact Code.poly_add
    | exact Code.poly_mul
    | exact Code.poly_le

/-- The paper's one-sided approximation convention, on every valid input. -/
def ApproximatesSensitivity (α : ℝ) (algorithm : Code TargetTy RatTy) : Prop :=
  ∀ x (h : ValidTarget x),
    targetSensitivity x h / α ≤ (rational (algorithm.eval x) : ℝ) ∧
      (rational (algorithm.eval x) : ℝ) ≤ targetSensitivity x h

def approximationDecider (t : ℚ) (algorithm : Code TargetTy RatTy) : Code TargetTy .bool :=
  .comp algorithm (thresholdCode (encodeRational t))

theorem approximationDecider_polynomial (t : ℚ) {algorithm : Code TargetTy RatTy}
    (h : algorithm.IsPoly) : (approximationDecider t algorithm).IsPoly :=
  h.comp (thresholdCode_polynomial _)

theorem approximationDecider_solves {α : ℝ} (hα : 1 ≤ α) {t : ℚ} (ht : 0 < t)
    {algorithm : Code TargetTy RatTy} (happrox : ApproximatesSensitivity α algorithm) :
    Solves (approximationDecider t algorithm) (gapSensitivity α hα t ht) := by
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  constructor
  · intro x hx
    obtain ⟨h, hyes⟩ := hx
    have ha := (happrox x h).1
    have hscore : (t : ℝ) ≤ (rational (algorithm.eval x) : ℝ) := by
      have h := (div_le_iff₀ hαpos).mp ha
      nlinarith
    apply (thresholdCode_correct _ _).mpr
    rw [rational_encodeRational t ht.le]
    exact_mod_cast hscore
  · intro x hx
    obtain ⟨h, hno⟩ := hx
    have hscore : (rational (algorithm.eval x) : ℝ) < (t : ℝ) :=
      (happrox x h).2.trans_lt hno
    apply Bool.eq_false_iff.mpr
    intro heq
    have hle := (thresholdCode_correct (encodeRational t) (algorithm.eval x)).mp heq
    rw [rational_encodeRational t ht.le] at hle
    have hleR : (t : ℝ) ≤ (rational (algorithm.eval x) : ℝ) := by exact_mod_cast hle
    exact (not_le_of_gt hscore) hleR

/-- A polynomial α-approximation, together with source gap hardness, puts
every NP language in P in the specified bit-cost model. -/
theorem approximation_implies_np_subset_p {ρ α : ℝ} (hα : 1 ≤ α) (hαρ : α < ρ)
    (params : GapParameters ρ α)
    (hhard : NPHard (gapKMeans ρ (lt_of_le_of_lt hα hαρ)))
    {algorithm : Code TargetTy RatTy} (hpoly : algorithm.IsPoly)
    (happrox : ApproximatesSensitivity α algorithm) :
    ∀ L : List Bool → Prop, InNP L → InP L := by
  intro L hL
  exact (npHard_sensitivity_of_gap hα hαρ params hhard).inP_of_solver
    (approximationDecider_polynomial params.threshold hpoly)
    (approximationDecider_solves hα params.threshold_pos happrox) hL

theorem no_polynomial_approximation {ρ α : ℝ} (hα : 1 ≤ α) (hαρ : α < ρ)
    (params : GapParameters ρ α)
    (hhard : NPHard (gapKMeans ρ (lt_of_le_of_lt hα hαρ)))
    (hseparation : ∃ L : List Bool → Prop, InNP L ∧ ¬ InP L) :
    ¬ ∃ algorithm : Code TargetTy RatTy, algorithm.IsPoly ∧ ApproximatesSensitivity α algorithm := by
  rintro ⟨algorithm, hpoly, happrox⟩
  obtain ⟨L, hL, hnot⟩ := hseparation
  exact hnot (approximation_implies_np_subset_p hα hαρ params hhard hpoly happrox L hL)

end FTC.Hardness
