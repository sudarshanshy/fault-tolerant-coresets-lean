import FaultTolerantCoresets.Corruption
import FaultTolerantCoresets.Sensitivity
import FaultTolerantCoresets.Filtering

/-!
# The deterministic heart of Theorem 3.1

Only the clean coreset property and a uniform bound `δ * reference s` for
each clean entry are used. Sampling is deliberately absent from this file.
The budget condition is `f * α * δ ≤ ε`. The theorem covers arbitrary
point/weight corruptions through the entrywise wrapper at the end.
-/

namespace FTC

variable {I S X : Type*} [DecidableEq I]

/-- Equation (1) of the paper, for any state that has lost at most `f` indices. -/
theorem clean_core_bounds {c d : I → S → ℝ} {reference : S → ℝ}
    {U B Q : Finset I} {f : ℕ} {ε δ : ℝ}
    (hc : ∀ i s, 0 ≤ c i s) (hreference : ∀ s, 0 ≤ reference s)
    (hcoreset : IsCoreset ε reference (cost c U))
    (hagrees : ∀ i ∈ U, i ∉ B → ∀ s, d i s = c i s)
    (hentry : ∀ i ∈ U, ∀ s, c i s ≤ δ * reference s)
    (hQ : Q ⊆ U) (hB : B.card ≤ f) (hlost : (U \ Q).card ≤ f)
    (hδ : 0 ≤ δ) (hbudget : (f : ℝ) * δ ≤ ε) :
    ∀ s, (1 - 3 * ε) * reference s ≤ cost d (Q \ B) s ∧
      cost d (Q \ B) s ≤ (1 + ε) * reference s := by
  intro s
  let A := Q \ B
  have hAU : A ⊆ U := (Finset.sdiff_subset : Q \ B ⊆ Q).trans hQ
  have heq : cost d A s = cost c A s := by
    apply cost_congr
    intro i hi t
    have hiQ := (Finset.mem_sdiff.mp hi).1
    exact hagrees i (hQ hiQ) (Finset.mem_sdiff.mp hi).2 t
  have hcompl : U \ A ⊆ B ∪ (U \ Q) := by
    intro i hi
    obtain ⟨hiU, hiA⟩ := Finset.mem_sdiff.mp hi
    by_cases hiB : i ∈ B
    · exact Finset.mem_union_left _ hiB
    · apply Finset.mem_union_right
      apply Finset.mem_sdiff.mpr
      refine ⟨hiU, ?_⟩
      intro hiQ
      exact hiA (Finset.mem_sdiff.mpr ⟨hiQ, hiB⟩)
  have hcard : (U \ A).card ≤ 2 * f := by
    have h1 := Finset.card_le_card hcompl
    have h2 := Finset.card_union_le B (U \ Q)
    omega
  have hcardR : ((U \ A).card : ℝ) ≤ 2 * (f : ℝ) := by exact_mod_cast hcard
  have hloss : cost c (U \ A) s ≤ 2 * ε * reference s := by
    calc
      cost c (U \ A) s ≤ ((U \ A).card : ℝ) * (δ * reference s) :=
        cost_le_card_mul (fun i hi => hentry i (Finset.mem_sdiff.mp hi).1 s)
      _ ≤ (2 * (f : ℝ)) * (δ * reference s) :=
        mul_le_mul_of_nonneg_right hcardR (mul_nonneg hδ (hreference s))
      _ = 2 * ((f : ℝ) * δ) * reference s := by ring
      _ ≤ 2 * ε * reference s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 2)) (hreference s)
  have hdecomp := cost_sdiff_add c hAU s
  have hmono := cost_mono hc hAU s
  have hco := hcoreset s
  change (1 - 3 * ε) * reference s ≤ cost d A s ∧
    cost d A s ≤ (1 + ε) * reference s
  rw [heq]
  constructor <;> linarith

/-- Main deterministic filtering theorem, with the actual iterative decoder.
It includes the empty-summary and zero-fault cases. -/
theorem filtering_decoder_correct_with_rule {c d : I → S → ℝ} {reference : S → ℝ}
    {U B : Finset I} {f : ℕ} {ε δ α : ℝ}
    (hc : ∀ i s, 0 ≤ c i s) (hd : ∀ i s, 0 ≤ d i s)
    (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε reference (cost c U))
    (hB : B.card ≤ f)
    (hagrees : ∀ i ∈ U, i ∉ B → ∀ s, d i s = c i s)
    (hentry : ∀ i ∈ U, ∀ s, c i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε)
    (oracle : ApproxSensitivityOracle d α)
    (rule : SelectionRule I) (hmaximum : rule.IsMaxFor oracle.score) :
    IsCoreset (6 * ε) reference (cost d (selectionRun rule f U)) := by
  have hα0 : 0 ≤ α := by linarith
  have hf : 0 ≤ (f : ℝ) := Nat.cast_nonneg f
  have hfd : (f : ℝ) * δ ≤ ε := by
    calc
      (f : ℝ) * δ = ((f : ℝ) * δ) * 1 := by ring
      _ ≤ ((f : ℝ) * δ) * α :=
        mul_le_mul_of_nonneg_left hα (mul_nonneg hf hδ)
      _ = (f : ℝ) * α * δ := by ring
      _ ≤ ε := hbudget
  let R := selectionRun rule f U
  have hR : R ⊆ U := selectionRun_subset rule f U
  have hcleanR := clean_core_bounds hc hreference hcoreset hagrees hentry hR hB
    (selection_removed_card_le rule f U) hδ hfd
  have hlower : ∀ s, (1 - 6 * ε) * reference s ≤ cost d R s := by
    intro s
    have hmono := cost_mono hd (Finset.sdiff_subset : R \ B ⊆ R) s
    have hlow := (hcleanR s).1
    have hnonneg := hreference s
    nlinarith
  by_cases hbad : (R ∩ B).Nonempty
  · obtain ⟨t, ht, g, hg, hgB, hmax⟩ :=
      selection_good_stage_of_bad_remaining rule hmaximum U B f hB hbad
    let Q := selectionRun rule t U
    have hQ : Q ⊆ U := selectionRun_subset rule t U
    have hRQ : R ⊆ Q := selectionRun_antitone rule ht.le U
    have hcleanQ := clean_core_bounds hc hreference hcoreset hagrees hentry hQ hB
      ((selection_removed_card_le rule t U).trans ht.le) hδ hfd
    have hgood : sensitivity d Q g ≤ 2 * δ := by
      apply sensitivity_le_of_contribution_le hd hg (by positivity)
      intro s
      have hsmall : d g s ≤ δ * reference s := by
        rw [hagrees g (hQ hg) hgB s]
        exact hentry g (hQ hg) s
      have hmono := cost_mono hd (Finset.sdiff_subset : Q \ B ⊆ Q) s
      have hlow := (hcleanQ s).1
      have hhalf : (1 / 2 : ℝ) * reference s ≤ cost d Q s := by
        have hcoef : (1 / 2 : ℝ) ≤ 1 - 3 * ε := by linarith
        have := mul_le_mul_of_nonneg_right hcoef (hreference s)
        linarith
      have hscale := mul_le_mul_of_nonneg_left hhalf hδ
      nlinarith
    have hbadSensitivity : ∀ b ∈ Q, sensitivity d Q b ≤ α * (2 * δ) := by
      intro b hb
      calc
        sensitivity d Q b ≤ α * oracle.score Q b := oracle.lower Q b hb
        _ ≤ α * oracle.score Q g := mul_le_mul_of_nonneg_left (hmax b hb) hα0
        _ ≤ α * sensitivity d Q g :=
          mul_le_mul_of_nonneg_left (oracle.upper Q g hg) hα0
        _ ≤ α * (2 * δ) := mul_le_mul_of_nonneg_left hgood hα0
    have hupperQ : ∀ s, cost d Q s ≤ (1 + 6 * ε) * reference s := by
      intro s
      have hcost0 := cost_nonneg hd Q s
      have hbadpart : cost d (Q ∩ B) s ≤ 2 * ε * cost d Q s := by
        have hcard : ((Q ∩ B).card : ℝ) ≤ (f : ℝ) := by
          exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right : Q ∩ B ⊆ B)).trans hB
        calc
          cost d (Q ∩ B) s ≤ ((Q ∩ B).card : ℝ) * ((α * (2 * δ)) * cost d Q s) := by
            apply cost_le_card_mul
            intro b hb
            have hbQ := (Finset.mem_inter.mp hb).1
            exact (contribution_le_sensitivity_mul_cost hd hbQ s).trans
              (mul_le_mul_of_nonneg_right (hbadSensitivity b hbQ) hcost0)
          _ ≤ (f : ℝ) * ((α * (2 * δ)) * cost d Q s) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = (2 * ((f : ℝ) * α * δ)) * cost d Q s := by ring
          _ ≤ 2 * ε * cost d Q s :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 2)) hcost0
      have hdecomp := cost_sdiff_add_inter d Q B s
      have hcleanupper := (hcleanQ s).2
      have htotal : (1 - 2 * ε) * cost d Q s ≤ (1 + ε) * reference s := by
        nlinarith
      have hcoef : 1 + ε ≤ (1 - 2 * ε) * (1 + 6 * ε) := by
        have : 0 ≤ ε * (1 - 4 * ε) := mul_nonneg hε (by linarith)
        nlinarith
      have hscale := mul_le_mul_of_nonneg_right hcoef (hreference s)
      have hden : 0 < 1 - 2 * ε := by linarith
      have hscaled : (1 - 2 * ε) * cost d Q s ≤
          (1 - 2 * ε) * ((1 + 6 * ε) * reference s) := by
        calc
          (1 - 2 * ε) * cost d Q s ≤ (1 + ε) * reference s := htotal
          _ ≤ (1 - 2 * ε) * ((1 + 6 * ε) * reference s) := by nlinarith [hscale]
      exact le_of_mul_le_mul_left hscaled hden
    intro s
    exact ⟨hlower s, (cost_mono hd hRQ s).trans (hupperQ s)⟩
  · have hbadEmpty : R ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hbad
    intro s
    refine ⟨hlower s, ?_⟩
    have hdecomp := cost_sdiff_add_inter d R B s
    have hcleanupper := (hcleanR s).2
    have hzero : cost d (R ∩ B) s = 0 := by simp [hbadEmpty]
    have hnonneg := hreference s
    nlinarith


/-- The original real-score decoder is a specialization of the selection-rule theorem. -/
theorem filtering_decoder_correct {c d : I → S → ℝ} {reference : S → ℝ}
    {U B : Finset I} {f : ℕ} {ε δ α : ℝ}
    (hc : ∀ i s, 0 ≤ c i s) (hd : ∀ i s, 0 ≤ d i s)
    (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε reference (cost c U))
    (hB : B.card ≤ f)
    (hagrees : ∀ i ∈ U, i ∉ B → ∀ s, d i s = c i s)
    (hentry : ∀ i ∈ U, ∀ s, c i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε)
    (oracle : ApproxSensitivityOracle d α) :
    IsCoreset (6 * ε) reference (cost d (peel oracle.score f U)) := by
  rw [peel_eq_selectionRun]
  exact filtering_decoder_correct_with_rule hc hd hreference hε hεsmall hδ hα
    hcoreset hB hagrees hentry hbudget oracle (classicalSelectionRule oracle.score)
    (classicalSelectionRule_isMaxFor oracle.score)

/-- Entry-level form: the decoder only uses the corrupted summary and the
approximate-sensitivity oracle for that summary. -/
theorem filtering_decoder_correct_of_corruption
    (loss : X → S → ℝ) (hloss : ∀ x s, 0 ≤ loss x s)
    (reference : S → ℝ) (hreference : ∀ s, 0 ≤ reference s)
    (U : Finset I) (entries corrupted : I → Entry X) {f : ℕ} {ε δ α : ℝ}
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε reference (cost (contribution loss entries) U))
    (hcorrupt : IsFCorruption f U entries corrupted)
    (hentry : ∀ i ∈ U, ∀ s, contribution loss entries i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε)
    (oracle : ApproxSensitivityOracle (contribution loss corrupted) α) :
    IsCoreset (6 * ε) reference
      (cost (contribution loss corrupted) (peel oracle.score f U)) := by
  obtain ⟨B, _, hB, hagrees⟩ := hcorrupt
  apply filtering_decoder_correct
    (contribution_nonneg loss entries hloss) (contribution_nonneg loss corrupted hloss)
    hreference hε hεsmall hδ hα hcoreset hB ?_ hentry hbudget oracle
  intro i hi hiB s
  simp only [contribution, hagrees i hi hiB]

end FTC
