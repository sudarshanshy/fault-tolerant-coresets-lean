import FaultTolerantCoresets.Hardness.SensitivityFormula
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Theorem 4.2: the gap-preserving reduction

For every pair of real constants `1 ≤ α < ρ`, choose an integer `c > 0` and
a *rational* threshold `t` once, independently of the input. Set
`L = c * D² / B`. Then `OPT ≤ B` implies `α*t ≤ σ(p⋆)`, while
`ρ*B < OPT` implies `σ(p⋆) < t`. Thus any admissible α-approximation
decides the original promised gap with one call and one comparison.

Using integer c and rational t also handles non-rational approximation factors
without treating an arbitrary real number as part of an executable input.
-/

namespace FTC.Hardness

open FTC.FiniteMetric

/-- Constants of the reduction, chosen once for the two approximation factors. -/
structure GapParameters (ρ α : ℝ) where
  copies : ℕ
  copies_pos : 0 < copies
  threshold : ℚ
  threshold_pos : 0 < threshold
  no_lt : 1 / (1 + (copies : ℝ) * ρ) < (threshold : ℝ)
  yes_le : (threshold : ℝ) ≤ 1 / (α * (1 + (copies : ℝ)))

/-- Explicit integer amplification and rational separation exist for every
constant slack, including irrational approximation factors. -/
theorem gapParameters_nonempty {ρ α : ℝ} (hα : 1 ≤ α) (hαρ : α < ρ) :
    Nonempty (GapParameters ρ α) := by
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hρpos : 0 < ρ := hαpos.trans hαρ
  have hgap : 0 < ρ - α := sub_pos.mpr hαρ
  obtain ⟨c, hc⟩ := exists_nat_gt (ρ / (ρ - α))
  have hcposR : 0 < (c : ℝ) := (div_pos hρpos hgap).trans hc
  have hcpos : 0 < c := by exact_mod_cast hcposR
  have hlarge : ρ < (c : ℝ) * (ρ - α) := (div_lt_iff₀ hgap).mp hc
  have hsep : α * (1 + (c : ℝ)) < 1 + (c : ℝ) * ρ := by nlinarith
  have hleft : 0 < 1 + (c : ℝ) * ρ := by positivity
  have hright : 0 < α * (1 + (c : ℝ)) := by positivity
  have hinv : 1 / (1 + (c : ℝ) * ρ) < 1 / (α * (1 + (c : ℝ))) := by
    exact (div_lt_div_iff₀ hleft hright).mpr (by simpa using hsep)
  obtain ⟨t, htleft, htright⟩ := exists_rat_btwn hinv
  have htpos : 0 < t := by
    exact_mod_cast (div_pos zero_lt_one hleft).trans htleft
  exact ⟨⟨c, hcpos, t, htpos, htleft, htright.le⟩⟩

/-- A concrete weight, using only the input threshold and a diameter bound. -/
noncomputable def amplification (c : ℕ) (D B : ℝ) : ℝ := (c : ℝ) * D ^ 2 / B

theorem amplification_pos {c : ℕ} (hc : 0 < c) {D B : ℝ}
    (hD : 0 < D) (hB : 0 < B) : 0 < amplification c D B := by
  unfold amplification
  positivity

variable {X : Type*} [DecidableEq X] [Fintype X] [MetricSpace X] {k : ℕ}

/-- The radius cancels out under the chosen amplification. -/
theorem amplified_sensitivity_formula (P : Finset X) (hk : 0 < k)
    (hkX : k ≤ Fintype.card X) {D B : ℝ} (hD : 0 < D) (hB : 0 < B)
    {c : ℕ} (hc : 0 < c) :
    sensitivity (gadgetContribution (k := k) D (amplification c D B))
      (extendedClients P) none = B / (B + (c : ℝ) * optimum P hk hkX) := by
  have hL := amplification_pos hc hD hB
  have hopt := optimum_nonneg P hk hkX
  have hcR : 0 ≤ (c : ℝ) := Nat.cast_nonneg c
  have hden : 0 < D ^ 2 + amplification c D B * optimum P hk hkX := by positivity
  have hden' : 0 < B + (c : ℝ) * optimum P hk hkX := by positivity
  rw [sensitivity_formula P hk hkX D hD hL.le]
  apply (div_eq_div_iff hden.ne' hden'.ne').mpr
  unfold amplification
  field_simp

/-- YES instances land above the α-times-threshold side of the target gap. -/
theorem sensitivity_yes (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X)
    {ρ α D B : ℝ} (params : GapParameters ρ α) (hα : 1 ≤ α)
    (hD : 0 < D) (hB : 0 < B) (hyes : optimum P hk hkX ≤ B) :
    α * (params.threshold : ℝ) ≤
      sensitivity (gadgetContribution (k := k) D (amplification params.copies D B))
        (extendedClients P) none := by
  rw [amplified_sensitivity_formula P hk hkX hD hB params.copies_pos]
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hc : 0 ≤ (params.copies : ℝ) := Nat.cast_nonneg _
  have hc1 : 0 < 1 + (params.copies : ℝ) := by positivity
  have hden : 0 < B + (params.copies : ℝ) * optimum P hk hkX :=
    add_pos_of_pos_of_nonneg hB (mul_nonneg hc (optimum_nonneg P hk hkX))
  have hsmall : α * (params.threshold : ℝ) ≤ 1 / (1 + (params.copies : ℝ)) := by
    apply (le_div_iff₀ hc1).mpr
    have h := (le_div_iff₀ (mul_pos hαpos hc1)).mp params.yes_le
    nlinarith
  apply hsmall.trans
  apply (div_le_div_iff₀ hc1 hden).mpr
  have h := mul_le_mul_of_nonneg_left hyes hc
  nlinarith

/-- NO instances land strictly below the rational threshold. -/
theorem sensitivity_no (P : Finset X) (hk : 0 < k) (hkX : k ≤ Fintype.card X)
    {ρ α D B : ℝ} (params : GapParameters ρ α) (hα : 1 ≤ α) (hαρ : α < ρ)
    (hD : 0 < D) (hB : 0 < B) (hno : ρ * B < optimum P hk hkX) :
    sensitivity (gadgetContribution (k := k) D (amplification params.copies D B))
      (extendedClients P) none < (params.threshold : ℝ) := by
  rw [amplified_sensitivity_formula P hk hkX hD hB params.copies_pos]
  have hρ : 0 < ρ := (lt_of_lt_of_le zero_lt_one hα).trans hαρ
  have hc : 0 < (params.copies : ℝ) := by exact_mod_cast params.copies_pos
  have hden : 0 < B + (params.copies : ℝ) * optimum P hk hkX :=
    add_pos_of_pos_of_nonneg hB (mul_nonneg hc.le (optimum_nonneg P hk hkX))
  have hden' : 0 < 1 + (params.copies : ℝ) * ρ := by positivity
  apply lt_trans _ params.no_lt
  apply (div_lt_div_iff₀ hden hden').mpr
  have h := mul_lt_mul_of_pos_left hno hc
  nlinarith

/-- A single approximate sensitivity value decides the promised gap instance.
The bound is the approximation convention used throughout the paper:
`σ / α ≤ score ≤ σ`. -/
theorem gap_decision_of_approximation (P : Finset X) (hk : 0 < k)
    (hkX : k ≤ Fintype.card X) {ρ α D B score : ℝ}
    (params : GapParameters ρ α) (hα : 1 ≤ α) (hαρ : α < ρ)
    (hD : 0 < D) (hB : 0 < B)
    (hpromise : optimum P hk hkX ≤ B ∨ ρ * B < optimum P hk hkX)
    (hlower : sensitivity
      (gadgetContribution (k := k) D (amplification params.copies D B))
      (extendedClients P) none / α ≤ score)
    (hupper : score ≤ sensitivity
      (gadgetContribution (k := k) D (amplification params.copies D B))
      (extendedClients P) none) :
    (params.threshold : ℝ) ≤ score ↔ optimum P hk hkX ≤ B := by
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  constructor
  · intro ht
    rcases hpromise with hy | hn
    · exact hy
    · have hbad := sensitivity_no P hk hkX params hα hαρ hD hB hn
      exact False.elim ((not_le_of_gt hbad) (ht.trans hupper))
  · intro hy
    have hgood := sensitivity_yes P hk hkX params hα hD hB hy
    have h := (div_le_iff₀ hαpos).mp hlower
    nlinarith

/-- The parameters in Theorem 4.2 satisfy the more general reduction above. -/
theorem paper_gapParameters_nonempty {ρ δ : ℝ} (hρ : 1 < ρ)
    (hδ : 0 < δ) (hδsmall : δ < ρ - 1) :
    Nonempty (GapParameters ρ (ρ - δ)) :=
  gapParameters_nonempty (by linarith) (by linarith)

end FTC.Hardness
