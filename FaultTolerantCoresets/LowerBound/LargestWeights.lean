import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Largest weights

The averaging step in Appendix A.2. The entries are indexed by an arbitrary
finite set, so equal points and equal weights remain separate entries.
-/

open scoped BigOperators

namespace FTC.LowerBound

variable {I : Type*} [DecidableEq I]

/-- A subset of `f` largest weights captures at least an `f / |s|` fraction
of the total weight. The cross-multiplied form also covers `f = 0`. -/
theorem exists_largest_weights (s : Finset I) (a : I → ℝ) (f : ℕ)
    (hf : f ≤ s.card) :
    ∃ t ⊆ s, t.card = f ∧
      (f : ℝ) * (∑ i ∈ s, a i) ≤ (s.card : ℝ) * ∑ i ∈ t, a i := by
  classical
  obtain ⟨t, ht, hmax⟩ :=
    (s.powersetCard f).exists_max_image (fun t => ∑ i ∈ t, a i)
      (Finset.powersetCard_nonempty.mpr hf)
  obtain ⟨hts, htf⟩ := Finset.mem_powersetCard.mp ht
  have horder : ∀ x ∈ t, ∀ y ∈ s \ t, a y ≤ a x := by
    intro x hx y hy
    have hys : y ∈ s := (Finset.mem_sdiff.mp hy).1
    have hyt : y ∉ t := (Finset.mem_sdiff.mp hy).2
    have hyerase : y ∉ t.erase x := by
      exact fun h => hyt (Finset.mem_of_mem_erase h)
    have hsub : insert y (t.erase x) ⊆ s := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hys
      · exact hts (Finset.mem_of_mem_erase hz)
    have hcard : (insert y (t.erase x)).card = f := by
      rw [Finset.card_insert_of_notMem hyerase, Finset.card_erase_of_mem hx]
      have : 0 < t.card := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have hle := hmax (insert y (t.erase x))
      (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
    rw [Finset.sum_insert hyerase] at hle
    have herase := Finset.sum_erase_add t a hx
    linarith
  have hcross : (t.card : ℝ) * (∑ y ∈ s \ t, a y) ≤
      ((s \ t).card : ℝ) * ∑ x ∈ t, a x := by
    calc
      (t.card : ℝ) * (∑ y ∈ s \ t, a y) =
          ∑ y ∈ s \ t, (t.card : ℝ) * a y := by rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ s \ t, ∑ x ∈ t, a x := by
        apply Finset.sum_le_sum
        intro y hy
        calc
          (t.card : ℝ) * a y = ∑ x ∈ t, a y := by simp
          _ ≤ ∑ x ∈ t, a x := Finset.sum_le_sum (fun x hx => horder x hx y hy)
      _ = ((s \ t).card : ℝ) * ∑ x ∈ t, a x := by simp
  have hsum := Finset.sum_sdiff hts (f := a)
  have hcard := Finset.card_sdiff_add_card_eq_card hts
  have hcardR : ((s \ t).card : ℝ) + (t.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast hcard
  refine ⟨t, hts, htf, ?_⟩
  rw [← htf, ← hsum, ← hcardR]
  nlinarith

/-- The precise mass-removal inequality used in the paper: if the number of
copies is less than `f / (2 ε)`, at most `f` entries remove more than a
`2 ε` fraction of their total weight. -/
theorem exists_destructive_subset (s : Finset I) (a : I → ℝ)
    (f : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hA : 0 < ∑ i ∈ s, a i)
    (hsmall : (s.card : ℝ) < (f : ℝ) / (2 * ε)) :
    ∃ t ⊆ s, t.card ≤ f ∧
      2 * ε * (∑ i ∈ s, a i) < ∑ i ∈ t, a i := by
  by_cases hsf : s.card ≤ f
  · refine ⟨s, Finset.Subset.refl s, hsf, ?_⟩
    nlinarith
  · have hfs : f ≤ s.card := by omega
    obtain ⟨t, hts, htf, hmass⟩ := exists_largest_weights s a f hfs
    have hsmall' : (s.card : ℝ) * (2 * ε) < (f : ℝ) :=
      (lt_div_iff₀ (by positivity)).mp hsmall
    have hcardpos : 0 < (s.card : ℝ) := by
      have hs : 0 < s.card := by
        by_contra h
        have : s = ∅ := Finset.card_eq_zero.mp (by omega)
        simp [this] at hA
      exact_mod_cast hs
    refine ⟨t, hts, htf.le, ?_⟩
    have hstrict := mul_lt_mul_of_pos_right hsmall' hA
    nlinarith

end FTC.LowerBound
