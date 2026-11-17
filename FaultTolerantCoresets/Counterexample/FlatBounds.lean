import FaultTolerantCoresets.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Costs with at most two exceptional entries

For the metric construction in Appendix A.1, every two-center query has a
common loss level. At most two genuine entries have a smaller loss. These
finite-sum lemmas turn that observation into the sensitivity bounds.
-/

open scoped BigOperators

namespace FTC.Counterexample

variable {I : Type*} [DecidableEq I]

/-- If all entries outside `E` have common nonnegative loss `L`, the total
cost contains at least `(|Q| - |E|) L`. -/
theorem sum_lower_bound_of_flat
    (Q E : Finset I) (c : I → ℝ) (L : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hL : 0 ≤ L)
    (hflat : ∀ i ∈ Q \ E, c i = L) :
    ((Q.card : ℝ) - (E.card : ℝ)) * L ≤ ∑ i ∈ Q, c i := by
  have hcard : (Q.card : ℝ) - (E.card : ℝ) ≤ ((Q \ E).card : ℝ) := by
    have h := Finset.card_le_card_sdiff_add_card (s := Q) (t := E)
    have hr : (Q.card : ℝ) ≤ ((Q \ E).card : ℝ) + (E.card : ℝ) := by
      exact_mod_cast h
    linarith
  calc
    ((Q.card : ℝ) - (E.card : ℝ)) * L ≤ ((Q \ E).card : ℝ) * L :=
      mul_le_mul_of_nonneg_right hcard hL
    _ = ∑ i ∈ Q \ E, c i := by
      rw [Finset.sum_congr rfl hflat]
      simp
    _ ≤ ∑ i ∈ Q, c i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hc i)

/-- At most two exceptions give a uniform contribution bound for every
entry below the common level. The total may include additional bad entries. -/
theorem contribution_mul_card_sub_two_le
    (Q E : Finset I) (c : I → ℝ) (L : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hL : 0 ≤ L)
    (hflat : ∀ i ∈ Q \ E, c i = L) (hE : E.card ≤ 2)
    (hQ : 2 ≤ Q.card) {i : I} (hi : c i ≤ L) :
    ((Q.card : ℝ) - 2) * c i ≤ ∑ j ∈ Q, c j := by
  have hq : 0 ≤ (Q.card : ℝ) - 2 := by
    have h : (2 : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hQ
    linarith
  have he : (E.card : ℝ) ≤ 2 := by exact_mod_cast hE
  calc
    ((Q.card : ℝ) - 2) * c i ≤ ((Q.card : ℝ) - 2) * L :=
      mul_le_mul_of_nonneg_left hi hq
    _ ≤ ((Q.card : ℝ) - (E.card : ℝ)) * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL
    _ ≤ ∑ j ∈ Q, c j := sum_lower_bound_of_flat Q E c L hc hL hflat

/-- At most two entries can receive an exceptional label from two centers. -/
theorem card_biUnion_le_two {X : Type*} [DecidableEq X]
    (C : Finset X) (exceptional : X → Finset I)
    (hC : C.card = 2) (hex : ∀ x, (exceptional x).card ≤ 1) :
    (C.biUnion exceptional).card ≤ 2 := by
  calc
    (C.biUnion exceptional).card ≤ ∑ x ∈ C, (exceptional x).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ C, 1 := Finset.sum_le_sum (fun x _ => hex x)
    _ = 2 := by simp [hC]

end FTC.Counterexample
