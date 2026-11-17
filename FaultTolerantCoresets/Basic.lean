import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Indexed nonnegative objectives

An index denotes an individual stored entry. Equal points with equal weights can
still have different indices, and corruption and filtering act on those indices.
The main proof uses contributions directly, and therefore applies to every
nonnegative pointwise-loss objective from Section 2 of the source paper.
-/

namespace FTC

variable {I S X : Type*} [DecidableEq I]

/-- A weighted entry, with the nonnegative-weight convention of Section 2. -/
structure Entry (X : Type*) where
  point : X
  weight : ℝ
  weight_nonneg : 0 ≤ weight

/-- Weighted contribution of one separately indexed copy. -/
def contribution (loss : X → S → ℝ) (entries : I → Entry X) (i : I) (s : S) : ℝ :=
  (entries i).weight * loss (entries i).point s

theorem contribution_nonneg (loss : X → S → ℝ) (entries : I → Entry X)
    (h : ∀ x s, 0 ≤ loss x s) (i : I) (s : S) :
    0 ≤ contribution loss entries i s :=
  mul_nonneg (entries i).weight_nonneg (h _ _)

/-- Cost over the active indices, with inherited contributions. -/
def cost (c : I → S → ℝ) (Q : Finset I) (s : S) : ℝ :=
  ∑ i ∈ Q, c i s

/-- The multiplicative coreset condition, including reference costs equal to zero. -/
def IsCoreset (ε : ℝ) (reference approx : S → ℝ) : Prop :=
  ∀ s, (1 - ε) * reference s ≤ approx s ∧ approx s ≤ (1 + ε) * reference s

theorem cost_nonneg {c : I → S → ℝ} (hc : ∀ i s, 0 ≤ c i s)
    (Q : Finset I) (s : S) : 0 ≤ cost c Q s :=
  Finset.sum_nonneg fun i _ => hc i s

theorem contribution_le_cost {c : I → S → ℝ} (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} (hi : i ∈ Q) (s : S) : c i s ≤ cost c Q s :=
  Finset.single_le_sum (fun j _ => hc j s) hi

theorem cost_eq_zero_contribution {c : I → S → ℝ} (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} (hi : i ∈ Q) {s : S} (hzero : cost c Q s = 0) :
    c i s = 0 := by
  have hle := contribution_le_cost hc hi s
  rw [hzero] at hle
  exact le_antisymm hle (hc i s)

theorem cost_mono {c : I → S → ℝ} (hc : ∀ i s, 0 ≤ c i s)
    {A B : Finset I} (h : A ⊆ B) (s : S) : cost c A s ≤ cost c B s :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hc i s)

theorem cost_congr {c d : I → S → ℝ} {Q : Finset I}
    (h : ∀ i ∈ Q, ∀ s, c i s = d i s) (s : S) : cost c Q s = cost d Q s :=
  Finset.sum_congr rfl fun i hi => h i hi s

@[simp] theorem cost_empty (c : I → S → ℝ) (s : S) : cost c ∅ s = 0 := by
  simp [cost]

theorem cost_sdiff_add_inter (c : I → S → ℝ) (Q B : Finset I) (s : S) :
    cost c (Q \ B) s + cost c (Q ∩ B) s = cost c Q s := by
  unfold cost
  rw [← Finset.sum_union (Finset.disjoint_sdiff_inter Q B), Finset.sdiff_union_inter]

theorem cost_sdiff_add (c : I → S → ℝ) {Q A : Finset I} (h : A ⊆ Q) (s : S) :
    cost c (Q \ A) s + cost c A s = cost c Q s := by
  simpa [Finset.inter_eq_right.mpr h] using cost_sdiff_add_inter c Q A s

theorem cost_le_card_mul {c : I → S → ℝ} {Q : Finset I} {b : ℝ} {s : S}
    (h : ∀ i ∈ Q, c i s ≤ b) : cost c Q s ≤ (Q.card : ℝ) * b := by
  calc
    cost c Q s ≤ ∑ _i ∈ Q, b := Finset.sum_le_sum h
    _ = (Q.card : ℝ) * b := by simp

theorem cost_erase_add (c : I → S → ℝ) {Q : Finset I} {i : I}
    (hi : i ∈ Q) (s : S) : cost c (Q.erase i) s + c i s = cost c Q s := by
  exact Finset.sum_erase_add _ _ hi

end FTC
