import FaultTolerantCoresets.Counterexample.Queries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Concrete query costs in the Appendix A.1 counterexample

This file computes the reference clustering and the query witnessing the
failure of proxy filtering. All costs refer to actual two-center queries in
the metric of `Metric.lean`, with individually indexed unit-weight entries.
-/

open scoped BigOperators

namespace FTC.Counterexample

noncomputable section

/-- Two distinct original points as centers. -/
def simplexQuery {n : ℕ} (j l : Fin n) (hjl : j ≠ l) : Query n :=
  pairQuery (p j) (p l) (by simpa using hjl)

/-- The reference clustering `{a,p_j}`. -/
def referenceQuery {n : ℕ} (j : Fin n) : Query n :=
  pairQuery a (p j) (by simp)

@[simp] theorem pointLoss_simplex {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i j l : Fin n) (hjl : j ≠ l) :
    pointLoss M hM (p i) (simplexQuery j l hjl) =
      if i = j then 0 else if i = l then 0 else 1 := by
  rw [simplexQuery, pointLoss_pair]
  by_cases hij : i = j <;> by_cases hil : i = l <;>
    norm_num [graphDist, unitDistance, hij, hil, hjl, Ne.symm hjl]

@[simp] theorem pointLoss_b_simplex {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (j l : Fin n) (hjl : j ≠ l) :
    pointLoss M hM b (simplexQuery j l hjl) = M ^ 2 := by
  rw [simplexQuery, pointLoss_pair]
  simp only [graphDist_b_p, min_self]

/-- The singleton's reference-query loss is exactly `1/4`. -/
theorem pointLoss_first_reference {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (first j : Fin n) (hfirst : first.val = 0) (hj : j.val ≠ 0) :
    pointLoss M hM (p first) (referenceQuery j) = 1 / 4 := by
  have hfj : first ≠ j := by
    intro h
    exact hj (h ▸ hfirst)
  rw [referenceQuery, pointLoss_pair]
  norm_num [graphDist, firstDistance, unitDistance, hfirst, hfj]

/-- The other genuine noncenter points have unit reference-query loss. -/
theorem pointLoss_other_reference {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i j : Fin n) (hi : i.val ≠ 0) (hij : i ≠ j) :
    pointLoss M hM (p i) (referenceQuery j) = 1 := by
  rw [referenceQuery, pointLoss_pair]
  norm_num [graphDist, firstDistance, unitDistance, hi, hij]

@[simp] theorem pointLoss_center_reference {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (j : Fin n) : pointLoss M hM (p j) (referenceQuery j) = 0 := by
  rw [referenceQuery, pointLoss_pair]
  rw [graphDist_self]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)]
  exact min_eq_right (sq_nonneg _)

/-- The corruption is assigned to `p_j` and contributes `M²`. -/
@[simp] theorem pointLoss_b_reference {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (j : Fin n) : pointLoss M hM b (referenceQuery j) = M ^ 2 := by
  rw [referenceQuery, pointLoss_pair]
  change min ((M + 1 / 2) ^ 2) (M ^ 2) = M ^ 2
  apply min_eq_right
  nlinarith

theorem pointLoss_reference_le_one {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i j : Fin n) : pointLoss M hM (p i) (referenceQuery j) ≤ 1 := by
  rw [referenceQuery, pointLoss_pair]
  calc
    min _ _ ≤ graphDist M (p i) (p j) ^ 2 := min_le_right _ _
    _ ≤ 1 := by
      by_cases hij : i = j <;> norm_num [graphDist, unitDistance, hij]

/-- Exact strict nearest-center assignment for the singleton. -/
theorem reference_first_nearest {n : ℕ} (M : ℝ) (first j : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) :
    graphDist M (p first) a < graphDist M (p first) (p j) := by
  have hfj : first ≠ j := by
    intro h
    exact hj (h ▸ hfirst)
  norm_num [graphDist, firstDistance, unitDistance, hfirst, hfj]

/-- Every other original point is strictly closer to `p_j` than to `a`. -/
theorem reference_other_nearest {n : ℕ} (M : ℝ) (i j : Fin n)
    (hi : i.val ≠ 0) : graphDist M (p i) (p j) < graphDist M (p i) a := by
  have hle := unitDistance_le_one i j
  change unitDistance i j < firstDistance i
  rw [firstDistance, if_neg hi]
  linarith

/-- The corruption is strictly closer to `p_j` than to `a`. -/
theorem reference_b_nearest {n : ℕ} (M : ℝ) (j : Fin n) :
    graphDist M b (p j) < graphDist (n := n) M b a := by
  change M < M + 1 / 2
  linarith

/-- A finite sum with two exceptional indices and a common value elsewhere. -/
theorem sum_two_specials {n : ℕ} (f : Fin n → ℝ) (x y : Fin n)
    (hxy : x ≠ y) (L : ℝ)
    (hf : ∀ i, i ≠ x → i ≠ y → f i = L) :
    (∑ i : Fin n, f i) = ((n : ℝ) - 2) * L + f x + f y := by
  let R : Finset (Fin n) := (Finset.univ.erase x).erase y
  have hy : y ∈ (Finset.univ : Finset (Fin n)).erase x := by
    simp [Ne.symm hxy]
  have hcx := Finset.card_erase_add_one (Finset.mem_univ x)
  have hcy := Finset.card_erase_add_one hy
  have hcN : (R.card + 1) + 1 = n := by
    calc
      _ = (Finset.univ.erase x).card + 1 := congrArg (fun t : ℕ => t + 1) hcy
      _ = (Finset.univ : Finset (Fin n)).card := hcx
      _ = n := by simp
  have hcR' : ((R.card : ℝ) + 1) + 1 = (n : ℝ) := by exact_mod_cast hcN
  have hcR : (R.card : ℝ) = (n : ℝ) - 2 := by linarith
  have hRsum : (∑ i ∈ R, f i) = (R.card : ℝ) * L := by
    calc
      (∑ i ∈ R, f i) = ∑ _i ∈ R, L := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hf i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          (Finset.mem_erase.mp hi).1
      _ = (R.card : ℝ) * L := by simp
  have hsx := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ x)
  have hsy := Finset.sum_erase_add (Finset.univ.erase x) f hy
  change (∑ i ∈ R, f i) + f y = ∑ i ∈ Finset.univ.erase x, f i at hsy
  calc
    (∑ i : Fin n, f i) = (∑ i ∈ R, f i) + f y + f x := by linarith
    _ = ((n : ℝ) - 2) * L + f x + f y := by rw [hRsum, hcR]; ring

@[simp] theorem cleanCost_simplex {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (j l : Fin n) (hjl : j ≠ l) :
    cleanCost M hM (simplexQuery j l hjl) = (n : ℝ) - 2 := by
  have hs := sum_two_specials
    (fun i => pointLoss M hM (p i) (simplexQuery j l hjl)) j l hjl 1
    (fun i hij hil => by rw [pointLoss_simplex, if_neg hij, if_neg hil])
  simp only [cleanCost, FTC.cost, cleanContribution_apply]
  simpa only [pointLoss_simplex, if_pos rfl, if_neg (Ne.symm hjl), ite_true,
    mul_one, add_zero] using hs

/-- Replacing one unit-weight entry changes every query cost by subtracting
its original loss and adding its new loss. -/
theorem corruptCost_eq_cleanCost_sub_add {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad : Fin n) (S : Query n) :
    corruptCost M hM bad S = cleanCost M hM S -
      pointLoss M hM (p bad) S + pointLoss M hM b S := by
  have hc := FTC.cost_erase_add (cleanContribution M hM)
    (Q := (Finset.univ : Finset (Fin n))) (i := bad) (Finset.mem_univ bad) S
  have hb := FTC.cost_erase_add (corruptContribution M hM bad)
    (Q := (Finset.univ : Finset (Fin n))) (i := bad) (Finset.mem_univ bad) S
  have he : FTC.cost (corruptContribution M hM bad) (Finset.univ.erase bad) S =
      FTC.cost (cleanContribution M hM) (Finset.univ.erase bad) S := by
    apply FTC.cost_congr
    intro i hi T
    simp only [corruptContribution_apply, if_neg (Finset.mem_erase.mp hi).1,
      cleanContribution_apply]
  change FTC.cost (cleanContribution M hM) (Finset.univ.erase bad) S +
    cleanContribution M hM bad S = cleanCost M hM S at hc
  change FTC.cost (corruptContribution M hM bad) (Finset.univ.erase bad) S +
    corruptContribution M hM bad bad S = corruptCost M hM bad S at hb
  simp only [corruptContribution_apply, ite_true] at hb
  simp only [cleanContribution_apply] at hc
  rw [he] at hb
  linarith

/-- The witness query has corrupted cost `n-3+M²`. -/
theorem corruptCost_simplex {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad j l : Fin n) (hjl : j ≠ l) (hbj : bad ≠ j) (hbl : bad ≠ l) :
    corruptCost M hM bad (simplexQuery j l hjl) = (n : ℝ) - 3 + M ^ 2 := by
  rw [corruptCost_eq_cleanCost_sub_add, cleanCost_simplex, pointLoss_b_simplex,
    pointLoss_simplex, if_neg hbj, if_neg hbl]
  ring

/-- Filtering out the genuine singleton leaves cost `n-4+M²` on the witness
query, since it also had unit loss there. -/
theorem cost_erase_first_simplex {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first j l : Fin n) (hjl : j ≠ l)
    (hbj : bad ≠ j) (hbl : bad ≠ l) (hfb : first ≠ bad)
    (hfj : first ≠ j) (hfl : first ≠ l) :
    FTC.cost (corruptContribution M hM bad) (Finset.univ.erase first)
      (simplexQuery j l hjl) = (n : ℝ) - 4 + M ^ 2 := by
  have he := FTC.cost_erase_add (corruptContribution M hM bad)
    (Q := (Finset.univ : Finset (Fin n))) (i := first) (Finset.mem_univ first)
    (simplexQuery j l hjl)
  have hf : corruptContribution M hM bad first (simplexQuery j l hjl) = 1 := by
    simp only [corruptContribution_apply, if_neg hfb, pointLoss_simplex,
      if_neg hfj, if_neg hfl]
  change FTC.cost (corruptContribution M hM bad) (Finset.univ.erase first)
      (simplexQuery j l hjl) + corruptContribution M hM bad first (simplexQuery j l hjl) =
    corruptCost M hM bad (simplexQuery j l hjl) at he
  rw [hf, corruptCost_simplex M hM bad j l hjl hbj hbl] at he
  linarith

theorem cleanCost_reference {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (first j : Fin n) (hfirst : first.val = 0) (hj : j.val ≠ 0) :
    cleanCost M hM (referenceQuery j) = (n : ℝ) - 2 + 1 / 4 := by
  have hfj : first ≠ j := by intro h; exact hj (h ▸ hfirst)
  have hs := sum_two_specials (fun i => pointLoss M hM (p i) (referenceQuery j))
    first j hfj 1 (by
      intro i hif hij
      have hi : i.val ≠ 0 := by
        intro hi0
        apply hif
        apply Fin.ext
        exact hi0.trans hfirst.symm
      exact pointLoss_other_reference M hM i j hi hij)
  simp only [cleanCost, FTC.cost, cleanContribution_apply]
  simpa only [pointLoss_first_reference M hM first j hfirst hj,
    pointLoss_center_reference, mul_one, add_zero] using hs

/-- The reference clustering has exactly the cost stated in Appendix A.1. -/
theorem corruptCost_reference {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first j : Fin n) (hfirst : first.val = 0)
    (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j) :
    corruptCost M hM bad (referenceQuery j) =
      (n : ℝ) - 3 + 1 / 4 + M ^ 2 := by
  rw [corruptCost_eq_cleanCost_sub_add, cleanCost_reference M hM first j hfirst hj,
    pointLoss_other_reference M hM bad j hbad hbj, pointLoss_b_reference]
  ring

end

end FTC.Counterexample
