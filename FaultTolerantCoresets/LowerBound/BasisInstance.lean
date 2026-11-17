import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum

/-!
# The Euclidean basis instance for the filtering lower bound

This file realizes the separating queries in Claim A.2 of the source paper.
The input consists of the `k` distinct standard basis vectors of `ℝ^k`.
All summaries are indexed, so repeated copies of a basis vector remain distinct.
-/

open scoped BigOperators

namespace FTC.LowerBound

abbrev BasisSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The standard basis vector `e_i`. -/
noncomputable def basisPoint {k : ℕ} (i : Fin k) : BasisSpace k :=
  EuclideanSpace.single i 1

@[simp] theorem basisPoint_apply {k : ℕ} (i j : Fin k) :
    basisPoint i j = if j = i then 1 else 0 := by
  simp [basisPoint, PiLp.single_apply]

@[simp] theorem basisPoint_ne_zero {k : ℕ} (i : Fin k) : basisPoint i ≠ 0 := by
  simp [basisPoint]

theorem basisPoint_injective {k : ℕ} : Function.Injective (@basisPoint k) := by
  intro i j h
  have h' := congrArg (fun x : BasisSpace k => x i) h
  by_contra hij
  simpa [basisPoint_apply, hij, Ne.symm hij] using h'

@[simp] theorem norm_basisPoint {k : ℕ} (i : Fin k) : ‖basisPoint i‖ = 1 := by
  simp [basisPoint]

@[simp] theorem dist_basisPoint_zero_sq {k : ℕ} (i : Fin k) :
    dist (basisPoint i) 0 ^ 2 = 1 := by
  simp

theorem dist_basisPoint_sq_of_ne {k : ℕ} {i j : Fin k} (h : i ≠ j) :
    dist (basisPoint i) (basisPoint j) ^ 2 = 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  norm_num [basisPoint, EuclideanSpace.inner_single_left, h]

/-- A genuine `k`-point Euclidean center set. -/
structure EuclideanQuery (k : ℕ) where
  centers : Finset (BasisSpace k)
  card_centers : centers.card = k
  nonempty : centers.Nonempty

/-- Squared distance to the closest center, the Euclidean `k`-means loss. -/
noncomputable def sqDistToCenters {k : ℕ} (x : BasisSpace k) (S : EuclideanQuery k) : ℝ := by
  classical
  exact S.centers.inf' S.nonempty (fun y => dist x y ^ 2)

theorem sqDistToCenters_nonneg {k : ℕ} (x : BasisSpace k) (S : EuclideanQuery k) :
    0 ≤ sqDistToCenters x S := by
  classical
  apply Finset.le_inf'
  intro y _
  exact sq_nonneg _

/-- The query `{e_j : j ≠ i} ∪ {0}` used in Claim A.2. -/
noncomputable def witnessCenters {k : ℕ} (i : Fin k) : Finset (BasisSpace k) := by
  classical
  exact insert 0 ((Finset.univ.erase i).image basisPoint)

@[simp] theorem zero_mem_witnessCenters {k : ℕ} (i : Fin k) :
    (0 : BasisSpace k) ∈ witnessCenters i := by
  classical
  simp [witnessCenters]

@[simp] theorem mem_witnessCenters {k : ℕ} (i : Fin k) (x : BasisSpace k) :
    x ∈ witnessCenters i ↔ x = 0 ∨ ∃ j : Fin k, j ≠ i ∧ basisPoint j = x := by
  classical
  simp [witnessCenters, Finset.mem_image]

@[simp] theorem card_witnessCenters {k : ℕ} (i : Fin k) :
    (witnessCenters i).card = k := by
  classical
  have hz : (0 : BasisSpace k) ∉ (Finset.univ.erase i).image basisPoint := by
    simp [Finset.mem_image]
  rw [witnessCenters, Finset.card_insert_of_notMem hz,
    Finset.card_image_of_injective _ basisPoint_injective]
  simpa using Finset.card_erase_add_one (Finset.mem_univ i)

noncomputable def witnessQuery {k : ℕ} (i : Fin k) : EuclideanQuery k where
  centers := witnessCenters i
  card_centers := card_witnessCenters i
  nonempty := ⟨0, zero_mem_witnessCenters i⟩

/-- The separating query charges exactly one unit at its omitted basis vector. -/
theorem loss_witnessQuery_same {k : ℕ} (i : Fin k) :
    sqDistToCenters (basisPoint i) (witnessQuery i) = 1 := by
  classical
  apply le_antisymm
  · exact (Finset.inf'_le (fun y : BasisSpace k => dist (basisPoint i) y ^ 2)
      (zero_mem_witnessCenters i)).trans_eq (dist_basisPoint_zero_sq i)
  · apply Finset.le_inf'
    intro y hy
    rcases (mem_witnessCenters i y).1 hy with rfl | ⟨j, hji, rfl⟩
    · simp
    · rw [dist_basisPoint_sq_of_ne (Ne.symm hji)]
      norm_num

/-- Every other basis vector is itself a center and has zero loss. -/
theorem loss_witnessQuery_other {k : ℕ} {i j : Fin k} (hji : j ≠ i) :
    sqDistToCenters (basisPoint j) (witnessQuery i) = 0 := by
  classical
  apply le_antisymm
  · have hmem : basisPoint j ∈ witnessCenters i :=
      (mem_witnessCenters i (basisPoint j)).2 (Or.inr ⟨j, hji, rfl⟩)
    change (witnessCenters i).inf' _ (fun y => dist (basisPoint j) y ^ 2) ≤ 0
    calc
      _ ≤ dist (basisPoint j) (basisPoint j) ^ 2 := Finset.inf'_le _ hmem
      _ = 0 := by simp
  · apply Finset.le_inf'
    intro y _
    exact sq_nonneg _

theorem loss_witnessQuery {k : ℕ} (i j : Fin k) :
    sqDistToCenters (basisPoint j) (witnessQuery i) = if j = i then 1 else 0 := by
  split_ifs with h
  · subst j
    exact loss_witnessQuery_same i
  · exact loss_witnessQuery_other h

/-- Unweighted cost of the basis input `P = {e_1, …, e_k}`. -/
noncomputable def basisReferenceCost {k : ℕ} (S : EuclideanQuery k) : ℝ :=
  ∑ j : Fin k, sqDistToCenters (basisPoint j) S

/-- Cost of a separately indexed weighted summary supported on the basis input. -/
noncomputable def supportedCost {I : Type*} [DecidableEq I] {k : ℕ}
    (Q : Finset I) (loc : I → Fin k) (a : I → ℝ) (S : EuclideanQuery k) : ℝ :=
  ∑ j ∈ Q, a j * sqDistToCenters (basisPoint (loc j)) S

@[simp] theorem basisReferenceCost_witness {k : ℕ} (i : Fin k) :
    basisReferenceCost (witnessQuery i) = 1 := by
  simp [basisReferenceCost, loss_witnessQuery]

/-- The witness query reads exactly the total weight at its omitted coordinate. -/
@[simp] theorem supportedCost_witness {I : Type*} [DecidableEq I] {k : ℕ}
    (Q : Finset I) (loc : I → Fin k) (a : I → ℝ) (i : Fin k) :
    supportedCost Q loc a (witnessQuery i) =
      ∑ j ∈ Q.filter (fun j => loc j = i), a j := by
  classical
  simp [supportedCost, loss_witnessQuery, Finset.sum_filter, mul_ite]

/-- Claim A.2: any Euclidean `k`-means coreset supported on the basis input
approximately preserves the total weight at each coordinate. -/
theorem weight_preservation {I : Type*} [DecidableEq I] {k : ℕ}
    {ε : ℝ} (Q : Finset I) (loc : I → Fin k) (a : I → ℝ)
    (h : ∀ S : EuclideanQuery k,
      (1 - ε) * basisReferenceCost S ≤ supportedCost Q loc a S ∧
      supportedCost Q loc a S ≤ (1 + ε) * basisReferenceCost S) (i : Fin k) :
    1 - ε ≤ ∑ j ∈ Q.filter (fun j => loc j = i), a j ∧
      (∑ j ∈ Q.filter (fun j => loc j = i), a j) ≤ 1 + ε := by
  simpa only [basisReferenceCost_witness, supportedCost_witness, mul_one]
    using h (witnessQuery i)

end FTC.LowerBound
