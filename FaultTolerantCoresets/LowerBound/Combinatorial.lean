import FaultTolerantCoresets.LowerBound.LargestWeights

/-!
# The quantitative counting obstruction

This file isolates the finite combinatorics of Theorem 3.4. Each stored copy has
an index, a bin (the basis vector it represents), and a nonnegative weight.
An adversary sets at most `f` separately indexed weights to zero. A decoder may
then only select active indices with their inherited weights.
-/

open scoped BigOperators

namespace FTC.LowerBound

variable {I : Type*} [DecidableEq I] {k : ℕ}

/-- Total weight at one coordinate, counting separately indexed copies. -/
def coordinateWeight (Q : Finset I) (a : I → ℝ) (loc : I → Fin k)
    (i : Fin k) : ℝ :=
  ∑ j ∈ Q.filter (fun j => loc j = i), a j

/-- Corrupt exactly the indices in `J` by replacing their weight by zero. -/
def zeroWeights (a : I → ℝ) (J : Finset I) (j : I) : ℝ :=
  if j ∈ J then 0 else a j

@[simp] theorem zeroWeights_of_mem (a : I → ℝ) {J : Finset I} {j : I}
    (hj : j ∈ J) : zeroWeights a J j = 0 := by simp [zeroWeights, hj]

@[simp] theorem zeroWeights_of_notMem (a : I → ℝ) {J : Finset I} {j : I}
    (hj : j ∉ J) : zeroWeights a J j = a j := by simp [zeroWeights, hj]

theorem zeroWeights_nonneg {a : I → ℝ} (ha : ∀ j, 0 ≤ a j)
    (J : Finset I) (j : I) : 0 ≤ zeroWeights a J j := by
  unfold zeroWeights
  split_ifs
  · exact le_rfl
  · exact ha j

theorem coordinateWeight_mono {Q R : Finset I} {a : I → ℝ}
    (ha : ∀ j, 0 ≤ a j) (loc : I → Fin k) (i : Fin k) (hRQ : R ⊆ Q) :
    coordinateWeight R a loc i ≤ coordinateWeight Q a loc i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ hRQ
  · intro j _ _
    exact ha j

/-- The weights outside the corrupted set are unchanged. -/
theorem coordinateWeight_zeroWeights (Q : Finset I) (a : I → ℝ)
    (loc : I → Fin k) (i : Fin k) {J : Finset I}
    (hJ : J ⊆ Q.filter (fun j => loc j = i)) :
    coordinateWeight Q (zeroWeights a J) loc i =
      coordinateWeight Q a loc i - ∑ j ∈ J, a j := by
  classical
  have hz : (∑ j ∈ J, zeroWeights a J j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact zeroWeights_of_mem a hj
  have hpart := Finset.sum_sdiff hJ (f := zeroWeights a J)
  have hpartA := Finset.sum_sdiff hJ (f := a)
  unfold coordinateWeight
  calc
    (∑ j ∈ Q.filter (fun j => loc j = i), zeroWeights a J j) =
        ∑ j ∈ (Q.filter (fun j => loc j = i)) \ J, a j := by
      rw [← hpart, hz, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      exact zeroWeights_of_notMem a (Finset.mem_sdiff.mp hj).2
    _ = (∑ j ∈ Q.filter (fun j => loc j = i), a j) - ∑ j ∈ J, a j := by
      linarith

/-- If the total number of copies is below `f*k/(2 ε)`, some bin is below
`f/(2 ε)`. This includes the empty-bin case. -/
theorem exists_small_bin (Q : Finset I) (loc : I → Fin k)
    (f : ℕ) (ε : ℝ) (_hε : 0 < ε)
    (hsmall : (Q.card : ℝ) < (f : ℝ) * k / (2 * ε)) :
    ∃ i : Fin k, ((Q.filter (fun j => loc j = i)).card : ℝ) <
      (f : ℝ) / (2 * ε) := by
  classical
  by_contra! h
  have hcount : (∑ i : Fin k, (Q.filter (fun j => loc j = i)).card) = Q.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter Q Finset.univ loc
  have hcountR : (∑ i : Fin k, ((Q.filter (fun j => loc j = i)).card : ℝ)) =
      (Q.card : ℝ) := by exact_mod_cast hcount
  have hle := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (f := fun _ => (f : ℝ) / (2 * ε))
    (g := fun i => ((Q.filter (fun j => loc j = i)).card : ℝ))
    (fun i _ => h i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  rw [hcountR] at hle
  have heq : (k : ℝ) * ((f : ℝ) / (2 * ε)) =
      (f : ℝ) * k / (2 * ε) := by ring
  linarith

/-- Quantitative form of the lower bound. The robustness assumption only asks
for the necessary coordinate lower bounds after zeroing corruptions; it is
therefore weaker than successful filtering into an ε-coreset. -/
theorem quantitative_filtering_lower_bound
    (Q : Finset I) (a : I → ℝ) (loc : I → Fin k)
    (ha : ∀ j, 0 ≤ a j) (f : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hclean : ∀ i : Fin k,
      1 - ε ≤ coordinateWeight Q a loc i ∧ coordinateWeight Q a loc i ≤ 1 + ε)
    (hrobust : ∀ J ⊆ Q, J.card ≤ f →
      ∃ R ⊆ Q, ∀ i : Fin k,
        1 - ε ≤ coordinateWeight R (zeroWeights a J) loc i) :
    (f : ℝ) * k / (2 * ε) ≤ (Q.card : ℝ) := by
  classical
  by_contra! hsmall
  obtain ⟨i, hi⟩ := exists_small_bin Q loc f ε hε hsmall
  have hA : 0 < coordinateWeight Q a loc i := by
    have := (hclean i).1
    linarith
  obtain ⟨J, hJ, hJf, hmass⟩ :=
    exists_destructive_subset (Q.filter (fun j => loc j = i)) a f ε hε hεhalf hA hi
  have hJQ : J ⊆ Q := fun j hj => (Finset.mem_filter.mp (hJ hj)).1
  obtain ⟨R, hRQ, hR⟩ := hrobust J hJQ hJf
  have hmono := coordinateWeight_mono (zeroWeights_nonneg ha J) loc i hRQ
  have hzero := coordinateWeight_zeroWeights Q a loc i hJ
  have hAupper := (hclean i).2
  have hRlower := hR i
  have hstrict : coordinateWeight Q (zeroWeights a J) loc i <
      (1 - 2 * ε) * coordinateWeight Q a loc i := by
    rw [hzero]
    change 2 * ε * coordinateWeight Q a loc i < _ at hmass
    linarith
  have hproduct : (1 - 2 * ε) * coordinateWeight Q a loc i ≤
      (1 - 2 * ε) * (1 + ε) := by
    apply mul_le_mul_of_nonneg_left hAupper
    linarith
  nlinarith [sq_pos_of_pos hε]

end FTC.LowerBound
