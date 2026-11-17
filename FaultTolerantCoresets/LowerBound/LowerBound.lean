import FaultTolerantCoresets.Corruption
import FaultTolerantCoresets.LowerBound.Combinatorial
import FaultTolerantCoresets.LowerBound.BasisInstance

/-!
# Theorem 3.4: quantitative Euclidean filtering lower bound

The deterministic successful realization of any fault-tolerant construction must
have at least `f*k/(2 ε)` separately indexed entries. The corruption witness only
sets selected weights to zero; it is admissible in the paper's more general
model allowing arbitrary changes of both locations and nonnegative weights.
-/

namespace FTC.LowerBound

variable {I : Type*} [DecidableEq I] {k : ℕ}

/-- Entries supported on the basis input; distinct indices may represent the
same basis vector. -/
noncomputable def basisEntries (loc : I → Fin k) (a : I → ℝ)
    (ha : ∀ j, 0 ≤ a j) (j : I) : FTC.Entry (BasisSpace k) where
  point := basisPoint (loc j)
  weight := a j
  weight_nonneg := ha j

/-- The explicit quantitative bound established by the proof of Theorem 3.4.
It holds for each successful coreset realization, independent of any
randomization used in constructing that realization. -/
theorem theorem_3_4
    (Q : Finset I) (loc : I → Fin k) (a : I → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (decoder : (I → FTC.Entry (BasisSpace k)) → Finset I)
    (f : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFT : FTC.IsFilteringFaultTolerant ε f basisReferenceCost
      (@sqDistToCenters k) Q (basisEntries loc a ha) decoder) :
    (f : ℝ) * k / (2 * ε) ≤ (Q.card : ℝ) := by
  classical
  apply quantitative_filtering_lower_bound Q a loc ha f ε hε hεhalf
  · intro i
    have hclean : ∀ S : EuclideanQuery k,
        (1 - ε) * basisReferenceCost S ≤ supportedCost Q loc a S ∧
        supportedCost Q loc a S ≤ (1 + ε) * basisReferenceCost S := by
      simpa only [FTC.IsCoreset, FTC.cost, FTC.contribution, basisEntries,
        supportedCost] using hFT.1
    exact weight_preservation Q loc a hclean i
  · intro J hJ hJf
    let corrupted := basisEntries loc (zeroWeights a J) (zeroWeights_nonneg ha J)
    have hcorrupt : FTC.IsFCorruption f Q (basisEntries loc a ha) corrupted := by
      refine ⟨J, hJ, hJf, ?_⟩
      intro j _ hjJ
      simp [corrupted, basisEntries, zeroWeights, hjJ]
    obtain ⟨hsub, hco⟩ := hFT.2 corrupted hcorrupt
    refine ⟨decoder corrupted, hsub, ?_⟩
    intro i
    have hcorrect : ∀ S : EuclideanQuery k,
        (1 - ε) * basisReferenceCost S ≤
          supportedCost (decoder corrupted) loc (zeroWeights a J) S ∧
        supportedCost (decoder corrupted) loc (zeroWeights a J) S ≤
          (1 + ε) * basisReferenceCost S := by
      simpa only [FTC.IsCoreset, FTC.cost, FTC.contribution, corrupted,
        basisEntries, supportedCost] using hco
    exact (weight_preservation (decoder corrupted) loc (zeroWeights a J) hcorrect i).1

end FTC.LowerBound

namespace FTC.LowerBound

/-- The same bound for arbitrary stored entries whose active locations are
basis vectors, without requiring a canonical representation outside `Q`. -/
theorem theorem_3_4_of_supported
    {I : Type*} [DecidableEq I] {k : ℕ}
    (Q : Finset I) (entries : I → FTC.Entry (BasisSpace k))
    (loc : I → Fin k)
    (hsupport : ∀ j ∈ Q, (entries j).point = basisPoint (loc j))
    (decoder : (I → FTC.Entry (BasisSpace k)) → Finset I)
    (f : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFT : FTC.IsFilteringFaultTolerant ε f basisReferenceCost
      (@sqDistToCenters k) Q entries decoder) :
    (f : ℝ) * k / (2 * ε) ≤ (Q.card : ℝ) := by
  classical
  let a : I → ℝ := fun j => (entries j).weight
  have ha : ∀ j, 0 ≤ a j := fun j => (entries j).weight_nonneg
  have hagree : ∀ j ∈ Q, basisEntries loc a ha j = entries j := by
    intro j hj
    have hp := hsupport j hj
    cases he : entries j with
    | mk p w hw =>
      simp only [he] at hp
      simp [basisEntries, a, he, hp]
  have hcost : ∀ S : EuclideanQuery k,
      FTC.cost (FTC.contribution (@sqDistToCenters k) (basisEntries loc a ha)) Q S =
        FTC.cost (FTC.contribution (@sqDistToCenters k) entries) Q S := by
    intro S
    apply FTC.cost_congr
    intro j hj T
    unfold FTC.contribution
    rw [hagree j hj]
  have hFT' : FTC.IsFilteringFaultTolerant ε f basisReferenceCost
      (@sqDistToCenters k) Q (basisEntries loc a ha) decoder := by
    constructor
    · intro S
      simpa only [hcost S] using hFT.1 S
    · intro corrupted hcorrupt
      apply hFT.2 corrupted
      obtain ⟨B, hBQ, hBf, hB⟩ := hcorrupt
      refine ⟨B, hBQ, hBf, ?_⟩
      intro j hj hjB
      exact (hB j hj hjB).trans (hagree j hj)
  exact theorem_3_4 Q loc a ha decoder f ε hε hεhalf hFT'

end FTC.LowerBound

namespace FTC.LowerBound

/-- The source theorem stated using only support on `P = {e_i}`. Locations of
inactive indices are unrestricted; a coordinate label is chosen only for the
proof. The empty-dimensional case has a zero required lower bound. -/
theorem theorem_3_4_of_support
    {I : Type*} [DecidableEq I] {k : ℕ}
    (Q : Finset I) (entries : I → FTC.Entry (BasisSpace k))
    (hsupport : ∀ j ∈ Q, ∃ i : Fin k, (entries j).point = basisPoint i)
    (decoder : (I → FTC.Entry (BasisSpace k)) → Finset I)
    (f : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFT : FTC.IsFilteringFaultTolerant ε f basisReferenceCost
      (@sqDistToCenters k) Q entries decoder) :
    (f : ℝ) * k / (2 * ε) ≤ (Q.card : ℝ) := by
  classical
  by_cases hk : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let loc : I → Fin k := fun j =>
      if hj : j ∈ Q then Classical.choose (hsupport j hj) else ⟨0, hkpos⟩
    have hloc : ∀ j ∈ Q, (entries j).point = basisPoint (loc j) := by
      intro j hj
      dsimp only [loc]
      rw [dif_pos hj]
      exact Classical.choose_spec (hsupport j hj)
    exact theorem_3_4_of_supported Q entries loc hloc decoder f ε hε hεhalf hFT

end FTC.LowerBound
