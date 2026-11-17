import FaultTolerantCoresets.Executable.Filtering
import FaultTolerantCoresets.Executable.FiniteMetricMatrix

/-!
# Exact finite-matrix decoder and certified work bounds

This combines a genuine executable exact sensitivity computation with the
executable filtering loop. No sensitivity-oracle specification is assumed in
`matrixDecode_correct`; exactness is proved from the finite query enumeration.
The arithmetic charge uses the largest possible intermediate active-set size.
As in the counted primitives, container operations and rational bit complexity
are deliberately not charged as rational arithmetic operations.
-/

namespace FTC.Executable

variable {I S : Type*} [LinearOrder I] [DecidableEq S]

def matrixDecode (c : I → S → ℚ) (queries : Finset S) (f : ℕ) (U : Finset I) : Finset I :=
  decode (fun Q i => rationalSensitivity c queries Q i) f U

def matrixDecodeCounted (c : I → S → ℚ) (queries : Finset S)
    (f : ℕ) (U : Finset I) : WorkResult I :=
  runCounted (fun Q i => rationalSensitivity c queries Q i) f U

theorem matrixDecodeCounted_value (c : I → S → ℚ) (queries : Finset S)
    (f : ℕ) (U : Finset I) :
    (matrixDecodeCounted c queries f U).remaining = matrixDecode c queries f U :=
  runCounted_remaining _ _ _

/-- Full finite-rational specialization of Theorem 3.1's deterministic core.
Both the numerical sensitivities and the filtering loop are executable. -/
theorem matrixDecode_correct {a c : I → S → ℚ} {reference : S → ℝ}
    {queries : Finset S} {U B : Finset I} {f : ℕ} {ε δ : ℝ}
    (ha : ∀ i s, 0 ≤ a i s) (hc : ∀ i s, 0 ≤ c i s)
    (hqueries : ∀ s : S, s ∈ queries) (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ)
    (hcoreset : IsCoreset ε reference (cost (realContribution a) U))
    (hB : B.card ≤ f)
    (hagrees : ∀ i ∈ U, i ∉ B → ∀ s, c i s = a i s)
    (hentry : ∀ i ∈ U, ∀ s, realContribution a i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * δ ≤ ε) :
    IsCoreset (6 * ε) reference (cost (realContribution c) (matrixDecode c queries f U)) := by
  refine decode_correct (realContribution_nonneg ha) (realContribution_nonneg hc)
    hreference hε hεsmall hδ (α := 1) (by norm_num) hcoreset hB ?_ hentry ?_
    (fun Q i => rationalSensitivity c queries Q i) ?_ ?_
  · intro i hi hiB s
    simp only [realContribution, hagrees i hi hiB s]
  · simpa using hbudget
  · intro Q i _
    rw [rationalSensitivity_cast_eq hc hqueries]
    simp
  · intro Q i _
    rw [rationalSensitivity_cast_eq hc hqueries]

theorem stepCounted_deletions_le_one (score : Finset I → I → ℚ) (Q : Finset I) :
    (stepCounted score Q).deletions ≤ 1 := by
  dsimp only [stepCounted]
  split <;> simp

theorem stepCounted_deletions_of_nonempty (score : Finset I → I → ℚ)
    {Q : Finset I} (hQ : Q.Nonempty) : (stepCounted score Q).deletions = 1 := by
  have hn := selectedPair_ne_none (score Q) hQ
  cases hp : selectedPair (score Q) Q with
  | none => exact False.elim (hn hp)
  | some p =>
    have hp' : (maximumCounted (evaluateScores (score Q) (Q.sort (· ≤ ·))).1).1 =
        some p := hp
    simp only [stepCounted, hp']

theorem stepCounted_balance (score : Finset I → I → ℚ) (Q : Finset I) :
    (stepCounted score Q).remaining.card + (stepCounted score Q).deletions = Q.card := by
  by_cases hQ : Q.Nonempty
  · have hcard := card_selectionStep_add_one (rationalRule score) hQ
    rw [← stepCounted_remaining] at hcard
    simpa [stepCounted_deletions_of_nonempty score hQ] using hcard
  · have hz : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    subst Q
    simp [stepCounted, evaluateScores, maximumCounted]

theorem runCounted_balance (score : Finset I → I → ℚ) (f : ℕ) (U : Finset I) :
    (runCounted score f U).remaining.card + (runCounted score f U).deletions = U.card := by
  induction f generalizing U with
  | zero => simp [runCounted]
  | succ f ih =>
    by_cases hU : U.Nonempty
    · have hrest := ih (stepCounted score U).remaining
      have hfirst := stepCounted_balance score U
      simp only [runCounted, if_pos hU]
      omega
    · simp [runCounted, hU]

theorem runCounted_deletions_le (score : Finset I → I → ℚ) (f : ℕ) (U : Finset I) :
    (runCounted score f U).deletions ≤ min f U.card := by
  have hsteps : (runCounted score f U).deletions ≤ f := by
    induction f generalizing U with
    | zero => simp [runCounted]
    | succ f ih =>
      by_cases hU : U.Nonempty
      · have hrest := ih (stepCounted score U).remaining
        have hfirst := stepCounted_deletions_le_one score U
        simp only [runCounted, if_pos hU]
        omega
      · simp [runCounted, hU]
  have hbalance := runCounted_balance score f U
  omega

/-- Each actual sensitivity call on an intermediate subset has this unit-cost
arithmetic upper bound, by the backend's instrumented implementation. -/
theorem matrixOracle_work_le (c : I → S → ℚ) (queries : Finset S)
    {Q U : Finset I} (hQU : Q ⊆ U) (i : I) :
    (rationalSensitivityCounted c queries Q i).2 ≤ queries.card * (2 * U.card + 3) := by
  rw [rationalSensitivityCounted_work]
  split_ifs
  · exact Nat.mul_le_mul_left _ (by have := Finset.card_le_card hQU; omega)
  · exact Nat.zero_le _

/-- Worst-case charge for the actual number of backend calls and cached-score
comparisons made by the counted loop. Every intermediate state is a subset of
`U`, so `matrixOracle_work_le` applies to every call. -/
def chargedMatrixWork (c : I → S → ℚ) (queries : Finset S) (f : ℕ) (U : Finset I) : ℕ :=
  let work := matrixDecodeCounted c queries f U
  work.scoreCalls * (queries.card * (2 * U.card + 3)) + work.comparisons

theorem chargedMatrixWork_bound (c : I → S → ℚ) (queries : Finset S)
    (f : ℕ) (U : Finset I) :
    chargedMatrixWork c queries f U ≤
      f * (U.card * queries.card * (2 * U.card + 3) + (U.card - 1)) := by
  have hcalls := runCounted_scoreCalls_le (fun Q i => rationalSensitivity c queries Q i) f U
  have hcomparisons := runCounted_comparisons_le (fun Q i => rationalSensitivity c queries Q i) f U
  have hscaled := Nat.mul_le_mul_right (queries.card * (2 * U.card + 3)) hcalls
  unfold chargedMatrixWork matrixDecodeCounted
  calc
    _ ≤ (f * U.card) * (queries.card * (2 * U.card + 3)) + f * (U.card - 1) :=
      Nat.add_le_add hscaled hcomparisons
    _ = _ := by ring

end FTC.Executable
