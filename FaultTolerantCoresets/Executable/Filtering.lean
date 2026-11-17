import FaultTolerantCoresets.Decoder
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Sort

/-!
# Executable rational-score filtering

Scores are evaluated once for each active index and cached before selecting a
maximum. The counted program records score calls, comparisons of cached scores,
and deletions. Container operations and rational bit complexity are outside
this explicit cost model. The mathematical guarantee is the same `6ε` theorem
as for the classical decoder, with no requirement on how ties are broken.
-/

namespace FTC.Executable

variable {I : Type*}

/-- Evaluate and cache each score, charging one oracle call per list entry. -/
def evaluateScores (score : I → ℚ) : List I → List (I × ℚ) × ℕ
  | [] => ([], 0)
  | i :: is =>
      let tail := evaluateScores score is
      ((i, score i) :: tail.1, tail.2 + 1)

@[simp] theorem evaluateScores_values (score : I → ℚ) (is : List I) :
    (evaluateScores score is).1 = is.map (fun i => (i, score i)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [evaluateScores, ih]

@[simp] theorem evaluateScores_calls (score : I → ℚ) (is : List I) :
    (evaluateScores score is).2 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [evaluateScores, ih]

/-- A maximum scan on cached values, charging exactly one comparison whenever
the nonempty tail already has a candidate. Ties retain the first candidate. -/
def maximumCounted : List (I × ℚ) → Option (I × ℚ) × ℕ
  | [] => (none, 0)
  | x :: xs =>
      let tail := maximumCounted xs
      match tail.1 with
      | none => (some x, tail.2)
      | some y => (some (if x.2 < y.2 then y else x), tail.2 + 1)

@[simp] theorem maximumCounted_value (xs : List (I × ℚ)) :
    (maximumCounted xs).1 = xs.argmax Prod.snd := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.argmax_cons]
    simp only [maximumCounted]
    rw [← ih]
    cases h : (maximumCounted xs).1 with
    | none => simp [h]
    | some y =>
      by_cases hxy : x.2 < y.2 <;> simp [h, hxy]

@[simp] theorem maximumCounted_comparisons (xs : List (I × ℚ)) :
    (maximumCounted xs).2 = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : (maximumCounted xs).1 with
    | none =>
      have harg : xs.argmax (Prod.snd : I × ℚ → ℚ) = none := by
        rw [← maximumCounted_value]
        exact h
      have hnil : xs = [] := List.argmax_eq_none.mp harg
      subst xs
      rfl
    | some y =>
      have hne : xs ≠ [] := by intro hz; simp [hz, maximumCounted] at h
      have hlen : 0 < xs.length := by
        cases xs with
        | nil => exact False.elim (hne rfl)
        | cons a as => simp
      simp only [maximumCounted, h, List.length_cons]
      simp only [ih]
      omega

section OrderedIndices

variable [LinearOrder I]

/-- The cached maximum on a deterministic enumeration of a finite active set. -/
def selectedPair (score : I → ℚ) (Q : Finset I) : Option (I × ℚ) :=
  (maximumCounted (evaluateScores score (Q.sort (· ≤ ·))).1).1

theorem selectedPair_eq_argmax (score : I → ℚ) (Q : Finset I) :
    selectedPair score Q =
      ((Q.sort (· ≤ ·)).map (fun i => (i, score i))).argmax Prod.snd := by
  simp [selectedPair]

theorem selectedPair_ne_none (score : I → ℚ) {Q : Finset I} (hQ : Q.Nonempty) :
    selectedPair score Q ≠ none := by
  intro h
  rw [selectedPair_eq_argmax] at h
  have hnil := List.argmax_eq_none.mp h
  have hlen := congrArg List.length hnil
  simp only [List.length_map, Finset.length_sort, List.length_nil] at hlen
  exact (Finset.card_pos.mpr hQ).ne' hlen

/-- The fallback is unreachable for a nonempty set, but makes the algorithm
total without classical extraction from an existence statement. -/
def rationalChoice (score : I → ℚ) (Q : Finset I) (hQ : Q.Nonempty) : I :=
  match selectedPair score Q with
  | none => Q.min' hQ
  | some p => p.1

theorem rationalChoice_spec (score : I → ℚ) (Q : Finset I) (hQ : Q.Nonempty) :
    rationalChoice score Q hQ ∈ Q ∧
      ∀ i ∈ Q, score i ≤ score (rationalChoice score Q hQ) := by
  cases hp : selectedPair score Q with
  | none => exact False.elim (selectedPair_ne_none score hQ hp)
  | some p =>
    have hp' : p ∈ ((Q.sort (· ≤ ·)).map (fun i => (i, score i))).argmax Prod.snd := by
      rw [← selectedPair_eq_argmax, hp]
      simp
    have hmem := List.argmax_mem hp'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    constructor
    · simpa [rationalChoice, hp] using (Finset.mem_sort (· ≤ ·)).mp hj
    · intro i hi
      have hpair : (i, score i) ∈ (Q.sort (· ≤ ·)).map (fun i => (i, score i)) := by
        exact List.mem_map.mpr ⟨i, (Finset.mem_sort (· ≤ ·)).mpr hi, rfl⟩
      have hle := List.le_of_mem_argmax hpair hp'
      simpa [rationalChoice, hp] using hle

def rationalRule (score : Finset I → I → ℚ) : SelectionRule I where
  select Q h := rationalChoice (score Q) Q h
  select_mem Q h := (rationalChoice_spec (score Q) Q h).1

theorem rationalRule_isMaxFor (score : Finset I → I → ℚ) :
    (rationalRule score).IsMaxFor (fun Q i => (score Q i : ℝ)) := by
  intro Q h i hi
  change (score Q i : ℝ) ≤ (score Q (rationalChoice (score Q) Q h) : ℝ)
  exact_mod_cast (rationalChoice_spec (score Q) Q h).2 i hi

/-- Computable decoder, suitable in particular for `I = Fin m`. -/
def decode (score : Finset I → I → ℚ) (f : ℕ) (Q : Finset I) : Finset I :=
  selectionRun (rationalRule score) f Q

structure WorkResult (I : Type*) where
  remaining : Finset I
  scoreCalls : ℕ
  comparisons : ℕ
  deletions : ℕ

def stepCounted (score : Finset I → I → ℚ) (Q : Finset I) : WorkResult I :=
  let evaluated := evaluateScores (score Q) (Q.sort (· ≤ ·))
  let scanned := maximumCounted evaluated.1
  match scanned.1 with
  | none => ⟨Q, evaluated.2, scanned.2, 0⟩
  | some p => ⟨Q.erase p.1, evaluated.2, scanned.2, 1⟩

@[simp] theorem stepCounted_scoreCalls (score : Finset I → I → ℚ) (Q : Finset I) :
    (stepCounted score Q).scoreCalls = Q.card := by
  dsimp only [stepCounted]
  split <;> simp

@[simp] theorem stepCounted_comparisons (score : Finset I → I → ℚ) (Q : Finset I) :
    (stepCounted score Q).comparisons = Q.card - 1 := by
  dsimp only [stepCounted]
  split <;> simp

theorem stepCounted_remaining (score : Finset I → I → ℚ) (Q : Finset I) :
    (stepCounted score Q).remaining = selectionStep (rationalRule score) Q := by
  by_cases hQ : Q.Nonempty
  · have hn := selectedPair_ne_none (score Q) hQ
    cases hp : selectedPair (score Q) Q with
    | none => exact False.elim (hn hp)
    | some p =>
      have hp' : (maximumCounted (evaluateScores (score Q) (Q.sort (· ≤ ·))).1).1 =
          some p := hp
      simp only [stepCounted, hp']
      simp [selectionStep, hQ, rationalRule, rationalChoice, hp]
  · have hzero : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    subst Q
    simp [stepCounted, evaluateScores, maximumCounted, selectionStep]

def runCounted (score : Finset I → I → ℚ) : ℕ → Finset I → WorkResult I
  | 0, Q => ⟨Q, 0, 0, 0⟩
  | n + 1, Q =>
      if Q.Nonempty then
        let first := stepCounted score Q
        let rest := runCounted score n first.remaining
        ⟨rest.remaining, first.scoreCalls + rest.scoreCalls,
          first.comparisons + rest.comparisons, first.deletions + rest.deletions⟩
      else ⟨Q, 0, 0, 0⟩

theorem selectionRun_empty (rule : SelectionRule I) (n : ℕ) :
    selectionRun rule n ∅ = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [selectionRun, selectionStep] using ih

theorem runCounted_remaining (score : Finset I → I → ℚ) (n : ℕ) (Q : Finset I) :
    (runCounted score n Q).remaining = decode score n Q := by
  induction n generalizing Q with
  | zero => rfl
  | succ n ih =>
    by_cases hQ : Q.Nonempty
    · simp only [runCounted, if_pos hQ]
      rw [ih, stepCounted_remaining]
      rfl
    · have hzero : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      subst Q
      simp [runCounted, decode, selectionRun_empty]

theorem runCounted_scoreCalls_le (score : Finset I → I → ℚ) (n : ℕ) (Q : Finset I) :
    (runCounted score n Q).scoreCalls ≤ n * Q.card := by
  induction n generalizing Q with
  | zero => simp [runCounted]
  | succ n ih =>
    by_cases hQ : Q.Nonempty
    · simp only [runCounted, if_pos hQ]
      have hrest := ih (stepCounted score Q).remaining
      have hsub : (stepCounted score Q).remaining ⊆ Q := by
        rw [stepCounted_remaining]
        exact selectionStep_subset _ _
      have hscale := Nat.mul_le_mul_left n (Finset.card_le_card hsub)
      rw [stepCounted_scoreCalls]
      nlinarith
    · simp [runCounted, hQ]

theorem runCounted_comparisons_le (score : Finset I → I → ℚ) (n : ℕ) (Q : Finset I) :
    (runCounted score n Q).comparisons ≤ n * (Q.card - 1) := by
  induction n generalizing Q with
  | zero => simp [runCounted]
  | succ n ih =>
    by_cases hQ : Q.Nonempty
    · simp only [runCounted, if_pos hQ]
      have hrest := ih (stepCounted score Q).remaining
      have hsub : (stepCounted score Q).remaining ⊆ Q := by
        rw [stepCounted_remaining]
        exact selectionStep_subset _ _
      have hscale := Nat.mul_le_mul_left n
        (Nat.sub_le_sub_right (Finset.card_le_card hsub) 1)
      rw [stepCounted_comparisons]
      nlinarith
    · simp [runCounted, hQ]

/-- The executable rational-score decoder inherits the full deterministic
filtering guarantee from the shared selector-parametric proof. -/
theorem decode_correct {S : Type*} {c d : I → S → ℝ} {reference : S → ℝ}
    {U B : Finset I} {f : ℕ} {ε δ α : ℝ}
    (hc : ∀ i s, 0 ≤ c i s) (hd : ∀ i s, 0 ≤ d i s)
    (hreference : ∀ s, 0 ≤ reference s)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 10) (hδ : 0 ≤ δ) (hα : 1 ≤ α)
    (hcoreset : IsCoreset ε reference (cost c U)) (hB : B.card ≤ f)
    (hagrees : ∀ i ∈ U, i ∉ B → ∀ s, d i s = c i s)
    (hentry : ∀ i ∈ U, ∀ s, c i s ≤ δ * reference s)
    (hbudget : (f : ℝ) * α * δ ≤ ε)
    (score : Finset I → I → ℚ)
    (hlower : ∀ Q i, i ∈ Q → sensitivity d Q i ≤ α * (score Q i : ℝ))
    (hupper : ∀ Q i, i ∈ Q → (score Q i : ℝ) ≤ sensitivity d Q i) :
    IsCoreset (6 * ε) reference (cost d (decode score f U)) := by
  let oracle : ApproxSensitivityOracle d α := ⟨fun Q i => (score Q i : ℝ), hlower, hupper⟩
  exact filtering_decoder_correct_with_rule hc hd hreference hε hεsmall hδ hα
    hcoreset hB hagrees hentry hbudget oracle (rationalRule score) (rationalRule_isMaxFor score)

end OrderedIndices
end FTC.Executable
