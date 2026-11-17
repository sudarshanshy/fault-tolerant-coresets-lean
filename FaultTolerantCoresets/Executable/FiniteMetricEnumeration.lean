import FaultTolerantCoresets.Executable.FiniteMetricMatrix
import Mathlib.Data.List.MinMax

/-!
# Executable exhaustive constrained optimization for rational matrices

Candidate queries are given as a computable list. Their rational costs are
cached exactly once and a linear scan returns a least-cost feasible query.
The list may have repeated queries; correctness and work bounds remain valid.
The counted implementation charges matrix lookups, rational additions and
rational comparisons, rather than claiming a polynomial optimizer.
-/

namespace FTC.Executable

variable {I S : Type*} [DecidableEq I] [DecidableEq S]

def cachedQueryCosts (c : I → S → ℚ) (U : Finset I) (candidates : List S) : List (S × ℚ) :=
  candidates.map (fun s => (s, rationalCost c U s))

def exactFiniteSolver (c : I → S → ℚ) (U : Finset I) (candidates : List S) : Option S :=
  ((cachedQueryCosts c U candidates).argmin Prod.snd).map Prod.fst

theorem exactFiniteSolver_none_iff (c : I → S → ℚ) (U : Finset I) (candidates : List S) :
    exactFiniteSolver c U candidates = none ↔ candidates = [] := by
  simp [exactFiniteSolver, cachedQueryCosts, List.argmin_eq_none]

theorem exactFiniteSolver_spec {c : I → S → ℚ} {U : Finset I} {candidates : List S}
    {s : S} (hsolve : exactFiniteSolver c U candidates = some s) :
    s ∈ candidates ∧ ∀ t ∈ candidates, rationalCost c U s ≤ rationalCost c U t := by
  unfold exactFiniteSolver at hsolve
  cases hbest : (cachedQueryCosts c U candidates).argmin Prod.snd with
  | none => simp [hbest] at hsolve
  | some best =>
    have hmem : best ∈ cachedQueryCosts c U candidates := List.argmin_mem hbest
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    have hts : t = s := by simpa [hbest] using hsolve
    subst s
    refine ⟨ht, ?_⟩
    intro q hq
    exact List.le_of_mem_argmin (f := Prod.snd)
      (a := (q, rationalCost c U q)) (m := (t, rationalCost c U t))
      (l := cachedQueryCosts c U candidates)
      (List.mem_map.mpr ⟨q, hq, rfl⟩) hbest

/-- Filtering candidates before the scan skips precisely the infeasible ones. -/
def constrainedFiniteSolver (c : I → S → ℚ) (U : Finset I) (candidates : List S)
    (admissible : S → Prop) [DecidablePred admissible] : Option S :=
  exactFiniteSolver c U (candidates.filter fun s => decide (admissible s))

theorem constrainedFiniteSolver_none_iff (c : I → S → ℚ) (U : Finset I)
    (candidates : List S) (admissible : S → Prop) [DecidablePred admissible] :
    constrainedFiniteSolver c U candidates admissible = none ↔
      ¬ ∃ s ∈ candidates, admissible s := by
  rw [constrainedFiniteSolver, exactFiniteSolver_none_iff]
  constructor
  · intro h ⟨s, hs, ha⟩
    have hm : s ∈ candidates.filter (fun s => decide (admissible s)) := by simp [hs, ha]
    rw [h] at hm
    exact List.not_mem_nil hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro s hs
    have hm : s ∈ candidates ∧ admissible s := by simpa using hs
    exact h ⟨s, hm.1, hm.2⟩

theorem constrainedFiniteSolver_spec {c : I → S → ℚ} {U : Finset I}
    {candidates : List S} {admissible : S → Prop} [DecidablePred admissible]
    {s : S} (hsolve : constrainedFiniteSolver c U candidates admissible = some s) :
    s ∈ candidates ∧ admissible s ∧
      ∀ t ∈ candidates, admissible t → rationalCost c U s ≤ rationalCost c U t := by
  obtain ⟨hmem, hopt⟩ := exactFiniteSolver_spec hsolve
  have hs : s ∈ candidates ∧ admissible s := by simpa using hmem
  refine ⟨hs.1, hs.2, ?_⟩
  intro t ht ha
  exact hopt t (by simp [ht, ha])

/-! ## Counters carried by the exhaustive scan -/

def cachedQueryCostsCounted (c : I → S → ℚ) (U : Finset I) :
    List S → List (S × ℚ) × ℕ
  | [] => ([], 0)
  | s :: candidates =>
    let value := rationalCostCounted c U s
    let rest := cachedQueryCostsCounted c U candidates
    ((s, value.1) :: rest.1, value.2 + rest.2)

theorem cachedQueryCostsCounted_value (c : I → S → ℚ) (U : Finset I) (candidates : List S) :
    (cachedQueryCostsCounted c U candidates).1 = cachedQueryCosts c U candidates := by
  induction candidates with
  | nil => rfl
  | cons s candidates ih =>
    simp [cachedQueryCostsCounted, cachedQueryCosts, ih]

theorem cachedQueryCostsCounted_work (c : I → S → ℚ) (U : Finset I) (candidates : List S) :
    (cachedQueryCostsCounted c U candidates).2 = 2 * U.card * candidates.length := by
  induction candidates with
  | nil => simp [cachedQueryCostsCounted]
  | cons s candidates ih =>
    simp only [cachedQueryCostsCounted, rationalCostCounted_work, ih, List.length_cons,
      Nat.mul_succ]
    omega

/-- A cached minimum scan, with one comparison at each nontrivial merge. -/
def argminCounted : List (S × ℚ) → Option (S × ℚ) × ℕ
  | [] => (none, 0)
  | a :: candidates =>
    let rest := argminCounted candidates
    match rest.1 with
    | none => (some a, rest.2)
    | some b => (some (if b.2 < a.2 then b else a), rest.2 + 1)

theorem argminCounted_value (candidates : List (S × ℚ)) :
    (argminCounted candidates).1 = candidates.argmin Prod.snd := by
  induction candidates with
  | nil => rfl
  | cons a candidates ih =>
    rw [List.argmin_cons]
    simp only [argminCounted, ← ih]
    cases h : (argminCounted candidates).1
    · rfl
    · simp only
      split_ifs <;> rfl

theorem argminCounted_work_le (candidates : List (S × ℚ)) :
    (argminCounted candidates).2 ≤ candidates.length := by
  induction candidates with
  | nil => exact le_rfl
  | cons a candidates ih =>
    simp only [argminCounted]
    cases h : (argminCounted candidates).1 <;> simp only [h]
    · exact ih.trans (Nat.le_succ _)
    · exact Nat.succ_le_succ ih

def exactFiniteSolverCounted (c : I → S → ℚ) (U : Finset I) (candidates : List S) :
    Option S × ℕ :=
  let cache := cachedQueryCostsCounted c U candidates
  let optimum := argminCounted cache.1
  (optimum.1.map Prod.fst, cache.2 + optimum.2)

theorem exactFiniteSolverCounted_value (c : I → S → ℚ) (U : Finset I) (candidates : List S) :
    (exactFiniteSolverCounted c U candidates).1 = exactFiniteSolver c U candidates := by
  simp [exactFiniteSolverCounted, exactFiniteSolver, argminCounted_value,
    cachedQueryCostsCounted_value]

/-- One cost evaluation per candidate and at most one cached comparison per
candidate: exponential candidate enumeration is exposed, not hidden. -/
theorem exactFiniteSolverCounted_work_le (c : I → S → ℚ) (U : Finset I) (candidates : List S) :
    (exactFiniteSolverCounted c U candidates).2 ≤
      (2 * U.card + 1) * candidates.length := by
  have h := argminCounted_work_le (cachedQueryCostsCounted c U candidates).1
  rw [cachedQueryCostsCounted_value] at h
  have hlen : (cachedQueryCosts c U candidates).length = candidates.length := by
    simp [cachedQueryCosts]
  rw [hlen] at h
  change (cachedQueryCostsCounted c U candidates).2 +
      (argminCounted (cachedQueryCostsCounted c U candidates).1).2 ≤ _
  rw [cachedQueryCostsCounted_work, cachedQueryCostsCounted_value]
  simpa [Nat.add_mul, Nat.one_mul] using
    Nat.add_le_add_left h (2 * U.card * candidates.length)

def constrainedFiniteSolverCounted (c : I → S → ℚ) (U : Finset I) (candidates : List S)
    (admissible : S → Prop) [DecidablePred admissible] : Option S × ℕ :=
  exactFiniteSolverCounted c U (candidates.filter fun s => decide (admissible s))

theorem constrainedFiniteSolverCounted_value (c : I → S → ℚ) (U : Finset I)
    (candidates : List S) (admissible : S → Prop) [DecidablePred admissible] :
    (constrainedFiniteSolverCounted c U candidates admissible).1 =
      constrainedFiniteSolver c U candidates admissible :=
  exactFiniteSolverCounted_value _ _ _

theorem constrainedFiniteSolverCounted_work_le (c : I → S → ℚ) (U : Finset I)
    (candidates : List S) (admissible : S → Prop) [DecidablePred admissible] :
    (constrainedFiniteSolverCounted c U candidates admissible).2 ≤
      (2 * U.card + 1) * candidates.length := by
  exact (exactFiniteSolverCounted_work_le _ _ _).trans
    (Nat.mul_le_mul_left _ (List.length_filter_le _ _))

end FTC.Executable
