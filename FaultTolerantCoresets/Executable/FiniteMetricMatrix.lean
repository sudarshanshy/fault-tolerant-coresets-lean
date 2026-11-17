import FaultTolerantCoresets.Sensitivity
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators

/-!
# Executable exact sensitivity for finite rational loss matrices

The query set is supplied explicitly as a finite set. Every operation in
`rationalSensitivity` is rational arithmetic or a finite fold; no ordering of
arbitrary real numbers and no supremum is evaluated. The real interpretation
is proved equal to the existing exact sensitivity when the query set is
complete. Entries remain separately indexed, including duplicate rows.
-/

namespace FTC.Executable

variable {I S : Type*} [DecidableEq I] [DecidableEq S]

/-- A finite maximum seeded with zero, computed over the original queries. -/
def rationalMax (queries : Finset S) (f : S → ℚ) : ℚ :=
  queries.fold max 0 f

@[simp] theorem rationalMax_empty (f : S → ℚ) : rationalMax ∅ f = 0 := rfl

theorem rationalMax_insert {queries : Finset S} {s : S} (hs : s ∉ queries)
    (f : S → ℚ) : rationalMax (insert s queries) f = max (f s) (rationalMax queries f) := by
  exact Finset.fold_insert hs

theorem rationalMax_nonneg (queries : Finset S) (f : S → ℚ) :
    0 ≤ rationalMax queries f := by
  induction queries using Finset.induction_on with
  | empty => exact le_rfl
  | @insert s queries hs ih =>
    rw [rationalMax_insert hs]
    exact ih.trans (le_max_right _ _)

theorem le_rationalMax {queries : Finset S} {s : S} (hs : s ∈ queries) (f : S → ℚ) :
    f s ≤ rationalMax queries f := by
  induction queries using Finset.induction_on with
  | empty => simp at hs
  | @insert t queries ht ih =>
    rw [rationalMax_insert ht]
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact le_max_left _ _
    · exact (ih hs).trans (le_max_right _ _)

theorem rationalMax_le {queries : Finset S} {f : S → ℚ} {r : ℚ}
    (hr : 0 ≤ r) (h : ∀ s ∈ queries, f s ≤ r) : rationalMax queries f ≤ r := by
  induction queries using Finset.induction_on with
  | empty => exact hr
  | @insert s queries hs ih =>
    rw [rationalMax_insert hs]
    exact max_le (h s (Finset.mem_insert_self _ _))
      (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

theorem rationalMax_cast_le {queries : Finset S} {f : S → ℚ} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ s ∈ queries, (f s : ℝ) ≤ r) :
    (rationalMax queries f : ℝ) ≤ r := by
  induction queries using Finset.induction_on with
  | empty => simpa using hr
  | @insert s queries hs ih =>
    rw [rationalMax_insert hs, Rat.cast_max]
    exact max_le (h s (Finset.mem_insert_self _ _))
      (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

/-- Rational cost of the active individual entries. -/
def rationalCost (c : I → S → ℚ) (U : Finset I) (s : S) : ℚ :=
  ∑ i ∈ U, c i s

/-- The same matrix interpreted as a real nonnegative pointwise objective. -/
def realContribution (c : I → S → ℚ) (i : I) (s : S) : ℝ := c i s

theorem realContribution_nonneg {c : I → S → ℚ} (hc : ∀ i s, 0 ≤ c i s) :
    ∀ i s, 0 ≤ realContribution c i s := by
  intro i s
  change 0 ≤ (c i s : ℝ)
  exact_mod_cast hc i s

@[simp] theorem rationalCost_cast (c : I → S → ℚ) (U : Finset I) (s : S) :
    (rationalCost c U s : ℝ) = cost (realContribution c) U s := by
  simp [rationalCost, cost, realContribution]

theorem rationalCost_nonneg {c : I → S → ℚ} (hc : ∀ i s, 0 ≤ c i s)
    (U : Finset I) (s : S) : 0 ≤ rationalCost c U s :=
  Finset.sum_nonneg (fun i _ => hc i s)

/-- Rational zero-cost ratios are zero, agreeing with the real API. -/
def rationalRatio (c : I → S → ℚ) (U : Finset I) (i : I) (s : S) : ℚ :=
  c i s / rationalCost c U s

@[simp] theorem rationalRatio_cast (c : I → S → ℚ) (U : Finset I) (i : I) (s : S) :
    (rationalRatio c U i s : ℝ) = realContribution c i s / cost (realContribution c) U s := by
  simp [rationalRatio, realContribution]

/-- Executable exact sensitivity of an active entry over a finite query matrix. -/
def rationalSensitivity (c : I → S → ℚ) (queries : Finset S) (U : Finset I) (i : I) : ℚ :=
  if i ∈ U then rationalMax queries (rationalRatio c U i) else 0

theorem rationalSensitivity_nonneg (c : I → S → ℚ) (queries : Finset S)
    (U : Finset I) (i : I) : 0 ≤ rationalSensitivity c queries U i := by
  unfold rationalSensitivity
  split_ifs
  · exact rationalMax_nonneg _ _
  · exact le_rfl

/-- The computed rational score casts to exactly the real supremum. This is
an equality of mathematical meanings, not an implementation of real suprema. -/
theorem rationalSensitivity_cast_eq {c : I → S → ℚ} {queries : Finset S}
    (hc : ∀ i s, 0 ≤ c i s) (hqueries : ∀ s : S, s ∈ queries)
    (U : Finset I) (i : I) :
    (rationalSensitivity c queries U i : ℝ) = sensitivity (realContribution c) U i := by
  have hcR := realContribution_nonneg hc
  by_cases hi : i ∈ U
  · unfold rationalSensitivity
    rw [if_pos hi]
    apply le_antisymm
    · apply rationalMax_cast_le (sensitivity_nonneg hcR U i)
      intro s _
      rw [rationalRatio_cast, sensitivity, if_pos hi]
      exact le_csSup (sensitivityRatios_bddAbove hcR hi) (Or.inr ⟨s, rfl⟩)
    · apply sensitivity_le_of_contribution_le hcR hi
        (by exact_mod_cast rationalMax_nonneg queries (rationalRatio c U i))
      intro s
      have hratio := le_rationalMax (hqueries s) (rationalRatio c U i)
      have hratioR : realContribution c i s / cost (realContribution c) U s ≤
          (rationalMax queries (rationalRatio c U i) : ℝ) := by
        rw [← rationalRatio_cast]
        exact_mod_cast hratio
      by_cases hz : cost (realContribution c) U s = 0
      · have hci := cost_eq_zero_contribution hcR hi hz
        simp [hz, hci]
      · have hpos : 0 < cost (realContribution c) U s :=
          lt_of_le_of_ne (cost_nonneg hcR U s) (Ne.symm hz)
        exact (div_le_iff₀ hpos).1 hratioR
  · simp [rationalSensitivity, hi, sensitivity_of_not_mem hi]

/-- A finite rational matrix gives the exact real oracle used by the filtering
theorem, while its score values are produced by executable rational code. -/
def rationalExactOracle (c : I → S → ℚ) (queries : Finset S)
    (hc : ∀ i s, 0 ≤ c i s) (hqueries : ∀ s : S, s ∈ queries) :
    ApproxSensitivityOracle (realContribution c) 1 where
  score U i := (rationalSensitivity c queries U i : ℝ)
  lower U i _ := by rw [rationalSensitivity_cast_eq hc hqueries]; simp
  upper U i _ := by rw [rationalSensitivity_cast_eq hc hqueries]

/-! ## An instrumented arithmetic implementation

One charge is made for each matrix lookup, rational addition, rational
division, and maximum comparison. Finite-container enumeration and the bit
complexity of rational arithmetic are outside this unit-cost model. Counters
are carried by the evaluation itself, rather than attached to its result
afterward.
-/

/-- The first component is the cost; each row requires one lookup and one
addition to the accumulating sum. -/
def rationalCostCounted (c : I → S → ℚ) (U : Finset I) (s : S) : ℚ × ℕ :=
  ∑ i ∈ U, (c i s, 2)

@[simp] theorem rationalCostCounted_value (c : I → S → ℚ) (U : Finset I) (s : S) :
    (rationalCostCounted c U s).1 = rationalCost c U s := by
  induction U using Finset.induction_on with
  | empty => rfl
  | @insert i U hi ih =>
    change (∑ j ∈ insert i U, (c j s, 2)).1 = ∑ j ∈ insert i U, c j s
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change c i s + (rationalCostCounted c U s).1 = c i s + rationalCost c U s
    rw [ih]

@[simp] theorem rationalCostCounted_work (c : I → S → ℚ) (U : Finset I) (s : S) :
    (rationalCostCounted c U s).2 = 2 * U.card := by
  induction U using Finset.induction_on with
  | empty => rfl
  | @insert i U hi ih =>
    change (∑ j ∈ insert i U, (c j s, 2)).2 = 2 * (insert i U).card
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    change 2 + (rationalCostCounted c U s).2 = 2 * (U.card + 1)
    rw [ih]
    omega

/-- In addition to the denominator, a ratio evaluates one numerator lookup
and one division. The zero-denominator convention is executable. -/
def rationalRatioCounted (c : I → S → ℚ) (U : Finset I) (i : I) (s : S) : ℚ × ℕ :=
  let denominator := rationalCostCounted c U s
  (c i s / denominator.1, denominator.2 + 2)

@[simp] theorem rationalRatioCounted_value (c : I → S → ℚ) (U : Finset I) (i : I) (s : S) :
    (rationalRatioCounted c U i s).1 = rationalRatio c U i s := by
  simp [rationalRatioCounted, rationalRatio]

@[simp] theorem rationalRatioCounted_work (c : I → S → ℚ) (U : Finset I) (i : I) (s : S) :
    (rationalRatioCounted c U i s).2 = 2 * U.card + 2 := by
  simp [rationalRatioCounted]

/-- Combining two counted maxima executes one comparison. Associativity and
commutativity make the fold independent of finite-set representation. -/
def maxWithWork (a b : ℚ × ℕ) : ℚ × ℕ := (max a.1 b.1, a.2 + b.2 + 1)

instance : Std.Commutative maxWithWork where
  comm a b := by
    apply Prod.ext
    · exact max_comm _ _
    · simp [maxWithWork, Nat.add_comm]

instance : Std.Associative maxWithWork where
  assoc a b c := by
    apply Prod.ext
    · exact max_assoc _ _ _
    · simp [maxWithWork, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def rationalSensitivityCounted (c : I → S → ℚ) (queries : Finset S)
    (U : Finset I) (i : I) : ℚ × ℕ :=
  if i ∈ U then queries.fold maxWithWork (0, 0) (rationalRatioCounted c U i) else (0, 0)

theorem countedMax_value (c : I → S → ℚ) (queries : Finset S) (U : Finset I) (i : I) :
    (queries.fold maxWithWork (0, 0) (rationalRatioCounted c U i)).1 =
      rationalMax queries (rationalRatio c U i) := by
  induction queries using Finset.induction_on with
  | empty => rfl
  | @insert s queries hs ih =>
    rw [Finset.fold_insert hs, rationalMax_insert hs]
    simp only [maxWithWork, rationalRatioCounted_value, ih]

theorem countedMax_work (c : I → S → ℚ) (queries : Finset S) (U : Finset I) (i : I) :
    (queries.fold maxWithWork (0, 0) (rationalRatioCounted c U i)).2 =
      queries.card * (2 * U.card + 3) := by
  induction queries using Finset.induction_on with
  | empty => simp
  | @insert s queries hs ih =>
    rw [Finset.fold_insert hs, Finset.card_insert_of_notMem hs]
    simp only [maxWithWork, rationalRatioCounted_work, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- The instrumented program computes exactly the uninstrumented score. -/
theorem rationalSensitivityCounted_value (c : I → S → ℚ) (queries : Finset S)
    (U : Finset I) (i : I) :
    (rationalSensitivityCounted c queries U i).1 = rationalSensitivity c queries U i := by
  unfold rationalSensitivityCounted rationalSensitivity
  split_ifs
  · exact countedMax_value c queries U i
  · rfl

/-- Exact unit-cost arithmetic count: one denominator scan and ratio/max step
per query; inactive indices are not evaluated. -/
theorem rationalSensitivityCounted_work (c : I → S → ℚ) (queries : Finset S)
    (U : Finset I) (i : I) :
    (rationalSensitivityCounted c queries U i).2 =
      if i ∈ U then queries.card * (2 * U.card + 3) else 0 := by
  unfold rationalSensitivityCounted
  split_ifs
  · exact countedMax_work c queries U i
  · rfl

end FTC.Executable
