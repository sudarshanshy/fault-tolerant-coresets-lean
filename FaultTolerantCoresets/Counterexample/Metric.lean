import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# The finite metric in the Appendix A.1 counterexample

The `n` original points form a unit simplex. The vertex `a` has distance
`1/2` from `p₁` (index zero), distance `3/2` from every other original point,
and distance `M + 1/2` from `b`. The vertex `b` has distance `M` from every
original point. These are precisely the distances in the graph described in
the PDF when `M ≥ 1`.

The metric is constructed directly from these distances. The exceptional-set
API states the common-distance property used for all two-center queries:
each center has at most one exceptional original point, and every exceptional
distance is at most the common distance.
-/

namespace FTC.Counterexample

abbrev Vertex (n : ℕ) := Fin n ⊕ Bool

abbrev p {n : ℕ} (i : Fin n) : Vertex n := Sum.inl i
abbrev a {n : ℕ} : Vertex n := Sum.inr false
abbrev b {n : ℕ} : Vertex n := Sum.inr true

noncomputable section

/-- Distance from the attachment vertex to an original point. -/
def firstDistance {n : ℕ} (i : Fin n) : ℝ :=
  if i.val = 0 then 1 / 2 else 3 / 2

/-- Unit-simplex distance between original points. -/
def unitDistance {n : ℕ} (i j : Fin n) : ℝ := if i = j then 0 else 1

/-- Explicit shortest-path distances of the counterexample graph. -/
def graphDist {n : ℕ} (M : ℝ) : Vertex n → Vertex n → ℝ
  | .inl i, .inl j => unitDistance i j
  | .inl i, .inr false => firstDistance i
  | .inr false, .inl i => firstDistance i
  | .inl _, .inr true => M
  | .inr true, .inl _ => M
  | .inr false, .inr true => M + 1 / 2
  | .inr true, .inr false => M + 1 / 2
  | .inr false, .inr false => 0
  | .inr true, .inr true => 0

@[simp] theorem graphDist_p_p {n : ℕ} (M : ℝ) (i j : Fin n) :
    graphDist M (p i) (p j) = if i = j then 0 else 1 := rfl

@[simp] theorem graphDist_p_a {n : ℕ} (M : ℝ) (i : Fin n) :
    graphDist M (p i) a = if i.val = 0 then 1 / 2 else 3 / 2 := rfl

@[simp] theorem graphDist_a_p {n : ℕ} (M : ℝ) (i : Fin n) :
    graphDist M a (p i) = if i.val = 0 then 1 / 2 else 3 / 2 := rfl

@[simp] theorem graphDist_p_b {n : ℕ} (M : ℝ) (i : Fin n) :
    graphDist M (p i) b = M := rfl

@[simp] theorem graphDist_b_p {n : ℕ} (M : ℝ) (i : Fin n) :
    graphDist M b (p i) = M := rfl

@[simp] theorem graphDist_a_b {n : ℕ} (M : ℝ) :
    graphDist (n := n) M a b = M + 1 / 2 := rfl

@[simp] theorem graphDist_b_a {n : ℕ} (M : ℝ) :
    graphDist (n := n) M b a = M + 1 / 2 := rfl

@[simp] theorem graphDist_a_a {n : ℕ} (M : ℝ) :
    graphDist (n := n) M a a = 0 := rfl

@[simp] theorem graphDist_b_b {n : ℕ} (M : ℝ) :
    graphDist (n := n) M b b = 0 := rfl

theorem unitDistance_nonneg {n : ℕ} (i j : Fin n) : 0 ≤ unitDistance i j := by
  unfold unitDistance
  split_ifs <;> norm_num

theorem unitDistance_le_one {n : ℕ} (i j : Fin n) : unitDistance i j ≤ 1 := by
  unfold unitDistance
  split_ifs <;> norm_num

theorem firstDistance_bounds {n : ℕ} (i : Fin n) :
    1 / 2 ≤ firstDistance i ∧ firstDistance i ≤ 3 / 2 := by
  unfold firstDistance
  split_ifs <;> norm_num

@[simp] theorem graphDist_self {n : ℕ} (M : ℝ) (x : Vertex n) :
    graphDist M x x = 0 := by
  rcases x with i | (_ | _) <;> simp [graphDist, unitDistance]

theorem graphDist_comm {n : ℕ} (M : ℝ) (x y : Vertex n) :
    graphDist M x y = graphDist M y x := by
  rcases x with i | (_ | _) <;> rcases y with j | (_ | _) <;>
    simp [graphDist, unitDistance, eq_comm]

/-- The triangle inequality, proved over the finite vertex cases. -/
theorem graphDist_triangle {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (x y z : Vertex n) : graphDist M x z ≤ graphDist M x y + graphDist M y z := by
  rcases x with i | (_ | _) <;>
    rcases y with j | (_ | _) <;>
      rcases z with k | (_ | _) <;>
        simp only [graphDist, unitDistance, firstDistance] <;>
          (try split_ifs) <;> (try simp_all) <;> linarith

theorem graphDist_nonneg {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (x y : Vertex n) :
    0 ≤ graphDist M x y := by
  have h := graphDist_triangle M hM x y x
  rw [graphDist_self, graphDist_comm M y x] at h
  linarith

theorem graphDist_eq_zero_iff {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (x y : Vertex n) :
    graphDist M x y = 0 ↔ x = y := by
  have hMne : M ≠ 0 := by linarith
  rcases x with i | (_ | _) <;> rcases y with j | (_ | _) <;>
    simp [graphDist, unitDistance, firstDistance, hMne] <;>
      (try split_ifs) <;> norm_num at * <;> linarith

/-- The actual finite metric space used in the counterexample. Install this
locally with `letI := metricSpace M hM`. -/
@[reducible] def metricSpace {n : ℕ} (M : ℝ) (hM : 1 ≤ M) : MetricSpace (Vertex n) where
  dist := graphDist M
  dist_self := graphDist_self M
  dist_comm := graphDist_comm M
  dist_triangle := graphDist_triangle M hM
  eq_of_dist_eq_zero := fun h => (graphDist_eq_zero_iff M hM _ _).mp h

@[simp] theorem dist_metricSpace {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (x y : Vertex n) :
    @dist (Vertex n) (metricSpace M hM).toDist x y = graphDist M x y := rfl

/-- The common distance from an original point to a center, outside that
center's exceptional set. -/
def baseline {n : ℕ} (M : ℝ) : Vertex n → ℝ
  | .inl _ => 1
  | .inr false => 3 / 2
  | .inr true => M

/-- Each center has at most one exceptional original point. -/
def exceptional {n : ℕ} : Vertex n → Finset (Fin n)
  | .inl i => {i}
  | .inr false => Finset.univ.filter (fun i => i.val = 0)
  | .inr true => ∅

@[simp] theorem exceptional_p {n : ℕ} (i : Fin n) : exceptional (p i) = {i} := rfl

@[simp] theorem exceptional_a {n : ℕ} :
    exceptional (a : Vertex n) = Finset.univ.filter (fun i => i.val = 0) := rfl

@[simp] theorem exceptional_b {n : ℕ} : exceptional (b : Vertex n) = ∅ := rfl

theorem exceptional_card_le_one {n : ℕ} (v : Vertex n) : (exceptional v).card ≤ 1 := by
  rcases v with i | (_ | _)
  · simp [exceptional]
  · apply Finset.card_le_one.mpr
    intro i hi j hj
    apply Fin.ext
    exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  · simp [exceptional]

theorem one_le_baseline {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (v : Vertex n) :
    1 ≤ baseline M v := by
  rcases v with i | (_ | _) <;> simp only [baseline] <;> linarith

theorem baseline_nonneg {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (v : Vertex n) :
    0 ≤ baseline M v := le_trans (by norm_num) (one_le_baseline M hM v)

/-- Exceptional original points have no larger distance than the common
level of a center. -/
theorem graphDist_le_baseline {n : ℕ} (M : ℝ) (i : Fin n) (v : Vertex n) :
    graphDist M (p i) v ≤ baseline M v := by
  rcases v with j | (_ | _)
  · exact unitDistance_le_one i j
  · exact (firstDistance_bounds i).2
  · exact le_rfl

/-- Outside its at-most-one exception, a center has exactly its common
original-point distance. -/
theorem graphDist_eq_baseline_of_notMem {n : ℕ} (M : ℝ) (i : Fin n) (v : Vertex n)
    (hi : i ∉ exceptional v) : graphDist M (p i) v = baseline M v := by
  rcases v with j | (_ | _)
  · have hij : i ≠ j := by simpa [exceptional] using hi
    simp [graphDist, unitDistance, baseline, hij]
  · have hi0 : i.val ≠ 0 := by simpa [exceptional] using hi
    simp [graphDist, firstDistance, baseline, hi0]
  · rfl

end

end FTC.Counterexample
