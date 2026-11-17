import FaultTolerantCoresets.Counterexample.Metric
import FaultTolerantCoresets.FiniteMetric.SensitivityReduction

/-! # Actual two-center Euclidean-free metric queries and indexed summaries -/

open scoped BigOperators

namespace FTC.Counterexample

abbrev Query (n : ℕ) := FTC.FiniteMetric.CenterSet (Vertex n) 2

noncomputable def pointLoss {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (x : Vertex n) (S : Query n) : ℝ := by
  letI : MetricSpace (Vertex n) := metricSpace M hM
  exact FTC.FiniteMetric.kmeansLoss x S

/-- A query consists of exactly two distinct vertices. -/
def pairQuery {n : ℕ} (x y : Vertex n) (hxy : x ≠ y) : Query n where
  centers := {x, y}
  card_eq := by simp [hxy]
  nonempty := by simp

@[simp] theorem pointLoss_eq_inf {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (x : Vertex n) (S : Query n) :
    pointLoss M hM x S = S.centers.inf' S.nonempty (fun y => graphDist M x y ^ 2) := rfl

theorem pointLoss_nonneg {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (x : Vertex n) (S : Query n) : 0 ≤ pointLoss M hM x S := by
  rw [pointLoss_eq_inf]
  apply Finset.le_inf'
  intro y _
  exact sq_nonneg _

@[simp] theorem pointLoss_pair {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (z x y : Vertex n) (hxy : x ≠ y) :
    pointLoss M hM z (pairQuery x y hxy) =
      min (graphDist M z x ^ 2) (graphDist M z y ^ 2) := by
  rw [pointLoss_eq_inf]
  apply le_antisymm
  · apply le_min
    · exact Finset.inf'_le _ (by simp [pairQuery])
    · exact Finset.inf'_le _ (by simp [pairQuery])
  · apply Finset.le_inf'
    intro v hv
    simp only [pairQuery, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- The clean coreset is the whole input, with one separately indexed unit
entry at each original point. -/
def cleanEntries {n : ℕ} (i : Fin n) : FTC.Entry (Vertex n) where
  point := p i
  weight := 1
  weight_nonneg := by norm_num

/-- Move just the entry with index `bad` to `b`; keep its unit weight. -/
def corruptedEntries {n : ℕ} (bad i : Fin n) : FTC.Entry (Vertex n) where
  point := if i = bad then b else p i
  weight := 1
  weight_nonneg := by norm_num

noncomputable def cleanContribution {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i : Fin n) (S : Query n) : ℝ :=
  FTC.contribution (pointLoss M hM) cleanEntries i S

noncomputable def corruptContribution {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad i : Fin n) (S : Query n) : ℝ :=
  FTC.contribution (pointLoss M hM) (corruptedEntries bad) i S

@[simp] theorem cleanContribution_apply {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i : Fin n) (S : Query n) : cleanContribution M hM i S = pointLoss M hM (p i) S := by
  simp [cleanContribution, FTC.contribution, cleanEntries]

@[simp] theorem corruptContribution_apply {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad i : Fin n) (S : Query n) :
    corruptContribution M hM bad i S =
      if i = bad then pointLoss M hM b S else pointLoss M hM (p i) S := by
  by_cases hi : i = bad <;> simp [corruptContribution, FTC.contribution, corruptedEntries, hi]

noncomputable def cleanCost {n : ℕ} (M : ℝ) (hM : 1 ≤ M) (S : Query n) : ℝ :=
  FTC.cost (cleanContribution M hM) Finset.univ S

noncomputable def corruptCost {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad : Fin n) (S : Query n) : ℝ :=
  FTC.cost (corruptContribution M hM bad) Finset.univ S

theorem cleanContribution_nonneg {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (i : Fin n) (S : Query n) : 0 ≤ cleanContribution M hM i S := by
  simp only [cleanContribution_apply]
  exact pointLoss_nonneg M hM _ _

theorem corruptContribution_nonneg {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad i : Fin n) (S : Query n) : 0 ≤ corruptContribution M hM bad i S := by
  simp only [corruptContribution_apply]
  split_ifs <;> exact pointLoss_nonneg M hM _ _

end FTC.Counterexample
