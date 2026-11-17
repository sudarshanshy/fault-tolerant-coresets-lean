import FaultTolerantCoresets.FiniteMetric.WeightedSensitivityReduction
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Appendix B: adjoining the distinguished point

The new point is `none`; old points are `some x`. Any positive upper bound
`D` on the original distances suffices, so the reduction need not compute an
exact diameter or exclude singleton metric spaces.
-/

namespace FTC.Hardness

open FTC.FiniteMetric

variable {X : Type*} [DecidableEq X] [MetricSpace X] {k : ℕ}

def oldPoint : X ↪ Option X := ⟨some, Option.some_injective X⟩

@[simp] theorem oldPoint_apply (x : X) : oldPoint x = some x := rfl

noncomputable def extensionDist (D : ℝ) : Option X → Option X → ℝ
  | none, none => 0
  | none, some _ => D
  | some _, none => D
  | some x, some y => dist x y

/-- The actual metric used by the hardness gadget. -/
@[reducible] noncomputable def extensionMetric (D : ℝ) (hD : 0 < D)
    (hdiam : ∀ x y : X, dist x y ≤ D) : MetricSpace (Option X) where
  dist := extensionDist D
  dist_self x := by cases x <;> simp [extensionDist]
  dist_comm x y := by cases x <;> cases y <;> simp [extensionDist, dist_comm]
  dist_triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp only [extensionDist]
    · norm_num
    · simp
    · linarith
    · rename_i x y
      have := dist_nonneg (x := x) (y := y); linarith
    · simp
    · rename_i x y
      have := hdiam x y; linarith
    · rename_i x y
      have := dist_nonneg (x := x) (y := y); linarith
    · exact dist_triangle _ _ _
  eq_of_dist_eq_zero := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact False.elim (hD.ne' h)
    · exact False.elim (hD.ne' h)
    · exact congrArg some (dist_eq_zero.mp h)

@[simp] theorem extensionDist_old (D : ℝ) (x y : X) :
    extensionDist D (some x) (some y) = dist x y := rfl

@[simp] theorem extensionDist_new_old (D : ℝ) (x : X) :
    extensionDist D none (some x) = D := rfl

omit [DecidableEq X] [MetricSpace X] in
theorem centerSet_ext {C E : CenterSet X k} (h : C.centers = E.centers) : C = E := by
  cases C
  cases E
  cases h
  rfl

/-- Lift an original query without adding a center. -/
def liftCenters (C : CenterSet X k) : CenterSet (Option X) k where
  centers := C.centers.map oldPoint
  card_eq := by simpa using C.card_eq
  nonempty := C.nonempty.map

@[simp] theorem none_not_liftCenters (C : CenterSet X k) :
    none ∉ (liftCenters C).centers := by simp [liftCenters, Finset.mem_map]

@[simp] theorem some_mem_liftCenters (C : CenterSet X k) (x : X) :
    some x ∈ (liftCenters C).centers ↔ x ∈ C.centers := by
  simp [liftCenters, Finset.mem_map]

section Finite

variable [Fintype X]

def oldCenters (C : CenterSet (Option X) k) : Finset X :=
  Finset.univ.filter (fun x => some x ∈ C.centers)

@[simp] theorem mem_oldCenters (C : CenterSet (Option X) k) (x : X) :
    x ∈ oldCenters C ↔ some x ∈ C.centers := by simp [oldCenters]

theorem map_oldCenters (C : CenterSet (Option X) k) (h : none ∉ C.centers) :
    (oldCenters C).map oldPoint = C.centers := by
  ext x
  cases x with
  | none => simp [Finset.mem_map, h]
  | some x => simp [Finset.mem_map]

/-- A query avoiding the new point is precisely an original k-center query. -/
def lowerCenters (C : CenterSet (Option X) k) (h : none ∉ C.centers) : CenterSet X k where
  centers := oldCenters C
  card_eq := by
    have hc := congrArg Finset.card (map_oldCenters C h)
    simpa [C.card_eq] using hc
  nonempty := by
    have hn : ((oldCenters C).map oldPoint).Nonempty :=
      (map_oldCenters C h).symm ▸ C.nonempty
    exact Finset.map_nonempty.mp hn

theorem lift_lowerCenters (C : CenterSet (Option X) k) (h : none ∉ C.centers) :
    liftCenters (lowerCenters C h) = C :=
  centerSet_ext (map_oldCenters C h)

end Finite

/-- Squared-distance loss in the extended metric, kept independent of the
metric-space instance so the numerical formulas have no proof parameters. -/
noncomputable def extensionLoss (D : ℝ) (p : Option X)
    (C : CenterSet (Option X) k) : ℝ :=
  C.centers.inf' C.nonempty (fun x => extensionDist D p x ^ 2)

theorem extensionLoss_nonneg (D : ℝ) (p : Option X) (C : CenterSet (Option X) k) :
    0 ≤ extensionLoss D p C :=
  Finset.le_inf' _ _ (fun _ _ => sq_nonneg _)

theorem extensionLoss_eq_kmeansLoss (D : ℝ) (hD : 0 < D)
    (hdiam : ∀ x y : X, dist x y ≤ D) (p : Option X) (C : CenterSet (Option X) k) :
    letI := extensionMetric D hD hdiam
    extensionLoss D p C = kmeansLoss p C := rfl

@[simp] theorem extensionLoss_old_lift (D : ℝ) (p : X) (C : CenterSet X k) :
    extensionLoss D (some p) (liftCenters C) = kmeansLoss p C := by
  simp [extensionLoss, liftCenters, Finset.inf'_map, extensionDist, kmeansLoss]

@[simp] theorem extensionLoss_new_lift (D : ℝ) (C : CenterSet X k) :
    extensionLoss D none (liftCenters C) = D ^ 2 := by
  simp [extensionLoss, liftCenters, Finset.inf'_map, extensionDist]

theorem extensionLoss_new_of_mem (D : ℝ) (C : CenterSet (Option X) k)
    (h : none ∈ C.centers) : extensionLoss D none C = 0 := by
  apply le_antisymm
  · change C.centers.inf' C.nonempty (fun x => extensionDist D none x ^ 2) ≤ 0
    calc
      _ ≤ extensionDist D none none ^ 2 := Finset.inf'_le _ h
      _ = 0 := by simp [extensionDist]
  · exact extensionLoss_nonneg D none C

/-- One old entry per original client, plus the single distinguished entry. -/
def extendedClients (P : Finset X) : Finset (Option X) :=
  insert none (P.map oldPoint)

@[simp] theorem none_mem_extendedClients (P : Finset X) : none ∈ extendedClients P := by
  simp [extendedClients]

@[simp] theorem extendedClients_card (P : Finset X) : (extendedClients P).card = P.card + 1 := by
  simp [extendedClients, Finset.mem_map]

/-- Old clients have weight L, while the distinguished point has weight one. -/
noncomputable def gadgetContribution (D L : ℝ) : Option X → CenterSet (Option X) k → ℝ
  | none, C => extensionLoss D none C
  | some x, C => L * extensionLoss D (some x) C

theorem gadgetContribution_nonneg (D : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∀ i (C : CenterSet (Option X) k), 0 ≤ gadgetContribution D L i C := by
  intro i C
  cases i
  · exact extensionLoss_nonneg D none C
  · exact mul_nonneg hL (extensionLoss_nonneg D _ C)

def gadgetEntries (L : ℝ) (hL : 0 ≤ L) : Option X → Entry (Option X)
  | none => ⟨none, 1, by norm_num⟩
  | some x => ⟨some x, L, hL⟩

theorem gadgetContribution_eq_weightedLoss (D : ℝ) (hD : 0 < D)
    (hdiam : ∀ x y : X, dist x y ≤ D) {L : ℝ} (hL : 0 ≤ L) :
    letI := extensionMetric D hD hdiam
    gadgetContribution (X := X) (k := k) D L = weightedLoss (gadgetEntries L hL) := by
  letI := extensionMetric D hD hdiam
  funext i C
  cases i <;> simp only [gadgetContribution, weightedLoss, contribution, gadgetEntries, one_mul]
  all_goals rfl

@[simp] theorem gadgetCost_lift (P : Finset X) (D L : ℝ) (C : CenterSet X k) :
    cost (gadgetContribution D L) (extendedClients P) (liftCenters C) =
      D ^ 2 + L * cost kmeansLoss P C := by
  simp [cost, extendedClients, Finset.sum_insert, Finset.mem_map,
    gadgetContribution, Finset.sum_map, ← Finset.mul_sum]

end FTC.Hardness
