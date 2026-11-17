import FaultTolerantCoresets.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Pointwise sensitivity of indexed summaries

The supremum is taken over individual weighted contributions, so two entries
with the same point and weight still have distinct indices.  A zero-cost query
has ratio zero (`Real.div`'s convention); the API proves that its individual
contributions are also zero.  Adjoining zero handles an empty solution type
without any nonemptiness hypothesis.
-/

namespace FTC

variable {I S : Type*} [DecidableEq I]

/-- Ratios defining the sensitivity, together with zero. -/
def sensitivityRatios (c : I → S → ℝ) (Q : Finset I) (i : I) : Set ℝ :=
  insert 0 (Set.range fun s : S => c i s / cost c Q s)

/-- Exact sensitivity of an entry; an inactive index has sensitivity zero. -/
noncomputable def sensitivity (c : I → S → ℝ) (Q : Finset I) (i : I) : ℝ :=
  if i ∈ Q then sSup (sensitivityRatios c Q i) else 0

variable {c : I → S → ℝ}

theorem contribution_ratio_le_one (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} (hi : i ∈ Q) (s : S) :
    c i s / cost c Q s ≤ 1 := by
  by_cases hz : cost c Q s = 0
  · simp [hz]
  · have hpos : 0 < cost c Q s := lt_of_le_of_ne (cost_nonneg hc Q s) (Ne.symm hz)
    exact (div_le_one hpos).2 (contribution_le_cost hc hi s)

theorem sensitivityRatios_bddAbove (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} (hi : i ∈ Q) :
    BddAbove (sensitivityRatios c Q i) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases hx with rfl | ⟨s, rfl⟩
  · norm_num
  · exact contribution_ratio_le_one hc hi s

theorem sensitivityRatios_nonempty (c : I → S → ℝ) (Q : Finset I) (i : I) :
    (sensitivityRatios c Q i).Nonempty :=
  ⟨0, by simp [sensitivityRatios]⟩

theorem sensitivity_nonneg (hc : ∀ i s, 0 ≤ c i s) (Q : Finset I) (i : I) :
    0 ≤ sensitivity c Q i := by
  by_cases hi : i ∈ Q
  · rw [sensitivity, if_pos hi]
    exact le_csSup (sensitivityRatios_bddAbove hc hi) (by simp [sensitivityRatios])
  · simp [sensitivity, hi]

theorem sensitivity_le_one (hc : ∀ i s, 0 ≤ c i s) (Q : Finset I) (i : I) :
    sensitivity c Q i ≤ 1 := by
  by_cases hi : i ∈ Q
  · rw [sensitivity, if_pos hi]
    apply csSup_le (sensitivityRatios_nonempty c Q i)
    intro x hx
    rcases hx with rfl | ⟨s, rfl⟩
    · norm_num
    · exact contribution_ratio_le_one hc hi s
  · simp [sensitivity, hi]

@[simp] theorem sensitivity_of_not_mem {Q : Finset I} {i : I} (hi : i ∉ Q) :
    sensitivity c Q i = 0 := by
  simp [sensitivity, hi]

/-- The sensitivity controls a contribution even for a zero-cost query. -/
theorem contribution_le_sensitivity_mul_cost (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} (hi : i ∈ Q) (s : S) :
    c i s ≤ sensitivity c Q i * cost c Q s := by
  by_cases hz : cost c Q s = 0
  · have hci : c i s = 0 := cost_eq_zero_contribution hc hi hz
    simp [hz, hci]
  · have hpos : 0 < cost c Q s := lt_of_le_of_ne (cost_nonneg hc Q s) (Ne.symm hz)
    apply (div_le_iff₀ hpos).1
    rw [sensitivity, if_pos hi]
    exact le_csSup (sensitivityRatios_bddAbove hc hi)
      (by exact Or.inr ⟨s, rfl⟩)

/-- A uniform contribution bound gives an upper bound on the exact supremum. -/
theorem sensitivity_le_of_contribution_le (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} {r : ℝ} (hi : i ∈ Q) (hr : 0 ≤ r)
    (hbound : ∀ s, c i s ≤ r * cost c Q s) :
    sensitivity c Q i ≤ r := by
  rw [sensitivity, if_pos hi]
  apply csSup_le (sensitivityRatios_nonempty c Q i)
  intro x hx
  rcases hx with rfl | ⟨s, rfl⟩
  · exact hr
  · by_cases hz : cost c Q s = 0
    · simpa [hz] using hr
    · have hpos : 0 < cost c Q s :=
        lt_of_le_of_ne (cost_nonneg hc Q s) (Ne.symm hz)
      exact (div_le_iff₀ hpos).2 (hbound s)

/-- The useful form for a good sampled entry during filtering: a per-entry
bound relative to the input, and a lower bound for the current summary, suffice. -/
theorem sensitivity_le_of_reference_bound (hc : ∀ i s, 0 ≤ c i s)
    {Q : Finset I} {i : I} {reference : S → ℝ} {δ β : ℝ}
    (hi : i ∈ Q) (hδ : 0 ≤ δ) (hβ : 0 < β)
    (hentry : ∀ s, c i s ≤ δ * reference s)
    (hcost : ∀ s, β * reference s ≤ cost c Q s) :
    sensitivity c Q i ≤ δ / β := by
  apply sensitivity_le_of_contribution_le hc hi (div_nonneg hδ hβ.le)
  intro s
  calc
    c i s ≤ δ * reference s := hentry s
    _ = (δ / β) * (β * reference s) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hβ.ne']
    _ ≤ (δ / β) * cost c Q s :=
      mul_le_mul_of_nonneg_left (hcost s) (div_nonneg hδ hβ.le)

/-- Removing entries can only increase the sensitivity of an entry retained. -/
theorem sensitivity_mono_denominator (hc : ∀ i s, 0 ≤ c i s)
    {Q R : Finset I} {i : I} (hQR : Q ⊆ R) (hi : i ∈ Q) :
    sensitivity c R i ≤ sensitivity c Q i := by
  apply sensitivity_le_of_contribution_le hc (hQR hi) (sensitivity_nonneg hc Q i)
  intro s
  exact (contribution_le_sensitivity_mul_cost hc hi s).trans
    (mul_le_mul_of_nonneg_left (cost_mono hc hQR s) (sensitivity_nonneg hc Q i))

/-- An `α`-approximate oracle, in the multiplicative form used in the peeling
proof. For positive `α`, `lower` is equivalent to `σ / α ≤ score`. -/
structure ApproxSensitivityOracle (c : I → S → ℝ) (α : ℝ) where
  score : Finset I → I → ℝ
  lower : ∀ (Q : Finset I) (i : I), i ∈ Q → sensitivity c Q i ≤ α * score Q i
  upper : ∀ (Q : Finset I) (i : I), i ∈ Q → score Q i ≤ sensitivity c Q i

theorem ApproxSensitivityOracle.div_le_score {α : ℝ}
    (oracle : ApproxSensitivityOracle c α) (hα : 0 < α)
    {Q : Finset I} {i : I} (hi : i ∈ Q) :
    sensitivity c Q i / α ≤ oracle.score Q i := by
  apply (div_le_iff₀ hα).2
  simpa [mul_comm] using oracle.lower Q i hi

theorem ApproxSensitivityOracle.score_nonneg {α : ℝ}
    (oracle : ApproxSensitivityOracle c α) (hc : ∀ i s, 0 ≤ c i s)
    (hα : 0 < α) {Q : Finset I} {i : I} (hi : i ∈ Q) :
    0 ≤ oracle.score Q i :=
  (div_nonneg (sensitivity_nonneg hc Q i) hα.le).trans
    (oracle.div_le_score hα hi)

/-- Exact sensitivity is an oracle with approximation factor one. -/
noncomputable def exactSensitivityOracle (c : I → S → ℝ) :
    ApproxSensitivityOracle c 1 where
  score := sensitivity c
  lower := by intros; simp
  upper := by intros; exact le_rfl

end FTC
