import FaultTolerantCoresets.Counterexample.Queries
import FaultTolerantCoresets.Filtering

/-! # Actual cluster-size proxies and one-step maximum filtering -/

open scoped BigOperators

namespace FTC.Counterexample

/-- The reference clustering has one singleton and one cluster with all other
separately indexed entries. -/
def clusterMembers {n : ℕ} (first i : Fin n) : Finset (Fin n) :=
  if i = first then {first} else Finset.univ.erase first

@[simp] theorem card_cluster_first {n : ℕ} (first : Fin n) :
    (clusterMembers first first).card = 1 := by simp [clusterMembers]

theorem card_cluster_other {n : ℕ} (first i : Fin n) (hi : i ≠ first) :
    ((clusterMembers first i).card : ℝ) = (n : ℝ) - 1 := by
  have h := Finset.card_erase_add_one (Finset.mem_univ first)
  have hR : (((Finset.univ : Finset (Fin n)).erase first).card : ℝ) + 1 = (n : ℝ) := by
    have hN : (((Finset.univ : Finset (Fin n)).erase first).card) + 1 = n := by simpa using h
    exact_mod_cast hN
  simp only [clusterMembers, if_neg hi]
  linarith

/-- The usual proxy, with exactly the scaling used in Appendix A.1. -/
noncomputable def proxy {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first : Fin n) (A : Query n) (i : Fin n) : ℝ :=
  2 / ((clusterMembers first i).card : ℝ) +
    2 * corruptContribution M hM bad i A / corruptCost M hM bad A

theorem proxy_first {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first : Fin n) (A : Query n) :
    proxy M hM bad first A first =
      2 + 2 * corruptContribution M hM bad first A / corruptCost M hM bad A := by
  simp [proxy]

theorem proxy_other {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first i : Fin n) (A : Query n) (hi : i ≠ first) :
    proxy M hM bad first A i =
      2 / ((n : ℝ) - 1) +
        2 * corruptContribution M hM bad i A / corruptCost M hM bad A := by
  rw [proxy, card_cluster_other first i hi]

theorem cluster_term_le_proxy {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first i : Fin n) (A : Query n) :
    2 / ((clusterMembers first i).card : ℝ) ≤ proxy M hM bad first A i := by
  have hc : 0 ≤ corruptCost M hM bad A :=
    FTC.cost_nonneg (corruptContribution_nonneg M hM bad) _ _
  have hsecond : 0 ≤ 2 * corruptContribution M hM bad i A / corruptCost M hM bad A :=
    div_nonneg (mul_nonneg (by norm_num) (corruptContribution_nonneg M hM bad i A)) hc
  unfold proxy
  linarith

/-- Ties elsewhere do not matter when the maximizing entry is strict. This
identifies the output of the actual Algorithm 1 function. -/
theorem peel_one_of_strict_max {I : Type*} [DecidableEq I]
    (score : Finset I → I → ℝ) (U : Finset I) (x : I)
    (hx : x ∈ U) (hstrict : ∀ i ∈ U, i ≠ x → score U i < score U x) :
    FTC.peel score 1 U = U.erase x := by
  have hU : U.Nonempty := ⟨x, hx⟩
  have hspec := FTC.chosenMax_spec score U hU
  have hchosen : FTC.chosenMax score U hU = x := by
    by_contra h
    exact (not_lt_of_ge (hspec.2 x hx)) (hstrict _ hspec.1 h)
  simp [FTC.peel, FTC.peelStep, hU, hchosen]

end FTC.Counterexample
