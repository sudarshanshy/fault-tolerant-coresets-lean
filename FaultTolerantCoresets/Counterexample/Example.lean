import FaultTolerantCoresets.Counterexample.ProxyReference
import FaultTolerantCoresets.Corruption
import Mathlib.Analysis.Real.Sqrt

/-!
# Full Appendix A.1 proxy-decoder counterexample

The public construction `appendix_A1_counterexample` supplies an actual finite
metric, indexed unit-weight clean/corrupted summaries, all-query sensitivity
bounds, an actual factor-two reference clustering and its cluster-size proxies,
and the outputs of the actual one-step filtering functions. Only the scalar
inequalities are reused from `CounterexampleArithmetic`; their metric and
query hypotheses are discharged in the preceding modules.
-/

namespace FTC.Counterexample

open FTC.CounterexampleArithmetic

noncomputable def proxyScore {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (bad first : Fin n) (A : Query n) : Finset (Fin n) → Fin n → ℝ :=
  fun _ i => proxy M hM bad first A i

theorem corruption_one {n : ℕ} (bad : Fin n) :
    FTC.IsFCorruption 1 Finset.univ cleanEntries (corruptedEntries bad) := by
  refine ⟨{bad}, by simp, by simp, ?_⟩
  intro i _ hi
  have hib : i ≠ bad := by simpa using hi
  simp [corruptedEntries, cleanEntries, hib]

theorem clean_is_exact {n : ℕ} (M : ℝ) (hM : 1 ≤ M) :
    FTC.IsCoreset 0 (cleanCost (n := n) M hM)
      (FTC.cost (cleanContribution M hM) Finset.univ) := by
  intro S
  simp [cleanCost]

theorem proxy_peel_output {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j : Fin n)
    (hfirst : first.val = 0) (hj : j.val ≠ 0) (hbad : bad.val ≠ 0) (hbj : bad ≠ j) :
    FTC.peel (proxyScore M hM bad first (referenceQuery j)) 1 Finset.univ =
      Finset.univ.erase first := by
  apply peel_one_of_strict_max _ _ first (Finset.mem_univ first)
  intro i _ hi
  exact proxy_strict_max M hM hn hM2 bad first j i hfirst hj hbad hbj hi

theorem exact_peel_output {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hn : 8 ≤ n) (hM2 : M ^ 2 = (n : ℝ) - 4)
    (bad j l : Fin n) (hjl : j ≠ l) (hbj : bad ≠ j) (hbl : bad ≠ l) :
    FTC.peel (FTC.sensitivity (corruptContribution M hM bad)) 1 Finset.univ =
      Finset.univ.erase bad := by
  apply peel_one_of_strict_max _ _ bad (Finset.mem_univ bad)
  intro i _ hi
  exact corruption_strict_sensitivity_max M hM hn hM2 bad j l hjl hbj hbl i hi

/-- Exact distortion at the explicit query `{p_j,p_l}` after proxy deletion. -/
theorem proxy_output_distortion {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j l : Fin n) (hjl : j ≠ l)
    (hbj : bad ≠ j) (hbl : bad ≠ l) (hfb : first ≠ bad)
    (hfj : first ≠ j) (hfl : first ≠ l) :
    FTC.cost (corruptContribution M hM bad) (Finset.univ.erase first)
        (simplexQuery j l hjl) / cleanCost M hM (simplexQuery j l hjl) =
      wrongDistortion (n : ℝ) := by
  rw [cost_erase_first_simplex M hM bad first j l hjl hbj hbl hfb hfj hfl,
    cleanCost_simplex, hM2]
  unfold wrongDistortion
  congr 1
  ring

theorem proxy_output_not_coreset {n : ℕ} (M : ℝ) (hM : 1 ≤ M)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hn : 8 / ε ≤ (n : ℝ))
    (hM2 : M ^ 2 = (n : ℝ) - 4) (bad first j l : Fin n) (hjl : j ≠ l)
    (hbj : bad ≠ j) (hbl : bad ≠ l) (hfb : first ≠ bad)
    (hfj : first ≠ j) (hfl : first ≠ l) :
    ¬ FTC.IsCoreset (6 * ε) (cleanCost M hM)
      (FTC.cost (corruptContribution M hM bad) (Finset.univ.erase first)) := by
  intro hco
  have hn8 := size_ge_eight hε hεsmall hn
  have hcpos : 0 < cleanCost M hM (simplexQuery j l hjl) := by
    rw [cleanCost_simplex]
    linarith
  have hratio := proxy_output_distortion M hM hM2 bad first j l hjl hbj hbl hfb hfj hfl
  have hgt := wrongDistortion_gt_tolerance hε hεsmall hn
  rw [← hratio] at hgt
  have hcostgt := (lt_div_iff₀ hcpos).mp hgt
  exact (not_le_of_gt hcostgt) (hco (simplexQuery j l hjl)).2

/-- All claims of the unnumbered Appendix A.1 counterexample, for one size.
The carrier is the actual finite metric `Vertex n` with `metricSpace M one_le_M`;
all costs and both decoders below operate on its actual two-center queries. -/
structure ProxyFailureAtSize (n : ℕ) (ε : ℝ) where
  M : ℝ
  one_le_M : 1 ≤ M
  M_sq : M ^ 2 = (n : ℝ) - 4
  bad : Fin n
  first : Fin n
  j : Fin n
  first_zero : first.val = 0
  j_nonzero : j.val ≠ 0
  bad_nonzero : bad.val ≠ 0
  singleton_genuine : first ≠ bad
  initial_exact : FTC.IsCoreset 0 (cleanCost (n := n) M one_le_M)
    (FTC.cost (cleanContribution M one_le_M) Finset.univ)
  admissible_corruption : FTC.IsFCorruption 1 Finset.univ cleanEntries (corruptedEntries bad)
  clean_sensitivity : ∀ i : Fin n,
    FTC.sensitivity (cleanContribution M one_le_M) Finset.univ i = 1 / ((n : ℝ) - 2)
  good_sensitivity : ∀ i : Fin n, i ≠ bad →
    FTC.sensitivity (corruptContribution M one_le_M bad) Finset.univ i ≤ 1 / ((n : ℝ) - 3)
  reference_cost : corruptCost M one_le_M bad (referenceQuery j) = referenceCost (n : ℝ)
  reference_two_approx : ∀ S : Query n,
    corruptCost M one_le_M bad (referenceQuery j) ≤ 2 * corruptCost M one_le_M bad S
  reference_nearest : ∀ i : Fin n,
    if i = first then graphDist M (corruptedEntries bad i).point a <
      graphDist M (corruptedEntries bad i).point (p j)
    else graphDist M (corruptedEntries bad i).point (p j) <
      graphDist M (corruptedEntries bad i).point a
  proxy_valid : ∀ i : Fin n,
    FTC.sensitivity (corruptContribution M one_le_M bad) Finset.univ i ≤
      proxy M one_le_M bad first (referenceQuery j) i
  proxy_unique_max : ∀ i : Fin n, i ≠ first →
    proxy M one_le_M bad first (referenceQuery j) i <
      proxy M one_le_M bad first (referenceQuery j) first
  exact_unique_max : ∀ i : Fin n, i ≠ bad →
    FTC.sensitivity (corruptContribution M one_le_M bad) Finset.univ i <
      FTC.sensitivity (corruptContribution M one_le_M bad) Finset.univ bad
  proxy_output : FTC.peel (proxyScore M one_le_M bad first (referenceQuery j)) 1 Finset.univ =
    Finset.univ.erase first
  exact_output : FTC.peel (FTC.sensitivity (corruptContribution M one_le_M bad)) 1 Finset.univ =
    Finset.univ.erase bad
  proxy_distortion : ∃ S : Query n,
    FTC.cost (corruptContribution M one_le_M bad) (Finset.univ.erase first) S /
      cleanCost M one_le_M S = wrongDistortion (n : ℝ)
  proxy_fails : ¬ FTC.IsCoreset (6 * ε) (cleanCost M one_le_M)
    (FTC.cost (corruptContribution M one_le_M bad)
      (FTC.peel (proxyScore M one_le_M bad first (referenceQuery j)) 1 Finset.univ))
  exact_succeeds : FTC.IsCoreset ε (cleanCost M one_le_M)
    (FTC.cost (corruptContribution M one_le_M bad)
      (FTC.peel (FTC.sensitivity (corruptContribution M one_le_M bad)) 1 Finset.univ))

/-- Full counterexample for every parameter choice in the source PDF.
`M = sqrt(n-4)`, `first = 0`, reference center `j = 1`, witness's other center
`l = 2`, and the corrupted index `bad = n-1` discharge all construction
hypotheses. There are no assumed metric, sensitivity, or decoder claims. -/
theorem appendix_A1_counterexample {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 10) (hn : 8 / ε ≤ (n : ℝ)) :
    Nonempty (ProxyFailureAtSize n ε) := by
  have hnR : (8 : ℝ) ≤ (n : ℝ) := size_ge_eight hε hεsmall hn
  have hn8 : 8 ≤ n := by exact_mod_cast hnR
  let M : ℝ := Real.sqrt ((n : ℝ) - 4)
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM2 : M ^ 2 = (n : ℝ) - 4 := Real.sq_sqrt (by linarith)
  have hM : 1 ≤ M := by nlinarith
  let first : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let l : Fin n := ⟨2, by omega⟩
  let bad : Fin n := ⟨n - 1, by omega⟩
  have hf : first.val = 0 := rfl
  have hj : j.val ≠ 0 := by norm_num [j]
  have hb : bad.val ≠ 0 := by dsimp [bad]; omega
  have hjl : j ≠ l := by intro h; have := congrArg Fin.val h; norm_num [j, l] at this
  have hbj : bad ≠ j := by intro h; have := congrArg Fin.val h; dsimp [bad, j] at this; omega
  have hbl : bad ≠ l := by intro h; have := congrArg Fin.val h; dsimp [bad, l] at this; omega
  have hfb : first ≠ bad := by intro h; have := congrArg Fin.val h; dsimp [first, bad] at this; omega
  have hfj : first ≠ j := by intro h; have := congrArg Fin.val h; norm_num [first, j] at this
  have hfl : first ≠ l := by intro h; have := congrArg Fin.val h; norm_num [first, l] at this
  have hpout := proxy_peel_output M hM hn8 hM2 bad first j hf hj hb hbj
  have heout := exact_peel_output M hM hn8 hM2 bad j l hjl hbj hbl
  refine ⟨{
    M := M, one_le_M := hM, M_sq := hM2,
    bad := bad, first := first, j := j,
    first_zero := hf, j_nonzero := hj, bad_nonzero := hb, singleton_genuine := hfb,
    initial_exact := clean_is_exact M hM,
    admissible_corruption := corruption_one bad,
    clean_sensitivity := clean_sensitivity_eq M hM (by omega),
    good_sensitivity := fun i hi => corrupt_good_sensitivity_le M hM (by omega) bad i hi,
    reference_cost := reference_cost_formula M hM hM2 bad first j hf hj hb hbj,
    reference_two_approx := reference_is_two_approx M hM hn8 hM2 bad first j hf hj hb hbj,
    reference_nearest := reference_assignment_nearest M bad first j hf hj hb,
    proxy_valid := fun i => sensitivity_le_proxy M hM hn8 hM2 bad first j i hf hj hb hbj,
    proxy_unique_max := fun i hi => proxy_strict_max M hM hn8 hM2 bad first j i hf hj hb hbj hi,
    exact_unique_max := fun i hi => corruption_strict_sensitivity_max M hM hn8 hM2 bad j l hjl hbj hbl i hi,
    proxy_output := hpout, exact_output := heout,
    proxy_distortion := ⟨simplexQuery j l hjl,
      proxy_output_distortion M hM hM2 bad first j l hjl hbj hbl hfb hfj hfl⟩,
    proxy_fails := ?_, exact_succeeds := ?_ }⟩
  · rw [hpout]
    exact proxy_output_not_coreset M hM ε hε hεsmall hn hM2 bad first j l hjl hbj hbl hfb hfj hfl
  · rw [heout]
    exact exact_deletion_isCoreset M hM (by omega) bad ε hε.le
      (distortion_and_deletion_bounds hε hεsmall hn).2.2

end FTC.Counterexample
