import FaultTolerantCoresets.Basic
import FaultTolerantCoresets.Selection
import Mathlib.Data.Finset.Max

/-!
# Iterative maximum-score filtering

`peel` is Algorithm 1 parameterized by its score function. Real-valued scores and
their maxima are mathematical (noncomputable) objects. The proof applies to any
implementation that returns a maximum with the specified oracle guarantees.
The function stops if its active set becomes empty.
-/

namespace FTC

variable {I : Type*} [DecidableEq I]

noncomputable def chosenMax (score : Finset I → I → ℝ) (Q : Finset I)
    (h : Q.Nonempty) : I :=
  Classical.choose (Q.exists_max_image (score Q) h)

theorem chosenMax_spec (score : Finset I → I → ℝ) (Q : Finset I)
    (h : Q.Nonempty) :
    chosenMax score Q h ∈ Q ∧
      ∀ y ∈ Q, score Q y ≤ score Q (chosenMax score Q h) :=
  Classical.choose_spec (Q.exists_max_image (score Q) h)

/-- The classical real maximizer as an explicit selection routine. -/
noncomputable def classicalSelectionRule (score : Finset I → I → ℝ) : SelectionRule I where
  select := chosenMax score
  select_mem := fun Q h => (chosenMax_spec score Q h).1

theorem classicalSelectionRule_isMaxFor (score : Finset I → I → ℝ) :
    (classicalSelectionRule score).IsMaxFor score :=
  fun Q h => (chosenMax_spec score Q h).2

noncomputable def peelStep (score : Finset I → I → ℝ) (Q : Finset I) : Finset I :=
  if h : Q.Nonempty then Q.erase (chosenMax score Q h) else Q

noncomputable def peel (score : Finset I → I → ℝ) : ℕ → Finset I → Finset I
  | 0, Q => Q
  | n + 1, Q => peel score n (peelStep score Q)

theorem peel_eq_selectionRun (score : Finset I → I → ℝ) (n : ℕ) (Q : Finset I) :
    peel score n Q = selectionRun (classicalSelectionRule score) n Q := by
  induction n generalizing Q with
  | zero => rfl
  | succ n ih =>
    simpa [peel, selectionRun, peelStep, selectionStep, classicalSelectionRule] using
      (ih (peelStep score Q))

theorem peelStep_removes (score : Finset I → I → ℝ) {Q : Finset I}
    (h : Q.Nonempty) :
    ∃ g ∈ Q, peelStep score Q = Q.erase g ∧ ∀ y ∈ Q, score Q y ≤ score Q g := by
  refine ⟨chosenMax score Q h, (chosenMax_spec score Q h).1, ?_,
    (chosenMax_spec score Q h).2⟩
  simp [peelStep, h]

theorem peelStep_subset (score : Finset I → I → ℝ) (Q : Finset I) :
    peelStep score Q ⊆ Q := by
  unfold peelStep
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

theorem card_le_peelStep_add_one (score : Finset I → I → ℝ) (Q : Finset I) :
    Q.card ≤ (peelStep score Q).card + 1 := by
  by_cases h : Q.Nonempty
  · obtain ⟨g, hg, hstep, _⟩ := peelStep_removes score h
    rw [hstep]
    have := Finset.card_erase_add_one hg
    omega
  · simp [peelStep, h]

theorem card_peelStep_add_one (score : Finset I → I → ℝ) {Q : Finset I}
    (h : Q.Nonempty) : (peelStep score Q).card + 1 = Q.card := by
  obtain ⟨g, hg, hstep, _⟩ := peelStep_removes score h
  rw [hstep]
  exact Finset.card_erase_add_one hg

theorem peel_subset (score : Finset I → I → ℝ) (n : ℕ) (Q : Finset I) :
    peel score n Q ⊆ Q := by
  induction n generalizing Q with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (ih _).trans (peelStep_subset score Q)

theorem peel_add (score : Finset I → I → ℝ) (n m : ℕ) (Q : Finset I) :
    peel score (n + m) Q = peel score m (peel score n Q) := by
  induction n generalizing Q with
  | zero => simp [peel]
  | succ n ih => simpa [Nat.succ_add, peel] using ih (peelStep score Q)

theorem peel_antitone (score : Finset I → I → ℝ) {n m : ℕ} (h : n ≤ m)
    (Q : Finset I) : peel score m Q ⊆ peel score n Q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [peel_add]
  exact peel_subset score d _

theorem card_le_peel_add (score : Finset I → I → ℝ) (n : ℕ) (Q : Finset I) :
    Q.card ≤ (peel score n Q).card + n := by
  induction n generalizing Q with
  | zero => simp [peel]
  | succ n ih =>
    have h := ih (peelStep score Q)
    have hstep := card_le_peelStep_add_one score Q
    change Q.card ≤ (peel score n (peelStep score Q)).card + (n + 1)
    omega

theorem card_peel_add_of_nonempty (score : Finset I → I → ℝ) (n : ℕ)
    (Q : Finset I) (h : (peel score n Q).Nonempty) :
    (peel score n Q).card + n = Q.card := by
  induction n generalizing Q with
  | zero => simp [peel]
  | succ n ih =>
    have hs : (peelStep score Q).Nonempty := h.mono (peel_subset score n _)
    have hq : Q.Nonempty := hs.mono (peelStep_subset score Q)
    have hcard := card_peelStep_add_one score hq
    have hind := ih (peelStep score Q) h
    change (peel score n (peelStep score Q)).card + (n + 1) = Q.card
    omega

theorem removed_card_le (score : Finset I → I → ℝ) (n : ℕ) (Q : Finset I) :
    (Q \ peel score n Q).card ≤ n := by
  rw [Finset.card_sdiff_of_subset (peel_subset score n Q)]
  have := card_le_peel_add score n Q
  omega

theorem removed_card_eq_of_nonempty (score : Finset I → I → ℝ) (n : ℕ)
    (Q : Finset I) (h : (peel score n Q).Nonempty) :
    (Q \ peel score n Q).card = n := by
  rw [Finset.card_sdiff_of_subset (peel_subset score n Q)]
  have := card_peel_add_of_nonempty score n Q h
  omega

/-- Every removed index was a maximum at an actual stage of the algorithm. -/
theorem removed_has_stage (score : Finset I → I → ℝ) {n : ℕ} {Q : Finset I}
    {x : I} (hx : x ∈ Q) (hgone : x ∉ peel score n Q) :
    ∃ t < n, x ∈ peel score t Q ∧
      ∀ y ∈ peel score t Q, score (peel score t Q) y ≤ score (peel score t Q) x := by
  induction n generalizing Q with
  | zero => exact False.elim (hgone hx)
  | succ n ih =>
    by_cases hs : x ∈ peelStep score Q
    · obtain ⟨t, ht, hxt, hmax⟩ := ih hs hgone
      refine ⟨t + 1, by omega, ?_, ?_⟩
      · simpa [peel] using hxt
      · simpa [peel] using hmax
    · obtain ⟨g, hg, hstep, hmax⟩ := peelStep_removes score ⟨x, hx⟩
      have heq : x = g := by
        by_contra hne
        exact hs (hstep.symm ▸ Finset.mem_erase.mpr ⟨hne, hx⟩)
      subst x
      exact ⟨0, Nat.zero_lt_succ n, hg, hmax⟩

/-- If a bad index survives `f` deletions, a good maximum was deleted earlier. -/
theorem good_stage_of_bad_remaining (score : Finset I → I → ℝ)
    (U B : Finset I) (f : ℕ) (hB : B.card ≤ f)
    (hbad : (peel score f U ∩ B).Nonempty) :
    ∃ t < f, ∃ g ∈ peel score t U, g ∉ B ∧
      ∀ y ∈ peel score t U, score (peel score t U) y ≤ score (peel score t U) g := by
  let R := peel score f U
  obtain ⟨b, hb⟩ := hbad
  have hbR : b ∈ R := (Finset.mem_inter.mp hb).1
  have hbB : b ∈ B := (Finset.mem_inter.mp hb).2
  have hcard : (U \ R).card = f := removed_card_eq_of_nonempty score f U ⟨b, hbR⟩
  have hex : ∃ g ∈ U \ R, g ∉ B := by
    by_contra h
    have hsub : insert b (U \ R) ⊆ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbB
      · by_contra hxB
        exact h ⟨x, hx, hxB⟩
    have hbnot : b ∉ U \ R := by simp [hbR]
    have hlarge := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hbnot, hcard] at hlarge
    omega
  obtain ⟨g, hg, hgB⟩ := hex
  obtain ⟨hgU, hgR⟩ := Finset.mem_sdiff.mp hg
  obtain ⟨t, ht, hgt, hmax⟩ := removed_has_stage score hgU hgR
  exact ⟨t, ht, g, hgt, hgB, hmax⟩

end FTC
