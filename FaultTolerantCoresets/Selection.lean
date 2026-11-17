import FaultTolerantCoresets.Basic

/-!
# Filtering with an explicit selection routine

The routine is data: it selects an active index from every nonempty active set.
Maximality is a separate proof obligation. This keeps the implementation free
of real suprema and classical choice, while allowing the same correctness proof
to cover both the mathematical decoder and executable rational decoders.
-/

namespace FTC

variable {I : Type*} [DecidableEq I]

structure SelectionRule (I : Type*) [DecidableEq I] where
  select : (Q : Finset I) → Q.Nonempty → I
  select_mem : ∀ Q h, select Q h ∈ Q

def SelectionRule.IsMaxFor (rule : SelectionRule I) (score : Finset I → I → ℝ) : Prop :=
  ∀ Q h, ∀ y ∈ Q, score Q y ≤ score Q (rule.select Q h)

def selectionStep (rule : SelectionRule I) (Q : Finset I) : Finset I :=
  if h : Q.Nonempty then Q.erase (rule.select Q h) else Q

def selectionRun (rule : SelectionRule I) : ℕ → Finset I → Finset I
  | 0, Q => Q
  | n + 1, Q => selectionRun rule n (selectionStep rule Q)

theorem selectionStep_spec (rule : SelectionRule I) {Q : Finset I}
    (h : Q.Nonempty) :
    ∃ g ∈ Q, selectionStep rule Q = Q.erase g := by
  exact ⟨rule.select Q h, rule.select_mem Q h, by simp [selectionStep, h]⟩

theorem selectionStep_removes (rule : SelectionRule I) {score : Finset I → I → ℝ}
    (hmax : rule.IsMaxFor score) {Q : Finset I} (h : Q.Nonempty) :
    ∃ g ∈ Q, selectionStep rule Q = Q.erase g ∧ ∀ y ∈ Q, score Q y ≤ score Q g := by
  exact ⟨rule.select Q h, rule.select_mem Q h, by simp [selectionStep, h], hmax Q h⟩

theorem selectionStep_subset (rule : SelectionRule I) (Q : Finset I) :
    selectionStep rule Q ⊆ Q := by
  unfold selectionStep
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

theorem card_le_selectionStep_add_one (rule : SelectionRule I) (Q : Finset I) :
    Q.card ≤ (selectionStep rule Q).card + 1 := by
  by_cases h : Q.Nonempty
  · obtain ⟨g, hg, hstep⟩ := selectionStep_spec rule h
    rw [hstep]
    have := Finset.card_erase_add_one hg
    omega
  · simp [selectionStep, h]

theorem card_selectionStep_add_one (rule : SelectionRule I) {Q : Finset I}
    (h : Q.Nonempty) : (selectionStep rule Q).card + 1 = Q.card := by
  obtain ⟨g, hg, hstep⟩ := selectionStep_spec rule h
  rw [hstep]
  exact Finset.card_erase_add_one hg

theorem selectionRun_subset (rule : SelectionRule I) (n : ℕ) (Q : Finset I) :
    selectionRun rule n Q ⊆ Q := by
  induction n generalizing Q with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (ih _).trans (selectionStep_subset rule Q)

theorem selectionRun_add (rule : SelectionRule I) (n m : ℕ) (Q : Finset I) :
    selectionRun rule (n + m) Q = selectionRun rule m (selectionRun rule n Q) := by
  induction n generalizing Q with
  | zero => simp [selectionRun]
  | succ n ih => simpa [Nat.succ_add, selectionRun] using ih (selectionStep rule Q)

theorem selectionRun_antitone (rule : SelectionRule I) {n m : ℕ} (h : n ≤ m)
    (Q : Finset I) : selectionRun rule m Q ⊆ selectionRun rule n Q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [selectionRun_add]
  exact selectionRun_subset rule d _

theorem card_le_selectionRun_add (rule : SelectionRule I) (n : ℕ) (Q : Finset I) :
    Q.card ≤ (selectionRun rule n Q).card + n := by
  induction n generalizing Q with
  | zero => simp [selectionRun]
  | succ n ih =>
    have h := ih (selectionStep rule Q)
    have hstep := card_le_selectionStep_add_one rule Q
    change Q.card ≤ (selectionRun rule n (selectionStep rule Q)).card + (n + 1)
    omega

theorem card_selectionRun_add_of_nonempty (rule : SelectionRule I) (n : ℕ)
    (Q : Finset I) (h : (selectionRun rule n Q).Nonempty) :
    (selectionRun rule n Q).card + n = Q.card := by
  induction n generalizing Q with
  | zero => simp [selectionRun]
  | succ n ih =>
    have hs : (selectionStep rule Q).Nonempty := h.mono (selectionRun_subset rule n _)
    have hq : Q.Nonempty := hs.mono (selectionStep_subset rule Q)
    have hcard := card_selectionStep_add_one rule hq
    have hind := ih (selectionStep rule Q) h
    change (selectionRun rule n (selectionStep rule Q)).card + (n + 1) = Q.card
    omega

theorem selection_removed_card_le (rule : SelectionRule I) (n : ℕ) (Q : Finset I) :
    (Q \ selectionRun rule n Q).card ≤ n := by
  rw [Finset.card_sdiff_of_subset (selectionRun_subset rule n Q)]
  have := card_le_selectionRun_add rule n Q
  omega

theorem selection_removed_card_eq_of_nonempty (rule : SelectionRule I) (n : ℕ)
    (Q : Finset I) (h : (selectionRun rule n Q).Nonempty) :
    (Q \ selectionRun rule n Q).card = n := by
  rw [Finset.card_sdiff_of_subset (selectionRun_subset rule n Q)]
  have := card_selectionRun_add_of_nonempty rule n Q h
  omega

theorem selection_removed_has_stage (rule : SelectionRule I)
    {score : Finset I → I → ℝ} (hmax : rule.IsMaxFor score)
    {n : ℕ} {Q : Finset I} {x : I}
    (hx : x ∈ Q) (hgone : x ∉ selectionRun rule n Q) :
    ∃ t < n, x ∈ selectionRun rule t Q ∧
      ∀ y ∈ selectionRun rule t Q,
        score (selectionRun rule t Q) y ≤ score (selectionRun rule t Q) x := by
  induction n generalizing Q with
  | zero => exact False.elim (hgone hx)
  | succ n ih =>
    by_cases hs : x ∈ selectionStep rule Q
    · obtain ⟨t, ht, hxt, hmaxT⟩ := ih hs hgone
      refine ⟨t + 1, by omega, ?_, ?_⟩
      · simpa [selectionRun] using hxt
      · simpa [selectionRun] using hmaxT
    · obtain ⟨g, hg, hstep, hmaxQ⟩ := selectionStep_removes rule hmax ⟨x, hx⟩
      have heq : x = g := by
        by_contra hne
        exact hs (hstep.symm ▸ Finset.mem_erase.mpr ⟨hne, hx⟩)
      subst x
      exact ⟨0, Nat.zero_lt_succ n, hg, hmaxQ⟩

theorem selection_good_stage_of_bad_remaining (rule : SelectionRule I)
    {score : Finset I → I → ℝ} (hmax : rule.IsMaxFor score)
    (U B : Finset I) (f : ℕ) (hB : B.card ≤ f)
    (hbad : (selectionRun rule f U ∩ B).Nonempty) :
    ∃ t < f, ∃ g ∈ selectionRun rule t U, g ∉ B ∧
      ∀ y ∈ selectionRun rule t U,
        score (selectionRun rule t U) y ≤ score (selectionRun rule t U) g := by
  let R := selectionRun rule f U
  obtain ⟨b, hb⟩ := hbad
  have hbR : b ∈ R := (Finset.mem_inter.mp hb).1
  have hbB : b ∈ B := (Finset.mem_inter.mp hb).2
  have hcard : (U \ R).card = f := selection_removed_card_eq_of_nonempty rule f U ⟨b, hbR⟩
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
  obtain ⟨t, ht, hgt, hmaxT⟩ := selection_removed_has_stage rule hmax hgU hgR
  exact ⟨t, ht, g, hgt, hgB, hmaxT⟩

end FTC
