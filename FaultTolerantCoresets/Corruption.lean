import FaultTolerantCoresets.Basic

/-! # Entrywise corruption and filtering with inherited weights -/

namespace FTC

variable {I X S : Type*} [DecidableEq I]

/-- At most `f` individual active entries are replaced. Even identical copies
have separate indices; the index set itself is unchanged by corruption. -/
def IsFCorruption (f : ℕ) (U : Finset I) (original corrupted : I → Entry X) : Prop :=
  ∃ B ⊆ U, B.card ≤ f ∧ ∀ i ∈ U, i ∉ B → corrupted i = original i

theorem IsFCorruption.refl (f : ℕ) (U : Finset I) (entries : I → Entry X) :
    IsFCorruption f U entries entries := by
  exact ⟨∅, Finset.empty_subset _, by simp, by intros; rfl⟩

/-- Deterministic success event from Definition 2.1. The decoder observes only
the corrupted entries, returns active indices, and inherits their weights.
The probability of this event is handled separately in `Sampling.lean`. -/
def IsFilteringFaultTolerant (ε : ℝ) (f : ℕ) (reference : S → ℝ)
    (loss : X → S → ℝ) (U : Finset I) (entries : I → Entry X)
    (decoder : (I → Entry X) → Finset I) : Prop :=
  IsCoreset ε reference (cost (contribution loss entries) U) ∧
    ∀ corrupted, IsFCorruption f U entries corrupted →
      decoder corrupted ⊆ U ∧
        IsCoreset ε reference (cost (contribution loss corrupted) (decoder corrupted))

end FTC
