import FaultTolerantCoresets.Executable.Decoder

/-!
# A runnable finite-matrix decoding example

There are eighty separately indexed entries: forty copies in each of two bins.
Each clean copy has weight 1/40. The first entry's weight is corrupted to 100.
The exact executable sensitivity decoder removes that individual entry.
-/

namespace FTC.Executable.Demo

def cleanMatrix (i : Fin 80) (s : Fin 2) : ℚ :=
  if (i.val < 40 ∧ s.val = 0) ∨ (40 ≤ i.val ∧ s.val = 1) then 1 / 40 else 0

def corruptedMatrix (i : Fin 80) (s : Fin 2) : ℚ :=
  if i.val = 0 ∧ s.val = 0 then 100 else cleanMatrix i s

def result : WorkResult (Fin 80) :=
  matrixDecodeCounted corruptedMatrix Finset.univ 1 Finset.univ

def main : IO Unit := do
  let r := result
  IO.println s!"Stored entries: {80}"
  IO.println s!"Remaining entries: {r.remaining.card}"
  IO.println s!"Corrupted index 0 removed: {decide ((0 : Fin 80) ∉ r.remaining)}"
  IO.println s!"Sensitivity calls: {r.scoreCalls}"
  IO.println s!"Cached-score comparisons: {r.comparisons}"
  IO.println s!"Deletions: {r.deletions}"

end FTC.Executable.Demo

def main : IO Unit := FTC.Executable.Demo.main
