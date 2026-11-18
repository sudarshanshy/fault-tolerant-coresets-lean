# Verification record

Checked on **17 November 2026**.

- Lean: **4.31.0**.
- Mathlib: **v4.31.0**, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `lake build`: **passed**, exit status 0 (2931 build jobs including dependencies).
- `lake env lean -j1 FaultTolerantCoresets/Audit.lean`: **passed**, exit status 0.
- `lake env lean -j1 --run FaultTolerantCoresets/Executable/Demo.lean`:
  **passed**, exit status 0.
- `lake env lean -j1 --run FaultTolerantCoresets/Hardness/Demo.lean`:
  **passed**, exit status 0.
- All 46 project Lean source files (7472 lines) were scanned: no `sorry`, `admit`, or
  project-defined `axiom` declarations.
- The project sources also contain no `unsafe` declarations or `native_decide`.
- All 67 audited public declarations depend only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- The audit output was checked against all 67 declarations requested in
  `Audit.lean`; no declaration was missing and no additional axiom appeared.
- The library root reaches all 43 library modules. The three other Lean files
  are the separately checked audit and two executable demos.
- The mathlib checkout matched the pinned commit and had no tracked changes.
- The authoritative source PDF still matches the SHA-256 in
  [source/SOURCE.md](source/SOURCE.md).

The build emitted linter warnings about unused variables/instances, unused
simplification arguments, and an unnecessary `simpa`; it had no errors. Build-job totals include dependency
targets and are not a count of project theorems.

The saved outputs are:

- [Build log](verification/build.txt).
- [Axiom audit](verification/axioms.txt).
- [Executable demo](verification/demo.txt): 80 stored entries, 79 remaining,
  corrupted index 0 removed, 80 sensitivity calls, 79 comparisons, one deletion.
- [Hardness demo](verification/hardness-demo.txt): the certified full-matrix
  reduction produces weights `[1,16,16]` and `[1,64,64]`, exact sensitivities
  `1/5` and `1/17`, and correct YES/NO decisions at threshold `1/11`.
  Its evaluated construction costs are 47,782 and 51,080 in the specified
  bit-cost model; these are not measured CPU-operation counts.
- [Portable file checksums](verification/SHA256SUMS), covering the source,
  configuration, documentation, source PDF, and verification logs.

The final checks include the complete Appendix A.1 metric counterexample,
the actual iid probability construction and its explicit sample bound,
executable finite-rational sensitivity filtering, exhaustive constrained
k-means optimization, the proved operation-count bounds, and the conditional
Theorem 4.2 hardness transfer. The hardness audit includes the actual metric
extension, exact sensitivity formula, gap separation, rational encoding,
full distance-matrix materialization, polynomial construction cost and output
size, reduction composition, and approximation-implies-NP-in-P theorem.
These modules
are included in the library import graph and the expanded axiom audit.

The generic sampling wrappers retain the ordinary sampler's success guarantee
as a hypothesis. The concrete iid constructions discharge that hypothesis
using the conservative bound documented in [FORMALIZATION.md](FORMALIZATION.md). General
real-valued optimization retains the constrained approximation-oracle
specification; the finite-rational executable backend proves exactness by
exhaustive enumeration. The audit checks proof dependencies, not algorithmic
efficiency. The separate hardness construction has a proved polynomial
binary bit-cost bound in `Hardness/Computation.lean`'s explicit program model.
Its `InP`, `InNP`, and `NPHard` predicates use that same model. Equivalence
with Turing-machine complexity is not formalized. The base gap-k-means
hardness theorem remains an explicit premise, exactly as in the paper's
conditional Theorem 4.2; the external Guha–Khuller result is not reproved.
Sharper external concentration results, bit-cost analysis of the exhaustive
optimizer, and machine running time are also outside the stated scope.

The original verification logs above are retained. Repository setup and graph
verification are recorded separately below. The current portable checksum list
excludes itself, dependency caches, compiled artifacts, and local development
helpers. Reproduce the build checks using [README.md](README.md#build-and-verify).


## Repository setup verification (17 November 2026)

- Fresh `bash bootstrap.sh` and `bash check.sh` passed with the pinned Lean 4.31.0 environment.
- All 67 expected axiom reports were present and used only the three standard logical axioms. Both executable demos passed.
- The audit validator also rejected deliberately missing output and an injected `sorryAx`.
- The blueprint extractor exported 1,856 compiled project constants and matched all 737 indexed source declarations.
- The 14-node overview and four detailed views were generated from compiled dependencies; every displayed edge was checked against its recorded dependency path.
- The generated overview image was visually inspected. Interactive browser testing was unavailable because the browser blocks local file URLs.
- The original proof sources and pinned dependencies were unchanged.
