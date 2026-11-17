# Fault-tolerant coresets in Lean

A modular formalization of the main results of **Fault Tolerant
Coresets**, including the conditional hardness transfer in Theorem 4.2,
using the exact attached `coreset_notes (29).pdf`. The source PDF,
its checksum, and page references are in [`source/`](source/SOURCE.md).

## Build

Requires Lean **4.31.0** through Elan. Mathlib and its dependencies are pinned in
`lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean -j1 FaultTolerantCoresets/Audit.lean
lake env lean -j1 --run FaultTolerantCoresets/Executable/Demo.lean
lake env lean -j1 --run FaultTolerantCoresets/Hardness/Demo.lean
```

The working copy retains its dependency cache. The downloadable source
archive excludes that cache; the commands above restore it on another machine.

The completed build, public-theorem axiom audit, and executable demonstrations
are recorded in [VERIFICATION.md](VERIFICATION.md), with their actual logs.

## Verified results

All declarations listed below have complete Lean proofs. There are no `sorry`,
`admit`, or project-defined axioms.

| Paper result | Main Lean declaration | File |
| --- | --- | --- |
| Lemma 3.2, each sampled copy contributes at most `(T/m) cost(P,S)` | `FTC.lemma_3_2` | `SamplingWeights.lean` |
| Equation (1), the clean-core invariant | `FTC.clean_core_bounds` | `Decoder.lean` |
| Deterministic Theorem 3.1, the actual iterative filtering decoder | `FTC.filtering_decoder_correct` | `Decoder.lean` |
| Arbitrary point/weight corruptions | `FTC.filtering_decoder_correct_of_corruption` | `Decoder.lean` |
| Theorem 3.1, sampling and success-event transfer | `FTC.theorem_3_1` | `Sampling.lean` |
| Theorem A.1, proxy-score sampling | `FTC.theorem_A_1` | `Sampling.lean` |
| Claim A.2, actual Euclidean basis witness queries | `FTC.LowerBound.weight_preservation` | `LowerBound/BasisInstance.lean` |
| Theorem 3.4, explicit quantitative lower bound | `FTC.LowerBound.theorem_3_4_of_support` | `LowerBound/LowerBound.lean` |
| Theorem 4.1, finite-metric constrained optimization reduction | `FTC.FiniteMetric.estimate_approximates_sensitivity` | `FiniteMetric/SensitivityReduction.lean` |
| Indexed weighted form of Theorem 4.1 | `FTC.FiniteMetric.weightedEstimate_approximates_sensitivity` | `FiniteMetric/WeightedSensitivityReduction.lean` |
| Theorem 4.2, conditional hardness transfer on explicit rational metric inputs | `FTC.Hardness.theorem_4_2_full_matrix` | `Hardness/FullReduction.lean` |
| Exact sensitivity of the hardness construction | `FTC.Hardness.weighted_sensitivity_formula` | `Hardness/SensitivityFormula.lean` |
| Polynomial construction cost and full output size | `FTC.Hardness.Encoding.fullReductionCode_cost_size` | `Hardness/FullReduction.lean` |
| Full Appendix A.1 counterexample, including actual metric and decoders | `FTC.Counterexample.appendix_A1_counterexample` | `Counterexample/Example.lean` |
| Actual iid sampler and a proved ordinary coreset success bound | `FTC.Probability.iid_coreset_success_of_sampleSize` | `Probability/FiniteIID.lean` |
| Fully specified exact/proxy iid fault-tolerant constructions | `FTC.Probability.sensitivitySampling_fault_tolerant_rounded`, `scoreSampling_fault_tolerant_rounded` | `Probability/ScoreSampling.lean` |
| Executable exact-sensitivity filtering | `FTC.Executable.matrixDecode_correct` | `Executable/Decoder.lean` |
| Exhaustive rational-metric k-means optimizer and sensitivity bridge | `FTC.Executable.exactRationalKmeans_spec`, `exactRationalKmeansSensitivity_cast_eq` | `Executable/FiniteMetricKMeans.lean` |

Import `FaultTolerantCoresets` for the complete library. The file paths in the
table are relative to the `FaultTolerantCoresets/` source directory.

## Upper-bound statement

The deterministic theorem assumes:

- A nonnegative reference objective and an `ε`-coreset of clean entries.
- Each clean indexed entry contributes at most `δ` times the reference cost.
- At most `f` entries are corrupted, with arbitrary nonnegative replacement
  contributions and agreement outside the corrupted indices.
- A sensitivity oracle satisfying `σ ≤ α * score` and `score ≤ σ`, where `α ≥ 1`.
- `0 ≤ ε < 1/10`, `δ ≥ 0`, and `f * α * δ ≤ ε`.

It proves that `peel oracle.score f U` is a `6ε`-coreset. The proof establishes
the clean-core invariant after every relevant deletion, proves that any surviving
bad entry forces an earlier good maximum to have been deleted, transfers that
maximum's sensitivity bound to every remaining bad entry, and absorbs their
total cost. The decoder stops on an empty set. The theorem includes zero faults,
zero costs, and summaries smaller than the deletion budget.

Exact sampling instantiates `δ = T/m`. Proxy sampling instantiates
`δ = T_proxy/m`. Proxy upper bounds are used for sampling; the decoder still
uses a multiplicative sensitivity approximation. The integer sample count is

```
m_sc + ceil(α * f * T / ε)
```

with an analogous proxy-score expression. Samples are maps from stored indices
to input indices; repeated values are allowed. Choosing the stored indices as
`Fin m` and the active set as `Finset.univ` gives exactly `m` separately
corruptible copies. `theorem_3_1_fin` and `theorem_A_1_fin` give this
specialization with an explicit stored-entry count.

The sampling wrapper takes the ordinary sampler's clean-coreset success
guarantee at the final augmented sample count as a hypothesis, matching the
paper's `m_sc(ε)` convention. It proves
that the **same measurable success event, with the same probability**, guarantees
recovery for every admissible corruption simultaneously. It does not assume that
the universal-adversary predicate is measurable: probability is certified by a
measurable witness event contained in that predicate. The statements work for
an arbitrary measure; a probability measure and a fixed positive success bound
give the paper's constant-probability interpretation.

## Lower-bound statement

The fully geometric theorem uses `EuclideanSpace ℝ (Fin k)`. For arbitrary
separately indexed weighted entries supported on `{e_1, …, e_k}`, a successful
filtering decoder for every `f`-fault point/weight corruption must satisfy

```
(f : ℝ) * k / (2 * ε) ≤ (U.card : ℝ)
```

when `0 < ε < 1/2`. This is a bound on each successful realization, not merely
an expected size. The separating query is the genuine `k`-center set containing
zero and all basis vectors except `e_i`. Its cost reads the total weight at `e_i`.
The adversary concretely sets at most `f` individual weights to zero. The output
is an inherited-weight subset of the corrupted entries, so it cannot recreate
the lost coordinate mass. The cases `k = 0` and `f = 0` are covered.

## Finite-metric oracle

Theorem 4.1 uses actual minimum squared distances to exactly `k` distinct,
nonempty centers. It skips infeasible radii and handles zero denominators.
Both the unweighted and indexed weighted reductions prove

```
σ / ρ ≤ estimate ∧ estimate ≤ σ
```

from the specified constrained approximation oracle, with at most `|X|` oracle
calls per sensitivity estimate. `indexedApproxSensitivityOracle` supplies the
exact oracle interface consumed by the filtering theorem. Duplicate locations
and zero-weight entries are supported.

## Conditional NP-hardness transfer

`Hardness/FullReduction.lean` proves Theorem 4.2: assuming the `ρ`-gap
finite-metric k-means problem is NP-hard, for `ρ > 1` and `0 < δ < ρ-1`,
pointwise weighted k-means sensitivity is hard to approximate within `ρ-δ`.
The base k-means hardness is an explicit theorem premise, as in the paper,
not a new Lean axiom. The source promise is `OPT ≤ B` versus `OPT > ρ*B`,
with a positive rational budget `B` and `1 ≤ k ≤ |X|`.

The proof constructs the actual metric obtained by adding a point `p⋆` at
distance `D > 0` from every original point, gives the original clients weight
`L`, and gives `p⋆` weight one. All `k`-center subsets of the enlarged metric
are allowed. The exact weighted sensitivity is proved to be

```
σ(p⋆) = D² / (D² + L*OPT).
```

For any real factors `1 ≤ α < ρ`, it proves the existence of a fixed positive
integer `c` and positive rational threshold `t` satisfying
`1/(1+c*ρ) < t ≤ 1/(α*(1+c))`. Taking `L = c*D²/B` yields
`σ = B/(B+c*OPT)`. YES instances have `α*t ≤ σ`; NO instances have `σ < t`.
Thus thresholding any estimate with `σ/α ≤ estimate ≤ σ` decides the gap
problem. The theorem `full_approximation_implies_np_subset_p` makes this
implication explicit for a polynomial approximation program.

The executable reduction takes binary natural-number pairs representing
nonnegative rationals, an explicit distance matrix, a client mask, a center
count, and the budget. It outputs the complete enlarged distance matrix and
individual weight list. A positive diameter bound is computed as one plus
the largest distance numerator, so singleton metrics are also supported.
No optimization oracle or real arithmetic is used in this construction.
Its value, validity, sensitivity, polynomial evaluation cost, and polynomial
output size are all proved. The cost and size bounds hold even on malformed
raw inputs; semantic correctness uses the stated validity predicates.

**Complexity-model scope.** `Hardness/Computation.lean` defines a finite
first-order program language with binary natural numbers, lists, arithmetic,
branching, mapping, and bounded iteration. Arithmetic is charged by operand
bit length. Polynomial time bounds both evaluation cost and output size;
composition and the operations used by the reduction have proved bounds.
`InP`, certificate-verifier `InNP`, promise reductions, and `NPHard` are all
defined in this same explicit model. No equivalence with a Turing-machine
model or compiler to that model is formalized. The result is therefore a
checked conditional hardness transfer in this bit-cost model, not a
machine-level proof of the external k-means hardness premise.

`sensitivity_hardness_below_limit` transfers any supplied family of base
gap-hardness results below a limit `R`. Instantiating the paper's `1+8/e`
corollary still requires the external Guha–Khuller hardness family in the
chosen model; that separate result is not reproved here.

`Hardness/Examples.lean` proves two concrete examples with `ρ=3`, `α=2`,
`c=4`, and `t=1/11`. The executable demo runs the certified matrix
construction and the existing exhaustive exact-sensitivity evaluator. The
two outputs have exact sensitivities `1/5` and `1/17`, respectively, and
fall on the correct sides of the threshold.

## Actual iid sampling guarantee

`Probability/FiniteIID.lean` constructs the actual finite product probability
measure for independent draws with replacement. It proves the marginal and
joint laws, independence, histogram expectation `m*q(x)`, and variance
`m*q(x)*(1-q(x))`. Chebyshev's inequality and a finite union bound produce a
measurable event on which every relative input frequency is accurate. This
implies the coreset property simultaneously for **all queries**, even when the
solution type is infinite.

For failure parameter `η > 0`, a fully proved ordinary sample count is

```
m_sc = ceil((sum over positive support x of 1/q(x)) / (η * ε^2)) + 1.
```

Every larger sample count also works. `ScoreSampling.lean` normalizes exact or
proxy sensitivities into the actual PMF, omits zero-score indices only after
proving that they have zero contribution, and combines this bound with the
additive `ceil(α*f*T/ε)` overhead. The resulting exact-count construction has
success probability at least `1-η` and no clean-success hypothesis. Choosing
`η = 1/2` gives constant probability. A zero total score is handled separately:
the reference objective is identically zero and the empty summary is exact.

This fallback is deliberately conservative. It does not assert the sharper
geometry-specific ordinary coreset sample bounds cited by the paper. The
original generic wrappers remain available for those sharper bounds.

## Complete proxy-decoder counterexample

`Counterexample/Example.lean` instantiates the source's construction for every
`0 < ε < 1/10` and integer `n ≥ 8/ε`. The finite metric is given by an explicit
distance table satisfying all metric axioms, with `M = sqrt(n-4)`.

The construction proves exact clean sensitivities `1/(n-2)`, genuine corrupted
sensitivities at most `1/(n-3)`, the factor-two reference clustering and strict
nearest-center assignments, valid cluster-size sensitivity upper bounds, and
strict opposite maxima for the proxy and exact scores. It proves the outputs
of the actual one-step decoders: the proxy deletes the genuine singleton and
has distortion `2*(n-4)/(n-2) > 1+6ε`, while exact sensitivity deletes the
corruption and returns an `ε`-coreset. Metric, query, and sensitivity facts are
proved rather than supplied as counterexample hypotheses.

## Executable finite rational algorithms and work model

`Selection.lean` separates a selection routine from its maximum-score proof.
The deterministic theorem `filtering_decoder_correct_with_rule` covers any such
routine. `Executable/Filtering.lean` supplies a computable rational selector,
caches each active score once, and proves correctness and agreement of the
instrumented and uninstrumented programs. It proves at most `f*|U|` score calls,
at most `f*(|U|-1)` cached-score comparisons, and at most `min(f,|U|)` deletions.

`FiniteMetricMatrix.lean` computes exact rational sensitivities over a complete
finite query matrix and proves equality with the real sensitivity supremum.
One active score uses exactly `|queries|*(2*|U|+3)` charged matrix/arithmetic
operations. The executable filtering theorem uses this backend without assuming
a sensitivity oracle. `chargedMatrixWork_bound` combines these bounds over the
whole filtering run.

`FiniteMetricEnumeration.lean` caches all feasible candidates' costs and proves
that the executable constrained solver returns a global optimum, or returns
none precisely when infeasible. `FiniteMetricKMeans.lean` supplies actual
rational metric data, nonnegative rational weighted entries, and a complete
list of k-center subsets of an admissible set Y. Its list length is exactly
`choose(|Y|, k)`. For positive `k`, it proves the real metric interpretation, the real weighted
k-means sensitivity equality, and the corresponding binomial work bounds.

This optimizer/filtering work model charges matrix evaluations, rational additions/divisions, and
maximum comparisons as unit operations. It does **not** formalize container
implementation costs, preprocessing the loss matrix, rational bit complexity,
or hardware running time. Exhaustive optimization is explicit and potentially
exponential; it does not replace the paper's approximation-oracle assumption
with a claimed efficient general exact solver.

The runnable demo stores eighty separately indexed weighted entries, corrupts
one entry's weight to 100, computes exact rational sensitivities, and filters it.
It reports the actual remaining entry count and carried work counters.

## Scope

The targeted numbered results from the PDF, the conditional Theorem 4.2
hardness transfer, and the full Appendix A.1 counterexample are covered.
The concrete iid construction uses the explicit
conservative sample count above. General real-valued objectives retain the
paper's approximation-oracle specification; executable exact optimization is
provided for finite rational data. The hardness reduction has a separate
binary bit-cost certificate. Machine-model equivalence, bit-cost analysis of
the exhaustive optimizer, the external base k-means hardness theorem, and
sharper coreset concentration theorems remain outside the stated scope.

`Audit.lean` checks the public declarations' axiom dependencies. Only standard
Lean logical axioms are used; no additional mathematical axioms are declared.
