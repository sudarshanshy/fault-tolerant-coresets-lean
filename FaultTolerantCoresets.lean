import FaultTolerantCoresets.Basic
import FaultTolerantCoresets.Corruption
import FaultTolerantCoresets.Sensitivity
import FaultTolerantCoresets.Filtering
import FaultTolerantCoresets.Decoder
import FaultTolerantCoresets.SamplingWeights
import FaultTolerantCoresets.Sampling
import FaultTolerantCoresets.LowerBound.LargestWeights
import FaultTolerantCoresets.LowerBound.Combinatorial
import FaultTolerantCoresets.LowerBound.BasisInstance
import FaultTolerantCoresets.LowerBound.LowerBound
import FaultTolerantCoresets.FiniteMetric.SensitivityReduction
import FaultTolerantCoresets.FiniteMetric.WeightedSensitivityReduction
import FaultTolerantCoresets.CounterexampleArithmetic
import FaultTolerantCoresets.Selection
import FaultTolerantCoresets.Probability.ScoreSampling
import FaultTolerantCoresets.Executable.Decoder
import FaultTolerantCoresets.Executable.FiniteMetricKMeans
import FaultTolerantCoresets.Counterexample.Example
import FaultTolerantCoresets.Hardness.Examples

/-!
# Fault-tolerant coresets

Lean formalization of the main results of *Fault Tolerant Coresets*, including
the conditional Theorem 4.2 hardness transfer in the explicit bit-cost model,
using the exact PDF recorded in `source/SOURCE.md`.

See `README.md` for the theorem map, build instructions, and precise scope.
-/
