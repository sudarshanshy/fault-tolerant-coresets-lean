import FaultTolerantCoresets

/-!
# Public theorem axiom audit

Run `lake env lean FaultTolerantCoresets/Audit.lean` after `lake build`.
Every printed dependency list should contain only standard Lean logical axioms,
and in particular must not contain `sorryAx` or any project-defined axiom.
-/

#print axioms FTC.lemma_3_2
#print axioms FTC.proxySampling_entry_bound
#print axioms FTC.clean_core_bounds
#print axioms FTC.good_stage_of_bad_remaining
#print axioms FTC.filtering_decoder_correct
#print axioms FTC.filtering_decoder_correct_of_corruption
#print axioms FTC.theorem_3_1
#print axioms FTC.theorem_A_1
#print axioms FTC.theorem_3_1_fin
#print axioms FTC.theorem_A_1_fin
#print axioms FTC.FilteringSuccess.to_isFilteringFaultTolerant
#print axioms FTC.LowerBound.weight_preservation
#print axioms FTC.LowerBound.exists_largest_weights
#print axioms FTC.LowerBound.quantitative_filtering_lower_bound
#print axioms FTC.LowerBound.theorem_3_4_of_support
#print axioms FTC.FiniteMetric.estimate_approximates_sensitivity
#print axioms FTC.FiniteMetric.weightedEstimate_approximates_sensitivity
#print axioms FTC.FiniteMetric.indexedApproxSensitivityOracle
#print axioms FTC.CounterexampleArithmetic.proxy_and_sensitivity_separations
#print axioms FTC.CounterexampleArithmetic.wrongDistortion_gt_tolerance
#print axioms FTC.filtering_decoder_correct_with_rule
#print axioms FTC.Probability.iidLaw_independent
#print axioms FTC.Probability.histogram_expectation
#print axioms FTC.Probability.histogram_variance
#print axioms FTC.Probability.badHistogram_measure_le
#print axioms FTC.Probability.iid_coreset_success_of_sampleSize
#print axioms FTC.Probability.scoreSampling_fault_tolerant_rounded
#print axioms FTC.Probability.sensitivitySampling_fault_tolerant_rounded
#print axioms FTC.Probability.cost_zero_of_totalScore_zero
#print axioms FTC.Executable.rationalSensitivity_cast_eq
#print axioms FTC.Executable.matrixDecode_correct
#print axioms FTC.Executable.runCounted_remaining
#print axioms FTC.Executable.runCounted_scoreCalls_le
#print axioms FTC.Executable.runCounted_comparisons_le
#print axioms FTC.Executable.runCounted_deletions_le
#print axioms FTC.Executable.chargedMatrixWork_bound
#print axioms FTC.Executable.exactRationalKmeans_spec
#print axioms FTC.Executable.exactRationalKmeans_none_iff
#print axioms FTC.Executable.centerCandidateList_length
#print axioms FTC.Executable.exactRationalKmeansSensitivity_cast_eq
#print axioms FTC.Counterexample.appendix_A1_counterexample
#print axioms FTC.Hardness.extensionMetric
#print axioms FTC.Hardness.sensitivity_formula
#print axioms FTC.Hardness.weighted_sensitivity_formula
#print axioms FTC.Hardness.gapParameters_nonempty
#print axioms FTC.Hardness.gap_decision_of_approximation
#print axioms FTC.Hardness.Computation.Code.IsPoly.comp
#print axioms FTC.Hardness.Complexity.NPHard.of_reduction
#print axioms FTC.Hardness.Complexity.inNP_of_inP
#print axioms FTC.Hardness.Encoding.reduce_valid
#print axioms FTC.Hardness.Encoding.reduce_sensitivity_formula
#print axioms FTC.Hardness.Encoding.reductionCode_polynomial
#print axioms FTC.Hardness.theorem_4_2
#print axioms FTC.Hardness.approximation_implies_np_subset_p
#print axioms FTC.Hardness.Encoding.materialize_valid
#print axioms FTC.Hardness.Encoding.fullSensitivity_materialize
#print axioms FTC.Hardness.Encoding.fullReductionCode_eval
#print axioms FTC.Hardness.Encoding.fullReductionCode_cost_size
#print axioms FTC.Hardness.theorem_4_2_full_matrix
#print axioms FTC.Hardness.full_approximation_implies_np_subset_p
#print axioms FTC.Hardness.no_polynomial_full_approximation
#print axioms FTC.Hardness.sensitivity_hardness_below_limit
#print axioms FTC.Hardness.Encoding.exactFullSensitivity_cast_eq
#print axioms FTC.Hardness.Examples.yes_promised
#print axioms FTC.Hardness.Examples.no_promised
#print axioms FTC.Hardness.Examples.yes_exact_value
#print axioms FTC.Hardness.Examples.no_exact_value
