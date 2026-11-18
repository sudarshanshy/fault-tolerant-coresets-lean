#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake exe cache get \
  Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Algebra.Order.Archimedean.Basic \
  Mathlib.Algebra.Order.Archimedean.Real.Basic \
  Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Algebra.Order.BigOperators.Group.List \
  Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.Analysis.Real.Sqrt \
  Mathlib.Data.Finset.Basic \
  Mathlib.Data.Finset.Card \
  Mathlib.Data.Finset.Fold \
  Mathlib.Data.Finset.Lattice.Fold \
  Mathlib.Data.Finset.Max \
  Mathlib.Data.Finset.Powerset \
  Mathlib.Data.Finset.Sort \
  Mathlib.Data.Fintype.Option \
  Mathlib.Data.Fintype.Sum \
  Mathlib.Data.List.GetD \
  Mathlib.Data.List.MinMax \
  Mathlib.Data.List.Sublists \
  Mathlib.Data.Nat.Size \
  Mathlib.Data.Rat.BigOperators \
  Mathlib.Data.Rat.Cast.Order \
  Mathlib.Data.Real.Basic \
  Mathlib.MeasureTheory.Constructions.Pi \
  Mathlib.MeasureTheory.Measure.MeasureSpaceDef \
  Mathlib.Order.ConditionallyCompleteLattice.Basic \
  Mathlib.Order.WithBot \
  Mathlib.Probability.Moments.Variance \
  Mathlib.Probability.ProbabilityMassFunction.Integrals \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.FinCases \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Positivity \
  Mathlib.Tactic.Ring \
  Mathlib.Tactic.SplitIfs \
  Mathlib.Topology.MetricSpace.Basic \
  Mathlib.Topology.MetricSpace.Defs
