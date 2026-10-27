import Mettapedia.ProbabilityTheory.Common.OrderedCombination
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
import Mettapedia.ProbabilityTheory.Hypercube.Basic

/-!
# Ordered representations and interval refinement

This entrypoint connects three independent interfaces: ordered combination,
credal intervals, and the probability hypercube's axiom labels. A label or a
toy-graph edge is not an interpretation or a proof of a representation theorem.

An injective additive representation forces commutativity. Its existence needs
the canonical Knuth–Skilling hypotheses. Different positive calibrations remain
possible even over the complete real numbers. Interval refinement yields a
unique point only with bounds, nesting and vanishing width, as specified in
`CredalSets.RefinedCredalAlgebra`. Completeness alone does not shrink an interval.

The sequential action in `Common.OrderedCombination` supplies an operational
interpretation of actual monoid values; additive observation is a separate map.
-/
