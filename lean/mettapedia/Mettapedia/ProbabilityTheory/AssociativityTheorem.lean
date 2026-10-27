import Mettapedia.ProbabilityTheory.Common.OrderedCombination

/-!
# Associativity and ordered representations

The common ordered-combination interface uses the canonical Knuth–Skilling
structures. `iterateEmbedding` identifies the generated natural-number scale;
`RepresentationResult` describes a representation of the entire carrier.
Global existence uses the standalone package's additional separation or
no-anomalous-pairs hypotheses. Associativity alone supplies neither existence
nor commutativity. Calibration and faithful sequential actions are provided by
`Mettapedia.ProbabilityTheory.OrderedCombination`.
-/
