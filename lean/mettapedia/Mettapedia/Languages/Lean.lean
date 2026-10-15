import Mettapedia.Languages.Lean.Lean4LeanEnvironmentGrowth
import Mettapedia.Languages.Lean.Lean4LeanDirectedReduction
import Mettapedia.Languages.Lean.Lean4LeanRungZeroDecision
import Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision
import Mettapedia.Languages.Lean.Lean4LeanRungTwoTypedBoundary
import Mettapedia.Languages.Lean.Lean4LessCheckerBoundary

/-!
# Lean as a hosted language family

This entry point gathers bounded SemanticService guest interfaces for Lean-family
kernels and explicit equality-profile translations.  It does not import or
trust an external Lean checker implementation.
-/
