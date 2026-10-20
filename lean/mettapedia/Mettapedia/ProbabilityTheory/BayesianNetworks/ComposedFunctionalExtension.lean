import Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension
import Mettapedia.ProbabilityTheory.FunctionalExtensionComposition

/-!
# Staged and fused factor interpretations

The second factor graph consumes the first deterministic extension table.
Its actual product-and-sum semantics agrees with a graph for the fused
function, for every final Boolean query and before normalization.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ComposedFunctionalExtension

open scoped NNReal
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

universe u
variable {Source Aux Output : Type u} [Fintype Source] [Fintype Aux] [Fintype Output]
  [DecidableEq Aux] [DecidableEq Output]

theorem staged_graph_mass_eq_fused (first : Source → Aux) (second : Source × Aux → Output)
    (weight : Source → ℝ≥0) :
    FunctionalExtension.massSemantics second (extend first weight) =
      FunctionalExtension.massSemantics (fun source => second (source, first source)) weight := by
  rw [FunctionalExtension.graph_mass_eq_source, FunctionalExtension.graph_mass_eq_source,
    extension_observation_mass]

end Mettapedia.ProbabilityTheory.BayesianNetworks.ComposedFunctionalExtension
