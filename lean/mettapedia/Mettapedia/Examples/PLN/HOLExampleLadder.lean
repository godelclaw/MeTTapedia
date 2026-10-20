import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.TermModel.HenkinCompletenessControls
import Mettapedia.Logic.HOL.WitnessedWorld
import Mettapedia.Logic.HOL.WitnessedSaturation
import Mettapedia.Logic.HOL.Embedding.FirstOrder
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore
import Mettapedia.PLN.Bridges.HOL.Probabilistic.BenchmarkBeliefBridge
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNProbHOLPlannerBridge

/-!
# HOL Example Ladder

This module curates theorem-level examples showing how the current higher-order
logic stack can already be instantiated across several layers:

- HOL soundness for closed theorems,
- classical Henkin satisfiability/model existence,
- the witnessed prime-extension and witness-axiom machinery,
- first-order embedding into real HOL,
- HOL-to-world-model consequence transfer,
- higher-order probabilistic belief tracking,
- and planner-facing higher-order PLN shadow theorems.

Positive examples:

- `closedTheoremSoundnessExample`
- `henkinSatisfiabilityExample`
- `henkinClassicalModelExistenceExample`
- `witnessedPrimeExtensionExample`
- `witnessAxiomExistsExample`
- `firstOrderEmbeddingSentenceExample`
- `singletonWorldModelAdequacyExample`
- `worldModelSingletonConsequenceExample`
- `benchmarkHierarchicalProbStrengthExample`
- `benchmarkBeliefTracksHierarchicalProbExample`
- `higherOrderSemanticContractionCarriesBeliefPriceExample`
- `plannerShadowTracksHierarchicalProbExample`

Negative examples:

- `singletonWorldModelCounterevidenceExample`
- `benchmarkBeliefNotGlobalOracleExample`
- `plannerShadowNotGlobalOracleExample`

This is an example ladder, not an end-to-end theorem. Soundness and
completeness over the original signature are
`Mettapedia.Logic.HOL.SevenVirtues.provable_iff_valid` (countable signatures with
a closed term at each base type, excluded middle as one axiom). The
probabilistic and planner-facing examples below use the HOL semantic layers; they
are not consequences of that theorem.
-/

namespace Mettapedia.Examples.PLN.HOLExampleLadder

/-- Positive example: closed HOL theorems are sound in every Heyting-Henkin
model of the corrected intuitionistic-extensional core. -/
abbrev closedTheoremSoundnessExample :=
  @Mettapedia.Logic.HOL.Soundness.theorem_sound

/-- Positive example: the witnessed + excluded-middle Henkin extension has a
general Henkin model whenever that extended theory is consistent. -/
abbrev henkinSatisfiabilityExample :=
  @Mettapedia.Logic.HOL.ClosedTheorySet.henkin_satisfiable

/-- Positive example: `ClosedTheorySet.henkin_model_exists_of_consistent_classical`
applied to the single excluded-middle axiom over the propositional signature with
parameters, which is consistent, mentions no parameter and proves every
excluded-middle instance. -/
abbrev henkinClassicalModelExistenceExample :=
  @Mettapedia.Logic.HOL.HenkinCompletenessControls.excludedMiddleTheory_has_model

/-- Positive example: consistent parameter-free theories extend to witnessed,
prime, deductively closed Henkin worlds. -/
abbrev witnessedPrimeExtensionExample :=
  @Mettapedia.Logic.HOL.exists_witnessed_prime_extension

/-- Positive example: the Henkin saturation contains an explicit witness axiom
for every enumerated existential body. -/
abbrev witnessAxiomExistsExample :=
  @Mettapedia.Logic.HOL.exists_witnessAxiom

/-- Positive example: first-order sentence truth is preserved by the standard
embedding into real Church-style HOL. -/
abbrev firstOrderEmbeddingSentenceExample :=
  @Mettapedia.Logic.HOL.Embedding.FirstOrder.denote_embedSentence_iff

/-- Positive example: truth of a closed HOL formula is equivalent to singleton
world-model strength `1` in the pointed-Henkin world-model bridge. -/
abbrev singletonWorldModelAdequacyExample :=
  @Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.singleton_adequacy_strength_one

/-- Negative example: falsity of a closed HOL formula yields singleton
counterevidence in the world-model bridge. -/
abbrev singletonWorldModelCounterevidenceExample :=
  @Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_singleton_of_not_satisfies

/-- Positive example: pointwise HOL implication is exactly singleton
world-model consequence on pointed Henkin states. -/
abbrev worldModelSingletonConsequenceExample :=
  @Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.pointwiseImplies_iff_singletonStrengthLE

/-- Positive example: the benchmark hierarchical query strength coincides with
the higher-order semantic value in the probabilistic HOL bridge. -/
abbrev benchmarkHierarchicalProbStrengthExample :=
  @Mettapedia.PLN.Bridges.HOL.Probabilistic.benchmarkHierarchicalProbQueryStrength_eq_higherOrderSemanticValue

/-- Positive example: the belief-day benchmark shadow tracks hierarchical
probability on the canonical sample. -/
abbrev benchmarkBeliefTracksHierarchicalProbExample :=
  @Mettapedia.PLN.Bridges.HOL.Probabilistic.benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn

/-- Positive example: the higher-order semantic contraction already carries the
same value as the benchmark belief price consumed by the PLN-facing layer. -/
abbrev higherOrderSemanticContractionCarriesBeliefPriceExample :=
  @Mettapedia.PLN.Bridges.HOL.Probabilistic.higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice

/-- Negative example: the benchmark belief adapter remains query-focused rather
than becoming a global oracle on the expanded sample. -/
abbrev benchmarkBeliefNotGlobalOracleExample :=
  @Mettapedia.PLN.Bridges.HOL.Probabilistic.benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top

/-- Positive example: the planner-facing shadow tracks the higher-order
hierarchical probability semantics on the benchmark sample. -/
abbrev plannerShadowTracksHierarchicalProbExample :=
  @Mettapedia.PLN.RuleFamilies.HigherOrder.benchmarkPlannerShadow_day_tracks_hierarchicalProbOn

/-- Negative example: the planner-facing shadow is not a global oracle for the
expanded benchmark sample. -/
abbrev plannerShadowNotGlobalOracleExample :=
  @Mettapedia.PLN.RuleFamilies.HigherOrder.benchmarkPlannerShadow_day_not_tracks_expandedSample

end Mettapedia.Examples.PLN.HOLExampleLadder
