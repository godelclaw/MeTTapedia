import Mettapedia.Logic.HOL.Syntax.Type
import Mettapedia.Logic.HOL.Syntax.Term
import Mettapedia.Logic.HOL.GuardedRetraction
import Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
import Mettapedia.Logic.HOL.Embedding.WeakTypeComprehension
import Mettapedia.Logic.HOL.Embedding.ConversionPrice
import Mettapedia.Logic.HOL.Embedding.ConversionEvidenceBridge
import Mettapedia.Logic.HOL.Embedding.ContextualStructure
import Mettapedia.Logic.HOL.Embedding.ContextualHenkinSemantics
import Mettapedia.Logic.HOL.Syntax.Subst
import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Syntax.ConstMap
import Mettapedia.Logic.HOL.DefinitionExtensionSemantics
import Mettapedia.Logic.HOL.Syntax.TypeSubstitution
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation
import Mettapedia.Logic.HOL.TypeSubstitutionSemantics
import Mettapedia.Logic.HOL.Syntax.TypeSubstitutionComposition
import Mettapedia.Logic.HOL.TypeSubstitutionCompositionSemantics
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.Logic.HOL.FullDomainInstitution
import Mettapedia.Logic.HOL.Semantics.LogicalRelationModel
import Mettapedia.Logic.HOL.TypeDerivedSignature
import Mettapedia.Logic.HOL.TypeDerivedSignatureExamples
import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.TransitionInvariant
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.BetaNormalization
import Mettapedia.Logic.HOL.ConversionTiers
import Mettapedia.Logic.HOL.CheckableFragment
import Mettapedia.Logic.HOL.Semantics.StandardTransport
import Mettapedia.Logic.HOL.TwoMembershipModels
import Mettapedia.Logic.HOL.StandardSemanticsBubbles
import Mettapedia.Logic.HOL.InstitutionTrinity
import Mettapedia.Logic.HOL.ProofSyntaxModulo
import Mettapedia.Logic.HOL.ProofSyntaxModuloStructural
import Mettapedia.Logic.HOL.ProofSyntaxModuloKripke
import Mettapedia.Logic.HOL.ProofSyntaxModuloConservativity
import Mettapedia.Logic.HOL.ImpredicativeProofModulo
import Mettapedia.Logic.HOL.ImpredicativeKripke
import Mettapedia.Logic.HOL.PublishedFacts
import Mettapedia.Logic.HOL.HornConsequence
import Mettapedia.Logic.HOL.Embedding.InferenceRuleInstances
import Mettapedia.Logic.HOL.ProofCarryingPipeline
import Mettapedia.Logic.HOL.UniformListMapFusion
import Mettapedia.Logic.HOL.Embedding.GroundUnaryEquationalProofSyntax
import Mettapedia.Logic.HOL.Lindenbaum
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.LindenbaumSet
import Mettapedia.Logic.HOL.PrimeHenkinExtension
import Mettapedia.Logic.HOL.Syntax.FreshConst
import Mettapedia.Logic.HOL.CanonicalQuantifierBridges
import Mettapedia.Logic.HOL.WitnessedExtension
import Mettapedia.Logic.HOL.WitnessedSaturation
import Mettapedia.Logic.HOL.MaximalConsistent
import Mettapedia.Logic.HOL.WitnessedWorld
import Mettapedia.Logic.HOL.IntuitionisticWorld
import Mettapedia.Logic.HOL.WorldEquality
import Mettapedia.Logic.HOL.ClassicalExcludedMiddle
import Mettapedia.Logic.HOL.ClassicalWorld
import Mettapedia.Logic.HOL.Semantics.Satisfaction
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Logic.HOL.Semantics.ModelPropertySoundness
import Mettapedia.Logic.HOL.StandardAxiomProperties
import Mettapedia.Logic.HOL.HenkinInstitution
import Mettapedia.Logic.HOL.HenkinInstitutionDerivation
import Mettapedia.Logic.HOL.HenkinInstitutionCanary
import Mettapedia.Logic.HOL.Semantics.KripkeHenkin
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCountermodel
import Mettapedia.Logic.HOL.Semantics.ForkedFrameCountermodel
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonicalGeneral
import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mettapedia.Logic.HOL.Semantics.HeytingCompleteness
import Mettapedia.Logic.HOL.Semantics.GoedelDummett
import Mettapedia.Logic.HOL.Semantics.GoedelDummettCountermodel
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinBridge
import Mettapedia.Logic.HOL.TermModel.Domain
import Mettapedia.Logic.HOL.TermModel.Truth
import Mettapedia.Logic.HOL.TermModel.Realize
import Mettapedia.Logic.HOL.TermModel.Denote
import Mettapedia.Logic.HOL.TermModel.PreModelWrapper
import Mettapedia.Logic.HOL.TermModel.Fundamental
import Mettapedia.Logic.HOL.TermModel.HenkinCompleteness
import Mettapedia.Logic.HOL.Semantics.KripkeFrameModel
import Mettapedia.Logic.HOL.Semantics.ProofSyntaxModuloKripkeHenkin
import Mettapedia.Logic.HOL.Semantics.ImpredicativeKripkeHenkin
import Mettapedia.Logic.HOL.PropositionalSlice

/-!
# Higher-Order Logic Core

Public interface for HOL: the trusted substrate plus the completed **classical Henkin
completeness** development.

Substrate:
- typed syntax and substitutions, const-map transport,
- extensional natural deduction, closed-theory provability,
- Lindenbaum machinery, prime-extension infrastructure.

Completeness (Henkin 1950 for the theory of types — sorry-free, axiom-clean):
- the fresh-constant generalization `provable_all_intro_fresh` and the Henkin
  witnessing/saturation chain (`witnessLimit_consistent`, `exists_witnessAxiom`),
- the Lindenbaum maximal extension and the classical canonical world
  (`exists_classical_world`, including the `all_counterexample` field),
- the canonical Henkin **general** term model (`TermModel/`), the fundamental lemma,
  and `models_iff_mem`,
- the headline `ClosedTheorySet.henkin_satisfiable` (`TermModel/HenkinCompleteness`): a
  consistent *witnessed + excluded-middle* theory has a Henkin general model satisfying it.
- the corollary `ClosedTheorySet.henkin_model_exists_of_consistent_classical` and its
  extensional form: a consistent theory over `WithParams` in which no parameter occurs
  and which proves every excluded-middle instance has a Henkin general model of the
  theory itself (instances in `TermModel/HenkinCompletenessControls`).
- over the original signature, `SevenVirtues.provable_iff_valid` and
  `SevenVirtues.consistent_iff_satisfiable` (`SevenVirtues/Completeness`): with excluded
  middle as one axiom, the calculus is sound and complete for extensional Henkin models
  over countable signatures with a closed term at each base type.

Kripke models and the propositional slice:
- `Semantics.KripkeFrameModel.model`: every preordered set of worlds, with carriers and
  admissible constants, gives a Kripke-Henkin general model, with impredicative
  quantification over all admissible values. Equality of base elements may grow along the
  worlds, and admissible functions respect it.
- `Semantics.ProofSyntaxModuloKripkeHenkin`, `Semantics.ImpredicativeKripkeHenkin`: proofs
  modulo conversion are sound for Kripke-Henkin general models, and the impredicative
  connectives mean conjunction, disjunction, falsity and existence there.
- `PropositionalSlice`: on propositional formulas, the EM-free calculus proves exactly the
  intuitionistic tautologies and is complete for Kripke-Henkin general models
  (`provable_iff_int`, `provable_iff_kripkeHenkin`); with the excluded-middle schema it proves
  exactly the classical tautologies and is complete for extensional Henkin models
  (`provable_em_iff_cl`, `provable_em_iff_henkin`).
- `ProofSyntaxModuloKripke`, `ImpredicativeKripke`: proofs modulo conversion are sound for
  Kripke models whose propositions are all upward-closed sets, and the impredicative
  connectives mean conjunction, disjunction, falsity and existence there.

Legacy `WorldModelCompleteness.lean` (hypothesis-parameterised) is retained but is not
the active completeness interface.
-/
