import Mettapedia.GSLT.LanguageDef.ResourcePreorder
import Mettapedia.GSLT.LanguageDef.ResourceMachineBounds
import Mettapedia.GSLT.LanguageDef.ResourceSelection
import Mettapedia.GSLT.LanguageDef.ResourceExecutionControls
import Mettapedia.Logic.ProofSearch.CertificateBounds
import Mettapedia.Logic.ProofSearch.SearchBounds
import Mettapedia.Logic.ProofSearch.SearchTransportControls
import Mettapedia.Logic.ProofSearch.ExecutedBudgetsControls
import Mettapedia.Logic.ProofSearch.FiniteCertificateExecutionControls
import Mettapedia.Logic.ProofSearch.FirstCertificateExecutionControls
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ExecutedSoundness
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ProofRunExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremCommandExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.SlotExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AssertionMatchExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.RecursiveMatchExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AllocationExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremSignatureExecution
import Mettapedia.Languages.HOLLight.MM0Meaning
import Mettapedia.Languages.HOLLight.ModelInstanceCoherence
import Mettapedia.Languages.HOLLight.ConstantHistoryInstanceCoherence
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionFamily
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionModels
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionSupport
import Mettapedia.Languages.HOLLight.ConstantHistoryExpandedTypes
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionInstances
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionExtensions
import Mettapedia.Languages.HOLLight.MixedDefinitionHistory
import Mettapedia.Languages.HOLLight.InferenceCompilerSize
import Mettapedia.Languages.HOLLight.QuantifierEmission
import Mettapedia.Languages.HOLLight.ArgumentVectorProgram
import Mettapedia.Languages.HOLLight.ArgumentListProgram
import Mettapedia.Languages.HOLLight.RuleArgumentRendering
import Mettapedia.Languages.HOLLight.RuleArgumentProgram
import Mettapedia.Languages.HOLLight.RuleArgumentRetentionProgram
import Mettapedia.Computability.FramedWordMappingControls
import Mettapedia.Computability.StackMachineCompositionSpaceControls
import Mettapedia.Languages.Megalodon.NormalizationGrowth
import Mettapedia.Languages.Megalodon.NormalizationSharing
import Mettapedia.Languages.Lean.Lean4LeanRungTwoTypedBoundary

import Mettapedia.Languages.HOLLight.ArgumentNamingMachine
import Mettapedia.Languages.HOLLight.QuantifierArgumentEmission
import Mettapedia.Languages.HOLLight.QuantifierArgumentProgram
import Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily
import Mettapedia.Languages.HOLLight.MixedTypeDefinitionModels
import Mettapedia.Languages.HOLLight.MixedTypeDefinitionExtensions
import Mettapedia.Languages.HOLLight.MixedDefinitionModels
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MatchAuthority
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AllocationResolution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AllocationRunExecution
import Mettapedia.Languages.HOLLight.DefinitionSchemaClosure
import Mettapedia.Languages.HOLLight.DefinitionSchemaInstances
import Mettapedia.Languages.HOLLight.SourceQuantifierEmission
import Mettapedia.Logic.ProofSearch.ShortCircuitCertificateExecution
import Mettapedia.Logic.ProofSearch.ShortCircuitBoundedSearch
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ConstructorExecution
import Mettapedia.Languages.HOLLight.DefinitionSchemaSubstitution
import Mettapedia.Languages.HOLLight.DefinitionHistorySchemas
import Mettapedia.Languages.HOLLight.ClaimCheckingMachine
import Mettapedia.Languages.HOLLight.DefinitionHistoryMeaning
import Mettapedia.Languages.HOLLight.UniversalDefinitionHistory
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.RecordedWitnessAuthority
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremMatchExecution
import Mettapedia.Languages.HOLLight.UniversalDefinitionMeaning
import Mettapedia.Computability.FramedFieldSelection
import Mettapedia.Languages.HOLLight.CachedClaimChecking
import Mettapedia.Languages.HOLLight.CachedClaimCheckingProgram
import Mettapedia.Languages.HOLLight.SharedPremiseProgram
import Mettapedia.Languages.HOLLight.SchemaAxiomEmission
import Mettapedia.Languages.HOLLight.SourceRuleSpecializationProgram
import Mettapedia.Languages.HOLLight.DynamicModusPonensTreeProgram
import Mettapedia.Languages.HOLLight.OriginalChildJobsProgram
import Mettapedia.Languages.HOLLight.AuthoredNodeDispatchProgram
import Mettapedia.Languages.HOLLight.GraphAddressAdditionProgram
import Mettapedia.Languages.HOLLight.GraphAddressSequenceProgram
import Mettapedia.Languages.HOLLight.GraphRelocationEmission
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremApplicationExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremDriverExecution
/-!
# Resource-aware proof checking

This entry point joins the executed resource theory and its checked system
fragments. Original configured authority, certificate translation, discovery,
checking, output storage and peak live storage remain separate objects.
Polynomial translations form a preorder under physical composition; general
executed clocks need not be polynomial. Exact replay of a compiler's output
does not imply reflection or efficient extraction from arbitrary host proofs.

The MM0 modules qualify original acceptance and actual quoted command
fragments. Their whole-file theorem retains declaration-correspondence
premises. The HOL modules connect configured acceptance to source derivation
and model truth, construct full-domain models of arbitrary admitted mixed
constant/type histories, and execute argument-vector rendering and joined
source admission, rendering, argument naming/SPEC emission and independent
saved-claim comparison. The original definition chronology admits existence
proofs from the preceding universal background. Its constructed model supplies
truth for actual configured acceptance and preserves validated original
type-and-term substitutions. The complete translator driver remains a further join.
These imports do not assert that either whole source kernel has been
qualified end to end.

The Mathdata profile exhibits exponential full-tree emission alongside
polynomial shared storage. It does not identify that modeled normalizer with
the original Megalodon conversion algorithm. The Lean boundary distinguishes
raw beta/delta execution from typed kernel authority. Neither profile claims
a single universal numeric tier or verification of the whole Lean kernel.
-/
