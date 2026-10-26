import Mettapedia.Logic.InferenceBasisControls
import Mettapedia.Logic.InferenceBasisCompilerControls
import Mettapedia.Logic.HOL.GuardedRetractionControls
import Mettapedia.Languages.HOLLight.GuardedRetraction
import Mettapedia.Languages.HOLLight.InferenceOnlyReplayControls
import Mettapedia.Languages.HOLLight.TypeDefinitionEqualityControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRetraction
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLPredicate
import Mettapedia.GSLT.LanguageDef.IndexedInductiveRecursiveSpaceControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveConstructorDataControls
import Mettapedia.Languages.HOLLight.PredicateFixedPoint
import Mettapedia.Languages.HOLLight.PolynomialPredicate
import Mettapedia.Languages.HOLLight.PointedPredicate
import Mettapedia.Languages.HOLLight.DefinitionReplayModels
import Mettapedia.Languages.HOLLight.TypeInstantiationCertificates
import Mettapedia.Languages.HOLLight.PointedPredicateInstantiation
import Mettapedia.Languages.HOLLight.RegisteredSubstitution
import Mettapedia.Languages.HOLLight.RegisteredPointedPredicate
import Mettapedia.Languages.HOLLight.RegisteredPointedTypeDefinition
import Mettapedia.Languages.HOLLight.RegisteredPointedModels
import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
import Mettapedia.Languages.HOLLight.RecursiveSpaceSourceReadback
import Mettapedia.Languages.HOLLight.IndexedRegisteredFamilyModels
import Mettapedia.Languages.HOLLight.RecursiveSpacePredicate
import Mettapedia.Logic.HOL.IndexedFamilyPredicate
import Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions
import Mettapedia.GSLT.LanguageDef.InferenceBasisBoundary
import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.HeuristicEvidence
import Mettapedia.Computability.FuelledConversionEvidence
import Mettapedia.Languages.Metamath.CheckingDiscipline
import Mettapedia.Languages.MM0.CheckingDiscipline
import Mettapedia.Languages.MM0.NaturalClosure
import Mettapedia.Languages.MM0.NaturalInduction
import Mettapedia.Languages.MM0.NaturalCarrier
import Mettapedia.Languages.MM0.NaturalType
import Mettapedia.Languages.MM0.NaturalRecursion
import Mettapedia.Languages.MM0.NaturalFactsMeaning
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorRawPreservation
import Mettapedia.Languages.MM0.HOLTypeDefinitionBoundary
import Mettapedia.Languages.HOLLight.KernelAtlas
import Mettapedia.Languages.Megalodon.FuelledConversionProfile
import Mettapedia.Languages.Megalodon.FuelledConversionWitness
import Mettapedia.Languages.Megalodon.NaturalTheoryProfile
import Mettapedia.GSLT.LanguageDef.StandardSemanticAuthorityProfiles
import Mettapedia.Logic.HOL.ConversionTiers
import Mettapedia.Logic.HOL.CheckableFragment
import Mettapedia.Languages.HOLLight.RetainedElaboration
import Mettapedia.Languages.MM0.Kernel.SubstitutionStability
import Mettapedia.GSLT.Dedukti.ConstructionsConsistency
import Mettapedia.GSLT.Dedukti.HOLHubRoundTrip
import Mettapedia.TypeTheory.HypercubeBubbles
import Mettapedia.TypeTheory.ReifiedIndexElaboration
import Mettapedia.TypeTheory.HypercubeHOLHub
import Mettapedia.TypeTheory.HypercubeProfileStratification
import Mettapedia.TypeTheory.HypercubeSortRenaming
import Mettapedia.TypeTheory.PositiveInductiveScenarios
import Mettapedia.TypeTheory.IndexedPositiveContainer
import Mettapedia.TypeTheory.IndexedPositiveContainerInduction
import Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge
import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
import Mettapedia.GSLT.LanguageDef.ModuleSource.MutualWorkflowActionLowering
import Mettapedia.GSLT.LanguageDef.PositiveInductiveWorkflowActionGuest
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLFacts
import Mettapedia.GSLT.LanguageDef.IndexedInductiveBooleanHOL
import Mettapedia.Logic.HOL.GuardedQuantifierTransport
import Mettapedia.Languages.HOLLight.GuardedQuantifierTransport
import Mettapedia.Languages.HOLLight.BooleanFacts
import Mettapedia.GSLT.Dynamics.NaturalBackendHOLFacts
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal
import Mettapedia.Languages.MeTTa.Bridges.GSLT.FormationSensitiveBundleTraversal
import Mettapedia.GSLT.LanguageDef.NestedInductiveGuestBoundary
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveRegisteredListGuestLift
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveIndexedContainerBundleRealization
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestControls
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeElaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultsChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultUniversesChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllOriginalInputUniversesChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultLevelTransport
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerNativeResultAdapter
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestResultControls
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultChecking
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerUniverseControls
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerUniverseTreeControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverseMaps
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlansControls
import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeAuthorityBoundary
import Mettapedia.Languages.MeTTa.Bridges.GSLT.LFProfileAtomWire
import Mettapedia.Languages.MeTTa.Bridges.GSLT.HOLConversionPolicyAtomWire
import Mettapedia.TypeTheory.DependencyDescentCriterion
import Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport
import Mettapedia.TypeTheory.EqualityFamilyObserverFactorization
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
import Mettapedia.TypeTheory.ContextualCodeObserverFactorization
import Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeExecution
import Mettapedia.Languages.MeTTa.EquationKernel.Execution
import Mettapedia.Languages.MM0.Formats.MMB.MachineCost
import Mettapedia.Languages.Lean.HintedHeadConversion
import Mettapedia.GSLT.Logic.PropositionalLRAT
import Mettapedia.Logic.ProofSharingBounds
import Mettapedia.Logic.PropositionalHilbertChecking
import Mettapedia.Logic.PropositionalExtension
import Mettapedia.Logic.IntuitionisticDecision
import Mettapedia.Logic.EqualityRecipe
import Mettapedia.Logic.CertificateConservativeExtension
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorComputationProfiles
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorCheckingProfiles
import Mettapedia.Languages.MeTTa.Bridges.GSLT.NatVecCheckingProfileAtomWire
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedAppend
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeNaturalDomain
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeNaturalDecoderReturn
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendElaboration
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalHOL
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodon
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodonProfile
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMM0
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendChecking
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSource
import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedPolynomialGeneratedChecking
import Mettapedia.TypeTheory.IndexedPolynomialGuardedRepresentation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRawBoundary
import Mettapedia.Languages.Lean.Lean4LessCheckerBoundary
import Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower
import Mettapedia.Languages.Lean.LeanCheckerReleaseReceipt
import Mettapedia.Languages.VibeITP.CheckingMachine
import Mettapedia.Languages.Metamath.CheckingMachine
import Mettapedia.Languages.GuardedAtomRule.CheckingMachine
import Mettapedia.Logic.RuleMulticategoryKernels
import Mettapedia.Logic.MultiPremiseSteps
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFreeMulticategory
import Mettapedia.GSLT.Logic.PropositionalLRATActions
import Mettapedia.GSLT.Logic.KripkeTruthChecking
import Mettapedia.Languages.HOLLight.FirstOrder.PortableKernel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Checking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCheckingOSLF
import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLTowerModel
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLReadingComparison
import Mettapedia.Logic.HOL.ConversionRecipes

/-!
# Inference kernels: primitive bases, evidence and resources

The supplied MM0 HOL example's abstraction/representation equation is
checked against the maintained OpenTheory source checker
(`MM0.HOLTypeDefinitionBoundary`). Given `abs : A → N`, `rep : N → A`
and `a : N`, the operands have type `N`: equality at `N` checks, and equality
at `A` refuses when the types differ. The native source declaration exposed
the latter index. Both local example files now use the defined-type index;
the compiler, independent verifier and native qualification retain the
original argument/premise inventory and refuse the reverted specification.
This is a supplied-presentation typing repair, not an inconsistency theorem
or a proof of the full compiler/checker refinement. The retained native
closure/induction proof dependencies do not use the repaired axiom.

The conversion-policy graph now has proof-producing HOL edges over arbitrary
simple base sorts and typed constants (`HOL.ConversionRecipes`). Beta
permissions inspect the contracted redex type, eta permissions inspect its
domain and codomain, and equation permissions retain declaration occurrences.
Explicit typed substitution and binder congruence preserve the original judgment
fibre. Finite recipes check exactly the independently specified conversion
closure, reconstruct their submitted evidence trees and elaborate to retained
ordinary HOL equality proofs. Their OSLF reachability predicates agree with
certificate existence. Policy growth preserves these observations; reverse
transport, equal checking expense and identical histories do not follow.

`HOL.ProofSyntaxModulo.hasHOLProof` supplies the logical edge for the existing
implication/universal modulo calculus when every equation has a retained HOL
receipt. Proposition-valued conversion gives existence, while checked recipes
give actual proof reconstruction. Tactics and other elaboration producers
submit to the same checker through `HeuristicEvidence.screen`; they supply
no additional authority. This is not yet a raw-byte HOL checker, a full
dependent-fragment reflection theorem or a completed three-native-kernel join.

Two independently admissible rule packages over the same base compose
without changing derivability (`extendRules_union_sameDerivability_iff`).
Actual certificate compilers combine with the original local node budgets
(`AdditionalRuleCertificateCompiler.combine`). This logical composition law
does not discharge normalization or decision obligations of joined conversion
engines. Extensional semantic readouts and operational realizations remain
different graph edges with their separately declared observations.

Judgment, evidence, authority and execution observations are distinct
coordinates. Reachability is a genuine equation-kernel judgment; complete
evaluation results and mathematical multi-premise inference are other
judgments. Local rule data, trees, DAGs and finite licensed traces are
evidence representations. Logical LCF construction protects checked
judgments without requiring proof erasure; native capability enforcement
and optional evidence export remain separate implementation contracts.

The existing formation-sensitive dependent calculus now has an exact
`RuleWitness` connection (`FormationSensitiveChecking.interface`). Local
codes check the actual fourteen-rule signature, using finite structural
conversion evidence. Common trees, shared graphs and minted checked
judgments characterize the source typing relation. The maintained structural
replay checker also mints the same logical judgment directly; its existing
telescope certificates supply the formed-context boundary. The selected
instance is the already admitted natural-level cumulative tower
(`Tower.Checking.coverage`), not a new foundation or a full Lean profile.

The simple-inductive generator's actual constructor inventory now supplies
the same finite root interface (`IndexedPolynomialGenerated.Checking.decoder`).
Its raw iota relation and finite conversion recipes agree exactly. A separate
bidirectional evidence producer (`FormationSensitiveElaboration`) checks core
terms through the maintained replay boundary. Restricted implicit inference
reuses scoped schema matching, requires every omitted parameter to be
determined, and checks the resulting explicit application. These joins do
not identify annotated typed equality with structural conversion, generate
indexed guest eliminators, or establish a native C implementation.

The declared natural/vector instance also has a checked core append program
(`NativeNaturalVectorFamilies.Programs.append_typed`). Its motive universe
is selected by the existing level-instantiation morphism, retaining the
schematic element universe. Emitted finite evidence is checked against the
entire dependent function type; evidence production is outside that proof.
Its nil and cons equations hold under arbitrary scoped substitutions. The
scoped constructor-clause compiler consumes the admitted vector inventory,
abstracts written calls on recursive tails, and produces exactly that checked
core (`IndexedInductive.AppendElaboration.compiled_matches_reference`). The
concrete source interface carries noncomputable index meaning, so this is a
kernel-evaluated comparison rather than a qualified executable source reader.
Its compiled function is also typed by the actual natural-iota-only policy,
with full judgment inclusion into the original four-row declaration calculus.
The rejected smaller submissions show required permissions for this evidence,
not a global minimality or unprovability theorem.
The text frontend, full computational admission, set denotation and native
execution remain separate links.

MM0's existing natural-closure proof route also has closure-premised induction
(`Languages.MM0.NaturalInduction`). Its step needs the property only at
generated elements. The common intrinsic strengthened predicate is admitted
by Henkin term closure when its parameters are admitted, without full
function domains. A three-point interpretation separates that guard from an
ordinary unguarded step. The compiled source proof and independent expected
definition/statement are checked by upstream MM0 and the existing native
service; the same gate retains its ordinary-closure profile. This does not
supply primitive recursion, successor no-confusion or an infinite carrier.

The selected textual Nat/Vec/append fixture now has a finite executable
source route (`IndexedInductive.AppendSource`). The shared module reader and
maintained nullary-name resolver feed named constructor clauses to the same
compiler. Addition is compiled from its own preceding clauses. The resulting
append is exactly the independent checked function; its source vector plans
agree with the admitted inventory uniformly in payload type. The actual
declaration source is separately compared with the admitted Nat/Vec example.
This is correctness of the selected input, not of the untrusted producer for
all modules. Packed parsing, general typed operation-signature syntax,
uniform computational admission and Prime-mode execution remain open.

The informative generated vector candidate now participates in that checking
policy (`IndexedInductive.AppendChecking.signature_comparison`). Its original
declarations and two schemas join the checked natural prefix. Exact comparison
with the independent reference library justifies the executable specialization;
the selected maximum-level instantiation preserves full contexts and judgments.
The actual textual append checks against this generated policy. A source-bounded
schema embedding preserves acceptance and refusal, composes along links, and
prevents an invalid local ordinal from naming a different package's global row
(`SchemaTableConversionCode.Linking.decode_relocate`). Typed argument replay
also has exact finite-certificate coverage for a fixed occurrence and assignment.
This is not uniform computation admission.

The source comparison also retains the complete generated declaration library.
The live grammar reader submits its actual proposal to this generated policy,
with only the two natural rows enabled (`AppendChecking.replaySource_sound`).
The selected positive gate requires exact source-data agreement and records
the original enabled ordinals; this does not qualify all source modules or
the whole runtime chain.

The four actual canonical rows now have independent annotated typing proofs,
formed telescopes and checked agreement with the variable types and result
types inferred from their patterns (`Programs.Annotated.template_typed`).
Under typed simultaneous substitutions, licensed rows give admitted typed
equalities, with their arguments' annotations retained. Erasure gives the
selected raw typed-equality judgment, not an identification with the separate
formation-sensitive structural-conversion calculus. Former injectivity is
still an explicit premise of the wider annotated root-preservation result.
The natural-only policy satisfies unrestricted annotation lifting; the vector
patterns repeat parameters and need a separate coherence argument for that
lifting route. Neither classification establishes normalization or native
implementation correctness.

The actual opaque annotation now has unconditional former injectivity and
no-confusion (`Annotated.inactive_formerFacts`). All eight declarations and
the existing level/head policy remain; only the selected iota permissions are
disabled. The shared no-root theorem supplies the former facts, including
the richer typed equality. The common cumulative head-preservation law is
also reused by the existing set-profile client. Together these give
contextual beta/projection/head preservation and equality at the original
dependent type for this opaque annotation. The actual addition function is
typed there and has a checked beta step. Its product type is not a universe,
and its iota citation still refuses until computation is enabled. No former
facts for enabled Nat/Vec rows or annotation-coherence theorem follows.

The natural-only annotation also has a nontrivial domain reading
(`Annotated.NaturalDomain.valid`). The actual natural declaration,
constructors and dependent recursor agree with the maintained numeral
interpretation. Original row lookup reduces both enabled iota instances to
its projected recursor laws, retaining argument-spine and result-type
premises. The actual annotated one-plus-zero proof denotes successor of zero;
zero and successor of zero remain distinct, and their false annotated
equation is refuted. All eight declarations remain present, with the other
constants opaque. This is semantic validity of this selected policy, not
logical-relation adequacy, enabled former facts or native implementation
qualification.

The enabled natural annotation now also uses the maintained package sum to
add fresh opaque proposition/decoder declarations (`NaturalDomain.Decoder`).
The shared spine-fact transport and `ReadingValid.sum_opaque` prove semantic
validity without dropping original computation. Exact root coverage and the
required-premise comparison retain both original natural rows. An actual
zero step and the original typed one-plus-zero proof survive, while the false
constructor equation still refuses. This gives a forward judgment map and
valid semantic extension. Recursor adequacy and enabled former facts remain
separate from validity.

The return interpretation now expands the two decoder names to the existing
universe and identity definitions. A common schema-constant interpretation
law preserves the complete required-premise substitution as well as the root.
All eight declared types and all four row templates have checked support;
the resulting return map is uniform over their permission selections.
`NaturalDomain.Decoder.fixed_statement_iff` proves equal derivability for
statements fixed by the return map, retaining contexts and displayed types.
The actual natural-only and full-policy addition examples reflect, and a
fresh proposition has a changed, well-typed image. The natural-only false
constructor equation refuses through the return route too. This is a
theorem-level judgment interpretation, without a serialized proof-data
roundtrip, annotation-coherence result or native cost claim.

Accepted source constructor methods now have an operational reconstruction
law (`IndexedInductive.CaseElaboration.compileMethods_reduces`). Applying every
emitted method to its original fields and declared recursive results restores
its submitted body by beta reduction, in source order. The named-rule adapter
retains the exact matched left side and resolved right side; independently
checked append methods instantiate this law. Proposed calls still require
an admitted-inventory comparison and the result still requires typed replay.
This does not establish arbitrary nested source-plan generation.

Carrier qualification also retains emptiness. The admitted recursive-only
family has no finite values, proved by its generated fold into the empty type.
An explicit semantic Hilbert-choice family supplies inhabitants and therefore
precludes a faithful direct interpretation of that source as a simple base
type. A generic guarded reading instead represents the source inside an
inhabited Option carrier. Its typed HOL guarded universal and existential
formulas agree with source quantification. On the empty source, dropping the
guard changes both verdicts. Total source functions are equivalent to strict,
guard-preserving host extensions, with identity/composition coherence. Typed
HOL quantifiers over that function image agree with source quantification.
A non-strict extension can agree on every valid input and still differ at the
added invalid input; interface-relative agreement is therefore explicit. This is a semantic interpretation boundary, not
complete native-theory qualification or generic guarded proof emission
(`IndexedInductive.HOLFacts.InhabitanceBoundary.no_direct_choice_model`,
`IndexedInductive.HOLFacts.InhabitanceBoundary.guardedAll_iff`,
`IndexedInductive.HOLFacts.InhabitanceBoundary.guardedEx_iff`).

The admitted finite Boolean family has a selected native HOL Light fact
route (`IndexedInductiveBooleanHOL`). Its generated source fold commutes with
the explicit classical logical-Boolean reading. Recursion, induction,
constructor separation, cases and finiteness have typed statements and exact
native proof replay. A semantic choice family suffices for recursor
admissibility in the declared Henkin models; this is not a necessity claim.
The selected structural manifest omits infinity, and the finite source carrier
cannot supply an infinity witness. This selected fact interface is distinct
from general datatype proof generation, native-C refinement and release
provenance.

Guarded representation comparisons now have a reusable native HOL library.
Two maps preserve the declared guards and are inverse on valid values;
universal and existential observations transport with the predicate's actual
forward-map action. Both typed formulas are proved in every Henkin model,
without a full-domain or choice premise. An inhabited representation of an
empty carrier refutes the formula obtained by dropping the target guard. A
valid Boolean swap is a nonidentity positive comparison. Independent original
HOL Light proofs replay the same exact formulas through the native service.
Their explicit-rule closure retains five logical definitions and no AXIOM
nodes, and replays under the existing sealed axiom policy. This supplies logical transport lemmas, not a comparison certificate
for every representation or generic datatype proof generation
(`HOL.GuardedQuantifierTransport.all_models`,
`HOL.GuardedQuantifierTransport.guard_erasure_counterexample`,
`HOL.GuardedQuantifierTransport.Examples.swap_comparison`).

For the semantic observation class containing every predicate, exact
universal truth transport and exact existential truth transport each
characterize the image of the valid source values. Injectivity is not
necessary for those truth observations: projecting a pair of Booleans to its
first component preserves both quantified observation families and loses a
source coordinate. Consequently, truth agreement alone cannot qualify a
faithful value or witness comparison. This semantic boundary leaves the
native library's inverse-comparison admission contract unchanged
(`HOL.GuardedQuantifierTransport.exists_observations_iff_image`,
`HOL.GuardedQuantifierTransport.all_observations_iff_image`,
`HOL.GuardedQuantifierTransport.truth_transport_does_not_force_injectivity`).

The actual natural-only checking policy has a constructor-system presentation
(`ComputationProfiles.NaturalConversion`). It retains original ordinals 0 and 1;
coverage, linearity, variable coverage and non-overlap are proved for those
schemas. The maintained constructor-system theorem gives raw beta/iota
confluence and Pi/Sigma conversion boundaries. Addition at zero is a positive
witness; no raw conversion can identify the declared natural type with a Pi,
even along a path leaving the image. These are structural-conversion facts,
not annotated typed-eta former facts, a termination theorem or permission for
the repeated-parameter vector rows.

For this same actual structural policy, declaration-telescope recovery now
proves uniform root preservation (`NaturalConversion.Preservation.roots`).
The selected zero/successor rules recover their motive, methods and predecessor
from arbitrary formed-context typing, including its conversion and cumulativity
tails. `DeclarationSpine.applyTelescope` constructs the recursive call from the
renewed typed substitution. The maintained contextual theorem then preserves
the entire formed judgment under every existing contextual step. Concrete
typed zero/successor redexes, a four-step successor evaluation and refusal of
an altered Pi result provide non-vacuity and negative controls. This does not
promote raw conversion into annotated typed eta equality or admit the disabled
vector roots.

The same smaller checking judgment is preserved by all four original
operational iota roots (`Preservation.operational_roots`). The shared telescope
interface recovers the vector eliminator's six arguments and the cons
constructor's four arguments. The latter renew the original canonical context;
its contractum retains the actual recursive call and the source's exact
displayed type. Concrete canonical nil/cons sources are independently checked
under the smaller policy. Their operational steps preserve typing while the
cons citation remains refused as a checking conversion and is accepted by
the full policy. This is root preservation across two selected relations;
unrestricted dependent contextual closure requires a further transport law.

The actual natural computation inside append's length index now has a complete
Church-annotated function (`Annotated.Functions`). Its real motive and recursive
argument domains are typed using the existing declarations and finite typed
beta conversions. The maintained bidirectional annotator reconstructs that
independently typed function exactly. Typed zero/successor equations retain
their original row permissions. The closed function stays typed with all iota
roots disabled; a second genuinely typed motive has the same erasure but a
different domain.

The full dependent append now consumes that annotated addition. All six
eliminator arguments have independent dependent-telescope typings. Its
constructor method uses the permitted natural successor equation to retain
the exact result index; the nil branch uses the permitted zero equation.
Abstraction over the original five-entry context yields the actual closed
function at its dependent type. Both erase to the maintained raw M1 program
and type, and the existing annotator reconstructs this independently typed
function exactly. Omitting its expected type still erases to the source but
loses its domain annotations. This finite function proof does not discharge
uniform richer-package former facts, unrestricted vector annotation coherence
or enabled-vector-root computational admission.

The actual append nil and cons equations now retain their exact vector-row
permissions and typed simultaneous assignments (`Append.append_nil`,
`Append.append_cons`). A general relative-telescope beta law applies the method
arguments in declaration order while preserving its ambient variables and
substituted dependent type. Closed nil/nonempty-cons examples and typed erasure
retain the original recursive target. The same function is typed with both
vector rows disabled, while its concrete vector computation certificates refuse
under that smaller policy and accept under the full one. These finite program
equations still do not supply unrestricted vector annotation coherence or
uniform richer-package former facts.

Schema-family inclusions over the same declaration table now construct actual
premise-preserving annotated package morphisms. Their general composition
follows each target premise back through both edges. The selected Nat/Vec
permission edges preserve full statements, formed contexts and typed
substitutions. Actual append crosses natural-only, natural-plus-vector-nil and
full policies through the composed morphism; its closed nil equation holds at
the intermediate node, where its actual cons certificate still refuses.
These edges concern judgment and computation support, not full named-prover
compatibility, reverse transport or cost preservation.

The sequentially admitted natural carrier also interprets the existing HOL
Peano formulas (`IndexedInductiveNaturalHOL.models_axioms`). Its original
polynomial eliminator supplies the unique-recursion schema at every target
simple type (`models_recursion`), and its actual successor/zero equations
give no-confusion and an infinite carrier. This is a particular full-domain
semantic interpretation, not derivation extraction, a general Henkin claim,
or identification with the native source proof stream.

The actual retained HOL Light roots now share independently typed intrinsic
statements (`HOL.NaturalFacts`, `HOLLight.NaturalFacts`). They retain numeral
wrapping, result-before-predecessor recursion and Boolean successor equality.
An additional carrier-infinity theorem is derived from successor injectivity
and no-confusion. All five statements have the authored carrier's constructed
meaning at arbitrary result carriers; a Boolean recursion instance and a
collapsing finite countermodel witness the boundary. The native gate checks a
23225-node source closure and 67384 replay records, exact typed/source output
identity and altered claim/axiom/truncation plus packet refusals. The standard
HOL policy's three axioms remain declared. This is the selected law-signature
interface, not full source definition-history refinement or a proof of linked C.
MM0 and HOL Light reuse one intrinsic binder-naming interface; their printers
both commute with typed variable renaming.

The native Mathdata natural-closure definition and its zero, successor and
induction statements now have exact intrinsic HOL readings
(`Megalodon.NaturalClosure`). The first two finite proof objects also pass
the executable Lean Mathdata checker. The same predicate holds of every value
of the authored carrier; a collapsing successor fails that source comparison
(`IndexedInductiveNaturalMegalodon`). Native replay independently checks six
axiom-free source proofs and compares the exact definition and three statements
in both CeTTa dialects.

The shared closure syntax and Henkin interpretation live in
`HOL.NaturalClosure`. MM0's HOL syntax producer commutes with variable
renaming. Its independent specification prints the definition body from that
typed term; the actual MM1 proofs establish zero, successor and ordinary
closure elimination. Native CeTTa replay passes exact statements and altered
definition/conclusion/premise controls in HE, PeTTa and Prime modes. A separately
built upstream verifier checks the same artifact. This is the supplied HOL
presentation, not a completed adequacy theorem for all its axioms or the full
Nat recursion/no-confusion/infinity export.

The selected recursion extension (`Megalodon.NaturalRecursion`) defines the
least recursion graph and proves conditional unique recursion without imported
axioms. The actual exported batch replays through compiled Lean checking and
the native CeTTa checker. An independently typed, semantically interpreted
statement is erased and checked against the retained native proof. The graph's
full-domain reading agrees with the independent inductive graph, and the
authored natural interpretation identifies every valid selector's function
with its existing eliminator. The source successor discharges zero separation
and injectivity; a classical interpretation supplies the explicitly scoped
selector at inhabited targets. A constant-zero selector gives a wrong-result
control. Native no-confusion/infinity discharge remains a separate route.
Compiled batch acceptance is not itself a kernel-reduced Lean proof of that
finite acceptance proposition; the mathematical comparison theorems are
ordinary Lean proofs.

The optional classical natural profile makes its commitments explicit
(`Megalodon.NaturalTheoryProfile`). A polymorphic selector and its law,
double-negation elimination and Dedekind infinity are independent profile
items; none is seeded by the Egal kernel tag. They derive a selected zero and
successor, separation, injectivity, guarded induction, infinity and recursion
on the generated carrier. Native admission checks one parameter, three exact
axioms and every resulting proof; omitting any selected axiom refuses.

The corresponding authored-carrier interpretation
(`IndexedInductiveNaturalMegalodonProfile`) chooses the existing successor as
the infinite injection and the existing zero as its omitted point. Therefore
the selected operations agree at the mathematical boundary, and graph-selected
recursion agrees with the maintained source eliminator at every result type.
A singleton refutes the infinity option, and a constant successor refutes the
authored instance. This is one optional theory node, not a new default kernel,
HOTG adoption, parametricity theorem or complete source-compiler refinement.

The admitted Nat/Vec package also has an explicit checking-profile graph
(`NativeNaturalVectorCheckingProfiles`).  The minimal node retains all four
typed iota receipts without licensing conversion.  The natural intensional
node licenses exactly the two Nat rows.  The scoped logical-extensional node
layers the same Nat computation above the maintained opaque proposition- and
function-extensionality declarations.  Inclusion and strict separation are
proved per capability field; dependent append is typed in the latter two
nodes and refused by the minimal replay.  No iota receipt is treated as an
object-theory equality proof, and the scoped node adds neither judgmental
extensionality, UIP nor equality reflection.  The general
intensional/extensional translation remains a separate edge.

The natural node has a second, incomparable child: the full four-row raw
operational profile.  Every original Nat/Vec root preserves the natural-only
formed checking judgment, without installing the vector roots in its
conversion.  This split is forced by a checked annotation boundary.  The
natural rows lift every raw instance to annotated computation; the full table
does not.  A vector-nil source can put two distinct lambda-domain annotations
at the repeated payload positions.  Erasure identifies them and admits the raw
root, while no single annotated substitution can produce that source.  Thus
the operational and logical-extensional branches form a genuine fork.  Typed
coherent vector instances remain available; unrestricted annotation lifting
and a common upper checking node would need an explicit coherence discipline.

This graph now has a finite MeTTa-data boundary
(`NatVecCheckingProfileAtomWire`). A manifest independently names tower or
legacy-ground elimination, propositional or judgmental identity principles,
and the receipt, propositional and judgmental observations of each actual
iota-table row. Its decoder checks every finite row index. Validation refuses
judgmental iota authority unless the corresponding typed receipt is retained.
Feature union preserves this law and embeds each input checking profile in the
joined contract.

The four maintained manifests validate to the existing minimal, natural
intensional, scoped logical-extensional and full raw operational profiles;
they are not parallel reimplementations. The natural encoded profile checks
the existing dependent append evidence, while the minimal profile refuses it.
The two licensed natural rows retrieve exactly the existing typed source and
target receipts. A missing-receipt license, an out-of-range row and malformed
profile data refuse. Arbitrary optional identity data, whether propositional
or judgmental, remains a contract request until a profile-specific realization
theorem is supplied; validation alone does not prove UIP, extensionality,
normalization or native execution.

The natural-intensional manifest now carries a separate interaction
certificate. Its actual declaration-aware rules are definitionally the
existing natural-only calculus: structural beta and pair projections plus
exactly the two selected Nat iota schemas. The retained constructor-system
proof supplies Church--Rosser, Pi and Sigma conversion boundaries and formed
subject reduction for arbitrary finite forward paths
(`CheckingProfiles.Interaction.naturalIntensionalCertificate`). The encoded
manifest is packaged with that certificate
(`NatVecCheckingProfileAtomWire.Profiles.naturalIntensional_encoded_qualified`).

This closes confluence and preservation for that exact join, not total
normalization. It also does not transfer automatically to the full raw vector
child: that child still fails unrestricted annotated interaction at repeated
payload occurrences. A validated feature union and a qualified interaction
certificate therefore remain different layers.

Accepted requests map through the original formed typing judgment to the
existing set-tower interpretation
(`TowerInterpretation.Checking.request_model_sound`). Checked conversion
preserves actual set values, and checked substitution components construct
the contextual arrow used in the semantic substitution comparison. That
comparison retains annotated component typing and erasure obligations and
the named `CofinalInaccessibles` hypothesis. The mathematical HOTG packages
and material hyperset families have their own declared model scope; neither
is automatically a native Mathdata translation or a faithful higher-path
model. Model equality does not authorize additional computation rules.

OSLF supplies a comparison of selected operational observations, rather than
a distinguished checking foundation. `FormationSensitiveCheckingOSLF` connects
the original structural conversion relation, finite certificate acceptance and
reachability in the bidirectional conversion-step GSLT. Raw conversion does
not supply formed typing. A checked higher-profile request determines a
finite sufficient declaration/computation restriction with source reflection;
this is neither a smallest kernel nor automatic computational admission.

The existing operational maps carry different strengths of predicate action:
`OperationalTranslation.preserves_semanticDiamond` is forward only,
`CoveredTranslation.semanticDiamond_iff` also reflects the observation, and
`OperationalRealization.preserves_semanticReach` permits fusion and lowering.
Equation-wise agreement gives equal semantic predicate reindexing, not equal
retained executions. The basic behavioral `GSLT.Morphism` does not carry these
stronger obligations. Cost, proof transport and native authority remain
separately checked comparisons. A suitable lower checking basis may therefore
be derived from a richer dependent profile without being identified with any
currently implemented foreign kernel.

`KripkeTruth.Checking` is a separate partial-truth profile, not a change of
every object logic. Its ten local codes present the existing strong Kleene
evidence constructors exactly. Grounded signed judgments coincide with closed
proofs and accepted certificates. For finite judgment domains, the original
least-fixed-point decision agrees with that certificate authority; completed
ungroundedness is kept distinct from an unfinished checking frontier.

This entry point joins the independently checked coordinates of the kernel
atlas. Rule generation compares consequences under open hypotheses; explicit
templates construct certificates; executed translations compare machine costs.
The concrete Metamath, MM0 and HOL Light observers describe their actual
interfaces without turning an operation inventory into a complexity theorem.

Finite-budget checking separates acceptance, refusal and exhaustion. Explicit
conversion paths compose even when a fixed search budget is insufficient to
rediscover the composite. Arbitrary proposed proofs retain the same checking
authority and model soundness.

The logical core precedes any checking machine: `Logic.Derivation` gives
judgments, finitary rule instances and exact finite witnesses, while the
open-derivation owners retain hypotheses and compose evidence into premise
slots. Multiple-premise composition is multicategorical; unary rewrites give
paths. Exchange, weakening, contraction and equations between proofs belong
to the selected presentation, rather than being silently imposed by replay.
`CertificateGSLT` gives an authored finite presentation of this structure.
Its existing classifying category identifies closed source proof terms with
arrows from the empty premise context to a singleton goal via the executable
`ClassifyingContext.closedDerivationEquiv`, preserving the proof in both
directions. VibeITP and Metamath expose their source comparisons at this
proof-category level as well as through graph and machine realizations.

Multiple-premise composition is now a theorem rather than a reading. Open
derivations over a proof-relevant rule signature form the free cartesian
multicategory on it (`RuleSignature.universal`); kernel derivability is closed
derivability there (`RuleWitness.derivable_iff_derives`); accepted certificate
trees are exactly its closed morphisms (`RuleWitness.closedEquiv`); every node of
an accepted shared graph unfolds to one (`RuleWitness.unfold_root`). Authored
calculi present the same structure on their rule applications
(`CertificateGSLT.OpenDerivation.termEquiv`, `toTerm_bind`). Holes may be
discarded or reused, so the structure is cartesian; closed derivations are
linear (`Term.closed_linear`). Graph checking and unfolding are invariant under
every order that keeps premises before consumers
(`DerivationGraph.replayWith_permute_iff`, `RuleWitness.unfold_permute`), and
reuse across a theory change revalidates exactly the used instances
(`DerivationGraph.revalidate_iff`). Translations are multifunctors: the
intuitionistic-to-classical and classical-to-extended inclusions are faithful,
the second conservative and the first not reflecting
(`Hilbert.inclusion_not_reflecting`, `Extension.inclusion_conservative`); HOL
Light's rule multicategory maps into its first-order calculus, preserving and
reflecting derivability (`HOLLight.FirstOrder.translation`,
`translation_reflects`). Logical work adds over substitution
(`Term.size_subst`); affine rule images are linear on trees
(`RuleSignature.lift_size_le`), while one contracting image is exponential on
trees and linear on graphs (`Contraction.contraction_gap`). Atomic
multi-pattern steps without consumption are graph replay
(`MultiPremiseSteps.run_monotone`); consumed occurrences cannot be reused, and
the split/join process cannot be represented by the tree-shaped single-wire-cut
grammar while preserving generator and wire counts
(`MultiPremiseSteps.consumed_not_cited`, `process_not_polycategorical`). This
does not exclude other categorical presentations. LRAT's RUP actions are retained as multi-premise
rule instances (`PropositionalLRATActions.check_sound`), and RAT additions are
extensions rather than instances (`rat_not_rule_instance`).

The native execution objects use the existing `ObservedMachine` category,
with their own occurrence and verdict types. The authored GSLT recipe and
MeTTa equation workers each inspect one original DAG node and retain refusal
with its suffix. Their verdicts agree with their original checkers. Actual
terminated authored checking is equivalent to the existing reaching native
type (`GeneralRewriteRecipeExecution.exists_finished_iff_reachingNativeType`),
including the original equations and an equation-respecting target predicate. The rho
worker inspects its original inference trees, with formation checked at the
request boundary. MM0 exposes its original command/unification microsteps;
HOL Light exposes its original registered-event receiver. The Lean4Lean
instance is the executable beta/delta/head profile, with explicit normalizing
strategy hints. It is not the full Lean kernel. These are objects at their
declared observation interfaces; morphisms between different interfaces
still require explicit observation maps and resource simulations.

Storage navigation is a further realization. The borrowed cursor preserves
source addresses and a checked prefix; it is neither a primitive proof rule
nor a required representation of every native checker. A stack, stream,
tree focus or dependency schedule may realize the same evidence structure.
Focus becomes a semantic observation only when explicitly selected and
preserved by a comparison. The cursor adapters below depend on their source
theories, while those theories remain independent of cursor machinery.

VibeITP's existing authored kernel also uses the common retained source-address
checker (`VibeITP.CheckingMachine.kernelCheckingObject`). Its graph coverage and retained
roots agree with its independent static judgment under `Hosted`; its auxiliary
term-operation judgments are preserved as well. `kernelModule_read` recovers
the exact theory-extended package through the verified portable module reader
and the original validator. This data surface is distinct from the upstream
theory-builder grammar; neither native C refinement nor binary protocol
correspondence follows merely from reading a module.
Metamath's projected snapshot also instantiates that cursor. Its accepted graph
judgments coincide with successful original `DB.stepNormal` label folds under
the established prefix-projection and empty-stack conditions. Portable loading
revalidates the complete snapshot, and target-facing export checks freshness;
parser provenance and compressed-proof execution retain their separate laws.
The guarded atom-rule calculus uses its original `Evidence.Source.presentation`
on the same cursor, with graph coverage and retained-root soundness against
its original conditional-atom meaning. This preserves the calculus's accurate
name and makes no claim about HE or PeTTa evaluation.

Algorithmic Lean-style judgment and ideal typing/equality are separate
scopes (`Lean4LessCheckerBoundary.IdealBoundary`). Reproducible budgets
enumerating a fixed algorithm do not fill gaps in its ideal interpretation.
Explicit equality recipes are exact for the generated equivalence relation;
ideal completeness requires a further generation theorem. Typed reflexivity
uses a formed-expression fibre rather than arbitrary raw syntax.

Lean-family checker authority also branches by theorem strength
(`LeanCheckerAuthorityFlower`). An exact decision characterizes its authored
judgment in both directions. A model-sound service supplies only the forward
edge from an accepted output to a semantic realization. One-way acceptance
refinement composes an optimized checker through a pure checker into that
model edge. Agreement between executables and refusal of one distinguished
contradiction do not imply general soundness. Reject, decline and operational
error remain distinct non-accepting outcomes. Checked reconstruction publishes
an elaborated certificate only after the destination checker recomputes it;
producer soundness is unnecessary. The existing finite-catalog Lean4Lean
beta/delta/head service is exact for its declared raw GSLT and generated OSLF
target predicate. No whole-Lean external checker instance is asserted by this
local comparison.

Release-bound Lean-family intake (`LeanCheckerReleaseReceipt`) keeps the
complete export stream and import closure, toolchain and exporter, checker
family/revision/mode, semantic profile and assumptions, primitive pins, and
executable digest in one exact coordinate. Invalid coordinates are errors;
different valid coordinates decline. Only the underlying checker's accepting
outcome produces a release receipt, and semantic or model soundness is
transported solely from that checker's theorem. The pinned con-leche protocol
retains accepted, rejected, declined, and error as four outcomes and keeps
verified and trusted modes distinct. Digest equality is applicability, not
authority or official-kernel parity.

Inductive admission now has four explicit petals
(`PositiveInductiveBlock`). The executable recognizer retains the ordered
constructor block. Successful recognition proves strict positivity and exact
reuse of the block's canonical parameter vector. Direct recursive fields and
recursive families under a named registered positive container are supported;
negative function domains, unknown containers, changed parameter vectors and
duplicate constructor names refuse. Positivity is independent of operational
finitarity. A separate finitary-registry capability supplies a finite position
type for every recognized constructor shape.

Every recognized block compiles to an indexed polynomial. Its ordinary
recursor and dependent eliminator are generated from the polynomial fixed
family rather than trusted from source input. Constructor computation is
definitional at that semantic layer. Initiality proves every
constructor-preserving map equal to the generated recursor; displayed
initiality gives the corresponding dependent-eliminator uniqueness theorem.
This packages recognition, positivity, generated elimination and
least-fixed-point semantics as separately reusable components. Object-language
formation and judgmental iota authority remain later edges.

Two agent-facing controls exercise the package
(`PositiveInductiveScenarios`). A nested search tree stores either one solved
Boolean answer or a registered `List` of recursive branches; its generated
recursor collects answers in source order, and a two-child branch has two
distinct recursive positions. A Boolean-indexed mutual workflow/action family
crosses from plans to actions and back; its generated recursor counts action
nodes through both directions. The previously admitted vector and even/odd
blocks enter the same richer recognizer through
`PositiveInductiveBlockBridge`, retaining constructor names and order. This
bridge now compares the complete compiled polynomial signatures: shape
fibres, recursive-position fibres and every position's required child index.
The vector and mutual-family inventories instantiate the comparison. Changing
the mutual odd constructor's child index refutes equivalence, so the law does
not collapse dependency information
(`PositiveInductiveBlockBridge.Controls.translated_odd_not_equiv_wrongChild`).

The shared `.module` syntax tree now has a lossless registered-container
lowering (`ModuleSource.PositiveInductiveLowering`). A profile codec resolves
named fields and indices; the generic boundary retains authored field and
constructor names, registry evidence for every nested container, and refuses
arrow fields. Quotation and lowering are inverse for telescopes, complete
families and the selected one-family module shell. The concrete
`SearchTree Answer` declaration with a `List (SearchTree Answer)` field lowers
to exactly the existing nested semantic block. Unknown containers, a negative
field, a changed family header, duplicate constructor names and extra module
blocks all refuse. This is source admission; guest declaration formation and
judgmental iota authority remain separate.

The same source boundary now retains a genuine two-family block
(`ModuleSource.MutualWorkflowActionLowering`). Distinct `Workflow` and `Action`
headers resolve recursive fields into one Boolean-indexed mutual polynomial.
A post-lowering target check prevents a constructor in either header from
returning the other family, while a whole-block name check rejects collisions
across headers. The accepted two-family module round-trips exactly and erases
to the independently specified workflow/action block, retaining constructor
order and both cross-family child indices. Swapped headers, cross-family name
duplication, negative fields and changed result families refuse.

The corresponding mutual object guest is also generated
(`PositiveInductiveWorkflowActionGuest`). The source erasure is exactly the
direct indexed block consumed by the existing guest compiler. One opaque
family, four constructors and a dependent eliminator form against a prefix
containing the natural tag representation and a distinct opaque permission
type. All four canonical computation endpoints form before their own iota
authority is installed. The retained schema list supplies one typed
proof-relevant receipt per source occurrence, in constructor order. Concrete
checks accept `done`, both cross-family constructors and an action with a typed
permission variable, while refusing `schedule done` because it supplies a
Workflow where an Action is required.

Direct-family publication is now single-sourced after structural admission
(`IndexedInductive.Guest.Package.fromAdmitted`). The producer elaborates the
complete declaration prefix, checks global name separation and checks every
generated computation row before exposing a candidate. Its soundness theorem
identifies the candidate's checker table with the complete table generated
from the admitted family; companion theorems retain the exact declaration
signature and proof-relevant computation root. The textual route is precisely
admission followed by this producer. The independent Vector source and the two-family
Workflow/Action source both reach that same boundary; the Workflow/Action
guest obtains its schemas from the published candidate. Zero elaboration fuel
and aliased mutual constructor names still refuse. This factors publication
plumbing; it does not strengthen structural admission or confer judgmental
iota authority.

Admitted indexed families now also expose a generic selected HOL fact boundary
(`IndexedInductive.HOLFacts`). A selected interpretation is an equivalence from
the actual tagged total fixed-point family to one HOL base carrier, so indices
remain observable data. The generated HOL signature has base types for the
carrier, a complete source constructor layer, the same layer after recursive
results are mapped, and an arbitrary result carrier. Its recursion sentence
states that every mapped-layer algebra has a fold; its no-confusion sentence
states that the complete constructor-layer map is injective. Its induction
sentence says that closure under every complete layer covers the carrier. The
constructed fold computes and is unique, and different authored constructor
occurrences remain disjoint. All three structural sentences hold for every
admitted family under every selected equivalence. Dedekind infinity is selected only when a separate
injective endomorphism with an omitted point is supplied. The authored natural
family supplies it; no finite carrier, including lifted Boolean, can. For that
family the four generic capabilities project exactly to the existing five
named facts---recursion, induction, zero/successor separation, successor
injectivity and infinity---and to their existing HOL Light statement wires.
These are semantic HOL formulas, selection laws and a statement projection.
Native proof generation for arbitrary admitted signatures remains separate.
The generic constructor projection also enumerates every ordered pair of
distinct authored constructor occurrences. Each structured pair name carries a
HOL formula saying that complete layers with those two tags cannot construct
the same carrier value. The theorem is uniform in the admitted signature and
selected carrier equivalence. For Nat the generated structured names are
exactly `(Zero, Succ)` and `(Succ, Zero)`. Rendering these new generic formulas
and generating native proofs for them remain separate from the already
qualified Nat statement route.

Both generic signatures now have typed HOL Light wire encoders. A structural
name record supplies the four base-type names and three typed constants; a
constructor-projection record additionally supplies the finite occurrence
names. Emission retains each source fact or named pair in the output record,
and the retained source formula remains valid in the selected model. The
mutual even/odd family is the first non-Nat control: it emits recursion,
induction and complete-layer no-confusion while omitting infinity, plus all six
ordered separation pairs among `zero`, `odd` and `even`. This is checked claim
emission. The shared wire carrier now has executable structural equality, and
a finite catalog decoder is proved sound unconditionally. Encode/decode
roundtrip follows from injective statement encoding. Every mutual structural
and constructor-pair statement round-trips under its distinct names. A
negative control gives all constructor occurrences the same name: two pair
statements collapse and the later pair fails to round-trip. Native proof
production remains open.

Selected HOL interpretations also transport along carrier equivalences.
Construction, mapped recursive layers and the generated fold commute with the
carrier map. An infinity witness transports its injective endomorphism and
omitted point, leaving the selected fact manifest unchanged. The Nat control
carries the authored polynomial carrier to lifted host naturals, material
von Neumann naturals and natural surreals. The lifted material-to-surreal route
forms the same triangle as the existing initial-algebra comparisons. Each fold
commutes and all four selected facts remain valid. These carriers are the
natural subtypes, not arbitrary hypersets or all surreals. This is semantic
representation transport; selected inverses need not be executable adapters,
and no cost theorem follows.

The guarded word backend now meets that selected HOL carrier at its exact
observation (`NaturalBackendHOLFacts`). Both the admitted `UInt64` branch and
the unbounded fallback decode to the authored successor. A finite word cannot
carry the infinity witness, while the tagged word-or-Nat result is deliberately
non-injective as a carrier representation because both tags may denote the
same number. Unchecked word successor fails at the boundary. Separately, every
exact-integer provider satisfying the existing roundtrip, successful-soundness
and fallback-availability contracts computes natural addition by one at the
same host carrier. The provider representation stays abstract; no C/GMP
implementation or cost is inferred.

The remaining guest edge cannot reuse the direct compiler unchanged. That
compiler allocates one recursive argument and hypothesis per recursive field.
For a branch containing a two-element list, the registered nested polynomial
has two recursive positions, while the one-field direct surrogate has one;
their position fibres and complete polynomial signatures are provably not
equivalent (`NestedInductiveGuestBoundary.Search.nested_polynomial_not_direct_surrogate`).
The required interface is now explicit: an induction bundle provides one
dependent motive witness per actual container position. The List instance is
equivalent to a source-ordered dependent list of witnesses. For canonical
typed List spines, the proof-relevant native `mapRel` family realizes that
bundle exactly: its target/evidence spine is equivalent to one typed pair per
source position. The same spine is identified directly with the actual
registered List induction bundle, and composing that identification with the
container law recovers one witness at every `Fin length` position. Its
encoding forms in the existing guest calculus, and the judgment transports
along every typed context substitution
(`FormationSensitiveRegisteredListGuestLift.canonicalLiftSemanticBundleEquiv`,
`FormationSensitiveRegisteredListGuestLift.canonicalLiftRegisteredPositionEquiv`,
`FormationSensitiveRegisteredListGuestLift.QualifiedLift.substitute`). The
existing native List eliminator remains the open-term traversal mechanism.
The first complete nested guest slice now combines those ingredients. The
textual `SearchTree` source generates an opaque family, two constructors and
a dependent eliminator in source order. Its branch method receives a sigma
bundle containing a target List of packed recursive results and a native
proof-relevant relation spine connecting each packed result to its exact
source child. The native List eliminator constructs that bundle for arbitrary
open child Lists. Both solved and branch endpoints independently recheck at
their displayed dependent types before becoming proof-relevant iota receipts;
the branch receipt transports through typed substitution. Removing the bundle
from the branch method is rejected. The resulting declaration signature is a
candidate: typed canonical receipts are present, while global preservation of
every raw iota instance remains a separate authorization obligation
(`PositiveInductiveSearchTreeGuest.branchReceipt`). The receipt-only profile
therefore installs no judgmental roots. A concrete raw branch witness built
from five copies of one undeclared constant exists, while the corresponding
schema substitution is provably untyped. This separates syntax-level iota
evidence from typed-instance authority rather than treating a checked row as
a licence for arbitrary arguments
(`PositiveInductiveSearchTreeGuest.rawEvidence_not_typedInstance`).

An authored nested fold now reaches that existing eliminator through a
result-view adapter. Its finite source plans are derived from the admitted
one-data-field and registered-List constructor forms. The emitted method
list beta-reconstructs both submitted clauses in constructor order. The
dependent branch receives the original child/result bundle; intrinsic List
map projects each result rather than reusing the source child. For every
finite source child spine, including open child terms, the bundle projection
and the source recursive map reach the same ordered List of object-level
recursive calls. The actual emitted adapter and whole fold independently
type-check. A changed source body can pass production while incorrectly
using children as results; independent replay refuses it. Missing, extra or
reordered clauses, wrong recursive inputs and unresolved source names also
refuse. This selected textual input uses the maintained module reader and
an explicit finite source-library expansion. It does not establish general
packed-parser adequacy, arbitrary nested plan generation, raw tree-iota
preservation or a semantic interpretation of an arbitrary open child List
(`PositiveInductiveSearchTreeElaboration.source_methods_reconstruct`,
`PositiveInductiveSearchTreeElaboration.bundleResults_common_output`,
`PositiveInductiveSearchTreeElaboration.source_typed`,
`PositiveInductiveSearchTreeElaboration.checkProposal_sound`,
`PositiveInductiveSearchTreeElaboration.all_verdicts`).

The authored fold name now has a fresh transparent declaration whose body is
the actual checked compiler output. Its type is independently formed and its
body contains no residual recursive source constant. Ordinary delta unfolding
preserves every displayed refined type, retaining the original conversion and
cumulativity tail. Applying the named function reaches the compiled eliminator
body by delta/beta steps. The named source `MapFold` helper and the dependent
bundle result view therefore reach the same ordered calls on every finite
child spine. Reusing the existing family name and installing a bare self-delta
definition are formally refused. This publication adds a checked definition;
it does not authorize global raw tree-iota preservation
(`PositiveInductiveSearchTreeElaboration.Definitions.formed`,
`PositiveInductiveSearchTreeElaboration.Definitions.typedUnfolding`,
`PositiveInductiveSearchTreeElaboration.Definitions.namedApplication`,
`PositiveInductiveSearchTreeElaboration.Definitions.namedBundleCommonOutput`,
`PositiveInductiveSearchTreeElaboration.Definitions.shadow_refused`,
`PositiveInductiveSearchTreeElaboration.Definitions.self_refused`).

The same authored fold now instantiates the existing branch schema by a
formation-sensitive context substitution. All five components independently
check, including its actual constant motive, leaf method and bundle-consuming
branch method. Substitution transports both fully formed endpoints; the
displayed motive application converts to the declared result type. The
resulting proof-relevant iota receipt retains the exact source fold, target
and result type. A branch that treats children as results fails the method
check. This is an explicit typed computation receipt, independent of global
raw-root preservation (`PositiveInductiveSearchTreeElaboration.Branch.contextMorphism`,
`PositiveInductiveSearchTreeElaboration.Branch.result_endpoints`,
`PositiveInductiveSearchTreeElaboration.Branch.receipt`,
`PositiveInductiveSearchTreeElaboration.Branch.children_as_results_refused`).

Open constructor and method types now have a generator over the complete
registered-container code grammar, including interleaved data, direct and
nested fields. The container output expression and recursive family index
remain separate. Each nested induction hypothesis is the complete dependent
bundle supplied by the selected registry, after all original fields and in
recursive-field order. Generation commutes with scoped substitution. On every
ordinary indexed code it agrees with the previous constructor and method
generator; the existing Nat-indexed Vec instantiates this comparison. The
actual admitted SearchTree and VectorTree codes reproduce the independently
checked declaration inventories. A mixed Vector source retains an earlier Nat
length across an intervening payload and independently forms its generated
method type. A faulty reader commutes with substitution and agrees on the
simple branch, yet its mixed method is refused. Thus registry syntax laws
alone grant no typing or iota authority. Generic formation completeness, source-program joins and arbitrary
open-container interpretation remain separate obligations
(`IndexedPositiveContainerGuestTypes.constructorType_substitute`,
`IndexedPositiveContainerGuestTypes.methodBody_substitute`,
`IndexedPositiveContainerGuestTypes.constructorType_ordinary`,
`IndexedPositiveContainerGuestTypes.methodBody_ordinary`,
`IndexedPositiveContainerGuestControls.Vectors.Mixed.method_formed`,
`IndexedPositiveContainerGuestControls.Vectors.Mixed.wrong_length_refused`).

Constructor formation now follows from primitive syntax typing over the
whole declared code grammar. The contracts cover data sorts, the family
kind, typed index expressions and the registered field-type operation.
All primitive domains and family fibres are formed in one selected universe;
a genuine Pi join with an exact or cumulative bound closes products there. The structural proof maintains the typed data
environment through interleaved binders. Closing the actual parameter
telescope forms the generated `constructorEntry`; name freshness then gives
its ordinary opaque prefix admission. None of these premises assumes
formation of that generated constructor type.

The actual registered-List source supplies a non-circular instance. Its
prefix installs only the family declaration over the existing native List
library. Every constructor code over that registry forms from those
primitives. The parsed branch's generated entry is then admitted through the
generic theorem and independently accepted by the existing executable
producer/replay. Omitting the family prefix refuses; an undeclared family
also refutes the primitive typing contract. Other universe policies, complete eliminator formation,
interpretation adequacy and computation authority remain separate
(`IndexedPositiveContainerGuestTypes.constructorType_formed`,
`IndexedInductive.Guest.Declarations.Registered.constructorEntry_formed`,
`IndexedInductive.Guest.Declarations.Registered.constructorEntry_admitted`,
`IndexedPositiveContainerGuestControls.Lists.Formation.primitives`,
`IndexedPositiveContainerGuestControls.Lists.Formation.every_constructor_formed`,
`IndexedPositiveContainerGuestControls.Lists.Formation.family_branch_admitted`,
`IndexedPositiveContainerGuestControls.Lists.Formation.source_branch_checked`,
`IndexedPositiveContainerGuestControls.Lists.Formation.missing_family_refused`,
`IndexedPositiveContainerGuestControls.Lists.Formation.missing_prefix_refused`).

The actual Vector registry now discharges the same constructor contracts in
its family-only prefix, including the mixed source whose length refers past
an intervening payload. Both generated constructors are admitted there and
independently checked; the payload-as-length variant refuses. The native
`All P xs` type forms in a context containing only the element type,
predicate, length and Vector, without a pointwise witness function. Its
finite structural evidence independently replays, and typed substitution
carries the formation result to every signature extension and typed input.
Consequently the actual registered bundle operation forms for arbitrary
typed predicates and fields, without assuming the requested evidence
(`NativeVectorAll.TypeFormation.allType_typed`,
`IndexedPositiveContainerGuestControls.Vectors.Formation.primitives`,
`IndexedPositiveContainerGuestControls.Vectors.Formation.bundle_formed`,
`IndexedPositiveContainerGuestControls.Vectors.Formation.branch_admitted`,
`IndexedPositiveContainerGuestControls.Vectors.Formation.mixed_admitted`,
`IndexedPositiveContainerGuestControls.Vectors.Formation.wrong_mixed_refused`).
The method-formation theorem below uses this primitive basis. Arbitrary open-container semantic decoding retains its separate
interpretation obligation.

A structural theorem now forms generated dependent methods throughout the
declared code grammar. It extends constructor primitives with typing for the
registered whole-field bundle. The actual motive and constructor must be
typed, and pending induction hypotheses must be formed. The proof retains
the typed data/index environment through every binder and appends each
direct hypothesis or whole nested bundle in source order. No premise assumes
formation of the generated method. The actual Vector branch is a closed
witness: its prefix contains only the family declarations and the branch
constructor, with no tree eliminator. Its constructor type matches the
authored source. The method forms through the generic theorem, closes over
its motive and is admitted as an ordinary opaque declaration. Independent
checking accepts that entry and refuses a missing or undeclared constructor
(`IndexedPositiveContainerGuestTypes.methodBody_formed`,
`IndexedPositiveContainerGuestTypes.methodType_formed`,
`IndexedPositiveContainerGuestControls.Vectors.MethodFormation.no_eliminator`,
`IndexedPositiveContainerGuestControls.Vectors.MethodFormation.source_method_formed`,
`IndexedPositiveContainerGuestControls.Vectors.MethodFormation.method_admitted`,
`IndexedPositiveContainerGuestControls.Vectors.MethodFormation.source_method_checked`,
`IndexedPositiveContainerGuestControls.Vectors.MethodFormation.missing_constructor_refused`,
`IndexedPositiveContainerGuestControls.Vectors.MethodFormation.undeclared_constructor_refused`).
This remains a formation result under the explicit primitive contracts and
common universe bound. The complete eliminator result below additionally
uses explicit domain and universe contracts; other universe cases, semantic
decoding and computation authority remain separate.

Complete eliminator formation now follows structurally from those method
contracts, actual constructor typings, a typed optional index domain and
explicit universe/product rules. The proof forms the motive in its upper
universe, forms the final dependent result, traverses the complete ordered
method inventory and binds the motive. It assumes no formation of the
generated eliminator. The actual VectorTree instance uses both authored
constructors at their original prefixes, with no tree eliminator present.
Generic constructor formation supplies their typings; the generated complete
eliminator type matches the original source declaration. Ordinary opaque
admission then reconstructs the full authored inventory. Independent checking
accepts the final entry and refuses missing constructors and the tested
lower-universe claim
(`IndexedPositiveContainerGuestTypes.motiveType_formed`,
`IndexedPositiveContainerGuestTypes.resultType_formed`,
`IndexedPositiveContainerGuestTypes.methodsType_formed`,
`IndexedPositiveContainerGuestTypes.eliminatorType_formed`,
`IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation.prefix_exact`,
`IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation.constructors_typed`,
`IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation.source_eliminator_formed`,
`IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation.full_inventory_admitted`,
`IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation.lower_universe_refused`).
The common-level criterion remains a sufficient specialization. The general
criterion separates the data/family, motive-result and method/bundle levels,
with explicit product and cumulative bounds. Semantic interpretation, raw
iota preservation and native implementation refinement remain separate.

Scoped index admission refines the same formation criterion. Every source
result, direct-recursive and nested-child index must carry its declared
admission; the unrestricted criterion is the universal-predicate instance.
The original Nat-indexed Vec constructor discharges the zero/variable/successor
contract before either vector constructor or eliminator is declared. Its
parameter-closed entry is ordinarily admitted and equals the original reference
entry. Independent checking accepts that entry and refuses missing Nat and
undeclared addition. The reference interpreter is unchanged: its undeclared
addition prevents the stronger unrestricted typing contract. Semantic
interpretation and computation authority retain separate obligations
(`IndexedPositiveContainerGuestTypes.constructorType_formedOn`,
`IndexedPositiveContainerGuestTypes.eliminatorType_formedOn`,
`IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission.source_cons_admitted`,
`IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission.source_generated_cons_checked`,
`IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission.native_total_contract_refused`).

The original indexed Vec also supplies an independently polymorphic eliminator
instance. Its generated type is formed and ordinarily admitted in the original
prefix containing both constructors and no vector eliminator. The data level
alpha and result level beta are independent; methods form at max(alpha,beta),
while binding a motive includes the successor of beta. Level instantiation
retains formation. Independent checking accepts both universe orderings and
the required motive bound, and refuses an omitted successor and missing
constructors. Elimination lift coherence, semantic interpretation and computation authority retain
separate obligations
(`IndexedPositiveContainerUniverseControls.generated_type_formed`,
`IndexedPositiveContainerUniverseControls.eliminator_admitted`,
`IndexedPositiveContainerUniverseControls.instantiated_type_formed`,
`IndexedPositiveContainerUniverseControls.missing_motive_successor_refused`).

The actual registered VectorTree supplies the nested instance at the same
independent universe coordinates. Its original child-vector fields retain
their length expressions and data universe. A universe-instantiated template
of the existing native All program forms the induction-evidence bundle in
max(alpha,beta), without a pointwise witness function. Typed substitution
qualifies this operation under extended signatures. The source prefix,
constructor inventory, motive and bundle operation assemble in one primitive
record; the structural theorem forms and ordinarily admits the generated
eliminator before its name is present. The independently written interface
checks, missing constructors refuse, and an original child vector has its
own declared type but cannot replace its induction-evidence bundle. These
are formation/admission results in the stated universe profile, with
semantic interpretation, elimination lift coherence and new computation
authority still separate
(`NativeVectorAll.Universes.allType_typed`,
`IndexedPositiveContainerUniverseTreeControls.generated_type_formed`,
`IndexedPositiveContainerUniverseTreeControls.source_inventory_admitted`,
`IndexedPositiveContainerUniverseTreeControls.source_bundle_formed`,
`IndexedPositiveContainerUniverseTreeControls.original_children_not_bundle`).

Explicit evidence maps compare the lower and upper All annotations even when
the source vector is neutral. Independent replay checks both open object
programs; substitution and application give an equivalence of inhabitation
under signature extensions. The two-position dependent predicate supplies a
concrete instance. A projection shortcut and a swapped certificate refuse.
These maps preserve the indexed interface; inverse laws and equality of the
two neutral type programs remain separate
(`NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.inhabited_iff`,
`NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.two_maps_typed`).

On constructor vectors, the maps compute on arbitrary supplied evidence,
including opaque evidence: their result is its raw pair expansion. Every
head position and the final tail preserve their source observations, also
through a round trip. Explicit pair spines compute back to themselves.
The result-view program reads arbitrary independent position witnesses and
actual registered Vector bundles through their exact position interface;
its older pointwise result is a corollary. That readout forgets the final
tail, as two checked source inputs with a shared result path demonstrate.
These are finite source computation and observation laws, with neutral-vector
inverse laws and open source-container decoding still separate
(`NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.canonical_steps`,
`NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.roundtrip_head`,
`NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.roundtrip_tail`,
`NativeVectorAll.ResultView.canonical_steps_observe`,
`NativeVectorAll.ResultView.semanticBundle_steps`,
`NativeVectorAll.ResultView.shared_result_distinct_inputs`).

The same source inventory now generates the complete dependent eliminator
interface: motive, ordered methods and final index/value binders. Only an
indexed family supplies an index-domain term; the unindexed interface has no
such binder. Generation commutes with substitution and preserves the complete
ordinary indexed eliminator interface. The actual List SearchTree and
VectorTree declaration inventories now use this generator rather than hand
assembly. Their entries retain the independently checked inventory comparisons;
source-prefix replay supplies admission and formation as described below. The actual Nat-indexed Vec supplies the
indexed comparison witness. Reversing the constructor inventory changes both
selected nested-family interfaces. These comparisons do not establish generic
formation/admission or authorize computation
(`IndexedPositiveContainerGuestTypes.eliminatorType_substitute`,
`IndexedPositiveContainerGuestTypes.eliminatorType_ordinary`,
`IndexedPositiveContainerGuestControls.Lists.eliminator_exact`,
`IndexedPositiveContainerGuestControls.Vectors.eliminator_exact`,
`IndexedPositiveContainerGuestControls.OrdinaryVectors.eliminator_exact`).

Registered-container declaration generation now closes the family, every
constructor and the complete eliminator under one parameter telescope. The
published names determine the prefixes inside those types. Complete ordinary
indexed inventories are preserved, with the actual Nat-indexed Vec as witness.
The existing independent checker replays each generated type at its source
prefix. An admitted dependency prefix composes with the accepted suffix to
form the final opaque signature; suffix acceptance alone does not form the
dependencies. Name separation follows from prefix evidence, and an eliminator
cannot alias its family at any producer budget over an admitted prefix.
Actual List SearchTree and VectorTree inventories use this path.
A family/eliminator name collision and a Vector length/data-sort mismatch
refuse. This is checked inventory integration, not automatic formation of every
registered syntax instance or a new iota authority
(`IndexedInductive.Guest.Declarations.Registered.entries_ordinary`,
`IndexedInductive.Guest.Declarations.Registered.admitInventory_formed`,
`IndexedPositiveContainerGuestControls.Lists.declarations_formed`,
`IndexedPositiveContainerGuestControls.Vectors.declarations_formed`,
`IndexedPositiveContainerGuestControls.OrdinaryVectors.entries_exact`).

Evidence production and independent replay also compose over consecutive
source blocks with exactly the same concatenated certificate list. Successful
production supplies one certificate per declaration. Whole-inventory acceptance
is the conjunction of both prefix-aligned acceptance results. The VectorTree
inventory proof uses this equation to share checked declaration facts, with
the original producer, checker, source inventory and budgets unchanged
(`IndexedInductive.Guest.Declarations.produce_append`,
`IndexedInductive.Guest.Declarations.elaborate_append`,
`IndexedInductive.Guest.Declarations.elaborate_isSome_append`,
`PositiveInductiveVectorTreeGuest.inventoryAccepted_eq_true`).

The source-call plan scanner now consumes that same admitted constructor code.
Earlier data values populate the environment for subsequent output and child
indices; direct and nested calls retain lexical order. The call list commutes
with substitution and contains one entry per direct IH or complete nested
bundle. The authored SearchTree producer uses this scanner and retains its
existing typed output and exact source reconstruction. A mixed Vector source
has five original fields and three call entries; separate source bodies compile
to the first, middle and last method-hypothesis slots. The first body has an
explicit beta reconstruction. Calling on a payload or changing the nested
output length refuses during call abstraction. These are raw clause-compiler
laws, not a typing proof for every mixed method. Generic whole-program
formation and complete-bundle/result-view adapters remain separate
(`IndexedPositiveContainerGuestPlans.calls_substitute`,
`IndexedPositiveContainerGuestPlans.compile_reconstructs`,
`IndexedPositiveContainerGuestPlansControls.VectorCalls.compilation_exact`,
`IndexedPositiveContainerGuestPlansControls.VectorCalls.first_beta`,
`IndexedPositiveContainerGuestPlansControls.VectorCalls.wrong_length_refused`).

The shared source header now reads every original field and its ambient
parameters. The SearchTree producer uses it; the five-field mixed source
compiles through the same named reader and refuses an aliased source pattern
or a recursive call on its payload. Ordinary index/child templates retain
their exact call list, with the existing Nat-indexed Vec append plan as a
comparison witness. A generic clause service compiles those code-derived
calls and replays the emitted method against its generated dependent type.
Successful replay retains the actual source compilation result
(`IndexedInductive.OperationSource.Header.fromPlan_slot_count`,
`IndexedPositiveContainerGuestPlans.calls_ordinary`,
`IndexedPositiveContainerGuestPlans.elaborateClause_sound`).

The authored VectorTree module supplies a dependent two-field branch. Its
actual declarations lower to the qualified inventory, its clauses retain the
earlier length and complete Vector-position bundle, and both emitted methods
independently check at their generated interfaces. The compiled branch
beta-reconstructs the parsed right side with typed endpoints. That exact
parsed target receives the existing VectorTree proof-relevant receipt. A
child Vector substituted for its complete induction bundle survives raw
compilation but refuses dependent checking. The application typing is
reconstructed from the checked method and its arguments; the bidirectional
producer is not assumed complete. These are clause-stage results. They do
not admit a new datatype, grant raw Tree iota conversion, prove whole-program
adequacy or qualify a native implementation
(`PositiveInductiveVectorTreeElaboration.source_inventory_exact`,
`PositiveInductiveVectorTreeElaboration.branch_typed`,
`PositiveInductiveVectorTreeElaboration.branch_beta`,
`PositiveInductiveVectorTreeElaboration.branch_endpoints_typed`,
`PositiveInductiveVectorTreeElaboration.sourceBranchReceipt`,
`PositiveInductiveVectorTreeElaboration.unbundled_refused`).

The constant-motive VectorTree specialization now retains the original
arity and child vector while projecting one recursive result per position.
The projection is an ordinary transparent definition with its actual checked
body and type. Independent replay checks the complete polymorphic fold, all
five components of the substitution into the original branch context, and
the parsed projected target. The substitution transports the original
proof-relevant iota witness; beta reconstruction then reaches the projected
node call with both endpoints typed at the result type. Delta unfolding
preserves the caller's displayed type. On every finite constructor spine,
including repeated or open child terms, the view reduces to the ordered
vector of recursive fold calls. A children-as-results adapter refuses.
This is a selected source specialization, not whole-program adequacy,
arbitrary open-container semantic decoding, global raw-iota preservation or
a native implementation qualification
(`NativeVectorAll.ResultView.program_formed`,
`NativeVectorAll.ResultView.canonical_steps`,
`PositiveInductiveVectorTreeGuest.ResultFold.checking_formed`,
`PositiveInductiveVectorTreeGuest.ResultFold.fold_typed`,
`PositiveInductiveVectorTreeGuest.ResultFold.contextMorphism`,
`PositiveInductiveVectorTreeGuest.ResultFold.sourceReceipt`,
`PositiveInductiveVectorTreeGuest.ResultFold.source_path`,
`PositiveInductiveVectorTreeGuest.ResultFold.source_target_typed`,
`PositiveInductiveVectorTreeGuest.ResultFold.projection_typedUnfolding`,
`PositiveInductiveVectorTreeGuest.ResultFold.childrenResults_canonical`,
`PositiveInductiveVectorTreeGuest.ResultFold.wrongBranch_refused`).

The result-adapter interface now has checked clients at two distinct
declaration profiles. In the List/identity/relator profile, a dependent view
retains the stored List of child/witness pairs. Four independently replayed
slot contracts derive the registered List branch's method adapter with its
carrier, motive, constructor, method and children all open. The closed adapter
transports through actual universe instances and typed target callers. For a
constant motive, the original native List-map body supplies the further
ordered witness readout; equal children do not merge their distinct witnesses
(`IndexedPositiveContainerListResultAdapter.Registered.programme_typed`,
`IndexedPositiveContainerListResultAdapter.Registered.Controls.raised_caller`,
`IndexedPositiveContainerListResultAdapter.constructor_results`).

In the common-capacity Vector profile, object identities compare the original
evidence-map/result-reading paths at neutral inputs. Expanding four checked
transparent definitions types the same identities in the preceding base and
proves conservativity on expansion-fixed syntax. Actual universe transport
preserves them, with no reflection claim for collapsing level assignments
(`NativeVectorAllResultComparison.Named.Erasure.conservative_on_fixed`,
`NativeVectorAllResultComparison.Named.Erasure.Controls.neutral_identity`,
`NativeVectorAllResultComparison.LevelTransport.identity_typed`). These results
do not identify the two declaration profiles, decode arbitrary open guest
values, establish global normalization or refine a native implementation.

The guarded-retraction inference has a native HOL Light proof block built
from the existing checked compilation operations. A retraction law at valid
source values, validity of both compared values and equality of their encoded
values produce source equality. The closed rule and functional-representation
example check with the empty axiom policy; native INST_TYPE supplies a checked
function-type instance. Complete inference-only graphs replay under every
axiom policy. An earlier eta-axiom node can still make replay policy-dependent
when an independently selected root has empty dependencies
(`HOLLight.GuardedRetraction.schema_accepted`,
`HOLLight.GuardedRetraction.functional_schema_instance_accepted`,
`HOLLight.InferenceOnlyReplay.checker`,
`HOLLight.InferenceOnlyReplay.Controls.policy_difference`).

Witnessed type definitions now supply an actual stored equation to a
computable equality-block producer. For arbitrary checked values of the
introduced carrier, equality of their representations yields equality of
the values in thirteen original primitive rule occurrences. The block shares
the definition equation, preserves the existence theorem's axiom dependencies
and refuses a different stored equation. The native history first replays the
existence witness and `NEW_TYPEDEF`, then the equality block; no defining
equation is introduced as an axiom
(`HOLLight.TypeDefinitionEquality.compileRepresentation_checked`,
`HOLLight.TypeDefinitionEquality.representationEqualityResult_axioms`,
`HOLLight.TypeDefinitionEquality.Controls.wrong_definition_seed_refused`).
This is a constructor for equality proofs after an admitted witnessed type
definition. It does not construct inductive definitions for every admitted
polynomial signature.

The actual admitted polynomial family supplies a constructor/destructor
retraction in a strict Option-lifted HOL model. Guards retain the original
possibly empty source layer; both target base carriers remain inhabited.
The object-HOL guarded injectivity proof and that semantic retraction are
assembled in the same model. This constructs the semantic contract, while
native proofs of datatype-specific definition/retraction laws remain open
(`IndexedInductive.HOLFacts.Retraction.models_retraction`,
`IndexedInductive.HOLFacts.Retraction.models_noConfusion`,
`IndexedInductive.HOLFacts.Retraction.Controls.empty_guard_refuses`).

Least-predicate induction and the pointwise fixed-point law now have retained
HOL proof programs. The latter keeps its object-language monotonicity premise.
Both compile to primitive HOL Light graphs under the empty axiom policy; the
compiler requires eta permission only for source proofs that use function
extensionality or eta. For every admitted first-order constructor document,
the actual polynomial layers define a monotone operator on the Option-lifted
tagged source carrier. Its least predicate denotes precisely present source
values. Actual child indices and the empty-family guard are retained
(`HOL.PredicateFixedPoint.fixed_point_schema`,
`HOLLight.PredicateFixedPoint.fixedPoint_accepted_empty`,
`IndexedInductive.HOLFacts.PredicateInterpretation.member_iff_valid`,
`IndexedInductive.HOLFacts.PredicateInterpretation.Controls.empty_no_member`).
This semantic interpretation does not supply a native definition for that
operator, datatype-specific monotonicity proofs or recursive-function
certificates. Registered nested extensions keep their separate obligations.

A typed constructor/child-relation operator now generates its own retained
monotonicity proof. Its native fixed-point program instantiates the preceding
generic schema and supplies that proof, leaving no external monotonicity
premise in the polynomial statement. Both graphs replay under the empty axiom
policy. The actual admitted-family interpretation identifies the typed
operator's denotation with its polynomial-layer operation and proves the same
guarded membership characterization
(`HOL.PolynomialPredicate.operator_monotone`,
`HOLLight.PolynomialPredicate.fixedPoint_accepted_empty`,
`IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.denote_operator`,
`IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.member_iff_valid`).
Constructor/child relation definitions and recursion remain datatype-specific
obligations. The predicate reading observes child support and does not preserve
occurrence counts.

The pointed-predicate producer constructs an explicit witness application
without assuming inhabitance of the original predicate. Its retained proofs
separate absence from presence and reflect equality of present encodings.
Native type admission checks closedness, fresh names and registered formation.
The command producer replays the generated witness graph before the actual
type-definition command; successful introduction retains registered source
derivations and an execution path. Its availability theorem keeps formation
of the primitive requests, outputs and definition laws explicit
(`HOLLight.PointedPredicate.admit_available`,
`HOLLight.PointedPredicate.introduce_available`,
`HOLLight.PointedPredicate.introduce_sound`).

A generic retained witness also specializes through the original native
`INST_TYPE` and `INST` operations. Its computed conclusion is the exact
pointed-predicate application, with empty hypotheses and no logical axiom
dependencies (`HOLLight.PointedPredicateInstantiation.specialized_conclusion`,
`specialized_hypotheses`, `specialized_axioms`). The registered substitution
producer checks every stored maplet, including unused entries. Its constructed
two-command execution preserves earlier proof addresses and source derivations,
adds two theorem outputs and two retained receipts, and supplies a GSLT path
(`HOLLight.RegisteredSubstitution.apply_available`, `preserves_lookup`,
`preserves_derivations`, `execution_path`). A nontrivial type-and-term instance
has the existing OSLF theorem-reachability readout; unused undeclared maplets
are refused. This observation concerns support. General registered pointed
type introduction and native implementation refinement retain their separate
formation and semantic obligations.

`HOLLight.PointedPredicateTemplate` independently checks one cached generic
primitive proof, its exact pointed endpoint and every registered formation
obligation. `HOLLight.RegisteredPointedPredicate.replay_available` receives it
in any signature extending the primitive core and specializes it using formed
carrier and predicate inputs. No per-node witness-formation or original
predicate-inhabitance premise is required. Its returned address contains the
original compiler theorem, and successful runs preserve source derivations.
`HOLLight.RegisteredPointedTypeDefinition.introduce_available` composes this
reception with the actual source type-definition command. Fresh names and
predicate closedness remain explicit; equation formation is constructed from
the registered primitive declarations and retained witness. The extended
signature's instance finder checks both the old input and new maps, with
successful source admission independent of the chosen successful certificates.
The two returned addresses hold exactly the two pointwise laws, and source
derivations survive (`introduce_roots`, `introduce_derived_laws`). The final
command adds two theorem outputs and one receipt.
The registered replay/model join now constructs semantic frames through all
three command kinds. Each type existence licence comes from the earlier cached
proof, and the existing model-family constructors install the actual new
symbols. Declaration steps retain source formation, ordinary universal schemas,
substitution closure and old-schema truth. The empty-policy replay theorem
constructs a full-domain model of the actual cache, with each sequent's source
hypotheses retained (`HOLLight.RegisteredReplayModels.replay_models`). The actual
pointed producer has one such model validating both returned hypothesis-free
laws (`HOLLight.RegisteredPointedModels.introduce_laws_models`). A relative
transitivity control retains both assumptions and refuses dropping them;
an independently translated falsity theorem cannot occur in the interpreted
cache. The retained η/choice/infinity profile now has a constructed initialization
at its nine-definition reference state (`HOLLight.SourceProfileModels.reference_replayed`).
One coherent primitive family fixes the individual carrier to lifted naturals,
interprets the original Boolean declarations, and validates the actual closed
source commitments. Adjoining their formed schemas enlarges the selected policy
while retaining the model. Accepted registered replay after that reference state
has a constructed full-domain model (`HOLLight.SourceProfileModels.replay_models`).
The original-order source-policy replay now constructs one full-domain model of
the complete cache (`HOLLight.SourceProfileModels.source_replay_model`). Exact
readings of six cached Peano/recursive-space facts suffice to construct the
natural-carrier and recursive-space correspondences in that same model
(`HOLLight.RecursiveSpaceModelComparison.replayCorrespondence`). This comparison
preserves bottom, constructor tags, payloads and every child.
`HOLLight.ExactFormulaReadback` proves the executable exact cache-reading check
sound. `HOLLight.RecursiveSpaceSourceReadback.checked_correspondence` consumes
its six successful readings; the retained trace passes them with declaration
identities, type annotations and numeral wrapping intact. A constructor-only
recursion equation still does not specify a bottom value. Full datatype proof production,
source-reader adequacy and native implementation refinement remain open. `HOLLight.RegisteredProofGraph` owns the shared
proof-graph reception construction and its converse; an undeclared constant
separates primitive replay from registered reception.

`HOLLight.IndexedFamilyModels` constructs the payload assignment and source
recursive-space algebra for each indexed presentation with natural-slot codes.
Its constructor law retains the original result index, shape and full padded
child map. `HOLLight.IndexedRegisteredFamilyModels` applies the same construction
to admitted ordered registered blocks, preserving both round trips and empty
fibers. These are semantic representations in the constructed source model;
native datatype certificate generation and executable decoding remain separate.

`HOL.PositivePredicate` generates retained monotonicity proofs from typed positive
formulas, including guarded implication and both quantifiers. Its fixed-point
program supplies the generated proof to the existing least-predicate theorem.
`HOLLight.RecursiveSpacePredicate` compiles these programs to primitive graphs
under the empty axiom policy. The recursive-space instance retains explicit
shape, active-position and edge predicates, plus canonical bottom padding.
Datatype-specific source guard definitions and the complete constructor/recursor
certificate package remain separate obligations.

`IndexedPolynomialRecursiveSpacePredicate` constructs the nonrecursive shape,
position and child-index guards from each natural-slot presentation. Its guarded
operator has exactly the represented family as its least predicate, including
canonical padding and a unique root index. `HOL.IndexedFamilyPredicate` assigns
those actual guards to the typed HOL signature and proves that the HOL least
predicate recognizes the same family. Admitted Natural, Vector and registered
SearchTree instances retain their source values; malformed tags, missing
payloads, hidden children and a wrong vector index are refused. This connects
the semantic guard definitions to the compiled positive syntax without claiming
that their source definitions have already been emitted for every declaration.

`HOL.IndexedConstructorTerms` compiles first-order constructor telescopes into
typed result-index and recursive-child-index functions, given a reading of the
declared index expressions. Its denotation laws follow the original data
evaluator. `IndexedInductiveHOLTerms` supplies the authored Nat/Vec arithmetic
reading. `HOLLight.IndexedConstructorDefinitions` supplies executable Vector
index bodies proved equal to that compiler's specialization, and passes their
source syntax to the existing registered definition checker. The full retained
source history admits both definitions at their original `num` and payload
types. The bare-core projection declares, while an unbound successor refuses.
The enclosing history retains its source-profile assumptions. Concrete payload
representations and complete shape/position/edge definition generation remain
separate from these index-function declarations.

In the full-domain interpretation, the actual pointed syntax is equivalent to
an optional original predicate witness. Applied at an admitted first-order
family's least predicate, presence recovers precisely its actual tagged
source values. The recursive-only empty family still has no present value;
unrestricted quantification over the inhabited pointed carrier changes that
meaning (`HOL.PointedPredicate.Semantics.denotationEquivalence`,
`HOL.PointedPredicate.Semantics.erased_guard_false`,
`IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.Pointed.presence_iff_source`).
These semantic inverses are not executable datatype decoders. Native
constructor definitions, recursion/no-confusion production and registered
nested-family joins remain separate obligations.

Constructor and child relations also have closed higher-order definition
bodies (`HOL.PolynomialPredicate.Relations.constructorDefinition`,
`HOL.PolynomialPredicate.Relations.childDefinition`). They accept typed
operations and layer/position guards as explicit arguments. Native constant
admission retains the actual definition equations without axiom dependencies;
two registered commands replay the definitions. The separate relation-body
beta certificates retain their primitive steps. The admitted-family operation
model interprets both definitions exactly, including indexed child positions,
and recovers the existing polynomial step. A wrong-owner position and an
absent layer are refused. These operation definitions do not supply the
underlying datatype representation or its recursion laws.

Finite first-order constructor descriptions have a source-order recursive
position codec (`Description.positionEquivFin`). Both inverses are proved;
independent telescope index evaluation agrees with the polynomial child index,
including data binders. The resulting signature equivalence replaces recursive
position types by finite ordinals and transports complete recursive families
and folds through the existing polynomial comparison. These fixed-point
transports are semantic, not executable storage adapters. The existing guest
result traversal agrees with the same ordered vector. Mixed-index and repeated
payload controls preserve separate child occurrences.

An unindexed polynomial-tree representation retains each source index and
constructor shape as labels. Its recursive validity predicate checks every
child at the index required by its own position and rejects the explicit
absent constructor. Encoding and proof-directed decoding are inverse
(`IndexedPolynomial.GuardedRaw.representation`); the constructor equation
assembles the existing algebra representation interface. Validity is exactly
membership in the least constructor-closed family of raw trees. A malformed
Vector child is rejected by both readings. A partial natural-slot code also
checks canonical padding outside the recursive-position image; a hidden extra
child is refused even when every required child is valid. The generic
recursive-space presentation retains the original index, shape, constructor
tag and complete child map, with both inverse laws and algebra coherence.
The relational model follows HOL Light's numerical and relational injections,
constructs its least generated subtype, and supplies full predicate induction,
separation and injectivity. Natural, Vector and ordered registered SearchTree
clients instantiate the comparison. Constructor-only recursion leaves the
bottom value free; a supplied bottom gives unique recursion. These semantic
constructions use the indexed eliminator and full function spaces. Typed
semantic identification of retained native histories, complete native datatype
proof production, executable storage and decidable validation remain separate
obligations. The complete native recursive-space closure separately passes the
typed registered source receiver under three explicit source axioms.
First-order constructor-data products reconstruct their complete indexed shapes;
result and child indices follow the original interpreter. The target payload
type and recursive-space algebra are fixed across parameter environments.
A changed parameter can require a different index for the same data tuple,
so the context remains part of the validity contract. This semantic description
uses host equality; it is not an erasure theorem for object proof syntax.

Actual registered constant replay and source-profile reference definitions now
construct their chronological model history. Every admitted definition equation
holds at every type instance; carriers and full function domains are preserved.
This validates definitions, rather than extra axiom commitments or
carrier-changing type definitions. The source receiver's actual schema matcher
also supplies complete instantiation certificates. Repeated parameters and
identity-map normalization retain their original meaning. Concrete annotation,
sequent, theorem and inference-parameter formation checks are exact without an
assumed certificate-selection family. This is formation, rather than proof-search
completeness or implementation refinement; inconsistent repetitions are refused.

The registered-container semantic interface is no longer restricted to an
unindexed `Unit` output. Each richer entry now owns an output-expression
language, its evaluation in the constructor environment, and an indexed
container at that output. The established List entry retains the previous
container and constant unit output exactly. A Vector entry instead evaluates a
length expression and exposes `Fin n` recursive positions. Its induction
bundle is a dependent list equivalent to one motive witness at every such
position. Lengths two and three have provably inequivalent position fibres,
so the generalized layer cannot erase the container output index
(`IndexedPositiveContainer.VectorControl.two_not_equiv_three`). The textual
source boundary now has a first indexed-output specialization. A constructor
can bind a natural length and use it in a later
`Vector n VectorTree` field; lowering retains the length expression and erases
exactly to the independently defined Vector code. Data-binder names are fresh
by construction, so named length lookup and quotation are inverse. Unbound
lengths, shadowed length binders and negative function fields refuse. This is
indexed source admission and semantic erasure; a formed proof-relevant Vector
bundle in the object guest calculus remains a separate edge
(`ModuleSource.IndexedPositiveVectorLowering.Controls.branch_erases_to_indexed_vector`).

The older registered-container grammar now has an explicit embedding into this
indexed grammar. Registry-coherent code retains equivalent constructor shapes
and recursive-position fibres, with the same child-family index at every
position. Selected source-order lists agree occurrence by occurrence under
that comparison, so arbitrary payload observations are preserved as ordered
lists. The resolved SearchTree source exercises the two erasures with two and
three children; reordered or missing observations differ. The existing mutual
Workflow constructor separately checks that its Action child keeps an index
different from the Workflow root. The signature comparison also transports
whole recursive families, with inverse round trips and commuting folds under
the transported constructor methods. For the complete admitted SearchTree
block, every tree retains its generated answer-collecting recursion; solved
false and solved true stay distinct. These semantic laws do not compile
complete open recursors
(`IndexedPositiveContainer.Unindexed.signatureEquiv`,
`IndexedPositiveContainer.Unindexed.ordered_observations_preserved`).

Actual List and Vector container values now have an exact physical list wire.
The Vector decoder checks its supplied length and refuses malformed or
ill-typed payloads. Executable structural encoding of a complete polynomial
fixed family agrees with its semantic fold, and is injective when shape
encoding is faithful and every recursive position is visited. The quoted
bottom-up fold program lifts one-layer constructor-method correctness to the
complete family. Its SearchTree instance computes the existing admitted
answer-collecting recursor on every tree; completed runs have exactly its
ordered answers and no state or I/O effects. Source quotations remain
injective. Native diagnostic controls exercise nested and repeated answers,
depth sixteen, width thirty-two and a method returning captured code data.
The emitted call is built with `cons-atom` before its single explicit `eval`,
so native variable-head dispatch cannot introduce a second evaluation.
These results concern the declared PeTTa model and the selected diagnostic
artifact; they do not establish arbitrary source-clause elaboration, open-term
guest interpretation or a native implementation refinement theorem
(`IndexedContainerWire.Recursive.encodeFix_injective`,
`IndexedContainerTraversal.Folding.fold_returns`,
`IndexedContainerTraversal.Folding.Search.answers_completed_iff`).

The formed List and Vector providers now reach the same visitor through an
exact comparison with their selected semantic bundle. The scoped term codec
retains source, target and witness syntax; List lookup agrees with the
registered proof-relevant bundle. A formed context with two evidence variables
of the same relation type gives equal source/target lists but different
ordered outputs. Completed model runs return exactly those selected witnesses.
The finite canonical source-spine adapter is not an interpretation of an
arbitrary open container variable
(`IndexedContainer.listInductionBundle_exact_cast`,
`FormationSensitiveBundleTraversal.ListProvider.selectedEntries_eq_entries`,
`FormationSensitiveBundleTraversal.ListProvider.Controls.same_values_different_output`).

The object-language bundle now has its reusable core. The existing native Vec
eliminator is instantiated with element universe `α` and elimination universe
`succ α`. A first elimination computes `All P n xs` in `U α`: nil is a
singleton identity type and cons is a dependent pair of the head witness and
the recursive tail evidence. A second elimination constructs this exact type
from a pointwise witness function. Both constructions commute with renaming
and substitution. The full formation replay checks the type and its inhabitant
and refuses a changed result type and an undeclared witness. This binds the
bundle to the actual source Vector rather than merely returning an unrelated
Vector of the same length. Its canonical computation is now tied back to the
semantic registered-container bundle: a source List selects the actual Vector
extension, the semantic bundle is equivalent to a source-ordered dependent
witness spine, and native `All` evidence reduces to the quotation of that
exact bundle. The two-position control retains both witnesses in order;
swapping distinguishable positions changes the quotation
(`NativeVectorAll.CanonicalAdequacy.allEvidence_steps_semanticBundle`,
`NativeVectorAll.Controls.CanonicalAdequacyControls.swapped_positions_refused`).

The common object-realization contract now records that connection without
collapsing its layers
(`FormationSensitiveIndexedContainerBundleRealization.SelectedObjectBundle`).
A selected registry entry contributes its actual semantic induction bundle;
the realization retains one inhabitant, a formation-checked object term, a
quotation of bundles and a computation to the quotation of that same
inhabitant. The container's existing exactness law then exposes one motive
witness at every position. Canonical List and Vector constructions inhabit the
contract through their actual registry lookups. An infinitary Reader with the
impossible motive has no semantic bundle and therefore no selected object
realization: formation cannot manufacture missing position witnesses. This is
a selected-realization interface; automatic construction for every supported
nested source remains a compiler obligation.

The first code-wide lift is also explicit. `Code.quoteBundle` folds a complete
registered constructor code, preserving data scope and combining direct
witnesses with the quotation supplied by the exact nested registry entry.
`Code.SelectedObjectBundle` ties one such quotation to a formed object term
and its computation; `Code.bundleExact` then exposes all direct and nested
positions. The mixed control contains one direct recursive child followed by
a length-two Vector field. Its object term pairs the direct reflexivity
witness with native `All` evidence, forms at the corresponding nested Sigma
type, computes to the generic code quotation, and yields three position
witnesses. Production of these formation proofs for arbitrary open source
inputs remains a separate compiler obligation.

Formation assembly is now generic once those leaves are supplied.
`Code.LeafRealizations` requests only the direct and nested leaves that occur
in one selected constructor shape; it is not a total callback over unrelated
container values. A `Code.PairAlgebra` combines their formed terms,
quotations and computations, and `Code.realizeFromLeaves` follows the same
constructor-code recursion to produce the complete formed bundle. In the
mixed control, the compiled semantic value, object term, nested Sigma type and
quotation agree exactly with the independently constructed reference. Leaf
production for arbitrary open authored inputs is still explicit.

That indexed guest edge is now checked. The accepted textual constructor
order generates the object declaration rows. The complete ordered inventory
contains the external `Answer` type, `VectorTree`, its solved and
length-indexed branch constructors, and its dependent eliminator. The branch
method receives `All P n children`; its iota target constructs that evidence
by applying the tree eliminator pointwise during native Vec elimination. Every
source, target and bundle term independently rechecks before becoming a typed
proof-relevant receipt, and the branch receipt transports through typed
substitution. Passing the raw child Vector in place of its `All` evidence is
refused. The candidate retains those receipts but does not infer global raw
judgmental preservation from them
(`PositiveInductiveVectorTreeGuest.branchReceipt`).

Checked reconstruction accepts a partial producer's result only after the
destination checks it (`Checker.reconstruct_eq_some`). This yields an
elaboration edge without assuming heuristic completeness. Reproducible fuel,
checkpoints and full traces are connected by exact endpoint and tick-count
laws in `Machines.ExecutionHints`; replay always continues
its computed internal state. Such checkpoints do not by themselves accelerate
the computation between them.

`ProofSharingBounds` supplies a fixed calculus with a genuine obstruction to
every polynomial-size DAG-to-tree translation: every accepted tree has
`2^(n+1)-1` nodes, while a checked DAG has `n+1` rows and quadratic size even
with unary indices. This is a representation separation for that calculus,
not a Frege/extended-Frege separation. `PropositionalLRAT` reuses the verified
standard-library RUP/RAT/deletion checker, preserving the native clause
semantics. Accepted refutations entail native resolution derivations; that
completeness argument supplies no polynomial LRAT-to-resolution compiler.
`PropositionalHilbertChecking` supplies native finite rule codes and tree/DAG
coverage for Foundation's standard intuitionistic and classical Hilbert
calculi, with a computable elaborator into the existing retained `PropDeriv`
terms. Excluded middle is admitted only in the classical rule profile.
`PropositionalExtension` adds fresh literal definitions, proves conservative
classical authority and tree/DAG coverage, and embeds Frege DAGs without
changing their replay verdict or expanding references. Its literal-unfolding
family has polynomial encoded source size and exactly exponential output
tree size. This is not an unrestricted Frege lower bound.
`IntuitionisticDecision` validates finite persistent Kripke countermodels,
proves coverage of non-theorems, and supplies an executable terminating
decision procedure by enumerating proof and countermodel certificates.
This exhaustive search is separate from native proof checking and has no
practical or polynomial-time claim. Executed Cook--Reckhow bounds remain
separate obligations.

Larger kernels elaborate into what smaller ones check. Accepted HOL Light proof
graphs elaborate, by a computable function, into retained natural-deduction
proofs (`HOLLight.RetainedElaboration.elaborateProved_correct`). For simply
typed beta, fuelled and explicit conversion evidence elaborate into each other
(`HOL.ConversionTiers.fuelledAboveExplicit`, `explicitAboveFuelled`, which rests
on strong normalization and confluence); retaining the explicit evidence costs
at most, and in the worst case exactly, an exponential in the fuelled
certificate's bit size (`fuelledElaboration_size`, `Controls.compression_gap`).
Binder hints make membership in the normalizing fragment decidable by one pass,
and a certificate outside it is refused before any conversion is run
(`HOL.CheckableFragment.check_outside`, `Controls.omega_outside`). MM0
derivability is stable under admissible substitution, which composes, so it is
a presheaf on contexts (`MM0.Kernel.Contextual.derivableFace`); checked proof
witnesses move along the same substitutions and form a presheaf over it
(`MM0.Kernel.Contextual.witnessFace`), onto which forgetting the witness is
surjective at every context (`MM0.Kernel.Contextual.forgetWitness_surjective`).
The calculus of constructions, the top of the lambda cube, is consistent
(`GSLT.Dedukti.ConstructionsModel.constructions_consistent`, by a
proof-irrelevant model), while a universal sort `∗ : ∗` is not.

Dependency has an exact, bounded necessity result in the same cube. A
well-formed context `A : Type, P : A → Type` and the direct Curry--Howard
proposition `Π x : A, P x` exist exactly when both the ordinary function and
value-to-type product rules are present
(`HypercubeBubbles.directValueIndexedForall_iff_contains_dependentProducts`).
The dependent vertex is a least formation basis for this interface under
every conversion bubble. Its actual abstraction and application rules retain
the same value in the evidence type, with application producing `P argument`.
The simple, polymorphic and type-operator vertices reject the interface under
every bubble: conversion cannot manufacture the missing formation rule.

The minimum changes when the interface changes. Adding the polymorphic
identity type and the kind `Type → Type` requires exactly the four CoC
formation rules
(`HypercubeBubbles.directFormationInterfaces_iff_contains_constructionProducts`).
Deleting any required rule defeats at least one of these three direct
interfaces. These are least formation bases in the existing annotated syntax,
not a least foundation for every encoding of logic. They neither identify
arbitrary conversion bubbles with ordinary CoC nor supply MLTT's universes,
identity eliminator or inductives. LF adequacy is a separate theorem for a
specified logic and signature; higher-order object logic does not by itself
force a CoC host. The Prime candidates therefore retain distinct profile
nodes rather than inheriting a selected universal checker.

The semantic comparison has three different levels of fidelity. Literal
descent through the canonical simple-family inclusion is exactly constancy
over an inhabited context (`DependencyDescentCriterion.descends_iff_constant`).
Descent up to fibrewise equivalence instead uses `FamilyFactorization`;
exact representation layers preserve and reflect its existence
(`DependentFamilyEquivalenceTransport.codeFamily_factorization_iff`).
Requiring all anchored equality families to survive an observer forces that
observer to be injective
(`EqualityFamilyObserverFactorization.EqualityFamilyFactorization.all_anchored_nonempty_iff_injective`).
Inhabitation alone is weaker than these data-preserving comparisons. These
semantic theorems complement the syntactic formation criterion; they do not
provide an interpretation of every cube profile into a CwF model.

Reifying indices into singleton codes or a second level changes the direct
contract and introduces a value/code coherence route. Exact recoding does not
make a genuinely varying family descend through an observer that erased its
relevant distinctions. Dependency also does not select function extensionality:
the existing simple and dependent beta function spaces each have extensional
and route-retaining models (`DependencyExtensionalityOrthogonality`). HoTT path
structure, identity principles, inductives and universe policies are further
features. Their admission, evidence and realization laws remain separate from
the formation graph and from one another.

There is already a proof-level comparison to reuse beside the formation
minimum. The STTfa hub compiles the maintained implication/universal HOL
proof calculus into lambda-Pi-modulo evidence. Its normal inhabitants reflect
closed implicational proofs; for the core universal fragment and free objects,
reflection retains an explicit witness-coding condition
(`GSLT.Dedukti.HOLHub.sttfa_adequate_coded_open`). Detour-free source proofs
with core witnesses have computed normal forms; every normal form of such a
compiled proof equals the computed one and retains the coding. Removing the
detour-free premise remains open in this checked comparison. This does not
supply normalization for every typed hub term. The uncoded bare-connective witness supplies a checked
failure of exact evidence reconstruction; its object conclusion still has a
HOL proof with a different witness. This separates evidence exactness from
theorem conservativity. The hub uses its own declarations and rewrite theory;
its adequacy theorem is not an interpretation of every product/bubble profile.

The hub's formation profile is now an exact edge of the same graph. Its
`LFProfile.standardLF` is definitionally the standard LF/λP dependent vertex:
ordinary functions and value-to-type families, with `Type : Kind`. More
generally, for every profile with that sort axiom, extension from `standardLF`
is equivalent to support
for the direct same-value universal interface
(`HypercubeHOLHub.standardLF_subsumed_iff_directInterface`). Thus forming the direct
Pi after its family is available is the short part; the exact boundary says
which profile makes the family and the Pi available together.

The connection reaches the actual proof service. The STTfa declarations are
formed, its bodies have their declared types, and all rewrite instances
preserve types at exactly this two-rule vertex. Subject reduction remains at
that vertex. Source contexts map pointwise to decoded types; source
substitution commutes with translation and remains typed. Every compiled
implication/universal HOL proof is typed in every larger profile supporting
the direct interface
(`HypercubeHOLHub.theorem_typed_of_directInterface`). Conversely the simple
vertex cannot form the actual declaration `eta : type → Type`, irrespective
of the hub conversion theory. This is a formation obstruction, not a claim
that HOL theoremhood itself requires dependent types.

The next comparison is between CoC formation and the historical MettaKernel
kind-result prototype. They share ordinary functions, value dependency and
type operators. CoC adds `(Kind, Type, Type)`; the prototype instead adds
`(Kind, Type, Kind)`, a rule outside the λ-cube. CoC supports the three direct
interfaces above. The prototype is the least profile containing every product
rule computed from the 31 frozen DTTBench statements. Neither profile subsumes
the other, and each fails the other's stated demand
(`HypercubeHOLHub.coc_mettaKernelPrototype_fork`).

Their literal rule union is not functional: the same domain/codomain sorts
receive both `Type` and `Kind` as result sorts. This is not by itself an
inconsistency theorem. It removes the functionality premise used by the
maintained uniqueness-of-types theorem, so a combined node needs a deliberate
resolution, stratification or different metatheory. The flower is therefore a
graph with interaction laws, rather than a bag of independently useful rules.

A coarser semantic readout can still forget this syntactic conflict. For the
literal CoC/prototype union, observed result sorts are functional exactly when
the readout identifies `Type` and `Kind`. A constant one-point readout does so;
every injective readout refuses. This is a common semantic shadow, not a common
faithful calculus or a model of typing and conversion
(`HypercubeProfileStratification.constructionMettaKernelPrototypeUnion_resultFunctionalUnder_iff`).
Adding `Type : Type` is a different syntactic move, and the maintained PTS
development proves its resulting profile inconsistent
(`TypeInTypeParadox.typeInType_inconsistent`).

The obstruction holds for every untagged upper profile on these two sorts,
not only for the displayed literal union. Any profile containing both
branches contains the conflicting pair, so it cannot satisfy functionality
(`HypercubeProfileStratification.no_functional_common_upper`). The maintained
common service therefore has two mode-indexed fibres. Each fibre is functional and
uses the exact profile checker; evidence from the shared `F,D,O` fragment
rechecks in both. Direct formation separates the CoC fibre, while the frozen
DTTBench demand computed at the prototype separates its rule record. It does
not separate raw-statement typability: the sound generic checker types all 31
statements under CoC as well, using different intermediate result sorts
(`LFDTTBenchDemand.coc_typable_of_mem`). This is a mode-stratified dispatch
interface, not a merged calculus. A single future calculus must
resolve the result sort, enlarge the sort syntax, or replace the uniqueness
metatheory.

The arbitrary-sort PTS layer now makes the sort-enlargement alternative
exact. Its sort-renaming morphisms preserve axioms, product rules, annotated
terms, beta conversion, contexts and full typing derivations; the maintained
two-sort presentation is equivalent to its generic instance. A functional
target receiving both branches while making their maps agree on the shared
`Type` and `Kind` necessarily identifies those images. The translated
`Type : Kind` axiom and `(Type,Type,Type)` rule then become a self-typed sort
and its closed Hurkens falsum inhabitant
(`HypercubeSortRenaming.commuting_functional_cocone_inconsistent`).

A concrete three-stratum comparison target instead places CoC at
`Prop : Type0` and the prototype at `Type0 : Type1`. Its seven translated
product rules are functional, both source derivations transport, and it has
no self-typed stratum. The two maps disagree on both source sorts, so this is
a noncommuting comparison span rather than a join of the shared fragment. It
is not identified with ECC or CIC, and no consistency, normalization or
decidable-checking result for the target is inferred. The mode-indexed
service remains the faithful interface for the original shared syntax.

Formation-profile union now has an executable admission boundary. The finite
check `HypercubeHOLHub.functionalProductsCheck` is equivalent to the
functionality premise used by the maintained uniqueness-of-types theorem.
`admitProductJoin` removes duplicate rules and accepts exactly functional
unions. Dependency joined with type operators passes; the CoC/prototype union
refuses. An accepted result subsumes both inputs, and every finite proof-tree
acceptance from either input has an accepted proof tree at the joined profile
through the existing exact profile checker. This is suitable as the reference
contract for a MeTTa-side profile declaration.

That declaration boundary is now concrete data rather than an analogy. The
profile wire stores both sort axioms and every ordered product rule in the
existing MeTTa `Atom` carrier. Its decoder is a left inverse, so the encoding
is injective. The atom-level join service first decodes both submissions,
requires identical sort axioms, and applies the functionality gate above. A
published result provably contains both input formation judgments and
satisfies the functionality premise. Dependency plus type operators is the
positive control; a conflicting sort axiom, the nonfunctional CoC/prototype
union, and malformed data all refuse
(`LFProfileAtomWire.joinEncoded_sound`). This is a source contract for a
runtime implementation, not a runtime-refinement or cost theorem.

This admission covers formation rules only. A union of conversion bubbles is
always a least upper bound in the conversion order and grows typing, but it is
not thereby normalizing or decidable. The existing bubble-join theorems retain
the additional completion, commutation or disjointness hypotheses
(`BubbleConversion.convertible_join_least`, `BubbleConversion.join_normalizedBy`). A profile
service must therefore run the formation gate and conversion-package
admission as separate checks.

The conversion side now has a parallel finite wire for the existing HOL
recipe policy. A manifest selects beta and eta globally or at named simple
types, and selects all or individual licensed equations. Its recursive type
codec is parameterized by a lossless base-name codec. Atom decoding is a left
inverse and malformed or out-of-range entries refuse. Finite manifest union
denotes exactly `ConversionRecipes.Policy.join`, so both input local-step
judgments embed in the result. This result concerns the typed HOL conversion-
recipe checker. It neither supplies a dependent-calculus conversion package
nor proves normalization, confluence, decidability, conservativity or cost of
the joined policy
(`HOLConversionPolicyAtomWire.denote_join`,
`HOLConversionPolicyAtomWire.joinEncoded_sound`).

The reified-index alternative now has a precise semantic contract as well.
A beta-correct quote/splice pair defines a split readout from retained code to
its body. A code-indexed family descends through that readout exactly when
every code fibre is equivalent to the fibre at its canonical
quote-after-splice representative
(`ContextualCodeObserverFactorization.familyFactorization_iff_quoteSpliceFibreEquivalences`).
Preserving ordinary source equality is stronger and holds exactly when the
quote/splice eta law makes the readout exact. The tagged-code negative control
shows beta can support body-constant families while tag-sensitive families and
source equality fail to descend.

Universe codes need a second coherence layer. Factoring the code carrier does
not ensure that the types denoted by those codes factor. The maintained Tarski
negative control has identical singleton code syntax at two observed levels
but decodes it to `PUnit` and `Bool`; code syntax descends and decoding cannot.
Thus reification is a valid branch, but it owes both value/code and
code/decoding coherence. It is not a way to counterfeit the direct dependency
formation rule inside the same syntax.

The corresponding formation branch is concrete in the same annotated PTS.
Direct indexing forms `P x` from ordinary functions and value-to-type
dependency. Type reification instead forms
`Π X : Type. Π x : X. Q X` from ordinary functions, polymorphism and type
operators. Each profile supports its own interface and refuses the other,
under every conversion bubble. The sound executable checker accepts both
universal types at structural fuel five. Applying the direct function needs
fuel five; the reified route applies first to the type code and then to its
witness, needing fuel six in this checker. Its concrete application has five
syntax nodes instead of three, and its result type retains the type-code
variable rather than the witness. This is a scoped reference-checker and
syntax measurement, not an asymptotic complexity claim. Formation still does
not supply the separate decoding factorization
(`ReifiedIndexElaboration.direct_reified_formation_fork`,
`ReifiedIndexElaboration.Controls.result_transport_surface`).

The abstract operations named quotation and splicing in those modal theorems
are not definitions of the candidate runtime's surface `quote` or `@`. Its `quote` remains
an evaluation-blocking constructor whose interior variables participate in
structural matching. `@` retains its separate name-making role, with `lift`
at the boundary where matching enters names. Any adapter from those runtime
forms to a contextual-code model must prove its own beta, eta and binding laws.

The standard-semantics examples have precise scopes: universal affine
inequalities over natural numbers, and recurrence from a selected root under
a fixed controller on a finite state space. They do not supply general
Presburger, S1S or S2S decision procedures. The atlas likewise does not assert
a universal weakest kernel, universal polynomial equivalence, full Lean
refinement, or completion of the physical calculus-to-HOL compiler.

The one-base simple computational component now has an exact HOL comparison:
HOL beta joinability, intrinsic beta conversion, the sealed tower's structural
conversion on the image, and the intrinsic normal-form checker agree
(`SingleBaseSTLC.HOLComparison.holJoinable_iff_towerConv`). Contexts and
substitutions give a functor. The common conversion-bubble interface elaborates
beta/eta paths to retained HOL equality proofs, and its OSLF beta observation
has an exact decision procedure. Lawful dependent HOL readings type the computed
simple codes and preserve their substitution. The annotated set comparison
retains `CofinalInaccessibles` explicitly.

The tower's typed equality has eta while the structural conversion just
compared does not (`SingleBaseSTLC.HOLTowerModel.typed_equality_not_structural_conversion`).
This compares a computational fragment, not all HOL proof rules or arbitrary
dependent inhabitants of simple-looking types. Full proof-level reflection,
logical profiles and native-kernel realization remain separate obligations.

Selected inductive computation now has a finite checking connection.
`SchemaTableConversionCode` retains an original schema row and explicit
arguments, with exact root decoding and checked renaming/substitution laws.
`IndexedFamily.Checking` consumes existing typed iota schemas. The selected
rules include into the original declaration rules, preserve full formed
judgments and give an OSLF conversion route. Missing root permissions do not
automatically become propositional identity proofs.

`FormationSensitiveChecking.SubstitutionRequest` checks target-context
formation and every argument at its substituted source-context type, including
the zero-argument boundary. Successful iota replay reconstructs the original
typed, proof-relevant receipt at the requested endpoints and displayed type.
It does not turn an informative family candidate into a uniformly preserving
authorized signature.

The actual cumulative Nat/Vec signature has an exact decoder for all four of
its independently defined iota rules, connected to common conversion and
formation-sensitive checking. The finite controls include a typed natural
eliminator instance and weakening of its dependent telescope. The Vec root
controls and generic coverage do not qualify compiled append, all vector
elaboration, raw signature preservation or native CeTTa execution. No new
universal profile record, eliminator derivation or three-kernel equivalence
is asserted.

Authorization names its judgment. The legacy
`Declaration.IndexedFamily.Authorized` asks for uniform preservation of raw
`HasType`, while the maintained checker uses the formed-context
`FormationSensitive.Judgment`; the richer annotation has its own typing and
equality. Forgetting refined derivations supplies raw derivations, without
a converse upgrade. The generic `FormationSensitive.no_uniform_raw_upgrade`
uses the legacy identity rule at a missing domain: even an empty formed
context does not supply its omitted domain-formation proof. The exact
Nat/Vec permission family witnesses this boundary in
`scripts/check_native_inference_authorization.lean`, alongside the checked
append's positive refined/raw views. This is an intentional judgment
distinction, not failure of the legacy preservation property or a strength
claim about a dependent candidate. Neither annotated former facts nor the
already proved operational preservation under the smaller checker alone
fills that legacy authorization field.

The selected natural-only policy now has its own direct raw proof
(`NaturalConversion.RawPreservation.declared_preserves`). Generic raw
declaration spines reuse the existing generation, conversion boundary and
typed telescope application; the formed spine view erases into that common
analysis while keeping its formation-sensitive replay. Uniform raw root
preservation retains every observed conversion/cumulativity tail in arbitrary
raw contexts. All eight original declaration types check with iota disabled,
and their formation evidence transports to every permission selection.
Together these construct the existing `Declaration.CheckedSignature` for the
two selected natural roots, including the actual checked append. Missing
names and a lower claimed universe refuse. This does not authorize the
original four-row family candidates, unrestricted vector computation or
annotated equality by a raw-to-formed upgrade.
-/

/-! The native MM0 primitive-recursion extension derives a total functional
binary graph over its qualified natural subtype and selects its unique value.
The exact recursion statement retains the arbitrary result type and the
result-before-predecessor method order. Its intrinsic formula has the same
standard interpretation as the shared natural fact, with numeral wrapping
interpreted as identity. Exact native statement/dependency/mutation checks
remain distinct from Lean proof checking.

The exact typed graph and guarded induction sequent now share the authored
natural interpretation (`MM0.NaturalFactsMeaning`,
`IndexedInductiveNaturalMM0`). The native constructor, induction, recursion
and infinity readings agree with the five shared laws in that standard
interpretation. Definition reducts account for named infinity predicates;
Boolean equality and numeral wrapping retain their declared meanings.
The graph contains exactly the source recursor value, transposing method
arguments once and transporting the natural index through ULift. Every
selector satisfying its explicit selection law agrees with that value;
a wrong successor output refuses. The definition-reduct comparison applies
to arbitrary Henkin models, whereas graph/source and shared-law comparisons
here retain their stated standard interpretation. This is not proof-object
transport, complete soundness for the supplied HOL presentation or
compiler/native-C refinement. -/
