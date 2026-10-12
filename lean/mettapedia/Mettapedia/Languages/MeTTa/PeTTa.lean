import Mettapedia.Languages.MeTTa.PeTTa.TableReuse
import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Answers
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Space
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Commands
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef
import Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataNormalizedExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ModuleAssemblyExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationContextExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramDriverExecution
import Mettapedia.Languages.MeTTa.PeTTa.DispatchCoverage
import Mettapedia.Languages.MeTTa.PeTTa.BodyClosureFusion
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.FunctionFreeLPBridge
import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTLayers
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDeterminism
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDecision
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTComposition
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTPlan
import Mettapedia.Languages.MeTTa.PeTTa.TypedOperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypedEval
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.StdLib
import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle
import Mettapedia.Languages.MeTTa.PeTTa.PrologBridge
import Mettapedia.Languages.MeTTa.PeTTa.TranslateExpr
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
import Mettapedia.Languages.MeTTa.PeTTa.BindingForms
import Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation
import Mettapedia.Languages.MeTTa.PeTTa.CallGuardOptimization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineGroundProvider
import Mettapedia.Languages.MeTTa.PeTTa.DispatchErrorScope
import Mettapedia.Languages.MeTTa.PeTTa.RaiseFree
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.SemanticForms
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2
import Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardWire
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTyped
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTypedOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSemanticComposite
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardResumableControl
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControlNTT
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredC
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredCSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHotStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteRulePlanCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteFusedDecisionProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteMatchMachinePass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardConformanceCorpus
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

/-!
# PeTTa

Public import interface for the PeTTa formalization.

## Semantics of PeTTa programs

- `SpaceSemantics`, `Effects`, `StdLib`: reading, programs, ordered selection,
  named spaces, cells and primitives over `OSLFCore.Atom`.
- `Answers`: ordered Atom values, preserving duplicate occurrences.
- `DeclarativeSpec`: independent transitions and finite whole-program judgments.
- `Eval`: the executable machine, its adequacy theorem and execution laws.
- `OperationalGSLT`: the judgment as an OSLF-generating GSLT, with executable
  correspondence and observation laws.
- `Bridges.MeTTaIL.MatchAutomataExecution`: both retained-source matcher entries
  compute the exact canonical first-order matches, including occurrence order,
  bindings and source inspection counters. Root rule execution, equations and
  contextual permissions remain separate from matching.
- `Bridges.MeTTaIL.MatchAutomataNormalizedExecution`: the optional source
  partitions and rebases derivative obligations, interns shared controls and
  expands them back into their original ordered occurrences. Its full matcher
  result agrees with canonical matching, with exact completed state and I/O.
- `Bridges.MeTTaIL.RuleInstantiationExecution`: the retained rule source
  constructs the full canonical Pattern RHS with exact substitution, retained
  binders, canonical explicit substitution and checked collection-rest splicing.
  Captured replacement values remain opaque. Local scoped capture, validated
  recovery and assignment operations retain dependency and ambient metadata;
  declaration-site admission and rewrite permission remain separate.
- `Bridges.MeTTaIL.RelationPremiseExecution`: actual queries and their ordered
  fold retain preceding bindings, canonical merge order and duplicate witnesses.
- `Bridges.MeTTaIL.RootRuleExecution`: actual ordered root execution reflects
  exactly to GSLT steps for admitted equation-free first-order rules with
  relation-query premises and a literal finite provider; a child match does
  not authorize a child rewrite. Both matcher strategies feed the actual
  guarded entry, retaining physical rule and premise-witness occurrences.
- `Bridges.MeTTaIL.RuleTraceExecution`: a receipt-driven source loop computes
  each complete ordered frontier, selects a physical occurrence, and re-enters
  the rules. Its whole-run characterization retains residuals, unread receipts,
  stopping, refusal and fuel exhaustion, with exact store and I/O observations.
- `Bridges.MeTTaIL.ContextualRuleExecution`: both retained matcher strategies
  implement canonical recursive congruence, relation-query and freshness premises, with
  exact completed frontiers and preservation/reflection to actual GSLT steps.
  Freshness uses the preceding branch's bindings and retains authored guard
  order. Scoped and quantified premise profiles remain separate extensions.
- `Bridges.MeTTaIL.ModuleAssemblyExecution`: the source assembles all four
  declaration families in order. Explicit coherent-origin and structural-view
  imports keep the first identical declaration and refuse conflicts. Body rule
  occurrences remain ordered, including duplicates. Checked imports compose
  with contextual execution and the actual assembled language's GSLT step.
- `Bridges.MeTTaIL.PremiseOperationsExecution`: canonical free-variable and
  freshness operations cover the full Pattern carrier, including binder
  metadata and collections. Name resolution retains the first binding and
  refuses non-name replacements. The freshness step has exact completed
  observations and is used by the shared contextual premise dispatcher.
- `Bridges.MeTTaIL.EquationExecution`: physical equation receipts retain
  direction, initial captures, ordered query occurrences, final captures and
  target. Validation reflects to the canonical equation relation. Equations
  remain distinct from rewrite permissions and normalization policy.
- `Bridges.MeTTaIL.EquationContextExecution`: exact physical positions select
  and replace canonical contexts. Retained-source receipt validation and path
  replay preserve equation witnesses and reflect to canonical equivalence;
  supplied reverse predecessors recheck the original forward equation and its
  current endpoint. Checked paths compose before and after the actual rule
  frontier, with exact witnessed observations and original-GSLT soundness.
  Neither receipt acceptance nor structural traversal grants rewrite authority.
- `Bridges.MeTTaIL.GeneralRuleJobExecution`: the complete original scoped
  matcher, conditional premise machine and authorized receipt readout for
  finite typed presentations. Actual bounded execution retains pending work,
  lexical quantifiers, finite providers, physical unordered choices, captured
  dependencies and ordered duplicate answers. Machine execution followed by
  receipt readout preserves and reflects the original authorized receipts;
  completeness uses the original declaration-stratification check.
- `Bridges.MeTTaIL.GeneralRuleDriverExecution`: actual MeTTa operations advance
  and resume the original job scheduler, retaining pending obligations,
  physical answer cursors, ordered receipts and the original work account.
- `Bridges.MeTTaIL.GeneralProgramDriverExecution`: native typed occurrence
  generation selects the original jobs from presentation data, then the
  authored driver runs and joins them in order. Saturated, stratified,
  equation-free execution preserves and reflects the original source GSLT
  successors. Independently observed target output families retain receipt
  ordinals and full evidence, supporting native membership and universal
  properties of returned successors. A proved pure readout cache reuses
  replacement checks while reconstructing each current receipt. Effectful
  providers, general equation profiles and broader modal transport remain
  separate integrations.

## Selected Pattern rewrite view

`PatternRewrite.Answers`, `PatternRewrite.Space`, `PatternRewrite.Commands` and
`PatternRewrite.OperationalGSLT`, together with `PatternRewrite.DeclarativeSpec`,
`MeTTaEval`, `TypedEval` and `MinimalInstructions`, state
one-step rewrite and query relations over `Pattern`. A selected right-hand
side is not a completed program answer. These relations remain for their
downstream users.

## Retired modules

The March 2026 stage-indexed OSLF and artifact-export route (`OSLFInstance`,
`GSLTVertex`, `StageIndex`, `OSLFPackage`, `StageFiber`, `SemanticBundle`,
`ArtifactBundle`, `ContractCatalog`, `ContractExport`, `BoundaryContract`,
`ExecutableBoundary`, `ExecutionContract`, `Artifacts`, `Unit`, `LookupPlan`),
with `Conformance.PeTTaArtifactBridge` and its export scripts, is in
`_archive/petta-retirement-2026-10-05`. Its OSLF was built from user rewrite
rules only. The rule-only OSLF is `langOSLF (pettaSpaceToLangDef s) "Expr"`
from the framework; its LP soundness theorem is `petta_safe_space_ruleApp_lp_sound`
in `LPSoundness`; its modal laws are the framework's generic ones; the lookup
plan is `Algorithms.MeTTa.LookupPlans`; the shared-variable `spaceMatch`
checks are examples in `PatternRewrite.Space`.
-/
