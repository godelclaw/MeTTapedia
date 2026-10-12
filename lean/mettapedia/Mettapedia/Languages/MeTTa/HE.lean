import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.ModuleSpace
import Mettapedia.Languages.MeTTa.HE.ModuleInvalidation
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.TypeCheck
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.SyntaxSpec
import Mettapedia.Languages.MeTTa.HE.Conformance
import Mettapedia.Languages.MeTTa.HE.Properties
import Mettapedia.Languages.MeTTa.HE.DeclarativeSpec
import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.ExecutionContract
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR
import Mettapedia.Languages.MeTTa.HE.RewriteIRV2
import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.HE.ArgumentResultCorrectness
import Mettapedia.Languages.MeTTa.HE.ArgumentResultControls
import Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification
import Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan
import Mettapedia.Languages.MeTTa.HE.NativeArgumentProjectionControls
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlControls
import Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafService
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary
import Mettapedia.Languages.MeTTa.HE.Certification
import Mettapedia.Languages.MeTTa.HE.SemanticForms
import Mettapedia.Languages.MeTTa.HE.CoreFragment
import Mettapedia.Languages.MeTTa.HE.LetChainResumption
import Mettapedia.Languages.MeTTa.HE.ArgTraversal
import Mettapedia.Languages.MeTTa.HE.ArgTraversalControls
import Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution
import Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecutionControls
import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness
import Mettapedia.Languages.MeTTa.HE.RecursiveControls
import Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery
import Mettapedia.Languages.MeTTa.HE.EquationScopeControls
import Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery
import Mettapedia.Languages.MeTTa.HE.NativeBindingsDataControls
import Mettapedia.Languages.MeTTa.HE.BulkTransferSoundness
import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.SmallStepSound
import Mettapedia.Languages.MeTTa.HE.SmallStepQuiescence
import Mettapedia.Languages.MeTTa.HE.SmallStepContext
import Mettapedia.Languages.MeTTa.HE.SmallStepMaster
import Mettapedia.Languages.MeTTa.HE.MatcherBridge
import Mettapedia.Languages.MeTTa.HE.OutcomeListContracts
import Mettapedia.Languages.MeTTa.HE.LanguageDefRuleInventory
import Mettapedia.Languages.MeTTa.HE.NativeGroundFastPath
import Mettapedia.Languages.MeTTa.HE.HOLContract

/-!
# Hyperon Experimental MeTTa Semantics

Authoritative Lean 4 formalization of the HE MeTTa evaluation specification.

## Source of Truth
1. `https://trueagi-io.github.io/hyperon-experimental/metta/` (spec)
2. Conformance with `metta` CLI (conda hyperon environment)

## Module Structure
- `Types` — Error codes, Bindings (assignments + equalities), ResultSet
- `Space` — Atomspace queries, grounded dispatch
- `Matching` — match_atoms, merge_bindings, match_types (computable)
- `TypeCheck` — type_cast, check_argument_type (computable)
- `EvalSpec` — **Declarative spec**: mutual inductive relations for
               metta, interpretExpression, interpretFunction,
               interpretArgs, interpretTuple, mettaCall
- `Spec.Eval` — Executable-independent relational evaluator semantics
- `ArgumentResultCorrectness` — Tagged argument success and arbitrary raw-list
                               preservation, distinct from full native refinement
- `RetainedArgumentSpecification` — Constructed successful and failing argument
                                    histories with exact binding endpoints
- `NativeSelectedTypeScan` — First-success replay of visited service replies;
                            native applicability correspondence remains open
- `NativeArgumentProjection` — Lossless ITERATE/AFTER_ITER_CHILD snapshots and
                              constructed typed-consumer correspondence;
                              native export and other phases remain open
- `NativeArgumentControl` — Retained argument phases, service requests and
                           complete reply endpoints, with ordered histories
                           and administrative progress
- `FirstSuccessLeafService` — Independent leaf evaluation connected to recursive
                             first-success control, prepared raw arguments and
                             complete represented finite runs; full recursive
                             evaluator and native service correspondence remain
                             separate obligations
- `FirstSuccessSourceExecution` — Independent equation-free nonleaf evaluation
                                 with closed casts, checked argument domains, exact
                                 ordered replies, saved-prefix resumption and
                                 a represented resumable service; tuple fallback
                                 and native service adequacy remain separate
- `Spec.Eval.Minimal` — Minimal-instruction semantics with opaque host services
- `MinimalMeTTa` — Legacy structural validation relation for older small-step proofs
- `SyntaxSpec` — Authoritative HE syntax profiles
- `Conformance` — Derivation-tree conformance witnesses
- `Properties` — Universal theorems by induction on derivations
- `DeclarativeSpec` — Unified spec interface (rule forms, examples, audit index)
- `ExecutableBoundary` — Additive implementation-refined top-level HE boundary
- `LetChainResumption` — Resumable source/body frame refinement for `let`/`chain`
- `ArgTraversal` — Ordered argument products retaining selected values,
                   bindings and pending siblings, with exact prefix resumption
- `TypedApplyDataExecution` — Validated data steps and exact ordered resumption
                            for the existing typed argument component
- `RecursiveDataExecution` — Complete retained control for all six functions of
                             the fuelled read-only evaluator, with ordered data
                             execution and constructed progress; native and
                             effectful correspondence remain separate
- `ScopedEquationQuery` — Total freshening against incoming and retained names,
                          with independent query derivations and preserved
                          native binding records for every returned occurrence
- `LeaTTaScopedQuery` — Constructed hygiene and logical derivations for the
                        actual LeaTTa equation work-item generator
- `NativeBindingsData` — Guarded, lossless relation data; logical projection
                         derives the complete binding solution theory
- `Certification` — Light public entry point for the exported top-level
                   `EvalAtomCertified` theorem boundary
- `SemanticForms` — Named public facade for HE declarative, operational,
                   executable, and certified semantic layers
- `HOLContract` — The HOL contract that HE's type declarations mean, with
                  products, the agreement of HE's typing fragments with it, and
                  gradual typing read beside it

## Key Design Decisions
- Declarative inductive relations (no fuel, nondeterminism-native)
- Computable leaf operations (Matching, TypeCheck) for kernel-checked tests
- HE.Bindings with assignments + equalities (faithful to spec)
- Separate from PeTTa and MeTTaCore (no cross-contamination)
-/
