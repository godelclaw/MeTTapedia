# GSLT — Graph-Structured Lambda Theories (Lean 4)

## The idea

A programming language, at heart, is two things: a set of *terms* (programs) and a
notion of when two terms *mean the same thing*. In the λ-calculus, for instance,
`(λx. x) y` and `y` compute to the same value, so any sensible theory should equate
them. A **lambda theory** is exactly such an "equality theory": a congruence on
terms that extends β-equality. Different theories make different choices about the
hard cases — most famously, *what to do with non-terminating programs* like
`Ω = (λx.xx)(λx.xx)`. A theory is **sensible** if it lumps all such "meaningless"
terms together, and the beautiful classical result (Bucciarelli–Salibra) is that
there is a *unique maximal sensible* theory, captured by **Böhm trees**: the
possibly-infinite tree of "what a program eventually does."

A **Graph-Structured Lambda Theory (GSLT)** generalizes this from λ-calculus to *any*
computational system. It is a triple `S = (T, E, R)`:

- `T` — a grammar of terms (could be λ-terms, π-calculus processes, ρ-calculus,
  a tiny ML, a machine-state language…),
- `E` — equations saying which terms are structurally equal,
- `R` — small-step **rewrite rules** saying how terms evolve.

That single shape is enough to do a surprising amount of work. Because every system
is "just" terms-with-equations-and-rewrites, you get, *uniformly*:

- a **labeled transition system** and a notion of **bisimilarity** ("these two terms
  are indistinguishable to any observer"), with **Hennessy–Milner logic** to describe
  what an observer can see;
- a **causal structure** — traces record history, and reversing every step gives a
  *reversible envelope* `S†`, the computational analogue of CPT symmetry, where the
  arrow of time lives entirely in the boundary condition (the empty trace);
- a **categorical / topos semantics** — lambda theories become objects of a category
  with cartesian-closed structure and a subobject classifier, which is the direct
  infrastructure for *Native Type Theory*;
- a **path-integral / quantum layer** — assigning complex amplitudes to rewrite paths
  and summing over them, in the style of physics, with a resource-accounting
  conservation law.

This unification follows two lines of work: Bucciarelli & Salibra, *Graph Lambda
Theories* (2008) for the graph-model / Böhm-tree core, and G. Meredith,
*Computation, Causality, and Consciousness* (2026) for the causal, modal, and
path-integral superstructure. **Within Mettapedia, GSLT is also the formal contract
that the OSLF type-synthesis framework consumes** (see "OSLF interface" below): you
describe a language as a GSLT, and OSLF builds its modal/Galois type theory for you.

## Layout

| Subdir | Files | What it formalizes |
|--------|-------|--------------------|
| `Core/` | 4 | the abstract GSLT triple `(T,E,R)`, morphisms, rewrite paths, bisimilarity (`GSLT.lean`); lambda-theories as categorical objects with CCC + finite limits + a subobject fibration (`LambdaTheoryCategory.lean`); change-of-base / quantifier adjunctions (`ChangeOfBase.lean`); webs, coding functions, graph models (`Web.lean`) |
| `GraphTheory/` | 6 | graph lambda theories, interpretations, sensible/semisensible theories (`Basic.lean`); **Böhm trees** and the Böhm theory `B` (`BohmTree.lean`); finite approximants and weak products |
| `Causality/` | 2 | traces and the **reversible envelope** `S†` with embedding/projection (`Trace.lean`); closed vs open **synchronization trees** and causal partial orders (`SyncTree.lean`) |
| `Logic/` | 3 | context-decorated **Hennessy–Milner logic** and its satisfaction relation; minimal-context machinery |
| `Dynamics/` | 3 | weight/cost annotations and finite-support **path integrals** — amplitude-weighted GSLTs and transition amplitudes (`PathIntegral.lean`) |
| `Synthesis/` | 1 | Construction 10.1 — the **main conservation kernel**: reversible debit/credit ledger invariant under quantum-resource steps (`MainConservation.lean`) |
| `Topos/` | 3 | subobject classifier, the **predicate fibration** `πΩ` over presheaf categories, Beck–Chevalley |
| `Meredith/` | 11 | the interactive/cost/bisimulation bridges and modal (`Diamond`, `RewriteModality`) layer, with ρ-calculus examples |
| `Life/` | 2 | an assembly-theory experiment over the GSLT substrate |

## GSLT-ML and language definitions

GSLT-ML is Mettapedia's language for computation within GSLT fibres and explicit
transport between them. Its `at` and `via` commands come from
[`Core/IndexedOperational.lean`](Core/IndexedOperational.lean). Their semantics
distinguishes forward translations, exact covered translations, theory growth,
world revision, observer changes and physical realizations. A route earns its
claimed guarantees through the corresponding proofs.

The [`LanguageDef/GSLTIL.lean`](LanguageDef/GSLTIL.lean) family supplies the command
intermediate representation and its authored executor. MeTTaIL is the shared
format for declaring this command language, guest languages and their rules.
The indexed command theory and its observation/transport contracts belong to
this development; matching the shape of a Rust macro is a separate matter.

[`LanguageDef/GSLTILFibreExecution.lean`](LanguageDef/GSLTILFibreExecution.lean)
connects an equation-free LangDef with nonrecursive premises to actual `at`
execution. Query qualification is derived from the existing matcher and premise
executor. The resulting covered translation preserves source paths and reflects
arbitrary command paths to their actual source endpoints. It does not yet cover
recursive step premises or generated equation saturation. Relation environments
remain explicit, so native implementations of those queries need independent
qualification.

For example, a conditional rule can return duplicate successors through the
same command executor. Conversely, an equation can expose a redex that root
matching misses; omitting that equation closure would invent a false normal
form. A validated equation-free language with a recursive step premise also
has a step that the root query misses. Both controls are kernel-checked in
[`LanguageDef/GSLTILSemanticContracts.lean`](LanguageDef/GSLTILSemanticContracts.lean).
These are separate obligations from structural maps between LangDefs.

[`LanguageDef/MeTTaILSubtermMatchAutomata.lean`](LanguageDef/MeTTaILSubtermMatchAutomata.lean)
provides two concrete realizations of first-order subterm matching: a bottom-up
match-state automaton and top-down position derivatives. Both preserve the
complete canonical list of rule occurrences, positions and bindings, including
authored order and duplicate rules. Their structural selectors share constructor
observations and leave repeated-variable consistency to the canonical matcher.
The top-down realization uses position registers and a fixed preorder stream;
partition-and-lift scheduling is a separate optimization. Inspection counters
cover structural constructor reads; binding checks and candidate dispatches
remain additional work. Matching a subterm does not authorize a rewrite there:
context rules, premises, equation closure and effect policy remain separate.

[`LanguageDef/MeTTaILMatchAutomataExecution.lean`](LanguageDef/MeTTaILMatchAutomataExecution.lean)
composes either matcher's root bindings with the canonical premise evaluator
and rule instantiator. The ordered reduct list equals canonical contextual
execution, including recursive premises and duplicate premise witnesses.
For equation-free presentations, result membership at some finite depth is
equivalent to the actual `langGSLTUsing` step. Child matches alone grant no
rewrite permission. The execution controls include a missing guard, duplicate
guard witnesses, an undeclared context and an explicitly authorized context.

[`LanguageDef/MeTTaILFirstOrderContextualExecution.lean`](LanguageDef/MeTTaILFirstOrderContextualExecution.lean)
earns first-order syntax closure from the actual authored rows and finite
provider payloads. Captures, premise extensions and recursive reducts remain
admitted inputs at every contextual depth. Its profile includes recursive
congruence and scoped-step premises with empty local telescopes; binding
annotations and nonempty telescopes require the scoped interpretation.

[`LanguageDef/TopDownMatchDerivativeNormalization.lean`](LanguageDef/TopDownMatchDerivativeNormalization.lean)
computes connected dependency components, factors their common displacement,
and interns identical relative obligation vectors. Derivatives are cached per
control and displacement, then restored through the original ordered instance
vector. Expansion and execution agree exactly with the unshared derivative
machine, including offsets and duplicate occurrences. Kernel controls show
eight cached dispatches where the original machine performs twelve; these
counts exclude partitioning, normalization, cache lookup and evaluator costs.
The complete offline state graph is a separate construction.

[`MatchAutomataNormalizedExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/MatchAutomataNormalizedExecution.lean)
proves execution of the retained MeTTa normalization, expansion, cached
dispatch and canonical matching entries. Completed and declarative runs return
the exact ordered canonical matches with unchanged store and empty I/O. The
entry uses the canonical string-name wire and normalizes residual goals during
execution; it does not construct the complete offline state graph. Its counters
measure derivative dispatches, excluding normalization and lookup costs.

The PeTTa adapter
[`MatchAutomataExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/MatchAutomataExecution.lean)
proves execution of both retained MeTTa matcher entries: source compilation,
traversal and seeding, bottom-up states, top-down derivatives and canonical
binding completion. Each completed execution returns exactly the canonical
ordered match list and instrumented structural counters, with the store
unchanged and no I/O. The whole-run judgment has the same characterization.
These statements use constructor-data inputs and the existing quotation
boundary; they do not prove textual-reader correctness. The LanguageDef wire
adapter is a matching projection and does not admit scoped operational rules.

The retained rule-operation extension
[`RuleInstantiationExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/RuleInstantiationExecution.lean)
proves actual RHS construction on the full canonical Pattern carrier against
`Match.applyBindings`. Binder metadata is retained, explicit substitution uses
the canonical bound-variable operations, and a captured collection rest is
spliced only when its kind agrees and it is closed. Captured replacements remain
opaque, missing variables remain visible, and duplicate bindings retain
first-match priority. Local scoped capture operations separately retain
dependency and ambient-context metadata, validate occurrence arguments, recover
actual bodies and refuse conflicting repeated assignments. These operations do
not admit a declaration site or grant a contextual rewrite. Whole-run laws
preserve the supplied store and have no I/O.

[`RootRuleExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/RootRuleExecution.lean)
proves actual ordered root dispatch against the canonical rule frontier.
Completed observations are equivalent to GSLT steps for admitted first-order,
equation-free presentations with relation-query premises and a literal finite
provider. Each premise receives the preceding branch's bindings; surviving
branches and duplicate witnesses retain canonical order. Duplicate rule
occurrences remain distinct, and a child match grants no contextual rewrite
permission. Binding annotations and recursive context premises are refused by
this root-only compiler. The earlier premise-free entry has its own exact execution laws.
The `Matched` entries compose both actual matcher strategies with guarded
dispatch: retained root matches supply their bindings to the physical authored
rule row without a second left-hand-side match. Completed execution agrees with
the same canonical ordered frontier and GSLT step relation.

[`ContextualRuleExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ContextualRuleExecution.lean)
extends actual source execution to recursive congruence and freshness premises. A recursive
target is matched relative to its result, then merged with the original seed;
conflicting bindings refuse the branch. Both matcher strategies compute the
canonical contextual frontier with exact state and I/O, preserving ordered
duplicate rule and premise witnesses. Completed reduct membership preserves
and reflects the actual GSLT step. The current admitted wire remains
equation-free and first-order with finite literal providers; scoped steps and
quantified premises require their own source extensions. Freshness follows the
preceding branch's bindings: a captured free-variable name supplies the name,
an absent capture retains its authored spelling, and a non-name capture refuses
the branch. Freshness and relation queries remain in authored order.

[`PremiseOperationsExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/PremiseOperationsExecution.lean)
connects the shared MeTTa operations to the typed premise machine's lexical
bindings. Local parameters shadow their outer values, restoration retains body
outputs at other names, and contextual collection projection checks scope before
reading a concrete finite collection. Successful empty collections remain
distinct from missing values, wrong contexts and unresolved rests. The complete
typed premise-machine execution is realized by `GeneralPremiseExecution`;
its composition with scoped matching and authorized rule readout is below.

[`GeneralRuleJobExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/GeneralRuleJobExecution.lean)
joins the original scoped matcher, premise scheduler and receipt projection.
It covers every original premise task and continuation, finite provider
queries, lexical quantified bodies and preceding-declaration child searches.
Unordered matching retains physical choice traces, nonlinear checks and
residual captures; typed substitution validates every stored capture and
retains its dependencies. The target protocol runs `gslt:premise:machine-run`
and reads its ordered results through `gslt:rule:job-finish-root`.
`observes_receipt_iff_valid` preserves and reflects authorized receipts under
the original stratification admission check; the completed-list theorem
preserves order and duplicates, filtering only the original projection's
refusals. Exact state observations retain unfinished obligations and work.
This profile uses finite provider snapshots and supplied contextual permissions.
A single outer driver, effectful providers and general equation-saturated
execution remain further integrations.

[`ModuleAssemblyExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ModuleAssemblyExecution.lean)
proves source execution of complete-row ordered fragment assembly and its
composition with that contextual entry. The mathematical operation is the
existing `ModuleAlgebra.NativeAuthoring.assembleRaw`. Explicit coherent-origin
and structural-view import contracts use the shared checked list union: the
first identical declaration is retained, while incompatible declarations are
refused. Declaration identity remains distinct from the ordered occurrences in
its body. Fragment/local rule addresses relocate bijectively to physical
assembled rows, retaining repeated payloads. Recursive witnesses can cross
fragments because execution consults the assembled language. Row encoders are
explicit and assembly treats their payloads as data; operational admission is
checked separately. This precedes nullary resolution and whole-language
validation. It does not establish a byte-level `.module` reader.

[`EquationContextExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/EquationContextExecution.lean)
checks finite equation witnesses before and after the actual contextual rule
frontier. A positioned receipt retains the original equation, direction,
bindings and whole-term endpoints. A reverse edge supplies a predecessor and
rechecks the original forward equation at that predecessor, then compares its
target to the current term. This retains information discarded by a forward
equation. Completed source runs agree exactly with the ordered witnessed
frontier, and every reported reduct is a step of the original language's GSLT.
Equation traversal grants no rewrite permission; the separate rule event is
required. This validates supplied finite paths and does not prove completeness
of an equation-class search or choose a normalization policy.
The canonical-route adapter acquires original-oriented receipts from the ordered
contextual frontier and checks every actual intermediate vertex against the
admitted syntax profile. Admitted endpoints alone do not admit a route that
passes through unsupported syntax.

[`RuleTraceExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/RuleTraceExecution.lean)
proves the actual receipt-driven MeTTa loop. Each receipt selects a physical
occurrence in the complete current frontier; successful selection re-enters the
rules on its residual. The output retains consumed ordinals, every ordered
frontier, the final residual and unread receipts, distinguishing stopping,
refusal and fuel exhaustion. Stopped source traces correspond in both directions
to finite GSLT paths on the admitted equation-free first-order provider profile.
Stopping because receipts are exhausted does not assert normality. Intermediate
syntax closure follows from the admitted rule and provider payloads, and equal
residual values do not erase distinct rule or premise-witness occurrences.

[`RelationPremiseExecution.lean`](../Languages/MeTTa/PeTTa/Bridges/MeTTaIL/RelationPremiseExecution.lean)
proves actual relation-query execution and the ordered premise fold, including
literal finite tuple matching, relative extensions, seed merging and refusal
of conflicts. Builtin tuples precede provider tuples, and all surviving
duplicate witnesses are retained. Its provider projection does not establish
scoped signatures, modes or revision authority. Authorized contexts require a
separate source-execution join.

[`LanguageDef/GSLTILStructuralComparison.lean`](LanguageDef/GSLTILStructuralComparison.lean)
proves that a declaration-preserving map between validated languages can fail
to preserve bisimilarity when the target adds behavior. Behavioral transport
therefore needs the coverage conditions used by the indexed operational theory.

Concrete notation changes have a separate typed construction in
[`LanguageDef/BindingSignatureNotation.lean`](LanguageDef/BindingSignatureNotation.lean).
A bijection on actual grammar terminals induces inverse maps on the generated
binding terms, commutes with substitution and yields an equivalence of their
finite-product context categories. Single and repeated binders are retained.
Equation quotients and rule firing require their own transport laws.

[`LanguageDef/BindingSignatureEquationPresentation.lean`](LanguageDef/BindingSignatureEquationPresentation.lean)
places successfully compiled, sorted first-order equation rows in the binding
clone's quotient context category. The left and right arrows become equal there,
including after typed substitution. The compiler's scope is premise-free,
binder-free rows; the surrounding binding syntax remains richer.
[`LanguageDef/BindingSignatureReificationControls.lean`](LanguageDef/BindingSignatureReificationControls.lean)
checks actual authored rows, changed terminals, retained binding and rejected
sort, scope or premise mismatches.

[`LanguageDef/ScopedBindingElaboration.lean`](LanguageDef/ScopedBindingElaboration.lean)
reads dependency contexts and occurrence addresses from each actual scoped
rule. Its typed simultaneous substitution agrees with raw context action,
including constructor binder lifting. The computed variable-spine codec and
occurrence readback retain the ambient suffix separately. Typed input recovery
computes a preimage from intrinsic values and derives capture success from
that recovery, including repeated occurrences and conflicts. Recursive schema
elaboration joins both actual authored sides at the same physical rule index
to an existing contextual root instance and event. Ambient instantiation keeps
the supplied context independently fixed, rather than restricting captures to
closed bodies. Explicitly permitted binding paths retain their actual slots,
siblings and endpoint fill equations. General ambient matcher adequacy, authored
congruence permission translation and conditional operational-presentation
equivalence require their own joins.

### Definitions as equations of the language

A definition is an authored equation of a `LanguageDef`: no premises, a left
side that is a constructor applied to distinct metavariables, and a
first-order right side over them. No second notion of definitional equality
is introduced; the equality is the language's own equation theory.

[`LanguageDef/DefinitionalEquations.lean`](LanguageDef/DefinitionalEquations.lean)
and [`LanguageDef/DefinitionalNormalForms.lean`](LanguageDef/DefinitionalNormalForms.lean)
define unfolding and prove that, for definitions acyclic in authored order,
two patterns are equal in the equation theory exactly when their full
unfoldings coincide (`equationEquiv_iff_expand_eq`).
[`LanguageDef/DefinitionalTyping.lean`](LanguageDef/DefinitionalTyping.lean)
proves that unfolding preserves typing.
[`LanguageDef/DefinitionalBaseLanguage.lean`](LanguageDef/DefinitionalBaseLanguage.lean)
builds the base language, without the defined constructors and without
equations, and shows that the typed terms of a sort modulo the definitions
are the typed base terms of that sort (`typedQuotientEquiv`). It uses the
general fact of
[`LanguageDef/ConstructorSublanguage.lean`](LanguageDef/ConstructorSublanguage.lean):
typing in a sublanguage is typing by the kept declarations.
[`LanguageDef/DefinitionalAdmission.lean`](LanguageDef/DefinitionalAdmission.lean)
decides exactly whether a language is definitional (`checkDefinitional_iff`).

[`LanguageDef/SortedFirstOrderConversion.lean`](LanguageDef/SortedFirstOrderConversion.lean)
reads many-sorted inference rules modulo the equation theory: a derivation
may replace its conclusion by an equal term of the same type. Definitions
add nothing: a term is derivable modulo the definitions exactly when its
unfolding is derivable in the base presentation (`derivesModulo_iff_base`).
[`LanguageDef/SortedFirstOrderConversionCertificates.lean`](LanguageDef/SortedFirstOrderConversionCertificates.lean)
gives proof trees whose conversion nodes name their target and carry no
evidence, with an exact checker. The MM0 backend compiles each definition to
an MM0 definition and each conversion node to an MM0 conversion; see
`Languages/MM0/Translation/FirstOrderConversion.lean`.

Equations of another shape, such as commutativity, remain equations of
their language with the equation theory they generate. They are not
definitions, and the MM0 backend does not admit them. Rewriting modulo
definitions, bound variables in definitions and dummy variables are not
covered.

## Checked inference kernels (the native inference kernel, NIK)

From 2026-08-11 to 2026-10-08 this library pursued a *native inference kernel*
(NIK): supply a formal system as a presentation (syntax, judgments, rules, the
computations the rules use, admission), and obtain a checker for it that is
exactly sound and complete for that system's own derivability, realized on one
shared engine for every such system. Two stages: *formation*, from the
presentation to certificate-checking semantics adequate in both directions,
and *realization*, the shared engine with its agreement proved. The modules
were written under NIK names and renamed to subject names on 2026-10-08; each
renamed module records its former name and renamed declarations at the end of
its docstring. The idea is on hold, neither confirmed nor refuted: open are
whether formation scales to kernels whose binders are functions (Lean,
Megalodon) and whether one shared engine checks more cheaply than a kernel's
own checker.

| Subject | Module | Former name |
|---|---|---|
| What acceptance means: soundness and certificate completeness as `Checker.Authority`, and the projection to the guest's meaning | [`LanguageDef/KernelAuthority.lean`](LanguageDef/KernelAuthority.lean) | unchanged |
| The defining statement at one level: an implementation refines the replay of a signature exactly (`ReplayCorrect`); the generic checker is one (`checkRaw_correct`) | [`LanguageDef/BootstrapCell/ReplayCorrect.lean`](LanguageDef/BootstrapCell/ReplayCorrect.lean) | `CoreNIK` |
| The levelled reflexive cell | [`LanguageDef/BootstrapCell/ReflexiveLayer.lean`](LanguageDef/BootstrapCell/ReflexiveLayer.lean) | part of `CoreNIK` |
| The generic checker over a `CalculusLanguageDef` | [`LanguageDef/InferenceChecker.lean`](LanguageDef/InferenceChecker.lean) | unchanged |
| Checking as a GSLT: submitted, accepted, rejected | [`LanguageDef/CheckerGSLT.lean`](LanguageDef/CheckerGSLT.lean) | `NIKGSLT` |
| Computed leaves as conservative compression; authored computations with contracts | [`LanguageDef/InferenceComputedLeaves.lean`](LanguageDef/InferenceComputedLeaves.lean), [`LanguageDef/AuthoredComputation.lean`](LanguageDef/AuthoredComputation.lean) | unchanged |
| Semantic evidence: direct kernels and exact proof fibres; consequence relations | [`LanguageDef/SemanticEvidence.lean`](LanguageDef/SemanticEvidence.lean), `Logic/Consequence/PiInstitution.lean` | `NIKMetalogic` |
| Selection within a finite licensed family | [`LanguageDef/CapabilitySelection.lean`](LanguageDef/CapabilitySelection.lean) | `MaximalNativeCalculus` |
| Service faces | `UniversalAlgebra/SemanticService/` | `UniversalAlgebra/NIK/` |
| Guest kernels presented to the checker | `Languages/MM0/Presentation/Calculus.lean` (`kernelCalculus`, formerly `formMM0`), `Languages/Metamath/DatabaseCheckerAuthority.lean` (formerly `DatabaseNIKAuthority`), `Languages/VibeITP/` | |

The rename covered 122 modules; `rg 'Formerly `Mettapedia' Mettapedia` lists
them all with their old names.

## Relational and open-system dynamics

The current GSLT-ML integration treats proof-relevant relations as the primary
transport between language-indexed state fibres. A function is obtained only
when totality and proof-relevant endpoint determinism establish representability.
This is developed in `Core/LooseRelationEquipment.lean` and used concretely by:

- `Dynamics/WorldOfViews.lean`, where plural coordination can be partial or
  branching and functional transport is earned by a representability theorem;
- `Dynamics/AnswerDistinctionConservation.lean`, where order and multiplicity
  erasures are rejected whenever the declared answer observation distinguishes
  them;
- `LanguageDef/OpenSystemExtensionBoundary.lean`, where validated growth
  transports old judgments exactly while a merge of independently admitted
  layers must be revalidated at the new boundary.

This layer is intentionally more general than any one guest language or checker.
Prime DTT and native execution consume it as instances; they do not define its
relations.

[`Core/RelationalRouteSemantics.lean`](Core/RelationalRouteSemantics.lean)
interprets routes of authored steps in this equipment. A route denotes the
composite of its step relations; splitting it at an interface is an
equivalence that keeps every intermediate state and witness. A witness
transport between parallel routes extends through every serial context and
through generated rewrite cells, and no step relation needs to be total. It is
used by [`GraphTheory/Representation/ColoringTransport.lean`](../GraphTheory/Representation/ColoringTransport.lean),
which lifts colorings along representation conversions, and by
[`OSLF/MeTTaIL/PremiseRouteSemantics.lean`](../OSLF/MeTTaIL/PremiseRouteSemantics.lean),
where route support is exactly the premise engine's result set.

[`Core/ProofRelevantTranslationCategory.lean`](Core/ProofRelevantTranslationCategory.lean)
also compares full representable probes with evidence-erasing observations.
Swapping two actual transition occurrences changes a proof-relevant translation
while leaving its evidence-erased map unchanged; the full Yoneda interface
separates them. Reconstruction retains the structure selected by that category.

[`Dynamics/ScriptedBackup.lean`](Dynamics/ScriptedBackup.lean) constructs recordings,
ordinary replay and replay with dormant backup computation. A validated backup
matches direct execution for every input continuation and preserves its modal
observations through an actual cover. Its activity along the recorded path is
table reading; replacing its unused evaluator preserves that path. A separate
checking protocol computes each successor independently before comparing it to
the recording. These are abstract operational results with an explicit evaluator
boundary.

[`Causality/ScriptedExecution.lean`](Causality/ScriptedExecution.lean) places this
comparison in the existing admissible-context causal hierarchy. Finite contexts
can supply inputs or replace the evaluator while keeping the table fixed. A
direct executor and a valid backup agree at every rung for input-only contexts;
evaluator replacement can separate them at the intervention rung. Forgetting
component contexts merges behavioral classes, and a concrete separating formula
cannot be reconstructed from input behavior. In the terms-alone category,
direct execution embeds by a hosting map. Projection to the represented state
preserves and reflects transitions but fails static faithfulness, so it is not
hosting for these raw machine equations.

[`Causality/ContextualRealization.lean`](Causality/ContextualRealization.lean)
connects the existing intervention maps to equation-class operational covers.
A commuting square at every state transports saturated modal satisfaction and
the formula-generated OSLF native types. Coverage of target observations and
admitted contexts additionally transports equivalence at every causal rung.
The squares compose, and a context-theory hosting map supplies the required
operational and equivariance laws at each retained interface. This statement
does not identify the entire ambient native-type frames.

[`Causality/ScriptedExecutionRecoding.lean`](Causality/ScriptedExecutionRecoding.lean)
constructs such a realization: a state equivalence conjugates the evaluator,
recodes every table entry, and conjugates replacement commands. The independent
backup algorithm commutes with this change, including its activity labels.
Context composition, table multiplicity, inverse recoding and successive
recodings are preserved. The Boolean-to-`Fin 2` control retains the separating
component intervention. Conversely, projecting to displayed state alone cannot
represent that intervention as a function on displayed states.

## OSLF interface (how the rest of Mettapedia uses GSLT)

GSLT supplies the *spec* that OSLF turns into an executable modal type theory. The
operational front-end is `LanguageDef` (in the OSLF MeTTaIL modules): you declare
**sorts** (with one designated *process* sort), **constructor terms** for syntax and
state, **equations** for structural equality/normalization, **small-step rewrite
rules**, and any **premise** constraints (freshness, congruence, `relationQuery`).
A `RelationEnv` is optional — needed only if you use `relationQuery` premises.

From a `LanguageDef` you get the type-synthesis entry points
`langRewriteSystem`, `langDiamond`, `langBox`, `langGalois`, and `langOSLF`
(each with a `…Using` variant that threads an explicit `RelationEnv`):

```lean
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine

def myLang : LanguageDef := { /- sorts, terms, equations, rewrites, premises -/ }
def myRelEnv : RelationEnv := RelationEnv.empty

def myOSLF    := langOSLF myLang "Proc"
def myDiamond := langDiamondUsing myRelEnv myLang
def myBox     := langBoxUsing myRelEnv myLang
```

Any language that can be written as small-step rewrites over structured states fits:
functional languages via term-reduction rules, imperative languages as rewrites over
machine states, concurrent languages as rewrites over process/message networks.
Worked examples to copy: `OSLF/Framework/TinyMLInstance.lean`,
`MeTTaMinimalInstance.lean`, `MeTTaFullInstance.lean`,
`OSLF/MeTTaIL/ContextualStep.lean`,
`OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean`.

`LanguageDef` is the *executable* ingestion layer; the `Topos/` modules give the
matching **categorical semantics**, and the presheaf/predicate-fibration layer is the
infrastructure used by the Native Type Theory formalization. Paper-parity and strict
claim counts are tracked in `OSLF/Framework/NTTClaimTracker.lean`,
`PaperClaimTracker.lean`, and `FULLStatus.lean` (those trackers are authoritative —
prefer them over prose here for exact status).

## Formalization status

GSLT mixes settled classical theory with active research, so the proof state is
mixed and honest about it:

- The abstract core, causal/trace layer, HML logic, topos/predicate-fibration layer,
  and the conservation kernel are largely complete. `Synthesis/MainConservation.lean`
  deliberately makes its global hypotheses (probability normalization, the CPT
  automorphism) **explicit interfaces** rather than pretending they are already
  earned — the resource part of Theorem 10.1 is proved; the probability/CPT parts are
  stated as the assumptions they currently require.
- The **graph-theory lane carries the open work.** Five files still contain `sorry`s
  (see the footer): the Böhm-tree development (`BohmTree.lean`) and graph-model
  basics (`Basic.lean`, `Approximants.lean`, `WeakProduct.lean`, `Core/Web.lean`).
  These are genuine proof gaps in the classical Bucciarelli–Salibra results, not
  hidden axioms.

There are no source-level `axiom` declarations in this directory (a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a standard Mathlib axiom
transitively), and nothing here uses `native_decide`.

Reproduce from this directory — the `sorry`/`admit` regex is a *raw* scan that also matches
prose in comments/strings, so the footer's per-file figures are the authoritative
comment-stripped counts:

```bash
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .   # prints nothing
rg -n --glob '*.lean' 'native_decide' .                 # prints nothing
```

## References

- Antonio Bucciarelli & Antonino Salibra, [*Graph lambda theories*](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/graph-lambda-theories/6AA6D923589379EA6B3EC57C91FEEEC0), Mathematical Structures in Computer Science 18(5):975–1004 (2008) — the graph-model / Böhm-tree core ([open-access HAL copy](https://hal.science/hal-00149556)).
- Antonio Bucciarelli & Antonino Salibra, [*The Minimal Graph Model of Lambda Calculus*](https://doi.org/10.1007/978-3-540-45138-9_24), MFCS 2003 — minimal/maximal sensible graph theories.
- Henk Barendregt, [*The Lambda Calculus: Its Syntax and Semantics*](https://www.elsevier.com/books/the-lambda-calculus/barendregt/978-0-444-87508-2) (North-Holland, rev. ed. 1984) — Böhm trees and sensible λ-theories.
- L. G. Meredith (2026). *Computation, Causality, and Consciousness* — the causal, modal, and path-integral superstructure (manuscript; no public URL located).
- Christian Williams & Michael Stay, [*Native Type Theory*](https://arxiv.org/abs/2102.04672), arXiv:2102.04672 — the categorical/topos infrastructure GSLT feeds into OSLF.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 35 .lean files, 5 with sorries.*
- `Core/Web.lean` — 3 sorries
- `GraphTheory/Approximants.lean` — 2 sorries
- `GraphTheory/Basic.lean` — 3 sorries
- `GraphTheory/BohmTree.lean` — 8 sorries
- `GraphTheory/WeakProduct.lean` — 5 sorries
