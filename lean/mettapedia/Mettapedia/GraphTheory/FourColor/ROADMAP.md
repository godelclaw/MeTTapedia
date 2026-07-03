# FourColor: goal, status, and how to approach it

*Last restructured: 2026-06-10.  Last proof-state update: 2026-07-02.  This file replaces the 3,577-line
`Theorem49NextHardProblemSummary.lean` prose (now in `Legacy/`) as the
entry point.*

## The goal

By Tait's classical reduction, the Four Color Theorem is equivalent to: every
bridgeless cubic planar graph has a proper 3-edge-coloring
(`IsTaitEdgeColoring`).  Goertzel's v23 manuscript attacks this via an
inductive boundary argument.  The current live route is the manuscript's
Pillar-C execution step: the noncommuting Penrose-Kauffman/Kempe-operator
route whose local finite keystone is **Lemma 8.14**, `LKR_in` for the canonical
three-cell gadget.

`GoertzelLemma814.lean` is the current entry point for that actual route.  It
formalizes the canonical gadget state space, input-disjoint Kempe switches, an
indexed `LKR_in` path certificate, and the Lemma 8.15 tree-transparency finite
check.  The companion lab `lemma814_lkr_in_lab.py` enumerates the same gadget
with numpy/Sympy and reports 192 proper tau colorings, connected fixed-input
Kempe graphs, passing `sigmaL`/`sigmaR` checks, and passing tree transparency.
Lean now closes Lemma 8.14 by `lemma814_tau_lkrIn_audit`, a row-split finite
certificate theorem proving `lemma814_tau_lkrIn_finiteCheck = true`.
Lean also closes Lemma 8.15 by `lemma815_tau_tree_transparency_audit`, a
chunked finite certificate proving
`lemma815_tau_tree_transparency_finiteCheck = true` across all 192 canonical
gadget colorings and all two-color components.  The 8.15 audit is axiom-clean.
The manuscript's Lemma 8.18/Corollary 8.19 composition step does not currently
close from these finite gadget facts: `lemma818_pointwise_lift_preparation_obstruction`
checks a concrete `τ -> τ` state where the upstream switch exits at two
interface stubs, but the downstream fixed-input fiber cannot be prepared to
pair the corresponding stubs for the same color pair.  This pinpoints the
failed Step-1 premise in Lemma 8.18; it is not a counterexample to composite
`LKR_in`.

The first salvage gate is favorable: `lemma818_composite_lkr_gate1_lab.py`
directly checks all length-2 and length-3 `τ`/mirror-`τ` composite fixed-input
Kempe graphs and reports no disconnected fiber among the 12 words.  This means
the pointwise-preparation obstruction is not an immediate structural failure
of short composite `LKR_in`.  The Lean file now contains a build-checked
composite-chain model whose state counts match the lab, but the final proof
certificate is still missing: raw Lean closure search is too slow.  The next
Pillar-C task is a generated path/frontier automaton certificate that avoids
Ben's false pointwise preparation claim and proves composition before any
Section 9 assembly can be trusted.  This is still not a Four Color Theorem
claim.

Gate-2 checkpoint rule: stop the exploratory length sweeps at the finite-mode
surface already recorded in Lean.  The profile automaton is finite and
table-closed with 20 modes and 40 transitions; the archive-backed metadata
evidence contains 42 representative word/profile-hash rows, 30 direct
length-1-through-4 atom-connectivity rows, and two length-5 singleton
quotient-connectivity rows.  Every profile mode has source-consistent
per-fixed-input connectivity evidence with zero recorded failures, so no mode
is presently unverified at the profile/quotient evidence layer.  The open
frontier is semantic certification, not another open-ended length sweep.

The latest streaming lab checkpoint stopped at this boundary.  The exact
length-6 DFA surface has four representatives, `MTTTTT -> mode02`,
`TTTTTT -> mode12`, `TTTTTM -> mode14`, and `MTTTTM -> mode17`; all four
passed real per-fixed-input Kempe connectivity, with 324 fixed-input checks,
144 nonempty fibers, 12,610,560 chain states, max fiber size 262,144, and
zero recorded failures.  The exact length-7 surface also has four
representatives, `MTTTTTM -> mode05`, `TTTTTTT -> mode09`,
`TTTTTTM -> mode13`, and `MTTTTTT -> mode15`; the consolidated lazy-runner
verdict now has complete all-81-input coverage for all four representatives:
324 fixed-input verdicts, zero missing inputs, zero disconnected inputs,
maximum fiber size 2,097,152 states, and maximum recorded RSS 1,871,948 KiB.
The local archive filenames are
`fourcolor-lemma818-gate2-length7-lazy-20260702-consolidated-summary.json`
with SHA256
`cc9b5d1c7080c4b97c20aafd7f885055db70001105455c06299626bfef6d373d`, plus
`fourcolor-lemma818-gate2-length7-lazy-20260702-verdicts.jsonl` with SHA256
`f5880f42687d303aea0ea7cbb20aca256c13a4a1031f56cecf0d9cc99dc1c099`.

Thus the finite automaton is table-closed at the metadata layer, and the
length-6 and length-7 real-fiber corroboration is positive, but the semantic
all-chain consequence remains unproved.  Six base modes have real
single/length-2 chain certificates.  The live frontier route now represents
the finite state explicitly as `frontierState`, proves append congruence by
`frontierState_append_singleton`, and removes the old hard-coded
connectivity report Boolean from the active semantic route.  The named
remaining theorem is
`GoertzelLemma818SemanticBridge.semanticFrontierStateSufficientForChain`.
`GoertzelLemma818Fibration.lean` now supplies the abstract fibration lemma:
connected base relation plus connected fibers plus lifted base steps imply
connected total relation.  The next pass should instantiate that abstract
fibration with the real chain/interface relations, the Lemma 8.14 local input,
and the transparency/joint-interface lift.  The semantic bridge has also proved
the empty-prefix fibration seed and reduced the all-word obligation to the
append-one-gadget transfer closure theorem
`chainAuditFibrationTransferClosed`, with
`chainAuditForFrontierWord_ok_of_targets_and_transfer` as the final assembly
theorem under that single hypothesis.  If the concrete interface lift resists,
pin its exact quantified statement rather than returning to per-mode
certification.
The bridge now also has a concrete fixed-input layer:
`ChainFiberPoint` is an actual member of `chainFiberFrom`,
`ChainFiberFibrationCertificate` proves the real `chainFiberConnected` Boolean
via `closeChainFiber`, and `ChainWordConcreteFibrationCertificate` assembles the
all-input `chainLKRInAudit`.  This pins the proof-producing target as
`concreteChainAuditFibrationTransferClosed`; the concrete empty-word seed is
proved by `concreteChainWordFibrationEmptyCertificate_ok`, so
`chainAuditForFrontierWord_ok_of_concrete_transfer` is now the direct all-word
assembly theorem under that single concrete transfer hypothesis.  The adapter
`chainAuditFibrationTransferClosed_of_concrete_empty_and_transfer` carries that
concrete route back into the abstract final assembly.  The concrete transfer
target has been split into two smaller hooks:
`concreteChainStatesGeneratedCompatible`, proving that the chain-state generator
only emits compatible chains, and `concreteChainFiberFibrationTransferClosed`,
the per-input append-one-gadget fibration lift.  Together they imply
`concreteChainAuditFibrationTransferClosed` via
`concreteChainAuditFibrationTransferClosed_of_generated_and_fiber`.  The
generator hook is now proved by `concreteChainStatesGeneratedCompatible_ok`
using the general `allChainStates_compatible` prefix invariant, so the concrete
route has one remaining proof-producing hook:
`concreteChainFiberFibrationTransferClosed`.  This has been sharpened again:
`ChainFiberAppendFibrationLift` states the append step as a fibration from the
appended fixed-input fiber over the prefix fixed-input fiber.  The corrected
induction is nonempty-prefix: singleton words are seeds, since the empty chain's
artificial default input key is not a same-key prefix for arbitrary one-gadget
fibers.  The abstract singleton audit seeds are now proved by
`chainAuditFibrationSingletonSeeds_ok`, and
`semanticFrontierStateSufficientForChain_of_singletons_and_nonempty_transfer`
is the all-word route under the exact nonempty transfer hook
`chainAuditFibrationNonemptyTransferClosed`.  On the concrete route the
certificate quantifier has been tightened to the 81 audited
`colorAssignments4` keys, and `concreteChainWordFibrationSingletonSeeds_ok`
proves the singleton concrete seeds from the existing one-gadget audits.  Thus
`semanticFrontierStateSufficientForChain_of_append_lift` depends only on the
nonempty `concreteChainFiberAppendFibrationLiftClosed` hook.  That hook is now
split into `concreteChainFiberAppendProjectionClosed`, the structural
same-input projection from an appended fiber back to its prefix fiber, and
`concreteChainFiberAppendFibrationOverProjectionClosed`, the genuine
Kempe-lifting/fiber argument over such a projection; together they imply final
sufficiency via
`semanticFrontierStateSufficientForChain_of_projection_and_fibration`.  The
local generator fact `extendChainStates_mem_split`/`extendChainStates_mem_prefix`
records the one-step list-construction projection used by the structural side.
The projection side has also been factored to the exact data-level target:
`concreteChainFiberAppendPrefixClosed` follows from
`concreteChainStatesAppendPrefixClosed` plus
`concreteChainInputKeyAppendPrefixClosed`, and
`semanticFrontierStateSufficientForChain_of_prefix_and_fibration` is the final
route under that prefix theorem plus the remaining fibration-over-projection
theorem.  The structural prefix theorem is now closed:
`allChainStates_append_singleton_mem_prefix` proves that the chain-state
generator projects an appended generated chain back to a generated prefix,
`chainInputKey_append_prefix_take` proves fixed-input-key preservation, and
`concreteChainFiberAppendPrefixClosed_ok` combines them.  Consequently
`concreteChainFiberAppendPrefixProjection` is the exact projection used by the
route.  The old all-projections hook
`concreteChainFiberAppendFibrationOverProjectionClosed` remains as a stronger
compatibility target, but the active remaining theorem is now the canonical
prefix fibration `concreteChainFiberAppendPrefixFibrationClosed`, split into
`concreteChainFiberAppendPrefixFiberReachClosed` and
`concreteChainFiberAppendPrefixLiftStepClosed`; together they imply final
sufficiency via
`semanticFrontierStateSufficientForChain_of_prefix_fibration_fields`.  Since
`chainFiberRootClosureStep` is encoded as membership in root closure, these two
field obligations have been factored once more into explicit
`closeChainFiber` membership targets:
`concreteChainFiberAppendPrefixFiberClosureClosed` and
`concreteChainFiberAppendPrefixLiftClosureClosed`; they imply final sufficiency
via `semanticFrontierStateSufficientForChain_of_prefix_closure_fields`.  The
fixed-prefix route remains a sufficient proof path, but it is stronger than the
append induction needs.  The bridge now also exposes the quotient route
`ChainFiberAppendQuotientFibrationLift` and
`concreteChainFiberAppendQuotientFibrationClosed`: each appended fixed-input
fiber may project to an arbitrary connected finite base, with the fibration
fields carrying the lifted Kempe motion.  The field-level target
`concreteChainFiberAppendQuotientFibrationFieldsClosed` splits that route into
the exact three proof obligations: same-base fiber reach, lifted base steps,
and connectedness of the quotient base.  For generated finite checks, the
rooted form `concreteChainFiberAppendQuotientFibrationRootFieldsClosed` lets a
spanning-tree-style base certificate provide root reachability instead of a
raw `Connected` proof; it implies final sufficiency via
`semanticFrontierStateSufficientForChain_of_append_quotient_root_fields`.
Since quotient-base steps are intended to be witnessed by reversible Kempe
switches, the still smaller target
`concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed` needs only
base-step symmetry plus reachability from each base node to the root; it implies
final sufficiency via
`semanticFrontierStateSufficientForChain_of_append_quotient_symmetric_root`.
The listed variant
`concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed`
matches generated spanning-forest output: a finite base-node list covers the
quotient base, every listed node has a path to the root, and reversible base
steps supply the reverse paths.  It implies final sufficiency via
`semanticFrontierStateSufficientForChain_of_append_quotient_listed_symmetric_root`.
The parent-map variant
`concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed` matches the
existing generated parent-certificate style even more closely: parent edges
stay within the listed quotient base, each row is stationary or a base step,
and a bounded parent iteration reaches the root.  It implies final sufficiency via
`semanticFrontierStateSufficientForChain_of_append_quotient_parent_map`.
The row-list variant
`concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed` is the
preferred emitted form: explicit parent rows plus row coverage derive the
parent map and imply final sufficiency via
`semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows`.
The path-row variant
`concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed` also lets the
same generated row format supply same-base fiber reachability and lifted
base-step paths, implying final sufficiency via
`semanticFrontierStateSufficientForChain_of_append_quotient_path_rows`.
Thus finite per-input interface or trace-pair mobility can serve directly as
base connectivity, while any necessary prefix motion is absorbed by the
quotient base rather than forced through a fixed-prefix last-state invariant.
The length-two base has now been discharged at the concrete fibration layer:
`ChainWordConcreteFibrationCertificate.ofChainAudit` lifts a checked
`chainLKRInAudit` Boolean to concrete fixed-input fibration certificates,
`concreteChainWordFibrationLengthTwoSeeds_ok` covers `TT`, `TM`, `MT`, and
`MM`, and
`concreteChainFiberAppendQuotientFibrationParentRowsLengthTwoSeeds_ok`
instantiates the parent-rows append fields for all singleton appends and fixed
inputs.  This is a base checkpoint for the parent-rows route, not the arbitrary
append theorem.  The remaining parent-row append target is now named exactly as
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed`:
the length-two seeds discharge singleton prefixes, and the wrapper
`semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_non_singleton`
shows that proving this non-singleton-prefix field theorem is sufficient for
the semantic route.  The bridge now separates that target into generated
base-graph data and structural motion fields:
`ChainFiberAppendQuotientFibrationParentRowsBaseData` is the emitted-data
surface for `Base`, decidable equality, `baseStep`, and the parent-row rooted
certificate, while
`ChainFiberAppendQuotientFibrationParentRowsStructuralFields` supplies `proj`,
same-base `fiberReach`, and lifted `baseStep` motion.  Proving
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed`
and
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed`
is now enough via
`semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_and_structural`.
That exact pair of hypotheses also has direct transfer and all-word audit
wrappers:
`concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows_base_data_and_structural`,
`concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows_base_data_and_structural`,
`chainAuditForFrontierWord_ok_of_append_quotient_parent_rows_base_data_and_structural`,
and
`chainAuditForFrontierWord_ok_of_targets_and_append_quotient_parent_rows_base_data_and_structural`.
For generated output, prefer the paired target
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed`:
it supplies one emitted base-data record together with its structural fields for
each case, and the `_base_data_structural` wrappers carry that paired target
through field closure, transfer closure, semantic sufficiency, and the
target-gated all-word audit.  The `_base_data_and_structural` wrappers remain a
stronger split useful when finite base data and structural motion are proved as
separate global facts.
The current emitted-data shape is
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixConnectedLiftImageClosed`:
for each non-singleton append, emit the paired base record, a projection from
the appended fiber to that base, connectedness of the appended root-closure
graph, and an image witness for every requested base move.  The
`_of_connected_lift_image` wrappers convert this shape to the paired structural
target and then to semantic sufficiency without requiring the canonical prefix
projection, and
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_iff_connected_lift_image`
proves this witness is equivalent to the paired structural target.
The narrower generated target is
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixSurjectiveProjectionClosed`:
for nonempty prefix fibers, prove appended root-closure connectedness and emit a
surjective projection from appended fiber points onto prefix fiber points.  The
`_of_surjective_projection` theorem supplies the connected-lift-image witness,
while empty prefix fibers are discharged by the already proved prefix-closure
projection.  The matching semantic and target-gated all-word wrappers route
this target directly to `semanticFrontierStateSufficientForChain` and
`chainAuditForFrontierWord`.  The target is also exposed as the conjunction of
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixAppendedConnectedClosed`
and
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixProjectionSurjectiveClosed`,
with direct `_of_appended_connected_and_projection_surjective` wrappers.  This
lets generated data prove total appended connectedness separately from the
surjective projection table.  The appended-connectedness half has the parent-row
emitted form
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixAppendedParentRowsConnectedClosed`:
emit a `ParentRowsSymmetricRootedConnectedCertificate` for the appended
root-closure graph.  The projection half has the finite emitted form
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixProjectionFiniteSectionClosed`:
emit a projection, a finite list of appended preimage rows, and a selector from
each prefix fiber point to one selected row.  The combined emitted predicate
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixAppendedParentRowsProjectionFiniteSectionClosed`
packages both row-shaped certificates for generated files.  Its direct wrappers
now carry that single predicate through parent-row field closure, the concrete
fiber/audit nonempty-transfer closures, semantic sufficiency, the non-target
all-word audit, and the target-gated all-word audit.  The finite-section half
now follows from projection surjectivity by enumerating the finite prefix fiber,
so generated files may prove appended parent-row connectedness plus projection
surjectivity and use
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixAppendedParentRowsProjectionFiniteSectionClosed_of_appended_parent_rows_connected_and_projection_surjective`
to package the combined predicate.  Equivalently, generated files may emit the
right-inverse selector surface
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixProjectionSectionClosed`;
the `_of_projection_section` wrappers convert it to the same combined
predicate when paired with appended parent-row connectedness.
The projection surface is further reduced to the injective-selector form
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixProjectionInjectivePreimageClosed`:
emit one selected appended preimage for every prefix point and prove the
selector injective.  Lean then constructs the projection function and converts
the result back to `ProjectionSectionClosed`, so generated tables do not need
to define the projection map itself.
The row-connectedness side is also reduced: the new
`_of_appended_connected_and_projection_finite_section` wrappers construct the
parent-row certificate from appended root-closure connectedness plus projection
finite-section data, with selector and surjectivity variants.  Thus the live
generated-data obligations can be stated as appended connectedness plus either
projection surjectivity or an explicit projection section; a separate appended
parent-row table is no longer required when those two facts are available.
The theorem
`tttFiber32Rows_length_eq_two_mul_ttFiber32Rows_length` records the table-level
alignment for the known `TT` obstruction key: the same generated key appears in
the `TTT` light-fiber table at index 32, and generated rows grow from 8 to 16.
This is not the missing projection witness; it only says the obstruction is not
explained by a generated-table row-count shortage in that local case.
The same local table has a generated row-index selector:
`ttFiber32RowIndexToTttFiber32RowIndex` injects the eight `TT` fiber-32 row
indices into distinct even rows of the sixteen-row `TTT` fiber-32 table.  This
is the concrete finite shape wanted by the injective-preimage projection
surface, but it remains local table evidence until lifted to semantic
`ChainFiberPoint`s and generalized beyond this key.
The selector is now lifted to local semantic points for this key:
`ttFiber32PrefixPoint` and `ttFiber32SelectedTttFiber32Point` name the `TT` and
selected `TTT` `ChainFiberPoint`s, with real-fiber membership and `Nodup`
state-list checks.  The row-indexed prefix points are also proved surjective
onto the real `TT` fiber-32 prefix fiber by
`ttFiber32PrefixPoint_surjective`, with `ttFiber32PrefixPointIndex_spec`
choosing a row index for each semantic prefix point.  This is not a canonical
prefix-projection claim; it is a row-index semantic selector that still has to
be generalized into the global generated projection witness.
The prefix-fibration adapter
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_prefix_fibration`
now shows that `concreteChainFiberAppendPrefixFibrationClosed` is enough to
produce the paired parent-row target.  Its nonempty prefix-fiber branch uses
the canonical prefix projection and a root-star parent-row certificate on the
prefix fiber, while empty prefix fibers are handled vacuously.  The standalone
base-data split is also closed directly by
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed_of_prefix_root_star`,
so emitted finite data is no longer needed for that half of the split.  The
adapter remains only a sufficient implication: `not_concreteChainFiberAppendPrefixFibrationClosed`
proves the full prefix fibration false, and
`not_concreteChainFiberAppendRelativeSingletonPrefixFibrationRoute` retires the
relative-singleton route assumptions.  Continue through the paired
generated-data/structural quotient target instead.
`semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_structural`
is therefore the current one-hypothesis split route from
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed`
to semantic sufficiency.  The semantic wrapper
`semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_prefix_fibration`
records the same sufficient route through the parent-row quotient assembly.
Do not force the full-prefix projection if it becomes the bottleneck:
same-orientation appends have 48 tau states with no compatible next tau state
in each same-orientation direction, while the mixed directions have none.  The
generated or realized-prefix quotient base remains the right route when the
full-prefix lift is too strong.
The prefix-edge switched-color case for the relative singleton lift is now
closed by
`concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed_of_compatible_prefix`.
The helper `chainEdgeColor_chainCanonicalEdge_of_compatible` identifies the
canonicalized glued edge color in any compatible chain, so shifted local
switches are color-stable on prefix edges.  Downstream wrappers now consume
this prefix closure automatically, reducing the remaining shifted-step route to
component equality and the glued-edge switch case.
The glued last-edge switch case is now closed by
`concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed_of_input_trace`,
so the local shifted-switch proof is down to component equality.  The global
parent-row route still has one exact open pin:
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed`.
The wrappers around `BaseDataStructuralClosed` are conditional plumbing; they
do not produce an unconditional semantic sufficiency theorem without that
structural field theorem or an equivalent paired structural record.
The same-prefix closure side is now separated from prefix mobility:
`concreteChainFiberAppendPrefixSelfLiftClosureClosed_of_lift` derives a closed
appended representative over the current prefix from the lift-closure theorem
and the already-proved prefix certificate, while
`concreteChainFiberAppendSamePrefixClosureTransferClosed` is the remaining
local same-prefix transfer theorem.  The route now factors through
`semanticFrontierStateSufficientForChain_of_lift_and_same_prefix`.
This has been sharpened once more: prefix mobility can be supplied as either
`concreteChainFiberAppendPrefixRootClosureLiftClosed` or
`concreteChainFiberAppendPrefixPointClosureLiftClosed`, while local
same-prefix transfer can be supplied by the path-shaped
`concreteChainFiberAppendPrefixFiberReachClosed` via
`concreteChainFiberAppendSamePrefixClosureTransferClosed_of_reach`.  These
feed
`semanticFrontierStateSufficientForChain_of_root_lift_and_same_prefix_reach`
and
`semanticFrontierStateSufficientForChain_of_point_lift_and_same_prefix_reach`.
The same-prefix side now also has a raw list-prefix formulation:
`concreteChainFiberAppendRawPrefixReachClosed`, equivalent to the
projection-shaped reach target by
`concreteChainFiberAppendPrefixProjection_eq_iff_take`.  This is the preferred
interface for a last-gadget/local Kempe lift proof, since it asks directly for
reach when `x.1.take word.length = y.1.take word.length`.  The corresponding
sufficiency wrappers are
`semanticFrontierStateSufficientForChain_of_root_lift_and_raw_prefix_reach`
and
`semanticFrontierStateSufficientForChain_of_point_lift_and_raw_prefix_reach`.
The appended-state shape is now explicit too:
`GoertzelLemma814.allChainStates_append_singleton_mem_split` extracts
`states = pref ++ [last]` from `allChainStates (orients ++ [next])`, and
`concreteChainFiberAppendPoint_mem_split` lifts this to appended fiber points
with `pref ∈ concreteChainFiber word key`, `last ∈ allTauStates`, and the
glued-interface compatibility equation.  A local same-prefix proof should use
this split to reduce raw-prefix reach to last-gadget motion over a fixed
prefix.  The constructive converse is now available too:
`GoertzelLemma814.extendChainStates_mem_of_split` and
`GoertzelLemma814.allChainStates_append_singleton_mem_of_split` rebuild
appended generated chains from a generated prefix, a last Tau state, and the
boundary compatibility equation, and
`concreteChainFiberAppend_mem_of_prefix_last` lifts this to fixed-input
fibers.  This makes the next local theorem a pure fixed-prefix/last-state
reachability statement rather than another projection bookkeeping theorem.
The exact local target is
`concreteChainFiberAppendFixedPrefixLastReachClosed`; the wrapper
`concreteChainFiberAppendRawPrefixReachClosed_of_fixed_prefix_last_reach`
proves that this fixed-prefix last-state theorem implies the raw-prefix reach
hook used by the final sufficiency theorems.  The target is now split by the
last gadget's outgoing interface trace:
`concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed` is the
same-trace case, intended to be proved by reusing the checked Lemma 8.14
gadget audit relative to the fixed interface boundary, and
`concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed` is the
different-trace/base-mobility case, intended to be finite per representative.
The same-trace case is now factored again:
`concreteChainFiberAppendSameTraceRelativeSingletonReachClosed` isolates the
single appended-gadget audit reach at the fixed local input trace and equal
output trace, while `concreteChainFiberAppendRelativeSingletonLiftClosed` is
the separate lift that prefixes that local reach with the frozen chain prefix.
The singleton reach side is closed by
`concreteChainFiberAppendSameTraceRelativeSingletonReachClosed_of_singleton_seeds`,
which reuses the existing singleton fibration seeds; the remaining same-trace
work is the prefix lift.  The wrappers
`concreteChainFiberAppendRawPrefixReachClosed_of_singleton_lift_and_mobility`
and
`concreteChainFiberAppendPrefixFiberReachClosed_of_singleton_lift_and_mobility`
now reduce the raw/prefix reach route to exactly the frozen-prefix singleton
lift plus the different-trace interface-mobility hook.
The lift is sharpened to the closure-level hook
`concreteChainFiberAppendRelativeSingletonClosureLiftClosed`;
`concreteChainFiberAppendRelativeSingletonLiftClosed_of_closure_lift` derives
the reach-shaped lift from it by using the existing singleton seed closure.
The closure lift now reduces by
`concreteChainFiberAppendRelativeSingletonClosureLiftClosed_of_root_and_step_lift`
to two concrete obligations: lift the local singleton root into the global
closure, then lift one local fixed-input Kempe step through the frozen prefix.
The step obligation has now been narrowed again by
`concreteChainFiberAppendRelativeSingletonClosureStepLiftClosed_of_global_step`:
the local singleton target is known to embed as an appended fixed-input fiber
member, so it remains only to prove that a local singleton Kempe step becomes
the corresponding global Kempe step under `pref ++ [last]`, and that the global
root closure is closed under such an embedded step.
The Kempe-step side is further split by
`concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_specified_step`:
the Boolean local step is unpacked once into a specified color-pair/seed move,
leaving the real geometric lift as a specified-move statement.
That statement now factors through
`concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_shifted`:
the remaining local-to-global move proof is exactly that the specified local
move, shifted to occurrence `word.length`, is a valid specified global move.
That shifted-move proof is now split once more by
`concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed_of_seed_and_step`:
the shifted seed must be present in the appended chain edge list
(`concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed`), and the
shifted move must validate as the corresponding global specified Kempe step
(`concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed`).
The seed-membership side is closed by
`concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed_of_local_specified`:
a true local specified Kempe step cannot seed on an outer input edge, and
`concreteChainFiberAppendShiftedEdgePresent_of_not_input` embeds any remaining
last-gadget edge into the appended chain's representative edge list.  The
Kempe-lift branch is now reduced to
`concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed` via
`concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_shifted_step`.
That final shifted-step hook is now factored by
`concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_switch`:
the remaining component-confinement claim is
`concreteChainFiberAppendRelativeSingletonShiftedComponentClosed`, and the
remaining switch-agreement claim is
`concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed`.  The
input-disjointness part is already handled by
`concreteChainFiberAppendShiftComponent_avoids_inputs`, since every shifted
edge lives at occurrence `word.length`.
The switch-agreement side has been peeled to local edges by
`concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_pointwise`;
the pointwise hook is now split by
`concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_edge_cases`
into prefix edges
(`concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed`),
last-gadget non-glued edges
(`concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed`),
and glued-input edges
(`concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed`).
The prefix-edge branch now has the occurrence-separation lemmas
`concreteChainFiberAppendShiftComponent_contains_prefix_false` and
`concreteChainFiberAppendShiftComponent_contains_canonical_prefix_false`: a
component shifted into the appended last gadget cannot contain either a prefix
edge or its canonical representative.  The remaining prefix branch is therefore
the color-equality bookkeeping for unchanged prefix states, including canonical
glued-input comparisons via prefix compatibility.
The last-gadget non-glued branch now has reusable last-occurrence transport
facts: shifted-component membership is identified with local occurrence `0`,
edge colors over `pref ++ [last]` reduce to the singleton last-gadget color,
and non-glued last edges are their own chain-canonical representatives.  The
specified switched-color agreement for this branch is now closed by
`concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed_of_local_specified`.
The switch-agreement hook therefore reduces to the prefix-edge and glued-input
edge cases via
`concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_prefix_and_glued`;
component confinement remains separate.
The closure-under-step side is now reduced by
`concreteChainFiberAppendRelativeSingletonGlobalStepClosureClosed_of_bounded_saturation`
to the pure closure-iterator lemma
`GoertzelLemma814.closeChainFiberBoundedSaturationClosed`: after
`fiber.length` rounds, one additional round cannot add a new member.
`concreteChainFiberAppendFixedPrefixLastReachClosed_of_interface_trace_cases`
and `concreteChainFiberAppendRawPrefixReachClosed_of_interface_trace_cases`
assemble those two cases back into the existing sufficiency route.
`GoertzelLemma818SemanticProgress.lean` still packages the older post-`TTT`
generated-certificate progress surface, but the current local-to-global work
is the fibration-based frontier sufficiency theorem, not another length sweep.
`GoertzelLemma818MirrorTripleComponentSmoke.lean` and
`GoertzelLemma818MirrorTripleLightSlices.lean` now check the full light surface
for a second remaining target: `MMM`/`mode05`, covering 69 light fixed-input
fibers, 24 nonempty size-16 fibers, and 384 light states under the actual
mirror-chain word.  This confirms that the `TTT` component-row format
transfers to the mirror-triple target, but it does not complete `mode05`;
the large fixed-input fibers remain open except for four checked 64-row blocks
plus a fifth checked block of the reversed `[b,b,r,r]` large fiber.
Do not extend representatives or raise kernel limits from this checkpoint;
formalize the existing finite surface with compact per-fixed-input
chain/component certificates or an equivalent finite transition invariant.

## Build hygiene

Do not use the archival aggregate as the default edit-check target.  The
module `Mettapedia.GraphTheory.FourColor` imports the old CAP5/Theorem49
route material and the generated Lemma 8.18 large-fiber certificate archive;
at the current checkpoint it has 446 direct imports, a transitive FourColor
closure of 638 modules, and 507 large-fiber modules.  It is the exhaustive
archive build, not the day-to-day Pillar-C build.

Use `Mettapedia.GraphTheory.FourColor.PillarC` for fast local-to-global
interface work.  It imports the actual live route boundary: `GoertzelLemma814`,
the length-two base/frontier semantic bridge, and the compact component-row
certificate checker.  Its transitive closure has 12 FourColor modules
including the wrapper itself, and no large-fiber modules.  From the Lean
package directory, build it with:

```
lake -f lakefile.lean build Mettapedia.GraphTheory.FourColor.PillarC
```

Use `Mettapedia.GraphTheory.FourColor.GoertzelLemma818SemanticProgress` only
when checking the completed `TTT` target-progress surface, since that module
pulls in the generated large-fiber certificate layer.  Use the full
`Mettapedia.GraphTheory.FourColor` aggregate only for archival or release-style
checks.

The Lean certificate interface is now split at the right granularity for that
generated proof.  `GoertzelLemma814.lean` contains per-fixed-input certificate
records (`ChainFiberParentRow`, `ChainFiberCertificate`) and audits
(`chainFiberParentCertificateAudit`,
`chainAllFiberParentCertificateAudit`) that check exact fiber-index coverage,
same-fiber parent edges, specified input-disjoint chain Kempe moves, and
bounded parent iteration to the fiber root.  The theorem
`tauSingleNormalFiber0Certificate_ok` is a nontrivial smoke consumer for the
first single-`τ` fixed-input fiber `{0,1,2,3,48,49,50,51}`.  The remaining
work is to generate these small certificates for the representative/profile
surface and connect them to the frontier-mode induction; the interface itself
does not yet prove all-chain `LKR_in`.
The first generated base layer is also present:
`tauSingleNormalAllFiberCertificateAudit_ok` checks all 81 fixed-input color
assignments for the single normal `τ` chain in nine chunks, with nonempty
fiber certificates derived from the Lemma 8.14 path rows and validated through
the chain certificate checker.  This is the model for the next generated
representative-word certificates.  The mirror base orientation is now checked
too by `tauSingleMirrorAllFiberCertificateAudit_ok`, using the same local
parent rows under the mirror input order.  The next certificate step is no
longer one-gadget base coverage; it is generated representative/composite
coverage and the DFA induction consequence.
`GoertzelLemma818CompositeCertificate.lean` now checks the generated full
`τ,τ` direct parent/path table: `ttAllFiberCertificateAudit_ok` covers all 81
fixed-input keys, with 36 nonempty fibers, 960 generated chain states, and
maximum parent depth 4.  The proof is decomposed into individual row and
parent-iteration checks rather than a monolithic closure search.  This is the
first complete two-gadget generated table; the remaining work is still the
frontier/DFA lift to all finite chains.
`GoertzelLemma818TauMirrorCertificate.lean` now checks the next length-2 base
table: `tmAllFiberCertificateAudit_ok` covers all 81 fixed-input keys for the
`τ,mirror-τ` chain, with 36 nonempty fibers, 1152 generated chain states, and
maximum parent depth 4.  The other two length-2 orientation tables remain to
be generated before this base layer is complete.
`GoertzelLemma818MirrorTauCertificate.lean` now checks the third length-2 base
table: `mtAllFiberCertificateAudit_ok` covers all 81 fixed-input keys for the
`mirror-τ,τ` chain, with 36 nonempty fibers, 1152 generated chain states, and
maximum parent depth 4.  The last missing length-2 table is
`mirror-τ,mirror-τ`; the frontier/DFA lift remains the real local-to-global
step.
`GoertzelLemma818MirrorMirrorCertificate.lean` completes the length-2 base
table layer: `mmAllFiberCertificateAudit_ok` covers all 81 fixed-input keys
for the `mirror-τ,mirror-τ` chain, with 36 nonempty fibers, 960 generated
chain states, and maximum parent depth 4.  All four length-2 orientation
words now have generated direct parent/path certificate tables.  The remaining
local-to-global burden is still the frontier/DFA consequence for arbitrary
finite chains.
`GoertzelLemma818LengthTwoBase.lean` packages the four generated tables into a
small finite base interface: `lengthTwoCertificateAudit_ok` proves the audit
for each length-2 orientation constructor, and
`lengthTwoAllCertificateAudit_ok` checks the aggregate four-word base list.
This is the reusable base hook for the frontier/DFA lift; it does not itself
prove all-chain `LKR_in`.

Gate-2 frontier-mode status: stop treating longer exploratory sweeps as the
main work item.  The current lab surface is a finite 20-mode profile DFA with
40 transitions; 36 transitions are observed directly and 4 are inferred by the
singleton-summary transition law.  The stabilized evidence includes 936
frontier summaries, atom-refined fixed-input connectivity for every
`τ`/mirror-`τ` word of length 1 through 4, atom-transition congruence through
length 4, and a compact transition-congruent state key
`profile mode + frontier summary + local atom index`.  Length-5 targeted
profile checks show the alternating cases collapse back to existing singleton
modes and the remaining representatives either collapse to known modes or
produce two new singleton profile modes.  The two new singleton representatives
`TTTTM` and `MTTTT` have now passed independent per-fixed-input
quotient-connectivity checks: each has 336 singleton atoms, 36 nonempty
fixed-input fibers, and 0 disconnected quotient fibers.  The open item is no
longer whether a finite mode set exists, nor whether the representative new
singleton modes are connected; the open item is Lean formalization of
representative coverage and the per-fixed-input consequence to all-chain
`LKR_in`.  The first Lean table layer is now present in
`GoertzelLemma818FrontierMode.lean`: `tableClosedCheck_ok` axiom-free checks
the 20-mode, 40-transition profile-mode DFA table, `profileHashLookupCheck_ok`
checks the 20 archived profile hashes against the hash-to-mode lookup, and
`wordMode_inTable` is the abstract finite-mode induction skeleton for
nonempty orientation words.  The representative-word layer is also checked:
`representativeWordsSoundCheck_ok`, `representativeCoverageCheck_ok`, and
`modeWitnessWord_sound` show that every archived representative word folds to
the listed mode and every mode has a checked canonical representative.
`knownProfileWordHashCheck_ok` checks the 42 archived known word/profile-hash
pairs against both the DFA fold and the hash lookup, and
`knownTransitionHashCheck_ok` checks the 40 archived transition hash entries
against the Lean `step` function.  The actual structural induction hook is now
also present: `wordMode_induction` and `wordMode_bool_induction` lift any
step-preserved mode invariant from the two initial modes to every nonempty
orientation word.  The archived connectivity-witness layer is now checked too:
`archivedConnectivityCoverageCheck_ok` verifies 30 length-1-through-4
atom-connectivity rows, the two length-5 singleton quotient rows, and one
source-consistent witness for each of the 20 profile modes; and
`wordMode_hasArchivedConnectivityEvidence` lifts that witness coverage to
every nonempty orientation word.  This still is not the all-chain `LKR_in`
consequence: the remaining bridge is generated real chain/profile
certificates and per-fixed-input path certificates tying these archived rows
to actual Kempe connectivity.  Do not resume monolithic `decide` or open-ended
length sweeps for this step.
Checkpoint verdict: the finite 20-mode automaton and its transition closure
are checked, and all 20 modes have archived per-fixed-input connectivity
evidence at the metadata level.  No mode is presently flagged as lacking
connectivity evidence.  The open work is semantic certification: attach real
chain/profile certificates and per-fiber path certificates to the archived
rows, then use the DFA induction hook to obtain all-chain `LKR_in`.
This is the stop point for the current exploration pass.  Further work should
formalize the existing finite mode/certificate surface, not extend the
length-sweep search.  The next useful checkpoint is a generated representative
certificate layer that ties the archived atom/quotient rows to actual
chain-state Kempe paths and feeds `wordMode_induction`.
The first small bridge in that direction is
`GoertzelLemma818FrontierBaseBridge.lean`: it ties the four checked length-2
certificate audits to the corresponding frontier modes and archived
connectivity evidence.  The remaining bridge is broader representative-word
semantic certification, not another length sweep.
The current semantically certified base modes are now explicit in Lean:
`T/M/TT/TM/MT/MM` map to `mode07/mode16/mode10/mode18/mode11/mode04` and
pass `baseCertifiedFrontierCoverageAudit_ok` through real chain certificate
audits.  The next certificate-generation target is the other 14 frontier
modes, using representative words already recorded in the DFA table.
`GoertzelLemma818RepresentativeTargets.lean` now makes that target list
machine-checked: one chosen representative word for each remaining mode, no
overlap with the six base-certified modes, archived connectivity evidence for
each target mode, and complete coverage of the 20-mode frontier plan by
`plannedSemanticModeCoverageAudit_ok`.  The next non-metadata step is a compact
representative certificate generator: attach real per-fixed-input parent/path
certificates for these target words without monolithic closure search or large
row scans.
Stop checkpoint, 2026-07-01: the finite mode set has stabilized enough for
formalization.  The profile DFA is finite and closed at 20 modes and 40
transitions; all 20 modes have archived per-fixed-input connectivity evidence
at the metadata/quotient layer; no profile mode is currently known to lack such
evidence.  What is not yet checked is the semantic bridge from those archived
rows to actual chain-state Kempe paths for the 14 non-base representative
modes.  A `TTT` light-fiber prototype found the expected finite split
(45 empty fibers, 24 size-16 fibers, and 12 size-512 fibers), but the direct
row checker was still too large for the kernel at default recursion settings.
Leave that as archived WIP.  The next pass should generate smaller component
certificates or a finite transition certificate, then feed the result through
`wordMode_induction`; do not continue length sweeps or increase kernel limits.
`GoertzelLemma818SemanticBridge.lean` now provides the bookkeeping hook for
that pass: every profile mode has a checked planned semantic witness, the
witness words agree with the DFA mode fold and the chain-orientation
conversion, the witness coverage is closed under both profile transitions, and
`wordMode_hasSemanticModeAudit_of_targets` reduces arbitrary nonempty words to
the finite list of fourteen remaining target audits plus the six already
checked base audits.  The next useful theorem should instantiate those target
audits with real compact chain/component certificates, not add more metadata.
`GoertzelLemma818ComponentCertificate.lean` now supplies the intended compact
row checker: generated rows can give an explicit two-color component and prove
pair-color membership, seed-connectedness, closure, input avoidance, and switch
agreement without expanding `chainComponent`.  The first single-`τ` fiber is
already smoke-checked with explicit components.  Next, generate the same
row-split component certificates for one representative target, then scale that
format across the fourteen target audits.
The first non-base representative slice is now checked in
`GoertzelLemma818TripleTauComponentSmoke.lean`: `TTT`/`mode09`, fixed-input key
`[r,r,b,r]`, 16 states, explicit component rows, and parent-depth convergence.
This proves the component-certificate format works on a genuine remaining
representative mode.  `GoertzelLemma818TripleTauLightComponentCertificate.lean`
now expands the same component-row format to the light `TTT` slice:
`tttLightComponentCertificateAudit_ok` covers 69 light fixed-input fibers, 45
empty fibers, 24 nonempty size-16 fibers, and all 384 light chain states for
the `TTT`/`mode09` representative.  The next useful expansion is the 12 large
size-512 `TTT` fibers by a smaller transition/component certificate or further
row splitting, before moving to the other thirteen representative targets.
The first large-fiber row split is now checked in
`GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate.lean`:
`tttLargeFiber4Block0ComponentCertificateAudit_ok` covers the first 64 rows of
the first size-512 `TTT` fiber (`[r,r,b,b]`, root `2176`) with explicit
component rows, parent-map agreement, and parent-depth convergence.  A direct
continuation of that same generated 64-row block shape is not the right next
move: later generated blocks again exceed default kernel recursion in row or
parent-convergence checks.  Keep the checked block 0 theorem, leave the failed
block1-through-block7 WIP archived and unimported, and redesign the rest of
the large-fiber certificate as smaller per-fixed-input/per-component lemmas or
as a finite transition certificate before repeating the pattern on the other
eleven size-512 `TTT` fibers.
`GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate.lean` now
restarts that continuation successfully at a smaller grain: four 16-row chunk
modules certify rows 64 through 127 of the same `[r,r,b,b]` fiber.  The
parent-depth checks use local 16-source lists, avoiding the large expected-list
indexing that made the archived 64-row block shape brittle.  The first 128
rows of this size-512 fiber are now checked; rows 128 through 511 remain open.
`GoertzelLemma818TripleTauLargeFiber4Block2ComponentCertificate.lean` carries
the fresh-pass continuation through rows 128 through 191, again as four
16-row chunks.  Its parent-depth checks use explicit bounded parent paths to
root `2176`, avoiding the recursive parent-iterator normalization that made
the earlier generated WIP brittle.  Rows 0 through 191 of this size-512 fiber
are now checked; rows 192 through 511 remain open.
`GoertzelLemma818TripleTauLargeFiber4Block3ComponentCertificate.lean` carries
the same fresh-pass shape through rows 192 through 255, again as four 16-row
chunks with explicit bounded parent paths to root `2176`.  Rows 0 through 255
of this size-512 fiber are now checked; rows 256 through 511 remain open.
`GoertzelLemma818TripleTauLargeFiber4Block4ComponentCertificate.lean` carries
the same fresh-pass shape through rows 256 through 319, again as four 16-row
chunks with explicit bounded parent paths to root `2176`.  Rows 0 through 319
of this size-512 fiber are now checked; rows 320 through 511 remain open.
`GoertzelLemma818TripleTauLargeFiber4Block5ComponentCertificate.lean` carries
the same fresh-pass shape through rows 320 through 383, again as four 16-row
chunks with explicit bounded parent paths to root `2176`.  To keep high-side
parent paths small, `GoertzelLemma818TripleTauLargeFiber4Data.lean` now splits
the same finite parent map into 64-entry offset matchers under the unchanged
public `tttLargeFiber4ParentOf` interface.  Rows 0 through 383 of this
size-512 fiber are now checked; rows 384 through 511 remain open.
`GoertzelLemma818TripleTauLargeFiber4Block6ComponentCertificate.lean` carries
the same fresh-pass shape through rows 384 through 447, again as four 16-row
chunks with explicit bounded parent paths to root `2176`.  Rows 0 through 447
of this size-512 fiber are now checked; rows 448 through 511 remain open.
`GoertzelLemma818TripleTauLargeFiber4Block7ComponentCertificate.lean` carries
the same fresh-pass shape through rows 448 through 511, again as four 16-row
chunks with explicit bounded parent paths to root `2176`.  This completes all
512 rows of the first `[r,r,b,b]` size-512 `TTT` fiber.
`GoertzelLemma818TripleTauLargeFiber4Certificate.lean` aggregates the eight
block audits with the target/mode and count checks into
`tttLargeFiber4ComponentCertificateAudit_ok`, the downstream dependency point
for this completed fixed-input fiber.
`GoertzelLemma818TripleTauLargeFiber8Data.lean` and
`GoertzelLemma818TripleTauLargeFiber8Block0ComponentCertificate.lean`
start the next size-512 `TTT` fiber, `[r,r,p,p]`: ranges `4368..4623` and
`6000..6255`, root `4368`, max parent depth 6, and rows 0 through 63 checked
by explicit component rows, parent-map agreement, and bounded parent paths.
`GoertzelLemma818TripleTauLargeFiber8Block1ComponentCertificate.lean`
continues that fiber with rows 64 through 127, again split into four 16-row
chunks with explicit component rows, parent-map agreement, and bounded parent
paths to root `4368`.  Rows 0 through 127 of `[r,r,p,p]` are now checked.
`GoertzelLemma818TripleTauLargeFiber8Block2ComponentCertificate.lean` continues
the same fiber with rows 128 through 191 in the same four-chunk format.  Rows
0 through 191 of `[r,r,p,p]` are now checked, leaving 320 rows of that fiber
open.
`GoertzelLemma818TripleTauLargeFiber8Block3ComponentCertificate.lean` continues
the same fiber with rows 192 through 255.  Rows 0 through 255 of `[r,r,p,p]`
are now checked, leaving 256 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber8Block4ComponentCertificate.lean` continues
the same fiber with rows 256 through 319.  Rows 0 through 319 of `[r,r,p,p]`
are now checked, leaving 192 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber8Block5ComponentCertificate.lean` continues
the same fiber with rows 320 through 383.  Rows 0 through 383 of `[r,r,p,p]`
are now checked, leaving 128 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber8Block6ComponentCertificate.lean` continues
the same fiber with rows 384 through 447.  Rows 0 through 447 of `[r,r,p,p]`
are now checked, leaving 64 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber8Block7ComponentCertificate.lean` continues
the same fiber with rows 448 through 511.  All 512 rows of `[r,r,p,p]` are now
checked.
`GoertzelLemma818TripleTauLargeFiber8Certificate.lean` aggregates the eight
block audits with the target/mode and count checks into
`tttLargeFiber8ComponentCertificateAudit_ok`, the downstream dependency point
for this completed fixed-input fiber.
`GoertzelLemma818TripleTauLargeFiber10Data.lean` and
`GoertzelLemma818TripleTauLargeFiber10Block0ComponentCertificate.lean` start
the third size-512 `TTT` fiber, `[r,b,r,b]`: ranges `2448..2703` and
`4096..4351`, root `2448`, max parent depth `6`, and rows 0 through 63 checked
by four 16-row chunks.
`GoertzelLemma818TripleTauLargeFiber10Block1ComponentCertificate.lean`
continues the same fiber with rows 64 through 127.  Rows 0 through 127 of
`[r,b,r,b]` are now checked, leaving 384 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber10Block2ComponentCertificate.lean`
continues the same fiber with rows 128 through 191.  Rows 0 through 191 of
`[r,b,r,b]` are now checked, leaving 320 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber10Block3ComponentCertificate.lean`
continues the same fiber with rows 192 through 255.  Rows 0 through 255 of
`[r,b,r,b]` are now checked, leaving 256 rows of that fiber open.
`GoertzelLemma818TripleTauLargeFiber10Block4ComponentCertificate.lean` through
`GoertzelLemma818TripleTauLargeFiber10Block7ComponentCertificate.lean`
complete rows 256 through 511, and
`GoertzelLemma818TripleTauLargeFiber10Certificate.lean` aggregates all eight
blocks.  The third size-512 `TTT`/`mode09` large fiber `[r,b,r,b]` is now
fully checked; the other nine large `TTT` fibers remain open.

Checkpoint stop status, 2026-07-01: the exploration pass is checkpointed and
should not be extended by longer word sweeps.  The profile automaton is finite
and closed at the metadata layer: 20 modes, 40 transitions, 42 representative
word/hash checks, 30 length-1-through-4 atom-connectivity rows, and two
length-5 singleton quotient-connectivity rows.  Every mode has archived
per-fixed-input connectivity evidence; no profile mode is currently unverified
at that layer.  The remaining work is the semantic certificate layer: the six
base modes are backed by real single/length-2 chain certificates, and the
first non-base target `TTT`/`mode09` is backed by the light-fiber certificate
plus all twelve large-fiber certificates.  The thirteen other non-base
representative modes still need compact per-fixed-input chain/component
certificates or an equivalent finite transition certificate.
Once the target audits exist,
`GoertzelLemma818SemanticBridge.lean` provides the finite induction hook to
lift them to all nonempty `τ`/mirror-`τ` chains.

Immediate next goal: do not extend the exploration surface.  Build the
formalization from the stabilized finite-mode result already in hand: 20
profile modes, 40 closed transitions, archived per-fixed-input connectivity
evidence for every mode, six base modes certified by real chain tables, and the
completed `TTT`/`mode09` semantic certificate.  The remaining open certificate
set is
`mode00/mode01/mode02/mode03/mode05/mode06/mode08/mode12/mode13/mode14/mode15/mode17/mode19`.
Use smaller parent-path/component certificates or an equivalent transition
certificate for those modes.

Second stop checkpoint, 2026-07-01: a later generated block2-through-block7
continuation was left unimported and archived outside the public tree.  It is
not part of the checked proof surface.  The checkpoint verdict is unchanged
and should guide the fresh pass: the finite automaton is table-closed at 20
modes and 40 transitions, all 20 modes have archived per-fixed-input
connectivity evidence, and no profile mode is currently known to lack such
evidence.  What remains is not more exploratory sweeping; it is a compact
semantic certificate for the thirteen remaining target modes or an equivalent
finite transition invariant.

Current Gate-2 checkpoint, 2026-07-01: stop the open-ended connectivity sweeps
here.  The finite mode set has stabilized and is already the formal target:
20 modes, 40 closed table transitions, representative/hash coverage, 30
length-1-through-4 atom-connectivity records, two length-5 singleton quotient
records, and archived per-fixed-input connectivity evidence for every mode.
No metadata/profile mode is currently marked as connectivity-unverified.  The
open frontier is semantic, not exploratory: the six base modes have chain-level
certificates, `mode09` has its light `TTT` fibers plus all twelve large
fixed-input fibers certified, and the remaining work is the thirteen non-base
modes
`mode00/mode01/mode02/mode03/mode05/mode06/mode08/mode12/mode13/mode14/mode15/mode17/mode19`.
Formalize that finite surface next with compact per-fixed-input
chain/component certificates, or replace it by a finite transition invariant
that feeds the semantic bridge.  Do not extend lengths or representatives from
this checkpoint.

Fresh finite-surface formalization delta: the complete `TTT` target surface is
now explicit in `GoertzelLemma818TripleTauTargetProgress.lean`.  The theorems
`tttPartialTargetCertificateAudit_ok` and `tttTargetCertificateAudit_ok` check
the semantic witness for `mode09`, the light-fiber audit, all twelve completed
large-fiber audits, and the current exact state-count split: 6,528 certified
`TTT` states and 0 open states in the explicit representative target.  This is
the right accumulation layer for the fresh pass: it records real semantic
certificates without pretending that Lemma 8.18/8.19 or Section 9 is closed.

Additional checkpoint delta: `MMM`/`mode05` now has a full light-fiber audit
under the actual `[mirror, mirror, mirror]` chain word: 69 light fixed-input
fibers, 45 empty fibers, 24 nonempty size-16 fibers, and 384 checked light
states, with a reversed-key coverage audit tying the mirror fixed-input ids to
the original light partition.  This is still not a full `mode05` certificate;
the large fixed-input fibers and automaton closure remain open.  The first
large-fiber delta is now present too:
`mmmLargeFiber36Block1ComponentCertificateAudit_ok` and
`mmmLargeFiber36Block2ComponentCertificateAudit_ok` /
`mmmLargeFiber36Block3ComponentCertificateAudit_ok` /
`mmmLargeFiber36Block4ComponentCertificateAudit_ok` check four 64-row blocks of
the reversed `[b,b,r,r]` large fiber under the actual mirror-triple word.
`mmmLargeFiber36Block5PrefixComponentCertificateAudit_ok` adds the next three
16-row chunks, and `mmmLargeFiber36Block5ComponentCertificateAudit_ok`
completes that fifth block with an interval-membership row checker for chunk 3,
bringing this fixed-input fiber to 320 checked rows.  The interval checker
avoids broad traversal of the 512-row expected list; do not raise kernel limits
for the older simple mirror-word helper.

The older CAP5/F2, GP(12,2), and six-cut files are exploratory negative audits
of a divergent additive F2 route.  They remain useful for provenance and
infrastructure, but they are not Ben's actual route and should not be worked
as the main proof lane.

Read these four files first — they are the whole live surface:

| File | Contents |
|---|---|
| `GoertzelLemma814.lean` | Pillar-C finite model for Lemma 8.14: canonical three-cell gadget, finite proper-coloring state space, input-disjoint Kempe switches, indexed `LKR_in` path certificate, mirror check, Lemma 8.15 transparency finite check, the checked Lemma 8.18 pointwise-preparation obstruction, and the build-checked composite-chain model for the Gate-1 salvage audit |
| `GoertzelLemma818FrontierMode.lean` | Lab-facing finite profile-mode DFA table for the Lemma 8.18/8.19 repair: 20 mode constructors, profile hashes, representative words, two orientations, 40 total transitions, axiom-free `tableClosedCheck_ok`, `profileHashLookupCheck_ok`, abstract word-fold theorem `wordMode_inTable`, checked representative coverage theorems `representativeWordsSoundCheck_ok`, `representativeCoverageCheck_ok`, `modeWitnessWord_sound`, 42-word profile-hash consistency check `knownProfileWordHashCheck_ok`, 40-transition hash consistency check `knownTransitionHashCheck_ok`, structural induction hooks `wordMode_induction`/`wordMode_bool_induction`, and archived mode-connectivity witness coverage `archivedConnectivityCoverageCheck_ok`/`wordMode_hasArchivedConnectivityEvidence`; this is table closure/induction/hash/representative/evidence metadata only, not yet the all-chain `LKR_in` consequence |
| `GoertzelLemma818CompositeCertificate.lean` | Generated full `τ,τ` direct parent/path certificate table: `ttAllFiberCertificateAudit_ok` checks all 81 fixed-input keys, 36 nonempty fibers, 960 generated chain states, and parent depth at most 4 by row-split direct Kempe moves and parent-iteration checks; this is the base two-gadget table, not the all-chain `LKR_in` consequence |
| `GoertzelLemma818TauMirrorCertificate.lean` | Generated full `τ,mirror-τ` direct parent/path certificate table: `tmAllFiberCertificateAudit_ok` checks all 81 fixed-input keys, 36 nonempty fibers, 1152 generated chain states, and parent depth at most 4 by row-split direct Kempe moves and parent-iteration checks; this advances the length-2 base layer but is not the all-chain `LKR_in` consequence |
| `GoertzelLemma818MirrorTauCertificate.lean` | Generated full `mirror-τ,τ` direct parent/path certificate table: `mtAllFiberCertificateAudit_ok` checks all 81 fixed-input keys, 36 nonempty fibers, 1152 generated chain states, and parent depth at most 4 by row-split direct Kempe moves and parent-iteration checks; this advances the length-2 base layer but is not the all-chain `LKR_in` consequence |
| `GoertzelLemma818MirrorMirrorCertificate.lean` | Generated full `mirror-τ,mirror-τ` direct parent/path certificate table: `mmAllFiberCertificateAudit_ok` checks all 81 fixed-input keys, 36 nonempty fibers, 960 generated chain states, and parent depth at most 4 by row-split direct Kempe moves and parent-iteration checks; this completes the length-2 base table layer but is not the all-chain `LKR_in` consequence |
| `GoertzelLemma818LengthTwoBase.lean` | Finite aggregate interface for the four length-2 generated tables: `lengthTwoCertificateAudit_ok` proves the appropriate table audit for each constructor of `LengthTwoOrientWord`, and `lengthTwoAllCertificateAudit_ok` checks the complete four-word base list; this is a base hook, not the all-chain `LKR_in` consequence |
| `GoertzelLemma818TripleTauLightComponentCertificate.lean` | Generated explicit component-row certificate for the light part of the `TTT`/`mode09` representative target: `tttLightComponentCertificateAudit_ok` checks target/mode bookkeeping, 69 light fixed-input fibers, 45 empty fibers, 24 nonempty size-16 fibers, and 384 light chain states without expanding full `chainComponent`; the large-fiber certificates now complete the rest of `mode09`, while the other thirteen representative target modes remain the open semantic layer |
| `GoertzelLemma818TripleTauLargeFiber4Data.lean` / `GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber4Certificate.lean` | First large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[r,r,b,b]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and parent-depth convergence; the parent map is split into 64-entry offset matchers under the same public interface, and blocks 1 through 7 are split into four 16-row chunks, with blocks 2 through 7 using explicit bounded parent paths; `tttLargeFiber4ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber8Data.lean` / `GoertzelLemma818TripleTauLargeFiber8Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber8Certificate.lean` | Second large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[r,r,p,p]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and explicit bounded parent paths; `tttLargeFiber8ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber10Data.lean` / `GoertzelLemma818TripleTauLargeFiber10Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber10Certificate.lean` | Third large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[r,b,r,b]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and explicit bounded parent paths; `tttLargeFiber10ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber20Data.lean` / `GoertzelLemma818TripleTauLargeFiber20Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber20Certificate.lean` | Fourth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[r,p,r,p]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `4640`; `tttLargeFiber20ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber30Data.lean` / `GoertzelLemma818TripleTauLargeFiber30Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber30Certificate.lean` | Fifth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[b,r,b,r]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `0`; `tttLargeFiber30ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber36Data.lean` / `GoertzelLemma818TripleTauLargeFiber36Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber36Certificate.lean` | Sixth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[b,b,r,r]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `272`; `tttLargeFiber36ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber44Data.lean` / `GoertzelLemma818TripleTauLargeFiber44Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber44Certificate.lean` | Seventh large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[b,b,p,p]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `4912`; `tttLargeFiber44ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber50Data.lean` / `GoertzelLemma818TripleTauLargeFiber50Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber50Certificate.lean` | Eighth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[b,p,b,p]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `5184`; `tttLargeFiber50ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber60Data.lean` / `GoertzelLemma818TripleTauLargeFiber60Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber60Certificate.lean` | Ninth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[p,r,p,r]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `544`; `tttLargeFiber60ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber70Data.lean` / `GoertzelLemma818TripleTauLargeFiber70Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber70Certificate.lean` | Tenth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[p,b,p,b]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `2720`; `tttLargeFiber70ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber72Data.lean` / `GoertzelLemma818TripleTauLargeFiber72Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber72Certificate.lean` | Eleventh large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[p,p,r,r]` size-512 fiber and checks all 512 source rows by explicit component rows, parent-map agreement, and bounded parent paths to root `816`; `tttLargeFiber72ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauLargeFiber76Data.lean` / `GoertzelLemma818TripleTauLargeFiber76Block0ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block1ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block2ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block3ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block4ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block5ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block6ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Block7ComponentCertificate.lean` / `GoertzelLemma818TripleTauLargeFiber76Certificate.lean` | Twelfth large-fiber decomposition for `TTT`/`mode09`: records the parent map for the `[p,p,b,b]` size-512 fiber with ranges `2992..3247` and `3552..3807`, root `2992`, and max parent depth `6`; all 512 source rows are checked by explicit component rows, parent-map agreement, and bounded parent paths; `tttLargeFiber76ComponentCertificateAudit_ok` aggregates the completed fixed-input fiber |
| `GoertzelLemma818TripleTauTargetProgress.lean` | Semantic progress aggregator for the `TTT`/`mode09` representative target: `tttPartialTargetCertificateAudit_ok` and `tttTargetCertificateAudit_ok` verify the `mode09` semantic witness, the light-fiber audit, all twelve completed large-fiber audits, and the exact count split of 6,528 certified states versus 0 states open in the `TTT` target surface; this closes the explicit `TTT` representative audit but not the other thirteen target modes and not the all-chain lift |
| `GoertzelLemma818MirrorTripleComponentSmoke.lean` / `GoertzelLemma818MirrorTripleLightSlices.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Chunk0ComponentCertificate.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Block2ComponentCertificate.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Block3ComponentCertificate.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Block4ComponentCertificate.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Block5PrefixComponentCertificate.lean` / `GoertzelLemma818MirrorTripleLargeFiber36Block5ComponentCertificate.lean` | Partial semantic certificate for the `MMM`/`mode05` representative target: the smoke theorem `mmmFiber9ComponentCertificateAudit_ok` checks key `[r,b,r,r]`, `mmmLightComponentCertificateAudit_ok` checks the full mirror-triple light surface, and the block sequence checks five 64-row blocks of the reversed `[b,b,r,r]` large fiber; the large fixed-input fibers remain mostly open, so this is not a full target audit and not the all-chain lift |
| `Goal.lean` | The target (`Theorem49ShellClaim`), its reduction to four geometric oracles plus a fifth non-geometric algebraic cancellation oracle, and proofs that **all four geometric uniform oracles are false** — including the v23.5 residual/current-boundary lane, whose positive wrapper is fixed-embedding equivalent to the refuted collar-layer surface |
| `Shells.lean` | Bundled hypothesis packages (`ClosedWalkExactShell`, `SuccessorCycleExactShell`, `ClosedWalkCancellationShell`, …) replacing the historical 8–10-hypothesis telescopes |
| `Frontier.lean` | The maximal positive and negative results, stated over the bundles as thin wrappers, including detector-based cancellation sufficiency |
| `CAP5RouteVerdict.lean` | The current CAP5/F2 route verdict: either the executable report returns a concrete primitive portal/cycle checker gap, or the closed-frontier route is exactly the absence of the concrete target/off-target F2 evaders; it also names the unified emitted-kernel/remaining-map evader and proves, under no primitive gap, that this evader exists exactly when the closed route endpoint fails; in that same branch the CAP5/Jordan geometric separator repair is blocked by the cyclic-cut obstruction; `noGap_forall_boundaryEdge_crosses` and `cap5PrimitiveCheckerGap_of_boundaryEdge_odd_closed_walk` record the Gate-1 parity barrier for honest odd CAP5 boundary cycles |
| `CAP5RoutePayoff.lean` / `F2KernelCertificate.lean` / `CAP5WheelRouteData.lean` / `CAP5DodecahedralRouteData.lean` | Route payoff audit and finite gate surface: the former closed-route-to-`EdgeColorable 4` payoff is removed as vacuous because the root already has type `G.EdgeColoring Color`; the non-vacuous route endpoint is `CAP5RouteClosedSynthesisPayoff` (theorem-4.9 synthesis plus selected-boundary-zero classifier control); the finite no-gap pre-RREF input is named as `CAP5FiniteNoGapRouteInput`; checked finite left-inverse/RREF-style certificates land through `F2LeftInverseKernelCertificate`; empty-remaining finite certificates land through `CAP5FiniteNoGapRouteInput.routeClosed_of_remainingControlEdges_eq_empty`; `CAP5FiniteNoGapRouteInput.redInterior_mem_projectedColoringGeneratorSubspace` and `CAP5FiniteNoGapRouteInput.blueInterior_mem_projectedColoringGeneratorSubspace` expose the fixed-embedding formability condition that every interior-support red/blue coordinate probe must already lie in the projected generator span; `CAP5WheelRouteData.lean` proves one concrete exceptional five-edge wheel boundary is Gate-1 blocked; `CAP5DodecahedralRouteData.lean` records the strict incidence BREAK certificate for the cyclic-five/Tait dodecahedral six-cut; and the follow-up actual-route lab shows that same dodecahedral side is not a formable `CAP5FiniteNoGapRouteInput` because every required red/blue single-coordinate projected-generator membership is missing |

## Consolidated CAP5/F2 Verdict

This section is retained as exploratory route history.  It is superseded for
current Ben-route work by `GoertzelLemma814.lean` and the Pillar-C status above.

The current finite CAP5/F2 route is decided at the make-or-break level already:
the first formable cyclic-five/Tait survivor, GP(12,2), gives a wide Gate-2
BREAK in every sidecase under the checked finite criterion
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty`.
That result is the checkpoint represented by `cb729b3a`; later GP12 adapter and
two-row route-certificate commits are upside evidence only.

The generic six-cut meta-barrier has not been proved.  The non-boundary six-cut
degree of freedom remains open.  The consolidated route status is therefore:
decided current-route wide BREAK, six-cut residual open, no Four Color Theorem
claim, and no route-derived coloring payoff.

Consolidation verification: focused `CAP5RouteVerdict` build SHA256
`7b6ae89e8bfa82e8cc7df6070d84fd71e2ca1a6172f02db3ee5c9e2212d119c8`;
FourColor umbrella build SHA256
`737deefdb55e3f567d1a23d0caf36854be06e510a68be13d3eb6e0f39d18b99d`;
axiom audit driver/log SHA256
`b0110815b9229f6956455e7ad0e6940e15986836dff08631fb58b46b3204623c` /
`c599bbefab7d583e1d737e4edc5056bb57e984e54076e1b6821af0451e903b7e`,
baseline `[propext, Classical.choice, Quot.sound]`.

## Current status (one paragraph)

The positive lane is complete from geometry upward: repaired previous-boundary
witness geometry, explicit well-founded peel-witness data, or generic
interior-dual distance-peel data on the shell's embedding each yield full
`Theorem49BoundaryRootSynthesis` (`Frontier.lean`, wrapping the route files).
The same file now also exposes a non-geometric positive lane: an exact shell
plus the projected-generator detector certificate
(`BoundaryZeroProjectedGeneratorDetector`) also yields full synthesis, and
`Goal.lean` now packages both the old whole-closure uniform hypothesis
`AlgebraicCancellationOracle` and the weaker, lab-faithful
`AlgebraicNeighborhoodCancellationOracle`, which only asks for some explicit
detecting coloring family inside the shell Tait coloring's edge-Kempe closure.
The live shell/frontier surface now also carries the direct kernel-check form
of that same obligation: `Shells.lean` bundles exact shells together with an
explicit family whose concrete pairing map has trivial kernel, `Frontier.lean`
proves that this already yields full theorem-4.9 synthesis, and `Goal.lean`
packages the corresponding uniform hypothesis as
`AlgebraicNeighborhoodPairingKernelOracle`.
The negative lane is complete from the shells downward: the
wheel-with-inner-triangle and shared-interior-pair benchmarks inhabit the full
endpoint-bearing exact one-collar/v23 shells while refuting every named
geometric layer, so no uniform derivation from the manuscript's stated
hypotheses to the geometry its argument consumes can exist
(`Goal.lean: not_interiorDualPeelOracle, not_wellFoundedPeelOracle,
not_previousBoundaryGeometryOracle, not_residualBoundaryGeometryOracle`).
The last of these is the formal verdict on the v23.5 revision memo's repair
proposal: the residual/current-boundary lane as currently specified is
conservative over the refuted collar-layer surface, so only its unformalized
"algebraic cancellation certificate" obligation remained live in prose.  The
new live-surface files now formalize that obligation directly as the shell-wise
detector oracles above: it is no longer just roadmap prose, but unlike the
geometric oracles it is not presently refuted by the current shell-bearing
benchmarks.  Moreover, the new file
`Mettapedia/GraphTheory/FourColor/Theorem49ColoringGeneratorFamilyRoute.lean`
proves that a detector on any explicit coloring family inside the base
edge-Kempe closure already upgrades to the full theorem-4.9 synthesis
endpoint.  So the live non-geometric lane no longer has to be phrased as a
whole-closure detector; it can match the finite lab's smaller explicit
neighborhood certificates directly.  A new kernel-checked theorem now sharpens
the comparison:
`Theorem49DetectorStrength.lean` proves that on every shell-bearing embedding
the theorem-4.9 target `W₀(H)` is a proper subspace of the full
selected-boundary-zero chain space.  So the detector/cancellation oracle is
strictly stronger than the manuscript target on the current shell surface; it
is not merely a restatement of theorem 4.9 in different words.  Structurally, any shell with an
unblocked endpoint forces two distinct interior edges on some face boundary
(`Frontier.lean`), which is what kills the facewise-at-most-one,
canonical-choice, and source-preserving one-collar repair lanes.  Update
2026-06-11: the new finite lab under `scripts/4cp_lab/` directly decides the
current endpoint on the small explicit benchmarks.  It reproduces the positive
degenerate wheel and diamond-with-triangle cases, and finds
`Theorem49BoundaryRootSynthesis` true on the shell-bearing
`wheelWithInnerTriangleEmbedding` and `sharedInteriorPairAnnulusEmbedding` for
their explicit benchmark colorings; on the same embeddings it is also true for
all 36 wheel Tait colorings and all 72 shared-interior-pair Tait colorings
enumerated by the lab.  A follow-up detector experiment now localizes the
annihilator burden further: for the wheel benchmark, the explicit coloring
alone already kills every selected-boundary-zero annihilator, while for the
shared-interior-pair benchmark the explicit coloring plus its six one-step
Kempe neighbors already suffice.  The wheel explicit-coloring case is now
kernel-checked in Lean by
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelEndpointRegression.lean`,
and `Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelFullSweepRegression.lean`
now upgrades that explicit endpoint to all 36 wheel Tait colorings.  The
shared-interior-pair benchmark now has kernel-checked representatives for both
of the 36-color Kempe-closure classes found by the lab, via
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairEndpointRegression.lean`
and
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairSecondClosureEndpointRegression.lean`.
The new file
`Mettapedia/GraphTheory/FourColor/Theorem49SynthesisClosureInvariance.lean`
then proves that the full theorem-4.9 synthesis package depends only on the
underlying `EdgeKempeClosure` class of the base coloring, and can be
transported along mutual edge-Kempe reachability.  So the remaining Lean gap
on the current pathologies is no longer the wheel sweep, no longer a missing
shared representative, and no longer the shared class-membership /
classification step either: the new file
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairFullSweepRegression.lean`
now classifies every Tait coloring of the shell-bearing shared benchmark into
two parametric Kempe-closure families, proves four generic closure generators
per family, reduces each family to its explicit kernel-checked representative,
and upgrades theorem 4.9 to all 72 shared Tait colorings.  So the current
explicit shell-bearing benchmarks no longer leave a Lean gap at the level of
their full finite Tait sweeps; the remaining open burden on this path is
either a wider shell-bearing search or a new general computable F₂ layer that
scales beyond these two benchmarks.  Update later on 2026-06-11: the new file
`Mettapedia/GraphTheory/FourColor/Theorem49BoundaryProjectionDetector.lean`
shows that the selected-boundary projected-generator detector property is also
an edge-Kempe-closure invariant, and the wheel/shared full-sweep regression
files now upgrade not only `Theorem49BoundaryRootSynthesis` but also that
detector property to all 36 wheel and all 72 shared Tait colorings.  So the
current finite benchmarks are now closed in Lean at the detector layer as
well, not only at the final theorem-4.9 synthesis package.  Update later still
on 2026-06-11: the exact wheel radius-0 detector certificate exposed by the
finite lab is now kernel-checked directly in
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelRadiusZeroDetectorRegression.lean`,
showing that the explicit wheel coloring alone already detects every nonzero
selected-boundary-zero chain.  The exact shared radius-1 detector certificate
is now kernel-checked directly in
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairRadiusOneDetectorRegression.lean`.
So the finite lab's two minimal explicit detector certificates are both now
Lean-native.  Moreover, Lean sharpens the lab's seven-color shared radius-1
neighborhood: for the shared explicit benchmark coloring, the detector already
follows from a two-color witness subfamily consisting only of the base coloring
and one inner red/blue Kempe neighbor.

Update 2026-06-28: the live continuation branch now treats the old geometric
repair sequence as a fork to decide, not a place to bank more isolated packets.
The validation lab run archived locally as
`fourcolor-move2-f2-oracle-validation-lab-20260628.log`
found no top-level all-interior or declared/forcing-control F2 evader across
65 records, and the crux report still rejects the outside-crossing geometric
route on generated two-band annuli.  In Lean,
`CAP5PathXorDetector.lean` now exposes the target-level no-evader contract
`forcedEdgeBoundaryTargetCoverage_iff_no_targetEvader` and the Move-2 handoff
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_no_evader_of_no_missing_finsetControl`:
a completed CAP5 finite checker with no selected-boundary-zero evader closes
`Theorem49BoundaryRootSynthesis` and also proves forced-edge coverage of the
actual theorem-4.9 target `W0(H)`.  This advances the algebraic fork but does
not decide it uniformly; the remaining work is to derive the full no-evader
verdict from exact shell data or exhibit a genuine evader outside the current
finite sample.

Later on 2026-06-28: the all-interior Move-2 survivor is now route-facing in
Lean rather than only a lab observation.  The rerun archived locally as
`fourcolor-move2-interior-frontier-validation-lab-20260628.log` again saw
65 records and the algebraic-F2 implication
`forcing_interior_edges_nonempty => f2_all_interior_boundary_zero_only_no_evader`
survived with support 36 and purified support 18.  The new CAP5 detector
theorems `interiorSupportForced_synthesis_and_boundaryTargetCoverage` and
`interiorSupportForced_or_remainingEdge` say: if the closed primitive checker
has enumerated every ambient interior-support edge as forced, then theorem-4.9
synthesis and forced-edge coverage of `W0(H)` both follow; otherwise the
canonical interior-support worklist exposes a concrete remaining edge with a
strictly smaller erasure measure.  This converts the surviving F2 lane into a
success-or-next-edge frontier, but still leaves the uniform enumeration
problem open.

Later still on 2026-06-28: the same all-interior lane now has an executable
closed-worklist certificate.  The rerun archived locally as
`fourcolor-move2-empty-worklist-validation-lab-20260628.log` again confirmed
the finite F2 all-interior survivor on 65 records.  In Lean,
`remainingInteriorSupportEmpty_synthesis_and_targetCoverage` and
`remainingInteriorSupportEmpty_report_synthesis_and_targetCoverage` say that
an empty canonical interior-support worklist, together with the closed
primitive checker report, directly yields theorem-4.9 synthesis and forced-edge
coverage of `W0(H)`.  The remaining algebraic burden is now sharper: prove the
exact CAP5 shell reaches this empty worklist uniformly, or formalize the
remaining worklist edge as the genuine obstruction/evader source.

Subsequently on 2026-06-28: the closed executable report failure branch was
made route-facing.  In Lean,
`boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl`
and
`theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`
say that, once the primitive checker report is empty, a failed synthesis run
does not merely leave an abstract gap: it carries a genuine
selected-boundary-zero evader for the enumerated forced edges and a concrete
remaining interior-support edge with a decreasing worklist measure.  This
sharpens the algebraic fork to synthesis versus evader-plus-next-edge; it still
does not prove the exact CAP5 shell uniformly chooses the synthesis side.

After the fork-decision reset on 2026-06-28: the classifier/no-evader oracle is
now expressed as an exact Lean equivalence rather than only a sufficient
handoff.  The lab artifact
`fourcolor-move2-classifier-noevader-lab-20260628.json` records 65 benchmark
signatures: both all-interior F2 no-evader flags are true on all 65 records,
and both declared-forced no-evader flags are true on the 36 records with
nonempty forcing interior edges.  The exported projected-generator bundle
contains 65 certificate files and 80 rejected counterexample files; the two
algebraic-F2 cruxes still survive with support 36 and purified support 18.
In Lean,
`enumeratedExceptionalAnnulusForcedEdgeClassifierBoundaryZeroControl_iff_no_boundaryZeroEvader`,
`enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader`
and
`theorem49BoundaryTargetClassifierControl_iff_no_targetEvader` say that the
emitted CAP5 classifier coordinates control the full selected-boundary-zero
carrier, any chosen boundary-zero Kirchhoff target, and the theorem-4.9 target
`W0(H)`, exactly when no nonzero chain in the corresponding carrier evades
every enumerated CAP5 forced edge.  This does not decide the exact shell, but
it removes the algebraic ambiguity in the oracle statement: the remaining
Move-2 fork is now to prove that exact CAP5 data supplies the no-evader side,
or to exhibit the evader.

The no-evader direction now lands on the full boundary-zero classifier-control
surface, not only the theorem-4.9 target.  Lean proves
`theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_no_missing_finsetControl`
and the executable interior-support specialization
`theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`:
a closed CAP5 checker plus absence of a nonzero selected-boundary-zero evader
yields theorem-4.9 synthesis and proves that the emitted CAP5 coordinates
control the whole selected-boundary-zero subspace.  The remaining problem is
therefore not this direction of the oracle; it is deriving the no-evader
verdict from uniform exact-shell data, or producing the genuine evader.

Update 2026-06-29: the CAP5/F2 continuation is now packaged as a route verdict
in `CAP5RouteVerdict.lean`.  The theorem `cap5F2Route_irreducibleBarrier`
assembles the oracle, the target/off-target F2 split, and the geometric
CAP5/Jordan obstruction into one top-level statement.  Under the standard
cyclic-five finite F2 route data, Lean returns either a primitive
portal/cycle checker gap, or a closed-frontier equivalence:
no target/off-target F2 evaders iff theorem-4.9 synthesis plus full
selected-boundary-zero classifier control.  In the same closed-frontier
branch, the exceptional CAP5/Jordan cyclic-separator repair is impossible.
This is an irreducible-barrier verdict on this route, not a proof of 4CT and
not a positive-canary 4-colorability sufficient condition.

Follow-up on 2026-06-29: the primitive checker frontier was sharpened inside
`CAP5RouteVerdict.lean`.  Lean now proves that
`CAP5PrimitiveCheckerGap` is exactly nonempty
`missingCheckerEvidenceLatents` in the executable 16-latent report; conversely,
emptying that report is exactly `¬ CAP5PrimitiveCheckerGap`.  The same file
also proves that no primitive gap forces portal crossings for every latent and
forces both graph-side cycle witnesses, while absence of either side-cycle
witness immediately inhabits the primitive checker gap.  This is the precise
proof-level reason the current route verdict remains a barrier rather than an
unconditional closure: exact CAP5 data still has to supply the portal/cycle
evidence and decide the target/off-target F2 evader set, or accept the concrete
gap/evader branch already returned by the formal route.

Second follow-up on 2026-06-29: the side-condition discharge was pushed through
the packaged budget oracle as far as the current definitions permit.  The
theorem `budgetMetNoEvader_boundaryZeroControl_oracle_of_noGap` derives the
oracle's broad portal-crossing premise, both side-cycle witnesses, and the
no-missing checker premise from the single hypothesis
`¬ CAP5PrimitiveCheckerGap`.  The new constructor
`CAP5F2RouteCertificate.ofNoGap` does the same for the top-level route
certificate.  Lean also proves
`not_forall_no_cap5PrimitiveCheckerGap_allSides`: a completely side-uniform
checker-gap discharge is impossible because the constant-empty side has no
selected-side cycle and therefore directly inhabits `CAP5PrimitiveCheckerGap`.
So the remaining side-condition seam is not a report/latent transport gap; it
is the need to prove that the actual CAP5 side selected by exact shell data has
the two cycle witnesses and no primitive checker gap.  The surviving algebraic
barrier is now named directly: `CAP5F2UnifiedKernelMapEvader` is the unified
emitted-kernel/remaining-map obstruction, and under no primitive checker gap
Lean proves `CAP5F2NoUnifiedKernelMapEvader` iff `CAP5F2RouteClosed`, while
existence of such an evader is equivalent to failure of that closed endpoint.

Payoff correction on 2026-06-29: `CAP5RoutePayoff.lean` removes the former
route-closure-to-`G.EdgeColorable 4` payoff as vacuous.  The root `C₀` already
has type `G.EdgeColoring Color`, so colorability was coming from the type of
`C₀`, not from `CAP5F2RouteClosed`.  The replacement theorem
`cap5RouteClosedSynthesisPayoff_of_routeClosed` extracts only the route-native
consequences: theorem-4.9 synthesis and full selected-boundary-zero classifier
control.  The exact Tait bridge remains named as
`CAP5RouteClosedRootTaitBridge cert`, but a genuine route coloring payoff needs
a raw edge-labeling/properness bridge or a route-type refactor, not the current
`G.EdgeColoring Color` root.  The wheel-with-inner-triangle graph has the
independent coloring canary `WheelCAP5RoutePayoff.wheelColoringCanary`; this is
not a CAP5 route payoff.  The exact positive CAP5 canary still missing is
`WheelCAP5RoutePayoff.WheelCAP5FiniteRouteClosedCanary`: one finite checker
report plus a closed CAP5/F2 route certificate for an actual no-gap CAP5 side.
`CAP5WheelRouteData.lean` now fixes one concrete five-edge wheel boundary
enumeration and exceptional component-cover core, but proves this exact core
is not such a side: `wheelCAP5PrimitiveCheckerGap` shows every vertex-side
choice has a primitive checker gap because the `p0Inside/p4Outside` side case
would force `wit12`, `wit23`, and `wit31` to cross the same side, contradicting
the triangle parity lemma.  Consequently no `CAP5FiniteNoGapRouteInput` or
`CAP5FiniteRouteClosedWitness` exists for this concrete five-edge wheel core.
The finite pre-RREF input is explicit:
`CAP5FiniteNoGapRouteInput` combines a closed executable primitive-checker
report, the concrete forced-edge classifier, and all emitted/remaining
red-blue single-coordinate witnesses into the `CAP5F2RouteCertificate`
consumed by the unified-evader oracle.  The MAKE side is now wired directly:
`CAP5FiniteNoGapRouteInput.routeClosed_of_noUnifiedKernelMapEvader` turns that
input plus actual exceptional/cyclic side data and
`CAP5F2NoUnifiedKernelMapEvader` into `CAP5F2RouteClosed`, and
`CAP5FiniteNoGapRouteInput.toClosedWitness_of_noUnifiedKernelMapEvader`
packages the finite route-closed witness.  The BREAK side is named as
`CAP5FiniteUnifiedKernelMapEvaderWitness`, a concrete unified emitted-kernel/
remaining-map evader for the induced certificate.  So the next make-or-break
test is not another route fork; it is to instantiate that input for the actual
side and check `CAP5F2NoUnifiedKernelMapEvader`, or accept that named
obstruction.  The BREAK constructor
`CAP5FiniteNoGapRouteInput.exists_unifiedKernelMapEvader_of_boundaryZeroChain`
now handles the finite certificate shape exposed by the lab: a
selected-boundary-zero chain that vanishes on emitted coordinates and is
nonzero on one remaining control edge gives the named unified kernel-map
evader.

RREF-shaped finite gate update on 2026-06-29:
`F2KernelCertificate.lean` introduces `F2LeftInverseKernelCertificate`, a
finite basis-and-matrix certificate whose checked product equation reconstructs
a left inverse and proves the emitted map has trivial kernel.  In
`CAP5RoutePayoff.lean`,
`cap5F2NoUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot` proves
that a checked bottom emitted-pairing kernel certificate directly rules out the
unified emitted-kernel/remaining-map evader.  The finite-input wrappers
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot`,
`CAP5FiniteNoGapRouteInput.routeClosed_of_emittedFinsetPairingKernel_eq_bot`,
and
`CAP5FiniteNoGapRouteInput.toClosedWitness_of_emittedFinsetPairingKernel_eq_bot`
plus their `...LeftInverseCertificate` variants show exactly what a checked
RREF/kernel certificate has to feed.  This is only the certificate interface:
the actual CAP5 no-gap input, a concrete basis for its selected-boundary-zero
submodule, and its checked emitted matrix/certificate remain the make-or-break
artifact.

Lab-first finite Gate-2 verdict on 2026-06-29: the run recorded in
`fourcolor-cap5-f2-all-static-verdict-20260629.json` builds the current CAP5
forced-edge classifier matrix over F2 for all eight static benchmark JSONs and
decides the finite kernel question by exact mod-2 row reduction before adding
any more Lean apparatus.  The current Lean surface contains one concrete
component-cover core (`wheelCAP5ComponentCoverCore`) and zero concrete
positive `CAP5FiniteNoGapRouteInput` instances.  Seven static benchmarks have
zero Gate-1 no-gap sides.  The only Gate-1-positive benchmark is
chained-diamonds, with 32 no-gap sides and 368,640 route cases, all
`BREAK_evader`; one explicit unit witness is the red-scalar edge `cdt12` after
emitting `cdt46` and `cdt56`, with `cdt12` and `cdt45` remaining as controls.
Lean also proves `not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph`,
so that regression case cannot be promoted to an actual Tait-route BREAK
certificate.

Strict incidence Gate-2 verdict on 2026-06-29: the run recorded in
`fourcolor-cap5-strict-gate2-incidence-verdict-20260629.json` derives
`selectedBoundarySupport` and `interiorEdgeSupport` from face incidence, as
Lean's `PlaneEmbeddingWithBoundary` does, and then decides the unified
emitted-kernel/remaining-map question by exact F2 row reduction.  This
supersedes the earlier manual one-control prism MAKE: with incidence-derived
support the prism has all 18 edges as interior edges, all 3,840 no-gap route
cases are `BREAK_evader`, and a separate cyclic-cut audit shows the prism also
fails `CyclicallyFiveEdgeConnected`.  The strict run then builds a
dodecahedral six-cut candidate.  It is cubic, brute-force Tait-colorable,
cyclically five-edge-connected, and Gate-1-positive; exact F2 row reduction
finds 532 no-gap sides and 1,021,440 route cases, all `BREAK_evader`.  For the
distinguished side `{0,1,2,3,4,19}` and boundary slots
`dod0_10, dod1_8, dod2_6, dod4_5, dod4_17`, the
`p0Inside_p4Outside` matrix emits `dod18_19, dod4_17`, leaves 28 remaining
interior controls, has scalar rank 2 and kernel dimension 28, and the unit
red-scalar chain supported on `dod0_1` is a concrete evader: it is
boundary-zero, vanishes on emitted coordinates, and is detected by the
remaining map at `dod0_1`.

`CAP5DodecahedralRouteData.lean` now promotes the strict lab answer far enough
to be checked in Lean: it defines the dodecahedral graph, face-boundary
embedding, Tait coloring, exceptional component-cover core, distinguished
six-cut side, emitted edges `dod18_19,dod4_17`, and
`dodecahedralStrictF2KernelEvaderCertificate`.  That certificate records row
words `0x20000000,0x400`, RREF row words `0x400,0x20000000`, scalar rank 2,
kernel dimension 28, and the unit red-scalar evader on `dod0_1`.  The
follow-up actual-route lab then blocks route-input witness promotion for this
side: over the full edge-Kempe closure, the projected face-generator span has
rank 42 in the 60-dimensional chain space and contains none of the 60
emitted/remaining red/blue single-coordinate probes required by
`CAP5FiniteNoGapRouteInput`.  The dedicated forced-classifier matrix run
`fourcolor-dodeca-forced-classifier-matrix-lab-20260629.json` then checks all
four portal sidecases with numpy and SymPy over GF(2): every raw coordinate
matrix is `BREAK_evader`, with emitted ranks 6, 4, 4, and 4 in the
60-dimensional red/blue domain and the unit `dod0_1` coordinate as a raw
witness.  The formal answer for this actual dodecahedral side is still
`INVALID_ROUTE_INPUT_missing_projected_generator_memberships`, not MAKE and
not a formal BREAK witness, because the route family cannot be constructed.
The one-face-punctured dodeca repair was also checked in
`fourcolor-dodeca-punctured-route-f2-lab-20260629.json`: each omitted face
creates a genuine selected-boundary support, but across all 12 omitted faces
and four sidecases the projected-generator rank is 38 on the 50-dimensional
selected-boundary-zero domain and no case is formable; each case still misses
50, 52, or 54 route probes.  This rules out that natural repair of the
distinguished six-cut, not all non-boundary CAP5 supports.
Reruns
`fourcolor-dodeca-forced-classifier-matrix-lab-rerun-20260629.json` and
`fourcolor-dodeca-punctured-route-f2-lab-rerun-20260629.json` preserve those
answers.  Lean now records the fixed-embedding reason in
`CAP5FiniteNoGapRouteInput.false_of_missing_interior_red_probe` and
`CAP5FiniteNoGapRouteInput.false_of_missing_interior_blue_probe`: any missing
red or blue coordinate for an interior-support edge makes the finite route
input impossible, since the edge is necessarily either emitted or remaining.
The follow-up graph-generic filter
`fourcolor-small-cubic-tait-route-formability-dodeca-kempeclasses-lab-20260629.json`
shows that this is not merely a bad pinned dodeca root: all 60 dodecahedral
Tait colorings split into 10 Kempe classes of size 6, and every individual
class misses every required interior red/blue probe on the closed embedding
and on every one-face puncture, even though the union of all Tait classes has
full coordinate span.  The known-small-family run
`fourcolor-small-cubic-tait-route-formability-known20-capped-lab-20260629.json`
then checks 22 known cubic planar graphs through 20 vertices; formable Kempe
classes occur only in tetrahedral or non-cyclic-five cases, while the genuine
Tait cyclic-five case up to isomorphism is dodecahedral and remains
non-formable.  This is finite evidence plus a dodeca-wide Kempe-class barrier,
not yet the generic B1 meta-barrier.
No 4CT claim, MAKE certificate, or full
`CAP5FiniteUnifiedKernelMapEvaderWitness` is made here.

Actual GP(12,2) Gate-2 verdict on 2026-06-29: the cyclic-first known-family
filter through 24 vertices found `generalized_petersen_12_2` as a genuine
cyclic-five/Tait candidate with a closed formable Kempe class.  The dedicated
lab `fourcolor-gp12-cap5-gate2-verdict-lab-20260629.json` then builds the
actual CAP5 forced-edge classifier matrix for the first five-edge cyclic cut
`e0_1,e2_14,e3_4,e13_23,e15_17`.  The closed embedding has empty
selected-boundary support, all 36 edges are interior, and the selected Kempe
class has rank 72/72, so the finite route probes are present.  Exact numpy
RREF with SymPy `GF(2)` rank cross-check gives BREAK in all four sidecases:
emitted ranks 2, 2, 4, and 2; kernel dimensions 70, 70, 68, and 70; and
explicit unit red-coordinate evaders recorded in the JSON.  This lands the
finite decision for the first formable survivor: not MAKE, but
`BREAK_unified_kernel_map_evader_in_every_side_case`.  The Lean-side promotion
is now the exact current finite Gate-2 criterion:
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty`.
Any nonempty remaining-control set yields a unit red-coordinate unified
kernel-map evader, while empty remaining controls give the no-evader side.  The
equivalent coverage form
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset`
states the route-surface demand directly: the current CAP5 classifier must emit
the whole canonical interior support.  Missing-edge and cardinality corollaries
now package BREAK whenever an interior-support edge is not emitted, the emitted
interior count is too small, or the total emitted set is smaller than the
interior support.  The GP(12,2) sidecases leave 35, 35, 34, and 35 remaining
controls, so the lab verdict factors through the checked Lean criterion.  No
graph-specific GP(12,2) route-input witness is claimed yet, because the
projected-generator coordinate witnesses are still lab evidence rather than
Lean membership certificates.  The Gate-1 half is now checked in Lean:
`gp12FiveCutSide_noPrimitiveCheckerGap` proves the selected five-edge cut has
no primitive checker gap from the five boundary-slot crossing facts and
explicit cycles on both sides.  In addition, `CAP5GP12RouteData.lean` now
packages the concrete graph/embedding/Tait/CAP5 core and the four sidecase
unit-evader certificates matching the lab verdict.
The membership side has a new finite certificate artifact:
`fourcolor-gp12-membership-certificate-lab-20260629.json` verifies all 72
closed GP(12,2) interior red/blue probes in the chosen Kempe-class projected
span, with rank 72/72, SymPy GF(2) rank cross-check 72/72, 72 used generator
rows, and combination sizes 2..42.  Script/JSON SHA256:
`2615eefc5c4a09faf556e00a17b769a2bde6dff7cb843f5619b0a5182fede9be` /
`b96c76cb4660003371a3cd1902b162b53585d086ad2043dca9229f73754e761d`.
`fourcolor-gp12-kempe-path-certificate-lab-20260629.json` verifies the Kempe
paths from Lean `gp12TaitEdgeColoring` to the 11 coloring IDs used by those
rows: Lean base ID 5, maximum depth 4, and 15 distinct coloring IDs across the
paths.  Script/JSON SHA256:
`574553f65496cc7babe6ef1153700014a3766bb4a4a14a330df48d11c67a8aac` /
`77276a587f35964baa88342b53a28d9e5e09d055209d1496fd1099e6f26fb139`.
Lean now reduces the actual GP(12,2) route-input construction to those finite
memberships and Kempe-class closure via
`gp12FiniteNoGapRouteInput_of_allCoordinateMemberships`; no graph-specific
route-input witness is claimed until that finite certificate is packaged.
The additional closure-set adapter
`gp12FiniteNoGapRouteInput_of_closureCoordinateMemberships` removes the need to
name a separate finite coloring set in the route input: using the full
`EdgeKempeClosure gp12TaitEdgeColoring`, the remaining certificate package is
the 72 projected-generator finite-sum memberships in the closure subspace.
The finite-sum landing shape is now checked in Lean via
`finset_sum_projectedFaceGenerator_mem_projectedColoringGeneratorSubspace` and
`single_mem_projectedColoringGeneratorSubspace_of_finset_sum_projectedFaceGenerator_eq`.
As a first concrete slice, `CAP5GP12RouteData.lean` verifies the lab's two-row
certificate for `gp12_e8_20/red`: rows 26 and 194, both on face 8 with pair
`blue_purple`, sum to `Pi.single gp12_e8_20 red`.  The resulting theorem
`gp12_e8_20_red_mem_projectedColoringGeneratorSubspace_of_routeCertColorings_mem_closure`
still assumes the two involved colorings are in the Kempe closure, so it is not
yet a graph-specific route input.  The remaining full package is the Kempe
closure proofs for the used route-certificate colorings plus the rest of the
finite-sum coordinate certificates.  Smoke file
`fourcolor-gp12-two-row-certificate-smoke-20260629.lean` SHA256:
`79b6b90c1842f4f923e7d6da3c51e7125ecc8646de0709251f69af7358ecd435`.
Verification for this two-row route-certificate increment: focused
`CAP5GP12RouteData` build SHA256
`c72439a459caa6fb401efba52bbeb04c71f9ec9e481631b98b49b40adeac09e3`,
FourColor umbrella build SHA256
`b1828374afcbde99b5c3d02b8ceb52e98ba519fb6dd90728168b5bfa5399f6f7`,
and axiom audit driver/log SHA256
`3a878f943ba33d7c2522db0304e56360cdcee99f8b1727e832763c863f561222` /
`faf81cb4f15a4517e0f56ed58aaf36b7ebfc0baa07e71ad02e921d44db8c7987`
with baseline `[propext, Classical.choice, Quot.sound]`.
This does not upgrade the six-cut residual: the generic six-cut meta-barrier
is not proven, and the non-boundary six-cut degree of freedom remains open.
Verification for this closure-set adapter increment: focused
`CAP5GP12RouteData` build SHA256
`c5cf0251289caeb631efa958cbc2e78f3960812f36b3f680878a845e8cf96870`,
FourColor umbrella build SHA256
`af99f08c3c25acf21c284845e1f3b84ac7cb9f357dabf99089a4dcf73de4bbbe`,
and axiom audit driver/log SHA256
`8c2907f04d6c54ee3e173a7cfd331c0da24c33e86bdb529c931187c2e7ec7cf1` /
`37b88abc5bf1563500e2a736d493cf9073a00e54396ce8d7e0c4f5d55de909be`
with baseline `[propext, Classical.choice, Quot.sound]`.
Verification for the
Gate-1 no-gap increment: focused `CAP5GP12RouteData` build SHA256
`6a0465c7b5b2500101e4e7afa74c8c43c4c7738ca0afa47bc06c75850ab83360`,
FourColor umbrella build SHA256
`1c6dbe74bdaa401f5655b468a78884784eda313c787a725987421e8c0a2e2961`,
and axiom audit driver/log SHA256
`79f27c6c5494e9c06b955c2c322e839a7d768b1f4d45803cbd7bd5a2a12601dd` /
`e1db9e764ef2a54b6c3470e18adc175d631bc5ee83988349f7bbb4b5b55cfcaa`
with baseline `[propext, Classical.choice, Quot.sound]`.
The geometric strengthening
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_noncrossing_interiorEdgeSupport`
and
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sameSide_interiorEdgeSupport`
adds the repair-relevant current-surface barrier: any interior-support edge that
does not cross the selected vertex side remains un-emitted and yields a unified
kernel-map evader.  The stronger named side-bipartition wrappers
`CAP5FiniteNoGapRouteInput.interiorEdgeSupport_edges_cross_of_noUnifiedKernelMapEvader`
and
`CAP5FiniteNoGapRouteInput.interiorEdgeSupport_edges_cross_of_routeClosed`
state the successful current-route condition directly: the selected side must
cut every canonical interior-support edge.  Focused
`CAP5RoutePayoff` and FourColor umbrella builds passed, and the new criterion
axiom audits are baseline `[propext, Classical.choice, Quot.sound]`.
This has now been sharpened beyond odd parity.  The side-cycle theorem
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport`
shows that if Gate 1's selected-side cycle is wholly supported by canonical
interior edges, no no-evader certificate can exist.  Its all-interior
specialization
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_forall_mem_interiorEdgeSupport`
and route-closed form
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_forall_mem_interiorEdgeSupport`
rule out the closed/all-interior current finite surface even when the interior
graph is bipartite.  Focused `CAP5RoutePayoff` build SHA256
`4ebb17291eadc7fdfa20a925dd9ce713dfe0769bcedfa9513f3e36981ad4bbc4`.
The odd-interior-walk form remains available:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_interiorEdgeSupport_odd_closed_walk`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_interiorEdgeSupport_odd_closed_walk`
show that an odd closed walk inside canonical interior support forbids the
no-evader side, and forbids route closure under the usual exceptional/cyclic
equivalence.  The necessary-condition wrappers
`CAP5FiniteNoGapRouteInput.no_interiorEdgeSupport_odd_closed_walk_of_noUnifiedKernelMapEvader`
and
`CAP5FiniteNoGapRouteInput.no_interiorEdgeSupport_odd_closed_walk_of_routeClosed`
state the same result as an internal bipartiteness requirement on successful
current-route inputs.  In `CAP5GP12RouteData.lean`,
`gp12_not_noUnifiedKernelMapEvader_of_finiteNoGapRouteInput` now instantiates
the all-interior theorem rather than the face-0 odd-cycle special case: because
every GP12 edge is interior in the closed embedding, no-evader is impossible
for any finite no-gap GP12 route input, independent of side and `p0/p4`
sidecase.  `gp12_not_routeClosed_of_finiteNoGapRouteInput` gives the
route-closed obstruction once cyclic-five connectivity is supplied.  The
face-0 cycle `0-1-2-14-12-0` remains recorded as an odd-cycle witness, but the
main GP12 obstruction no longer depends on odd parity.  This is a stronger
current-surface GP12 BREAK than the four emitted-set sidecase witnesses, but it
is still not a route-independent repair-proof meta-barrier.
Focused `CAP5RoutePayoff`, focused `CAP5GP12RouteData`, and FourColor umbrella
builds passed with SHA256
`4ba71936046ffcbe56af1b281b0ffd5c32b9c25c7d95acbaa39f0225a8e9ed93`,
`2218bdab2ff586615c68280ae97b7839c66fa64822a01f0567dbb10b6b0e5082`, and
`5e9bd78b573fbfe4ac9ec9d80d70db706da56dffb08d2e67b47bcdcd51c1e07d`;
the axiom audit remains baseline `[propext, Classical.choice, Quot.sound]`
with log SHA256
`d840b6dfd5b523987e455e18708756dd1ca18b761232530ac908743919241cd5`.
The side-cycle/all-interior increment then passed focused builds with SHA256
`4ebb17291eadc7fdfa20a925dd9ce713dfe0769bcedfa9513f3e36981ad4bbc4`
for `CAP5RoutePayoff` and
`0428e629dc3fe6a9b56af418efacd69aaf4a88d6fbc0db26de64de1f6e4a3946`
for `CAP5GP12RouteData`; FourColor umbrella SHA256
`be8496df88da4efab22699fc57e0810c00bdbaf01ddc372e9d16e3e3170acaab`;
axiom audit driver/log SHA256
`275258792b1d337e665fe36b151d644b2e20c1ec5344da2c83bd02e2396ea6f2` /
`afe9cfe8a01ab5cfa77ee3c6ca6a14f04f55223d3e9ffc833c5fb8f7e728b409`,
baseline `[propext, Classical.choice, Quot.sound]`; `git diff --check`,
touched Lean proof-token scan, and public diff leak scan clean.
The side-cycle obstruction also now has a non-interior crossing form:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_nonInterior_edges_cross`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_nonInterior_edges_cross`
rule out no-evader and route closure when every non-interior edge already
crosses the selected side.  The boundary-slot corollaries
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_nonInterior_subset_boundaryEdge`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_nonInterior_subset_boundaryEdge`
specialize this to the case where every non-interior edge is one of the five
CAP5 boundary slots: no-gap makes all five slots cross, but Gate 1 also
supplies a selected-side cycle.  A surviving repair of the current finite
surface must therefore find a selected-side cycle edge outside canonical
interior support that is not merely a no-gap boundary slot.  This is a current
classifier/input-surface obstruction, not the final repair-robust B1
meta-barrier.  Focused `CAP5RoutePayoff`, focused `CAP5GP12RouteData`, and
FourColor umbrella builds passed with SHA256
`baf83bc864536339ace652630fe76b3e599db14aa5f3d291ab6b9340a4d72732`,
`693bd616b3420f260a081b7dfc12cace892414788ffdc5b5a3e449b37bddbfa2`, and
`6423fcb114a3354125db4ce80e2a57eef6a5b4db6246f4b1758923f5fa2fe00e`;
the axiom audit driver/log SHA256 are
`7f081459a669e1d1e34925a146d0237555f67c491209ae962f4cf0f726515382` /
`ac507e5c9c1061c160d3d7758765dbe4c49aa1e6f180da0d546e320d89bd2049`,
baseline `[propext, Classical.choice, Quot.sound]`.
The sharper local side-cycle version is checked as
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`:
it is enough that the Gate-1 selected-side cycle itself be covered by
canonical interior support or the five CAP5 boundary slots.  Six-cut
checkpoint status: this is finite-evidence/current-surface progress, not a
proven generic six-cut meta-barrier.  The non-boundary six-cut degree of
freedom remains open.  Focused `CAP5RoutePayoff`, focused
`CAP5GP12RouteData`, and FourColor umbrella builds passed with SHA256
`9f93d299da21e27eb3492abfdd0312b1c96ced1475b2994989638ae5917032f5`,
`b6e618c3603acc54be5a54deed1bfd502c196ba8e62216e4f416951191968069`, and
`ce461cfe7aa93c85d50a752bf7d19405286fc8474c3d3fcb1aaf2140ee13a8e5`;
the axiom audit driver/log SHA256 are
`252079c06d2416bd393f457ab8b57be8b5211106658a5bc721b1bcb3b8ad733e` /
`3ecc5bc92ce68601cf1b945fb15ce54f45bc2f9e00ce5138be4973d1121de5c0`,
baseline `[propext, Classical.choice, Quot.sound]`.
The same obstruction now has an explicit-cycle form:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`.
One side-contained cycle covered by canonical interior support plus the five
CAP5 boundary slots is enough to rule out no-evader or route closure.  A
current-surface survivor must therefore make every selected-side cycle escape
through a non-interior non-boundary-slot edge.  This is still not the generic
six-cut meta-barrier, but it is the right graph-side residual.  Focused
`CAP5RoutePayoff`, focused `CAP5GP12RouteData`, and FourColor umbrella builds
passed with SHA256
`d18b4d66459dd04dfcbda08c9aef4279530ded9a05b5242eb2fa3cfc39de365d`,
`98a2ec8a3513ce8348aeacd3f96fe7f8b6907a51365476956f12d52588eb6a38`, and
`6e72fb11a40bb6894da320174c0b887e40b60c1d589b2e5dec5821bd5207dd4e`;
the axiom audit driver/log SHA256 are
`9025abf124771a09382dd56560a9a83e4c17d2d63410ca45754d2d4720d75cc4` /
`ba6559862ad00a3993086afa49144ff51b919c3759aeb4f35b3e0fdb06dae284`,
baseline `[propext, Classical.choice, Quot.sound]`.
A finite dodeca audit against this explicit-cycle condition gives the current
lab boundary.  `fourcolor-dodeca-explicit-covered-cycle-audit-20260629.json`
finds all 4 closed strict sidecases have a covered side cycle.  Among the 48
one-face-punctured rows, 24 have a covered side cycle and 24 escape because the
omitted face is one of faces `0..5`, leaving the archived selected-side
pentagon with a non-interior non-boundary-slot edge.  All 48 punctured rows,
including the 24 escape rows, remain invalid route inputs by projected-generator
membership failure.  Audit SHA256
`fd1b7ce900538396200206b66dee682f63c56b4002cd1550442977e5e46ef734`.
The archived known/generalized-Petersen sweep through 24 vertices was also
post-audited against this side-bipartition requirement: the route-relevant
Kempe-formable class has 15 embeddings, all on `generalized_petersen_12_2`,
and zero have bipartite canonical interior support; the cyclic-five full-Tait
upper-bound formable class also has zero bipartite-interior survivors.  The
audit log SHA256 is
`5e654ecb29cb59261e74d28269a4f73e130e8d9b267b7c3bc74b1ba010d3faaa`.
This is finite evidence only, not the generic B1 meta-barrier.
The older archive candidates with apparent route-case verdicts were audited
before promotion.  `spoke-cut-prism-6` is Tait/cubic and had an old all-MAKE
lab abstraction, but it fails cyclic-five via nine size-four cyclic cuts.
`split-chained-diamonds` is Tait-colorable under backtracking and had an old
all-BREAK abstraction, but it is disconnected and not connected cubic
3-regular.  Evidence JSON SHA256
`3ab3a792466d092d81af761b5c841e7138b241b01880a25b6e0f9b2ff5edc3c6`.
Neither is an objective-A valid CAP5/Tait/cyclic-five input.

The current finite surface now also has an active-portal obstruction:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_activePortal_interiorEdgeSupport`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_activePortal_interiorEdgeSupport`
show that an active sidecase portal boundary edge in canonical interior support
cannot be emitted and therefore forces a unified kernel-map evader, and rules
out route closure under the usual exceptional/cyclic equivalence.  Focused
`CAP5RoutePayoff` build SHA256
`582e5065827594125f1da8bd6a68be437d42fbc5a503569c46ed26c357a4a760`.

A two-face annulus audit was added to test the obvious repair gap left by the
closed/one-face-punctured sweep.  Over known NetworkX cubic planar/Tait/cyclic-
five graphs through 24 vertices, all two-face omissions, and all five-edge
cyclic two-component cuts, the lab found 223 full-Tait formable annular
upper-bound surfaces and 91 Kempe-formable annular surfaces, but zero
side-bipartition-valid side rows and zero rows that could fit a sidecase
emitted portal-complement under any boundary ordering.  Evidence JSON SHA256
`1016cde08d7f2aec705488118bf7c12ee714290b24a6a54328f8970073266077`; run log
SHA256 `2efd5b38fb16788a4d6edcc7148af1d8dbc258fcb8805dbcddbccdd4ae5afc4b`.
This is wider finite evidence over legitimate annular DOF, not a generic
repair-robust meta-barrier.
Final verification for the active-portal/annulus refinement: focused
`CAP5GP12RouteData` build SHA256
`2e1faf197bd9d5fb7fa1ef9902e0d2acf1e791024ee2b9d201a17e72f5566a63`;
FourColor umbrella build SHA256
`c744a4994d825744513323cdfbeed1892f7bf5b639355aa8862df2dabc26e909`;
axiom audit driver SHA256
`fb4089155bc838ebf170b3bdfcb3227a63c2bbc21af083f00e05d3ed931d83d1`;
axiom audit log SHA256
`096d98e3fa7e9556b63cc8b9ede8c8e6f35ef7a7c57e03ab3603ec2032a8c802`,
baseline `[propext, Classical.choice, Quot.sound]`.  `git diff --check`,
the touched Lean proof-token scan, and the public diff leak scan are clean.

Boundary-cycle Gate-1 repair audit on 2026-06-29: the run recorded in
`fourcolor-dodeca-boundary-cycle-gate1-lab-20260629.json` checks the natural
dodecahedral repair where the five CAP5 boundary edges are an actual
pentagonal boundary cycle rather than the strict lab's five-of-six cut support.
Across all 12 pentagonal faces and all `2^20` vertex-side masks, it finds zero
sides crossing all five boundary edges and therefore zero Gate-1 no-gap sides.
Lean promotes the generic obstruction as
`cap5PrimitiveCheckerGap_of_boundaryEdge_odd_closed_walk`: if the five boundary
edges cover an odd closed walk, Gate 1 is impossible because no vertex-side cut
can cross every edge of that odd closed walk.  `CAP5RoutePayoff.lean` now
pushes that obstruction through the finite route surface:
`CAP5FiniteNoGapRouteInput.false_of_boundaryEdge_odd_closed_walk` and
`CAP5FiniteRouteClosedWitness.false_of_boundaryEdge_odd_closed_walk` rule out
both finite no-gap inputs and finite route-closed witnesses for any such
honest odd boundary.  This is a real barrier for honest odd CAP5 boundary
cycles, but it is not claimed as a full refutation of non-boundary cut-style
reformulations.

The next target-level corollary turns finite dimension into an explicit fork
test for exact CAP5 data.  In Lean,
`exists_theorem49BoundaryTargetEvader_of_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_lt`
says that a CAP5 classifier below the boundary-zero plus theorem-4.9 Kirchhoff
target dimension bound yields a genuine nonzero `W0(H)` evader for the
enumerated forced edges.  Conversely,
`edge_card_le_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_of_no_targetEvader`
says any no-evader classifier must pay that lower bound.  This does not prove
exact shell no-evader, but it makes the finite F2 fork executable: exact shell
data must either meet the target dimension budget or produce the evader branch.

The latest Move-2 bridge separates the target oracle from the remaining
boundary-zero obstruction.  In Lean,
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_offTargetBoundaryZeroEvader_of_no_missing_finsetControl`
says target classifier control closes the completed CAP5 checker exactly when
there is no off-target selected-boundary-zero evader.  Conversely,
`offTargetBoundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`
says a closed-checker failure under target control produces such an off-target
evader together with the decreasing interior-support worklist edge.  The
remaining algebraic fork is now explicit: prove exact CAP5 data excludes these
off-target evaders, or formalize one.

That off-target branch is now concrete rather than merely complementary.  Lean
proves
`CAP5TransportedEdgeComponentCoverCore.exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget`:
any selected-boundary-zero chain outside `W0(H)` fails a Kirchhoff equation at
some theorem-4.9 boundary vertex.  The route-facing versions
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl`
and
`boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`
therefore replace the abstract off-target fork by a concrete vertex-Kirchhoff
failure fork: exact shell data must either rule out forced-edge-vanishing
boundary-zero chains with a nonzero theorem-4.9 boundary-vertex Kirchhoff sum,
or exhibit one.

The vertex-failure fork now has the same lab-to-Lean interface as the target
oracle.  The finite F2 lab reports the additive signature
`f2_all_interior_boundary_zero_kirchhoff_failure_absent`: on the 65-record
2026-06-28 rerun it is true for every all-interior control set, and the crux
packet
`forcing_edges_to_f2_all_interior_boundary_zero_kirchhoff_failure_absent`
survives on the 36 records with nonempty forcing interior edges.  In Lean,
`no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`
turns the row-span/subset certificate into the no-failure hypothesis, while
`boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`
turns failure of that certificate into a genuine evader.  The route-facing
closure theorem
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl`
therefore makes the remaining algebraic obligation precise: prove the exact
shell subset certificate, or formalize the evader produced by its failure.
Lean now also records the equivalence
`forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
and the route-facing binary theorem
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl_of_no_missing_finsetControl`:
under target classifier control and a closed checker, the subset certificate
closes synthesis/target coverage, while failure of the certificate is already
the genuine vertex-Kirchhoff evader.  The next mathematical step is therefore
not another interface theorem; it is the exact shell subset certificate itself,
or a formalized counterexample to it.

The exact subset certificate is now proved on the executable empty-worklist
shell.  Lean has
`interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty`,
`forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_interiorEdgeSupport_subset_enumeratedForcedEdges`,
`forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty`,
`no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_remainingInteriorSupportEmpty`,
and
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_remainingInteriorSupportEmpty_of_no_missing_finsetControl`.
Thus an empty canonical interior-support worklist no longer just closes the old
no-evader route; it proves the row-span/subset certificate demanded by the
current binary fork and rules out the concrete vertex-Kirchhoff evader branch.
The remaining fork decision is narrower: prove exact CAP5 data reaches this
empty-worklist/subset side uniformly, or formalize the evader exposed when it
does not.

The empty-worklist path now has a structural obstruction rather than just an
implementation gap.  Lean proves
`exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport`
and
`not_remainingInteriorSupportEmpty_of_closed_walk_odd_length_in_interiorSupport`:
if an odd closed walk is entirely supported by ambient interior-support edges,
then any Boolean CAP5 forced-edge classifier leaves a concrete remaining
interior-support edge, with a strict erasure decrease of the canonical
worklist.  Therefore the all-interior empty-worklist proof path cannot be
uniform over odd-interior-walk supports.  Exact CAP5 data must either exclude
that structure while reaching the subset certificate, or the surviving branch
has to be pushed into the genuine vertex-Kirchhoff evader theorem already
formalized above.

The target-controlled executable fork now packages that pressure in one theorem
surface instead of leaving it spread across conditional lemmas.  Lean proves
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`:
with an empty checker report and target classifier control, the route returns
either theorem-4.9 synthesis plus target coverage, or a genuine
forced-edge-vanishing boundary-zero evader with nonzero Kirchhoff sum at a
theorem-4.9 boundary vertex and a decreasing remaining worklist edge.  The
odd-interior specialization
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_oddInteriorWorklistEdge_of_closed_walk_odd_length_in_interiorSupport`
adds that an odd closed walk in ambient interior support unconditionally leaves
such a remaining worklist edge.  Thus the exact shell cannot silently use the
empty-worklist subset proof on odd-interior supports; it must either prove the
target-controlled synthesis side by other exact CAP5 data or expose the
vertex-Kirchhoff evader branch.

The success side now excludes the odd-interior obstruction internally.  Lean
proves
`not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges`:
if every ambient interior-support edge is enumerated as forced by one CAP5 side,
then no odd closed walk lies in ambient interior support.  The route-facing
wrappers
`interiorSupportForced_synthesis_and_boundaryTargetCoverage_and_no_closed_odd_walk`
and
`remainingInteriorSupportEmpty_synthesis_and_targetCoverage_and_no_closed_odd_walk`
therefore say that the all-interior/empty-worklist subset branch both closes
theorem-4.9 synthesis with target coverage and certifies that the
odd-interior-worklist obstruction is absent.  The remaining exact-shell work is
not to reconcile those branches; it is to prove exact CAP5 data reaches this
success branch, or to instantiate the already formalized vertex-Kirchhoff
evader branch.

The complementary no-evader side now survives the odd-worklist witness itself.
Lean proves
`theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_and_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`:
if an odd closed walk lies in ambient interior support, the canonical worklist
is still nonempty, but target classifier control plus absence of the concrete
theorem-4.9 boundary-vertex Kirchhoff evader closes synthesis and target
coverage anyway.  Thus the odd-worklist obstruction only blocks the
empty-worklist proof path; it is not itself the surviving algebraic failure
mode.  The exact shell must now supply the no-evader/subset certificate by
other CAP5 data or produce the genuine vertex-Kirchhoff evader.

The executable CAP5 report now feeds directly into that algebraic fork.  Lean
proves
`theorem49Synthesis_and_boundaryZeroControl_of_noEvader_of_forcedAllLatents`,
`remainingInteriorEmpty_synthesis_and_targetCoverage_of_forcedAllLatents`, and
`targetControlledSynthesis_or_evader_of_forcedAllLatents`: under cyclic
five-edge-connectivity, the report verdict
`forcedCounterexampleLatents = all` closes the primitive missing-evidence
frontier and drives the existing F2 endpoints.  With a no-evader verdict it
yields theorem-4.9 synthesis plus full boundary-zero classifier control; with
an empty canonical interior-support worklist it yields the subset-certificate
success side; under target classifier control it returns the exact
synthesis-versus-genuine-vertex-Kirchhoff-evader fork.  This still does not
prove that exact CAP5 shell data supplies the no-evader/subset certificate,
but it removes the raw `missingCheckerEvidenceLatents = []` premise from the
route-facing F2 checkpoint.

The report-forced-all target-controlled interface is now split into its two
actual fork halves.  Lean proves
`targetControlledSynthesis_of_noEvader_of_forcedAllLatents` and
`targetControlledEvader_of_notSynthesis_of_forcedAllLatents`: once
`forcedCounterexampleLatents = all` closes the primitive missing-evidence
frontier, target classifier control plus absence of the concrete theorem-4.9
boundary-vertex Kirchhoff evader yields synthesis and target coverage; if
synthesis still fails, Lean returns exactly that genuine evader together with
a decreasing remaining-worklist edge.  This removes an interface ambiguity in
the executable report path, but it does not by itself prove that exact
CAP5/Jordan shell data supplies the no-evader/subset side.

The same report-forced-all failure branch now has a canonical path-xor payload
form.  Lean proves
`canonicalPayloadEvader_of_notSynthesis_of_forcedAllLatents` and
`synthesis_or_canonicalPayloadEvader_of_forcedAllLatents`: if the forced-all
report branch still fails theorem-4.9 synthesis, the canonical interior-support
runner returns the finite artifact the lab is designed to expose, namely a
forced-bin path-xor detector payload, a selected-boundary-zero chain vanishing
on every enumerated forced edge, a concrete remaining interior edge that is
not forced and where the chain is nonzero, a strict worklist decrease, and a
nonzero canonical red/blue family pairing.  This does not prove the exact-shell
no-evader/subset side, but it makes the alternative branch computational rather
than only existential.

The forced-all branch now also exposes the pure no-target F2 evader fork.  Lean
proves
`boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_notSynthesis_of_forcedAllLatents`
and
`theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`:
once the report forces all latents, failed theorem-4.9 synthesis is already a
genuine selected-boundary-zero evader for the enumerated CAP5 forced edges,
together with a decreasing remaining interior-support worklist edge.  The
target-controlled and canonical path-xor payload branches are therefore
refinements of this basic evader branch, not separate failure modes.

The forced-all F2 oracle is now packaged as the route-facing decision itself.
Lean proves
`theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroEvader_of_forcedAllLatents`:
once the report forces all latents, either the no-evader verdict closes
theorem-4.9 synthesis plus full selected-boundary-zero classifier control, or
there is an actual nonzero selected-boundary-zero evader for the enumerated
forced edges.  This is the correct fork surface for the remaining lab-to-Lean
work: exact CAP5/Jordan shell data must now supply the no-evader/subset side,
or the explicit evader side is the obstruction to formalize.

The empty-worklist side of that fork now carries the actual no-evader verdict.
Lean proves
`remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents`:
if the forced-all report has no remaining canonical interior-support worklist,
then every interior-support coordinate is already emitted as a forced edge, no
nonzero selected-boundary-zero chain can vanish on all forced edges, and
theorem-4.9 synthesis follows with full selected-boundary-zero classifier
control.  Thus the remaining exact-shell task is not to reinterpret the
empty-worklist certificate; it is to prove uniform CAP5/Jordan data reaches it
or to formalize the evader/worklist branch.

The forced-all finite scheduler fork is now explicit as well.  Lean proves
`remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_or_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`:
after the executable report has forced all latents, either the empty-worklist
no-evader/full-control branch holds, or there is a concrete remaining
interior-support edge whose erasure strictly decreases the finite worklist.
This makes the next exact-shell obligation operational: prove the remaining
worklist is empty from uniform CAP5/Jordan data, or use the returned edge to
drive the finite scheduler toward an evader/worklist obstruction.

On the geometric fork, the source-bound one-collar repair treadmill has now
been consolidated into a shell-level obstruction.  In
`FrontierGeometric.lean`, the theorems
`not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell`,
`not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell`, and
`not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell`
show that every closed-walk exact shell blocks the canonical witness choice
and all one-collar collar/previous-boundary witness geometries for the same
reason: the shell's unblocked endpoint already forces a face with two distinct
interior-support edges.  This is no longer a single failing packet; it is a
uniform obstruction for the canonical/one-collar positive-collar repair class.
The side-cut part now has the same structural treatment for the odd-walk
separator class: `not_exists_sideCut_crosses_closed_odd_walk_subset` and
`not_exists_exceptionalAnnulusCrossingOutsideEdge_of_closed_odd_walk_subset`
say that any finite side-cut support containing an odd closed walk cannot be
realized by a single vertex-side predicate, nor by the CAP5 exceptional
outside-crossing normal form.  The consolidated wrappers
`closedWalkExactShell_oneCollar_and_oddSideCut_obstruction` and
`closedWalkExactShell_oneCollar_and_CAP5OddSideCut_obstruction` package this
with the shell-wide one-collar obstruction.  The repair-removal side is now
exposed at the graph-facing cyclic-cut interface as well:
`CAP5ExceptionalCyclicSeparatorRepairRealization`,
`not_CAP5ExceptionalCyclicSeparatorRepairRealization_of_cyclicallyFiveEdgeConnected`,
and
`closedWalkExactShell_oneCollar_and_CAP5CyclicSeparatorRepair_obstruction`
say that realizing even one compatible exceptional CAP5/Jordan candidate as
cyclic-cut data produces a cyclic edge cut of size at most four, impossible in
a cyclically five-edge-connected graph; the wrapper packages this with the
exact-shell one-collar/canonical obstruction.  The remaining geometric work is
to close the residual generator surface.

The residual generator surface is now classified and decision-shaped.  In
`FrontierGeometric.lean`,
`closedWalkExactShell_oneCollar_and_CAP5GeneratorNode_residualClassifier`
proves that a generated CAP5 separator node in a cyclically five-edge-connected
graph is either missing primitive checker evidence or emits the concrete
outside-crossing edge outside candidate support.  The report-level theorem
`closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_residualClassifier`
adds the finite 16-latent statement: every generated latent is forced exactly
when the missing-evidence frontier is empty, and if not, Lean returns a
specific missing-evidence latent.  The new report-decision theorem
`closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_geometricRepairDecision`
uses the report equivalences
`missingCheckerEvidenceLatents_eq_nil_iff_all_checker_evidence` and
`missingCheckerEvidenceLatents_ne_nil_iff_exists_failed_checker_evidence`:
the missing branch is exactly failure of the primitive portal/cycle
prerequisites for the realized CAP5/Jordan separator-repair class; if those
prerequisites are present, the report is forced-all and the completed
repair branch is blocked by the same cyclic-five small-cut obstruction.
The completed-prerequisite wrapper
`closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction` records that
closed branch without another report fork: once the missing-evidence frontier
is empty, cyclic five-edge-connectivity forces all generated latents into the
counterexample bin and forbids the exceptional cyclic-separator repair
realization by the size-at-most-four cyclic-cut obstruction, while the
closed-walk shell still blocks the canonical and one-collar repair surfaces.
Thus the residual Move-1 task is no longer another packet refutation: either
prove exact shell data supplies the primitive prerequisites, or keep failed
prerequisites as outside the realized repair class.

## The open problem

Exactly two route forks are live; isolated repair-packet refutations are no
longer acceptable progress.

1. **Geometric fork**: consolidate the repaired CAP5/Jordan failures into a
   single structural obstruction theorem.  The source-bound
   canonical/one-collar part is now shell-wide: closed-walk exact shells force
   the same two-interior-edge face obstruction against canonical witness
   choice, one-collar collar geometry, and one-collar previous-boundary
   witness geometry.  The side-cut part is now structural for supports
   containing an odd closed walk: those supports cannot realize a cyclic
   separator by a single vertex side, including in the CAP5 outside-crossing
   normal form.  The repair-removal surface now also has the fundamental
   small-cut obstruction: any compatible exceptional CAP5/Jordan candidate
   realized as cyclic-cut data is a forbidden cyclic edge cut of size at most
   four under cyclic five-edge-connectivity.  The residual generator/report
   layer is now decision-shaped: under cyclic five-edge-connectivity every
   generated node either emits the outside-crossing edge outside candidate
   support or is missing primitive checker evidence; report-level missing
   evidence is exactly failure of the primitive portal/cycle prerequisites for
   the realized separator-repair class; and if those prerequisites are present,
   the completed branch is forced-all and blocked by the small-cut
   obstruction.  The completed-prerequisite wrapper
   `closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction` names that
   branch as the single CAP5/Jordan small-cut obstruction.  The remaining
   Move-1 gap is to prove exact shell data supplies those primitive
   prerequisites, or keep failed prerequisites outside the realized CAP5/Jordan
   repair class.
2. **Algebraic fork**: resolve the F2 cancellation oracle.  The current
   machine-checked statement is now packaged rather than exposed as case
   cartography: with the primitive checker gap absent,
   `budgetMetNoEvader_boundaryZeroControl_oracle` proves no unified
   emitted-kernel/remaining-map evader iff theorem-4.9 synthesis plus full
   selected-boundary-zero classifier control, and failure returns that same
   precise unified evader.  The supporting statements remain sharper than a
   one-way handoff: full
   selected-boundary-zero classifier control is equivalent to absence of a
   nonzero selected-boundary-zero evader, and the closed finite checker plus
   that no-evader verdict gives both theorem-4.9 synthesis and full
   boundary-zero classifier control.  The emitted-edge red/blue pairing kernel
   is now exact for the same no-evader verdict, so a finite rank certificate on
   the immutable emitted forced-edge coordinates closes the forced-all route,
   while kernel failure returns a genuine selected-boundary-zero evader;
   classifier control of the theorem-4.9
   target is also equivalent to absence of a nonzero target evader;
   underdimensioned classifiers produce a genuine target evader; target
   classifier control reduces the remaining failure branch to a
   forced-edge-vanishing selected-boundary-zero evader with a concrete
   theorem-4.9 boundary-vertex Kirchhoff failure, plus a decreasing worklist
   edge; and the row-span/subset bridge says the exact remaining certificate is
   that every forced-vanishing boundary-zero chain lies in the theorem-4.9
   target.  The empty-worklist shell
   now proves that exact subset certificate and eliminates the concrete
   vertex-Kirchhoff evader branch there, while odd-interior supports refute
   that empty-worklist proof path.  The all-interior/empty-worklist success
   side now also certifies that no odd interior closed walk exists, so the
   subset/no-evader branch explicitly excludes the odd-worklist obstruction;
   conversely, the new odd-interior no-evader closure shows that a nonempty
   odd-worklist witness does not prevent synthesis once the concrete
   vertex-Kirchhoff evader is excluded.  The target-controlled executable
   theorem packages the uniform route as synthesis/target coverage or a
   genuine vertex-Kirchhoff evader plus a decreasing worklist edge.  The
   generator report bridge now lets the route consume
   `forcedCounterexampleLatents = all` directly in place of the raw empty
   missing-evidence premise, and feeds that report verdict into full
   boundary-zero no-evader control, empty-worklist subset success, or the
   target-controlled synthesis-or-evader fork.  That report-forced-all fork is
   now split into its no-evader and failed-synthesis halves: absence of the
   concrete vertex-Kirchhoff evader closes synthesis, while failed synthesis
   produces the evader and a decreasing remaining-worklist edge.  The same
   forced-all failure side now also exposes the canonical path-xor payload
   evader: a boundary-zero chain, non-forced remaining interior edge, strict
   worklist decrease, and nonzero canonical red/blue family pairing.  The new
   residual scheduler wrapper records the same failure inside an explicit
   processed-state trace: complete checker histogram, forced-bin detector,
   selected-boundary-zero evader, traced remaining interior-support edge,
   residual-worklist membership, and strict residual decrease after inserting
   that edge into the processed set.  The residual transition theorem then
   proves the selected edge is not controlled by the immutable classifier
   output and returns the one-edge emitted/control update needed to insert it
   into the processed scheduler state.  The terminal residual-scheduler theorem
   closes the matching success endpoint: residual exhaustion plus the
   processed-control invariant proves no selected-boundary-zero evader, theorem
   4.9 synthesis, and full selected-boundary-zero classifier control.  The
   failed-terminal scheduler theorem now connects those endpoints: failed
   synthesis under forced-all cannot be sitting at an exhausted residual
   worklist, and instead returns a selected-boundary-zero evader, the next
   residual edge, immutable-control failure for that edge, the one-edge
   emitted/control update, and strict residual decrease.  The
   immutable-scheduler obstruction theorem then rules out the tempting but
   invalid next move: that same edge cannot be marked processed under the
   original classifier output.  Continuing the scheduler requires adding the
   one-edge emitted/control update as real new control information, or keeping
   the evading boundary-zero chain as the obstruction.  The route-facing
   residual scheduler decision now packages the current finite state into the
   exact alternatives needed by Move 2: terminal no-evader/synthesis,
   already-closed synthesis, or a promoted one-edge obstruction with immutable
   processing ruled out and strict residual decrease.  The coverage-form
   scheduler theorem then restates the terminal branch as the semantic
   invariant that the processed set covers every original remaining control
   edge, while preserving the same already-closed synthesis branch and promoted
   obstruction branch.  The trace-control fork now makes this terminal
   algebraic surface exact: canonical remaining-interior trace-control is
   equivalent to absence of a selected-boundary-zero evader, and failure of
   trace-control returns a genuine evader plus a concrete trace edge where it
   is nonzero.  The failure side now also carries the canonical red/blue
   single-coordinate family obstruction: with the remaining-edge generator
   certificates, the same trace-local evader has a nonzero canonical family
   pairing on that edge.  The remaining-family map oracle now makes the finite
   F₂ detector surface explicit: every genuine selected-boundary-zero evader
   has nonzero image under the canonical remaining-edge family-pairing map,
   while emitted classifier zeros plus zero image under that map force the
   boundary-zero chain itself to be zero.  The exact split now proves that
   absence of a map-detected evader is equivalent to absence of a
   selected-boundary-zero evader.  Under the forced-all report, trace-control,
   or equivalently no map-detected evader, closes theorem-4.9 synthesis plus
   full selected-boundary-zero classifier control; otherwise Lean returns the
   map-detected evader as the obstruction.  The emitted-edge kernel bridge now
   connects the lab-facing rank certificate directly to that same oracle: the
   canonical red/blue pairing kernel on the immutable emitted forced-edge
   coordinates is trivial iff no selected-boundary-zero evader exists.  Under
   forced-all this emitted-kernel certificate closes synthesis/control; failure
   returns a concrete nonzero selected-boundary-zero kernel witness vanishing
   on every enumerated forced edge.  The emitted-kernel/map equivalence now
   collapses the two failure languages: a nontrivial emitted-kernel witness has
   nonzero remaining-family map image, and a map-detected evader lies in the
   emitted kernel.  The forced-all rank fork therefore returns either
   synthesis/control or one genuine boundary-zero evader carrying both the
   emitted-kernel and remaining-map certificates.  The failed-synthesis
   corollary removes the success side from that fork under
   `¬ Theorem49BoundaryRootSynthesis`: if synthesis fails, Lean directly
   returns the unified emitted-kernel/remaining-map evader.  The exact
   kernel/map oracle theorem now gives the corresponding iff: under forced-all,
   no unified emitted-kernel/remaining-map evader is equivalent to theorem-4.9
   synthesis plus full selected-boundary-zero classifier control.  The exact
   emitted-rank oracle then makes the lab-facing finite F2 certificate itself
   equivalent to route closure: under forced-all, the emitted-edge pairing
   kernel is trivial iff theorem-4.9 synthesis plus full selected-boundary-zero
   classifier control holds.  The report-closed emitted-rank wrapper now removes
   that raw handoff from the public route state: the executable CAP5 report
   either has a primitive portal/cycle checker gap, or its closed frontier
   supplies forced-all and the same emitted-rank iff applies.  The stronger
   report-closed trace wrapper now removes the same raw handoff from the
   canonical trace-control fork: the executable report returns a primitive
   checker gap, theorem-4.9 synthesis with full selected-boundary-zero control,
   or a genuine trace-local selected-boundary-zero evader with a concrete
   remaining trace edge and nonzero canonical remaining-family pairing.  The
   failure-only report trace theorem removes the success branch under
   `¬ Theorem49BoundaryRootSynthesis`, so a failed route now returns a
   primitive checker gap or that trace-local evader directly.  The
   failure-only report kernel/map theorem gives the same failed route in the
   lab-facing rank language: primitive checker gap or unified
   emitted-kernel/remaining-map evader.  The report-level kernel/map split and
   no-gap/no-evader closure corollary give the complementary positive
   direction: excluding both primitive checker gaps and the unified
   emitted-kernel/remaining-map evader closes theorem-4.9 synthesis plus full
   selected-boundary-zero classifier control.  The exact report-level
   kernel/map oracle strengthens this to an iff: after a closed primitive
   frontier, no unified evader is equivalent to synthesis/control, and the
   executable report returns either a primitive gap or that exact equivalence.
   The emitted-rank/no-unified-evader bridge now identifies the lab-facing
   finite kernel certificate with absence of that unified obstruction after the
   same closed primitive frontier.  The report-level emitted-rank trichotomy
   then packages the finite verdict as the actual executable branch:
   primitive checker gap, emitted-rank close with synthesis/control, or
   rank-failure unified evader.  The target/off-target oracle is now tied to
   that same rank certificate:
   `no_boundaryZeroEvader_iff_theorem49BoundaryTargetClassifierControl_and_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   decomposes full no-evader into theorem-4.9 target classifier control plus
   absence of the concrete off-target boundary-vertex Kirchhoff evader, and
   `emittedFinsetPairingKernel_eq_bot_iff_theorem49BoundaryTargetClassifierControl_and_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   proves the emitted-edge pairing kernel is trivial exactly when this
   decomposed target/off-target oracle is closed.  The failure side is now
   route-facing as well:
   `emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_emittedFinsetPairingKernel_eq_bot_of_theorem49BoundaryTargetClassifierControl`
   proves that once target classifier control is known, emitted-rank failure
   returns the genuine evader with emitted-kernel membership, nonzero
   remaining-map image, and a concrete theorem-4.9 boundary-vertex Kirchhoff
   failure.
   The target-controlled split is now also an exact local rank decision:
   `emittedFinsetPairingKernel_eq_bot_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl`
   proves that, after theorem-4.9 target control, emitted-rank triviality is
   equivalent to absence of that concrete off-target Kirchhoff evader, and
   `emittedFinsetPairingKernel_eq_bot_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl`
   packages the close-or-witness branch with emitted-kernel and nonzero
   canonical remaining-map certificates.  The target-control side condition is
   now removed from the failure interpretation:
   `theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_emittedFinsetPairingKernel_eq_bot`
   turns nontrivial emitted-rank failure into either a nonzero theorem-4.9
   target chain vanishing on every enumerated forced edge or the off-target
   kernel/map/vertex-failure evader, and
   `emittedFinsetPairingKernel_eq_bot_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   packages the local finite F2 verdict as close, target evader, or off-target
   evader.  The same target/off-target split is now report-level:
   `ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   packages the executable branch as primitive checker gap, emitted-rank close
   with synthesis/control, target evader, or off-target kernel/map/vertex
   evader, and
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_theorem49BoundaryRootSynthesis`
   removes the close branch under failed synthesis.  A closed-frontier
   corollary now states the no-evader side in exactly this
   target/off-target vocabulary:
   `emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_iff_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missingCheckerEvidence`
   proves that, once the primitive checker frontier is closed, emitted-rank
   close with synthesis/control is equivalent to absence of both target-side
   and off-target report evaders.  The rank-certificate corollary
   `emittedFinsetPairingKernel_eq_bot_iff_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missingCheckerEvidence`
   removes the bundled-success wording: under the same closed primitive
   frontier, the emitted F2 pairing-kernel certificate itself is equivalent to
   absence of both concrete report evaders, with synthesis/control recovered
   from that certificate.  The emitted-rank route-close corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_emittedFinsetPairingKernel_eq_bot`
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_emittedFinsetPairingKernel_eq_bot`
   now consume that finite rank certificate directly: the executable report
   has only primitive checker gap or synthesis/control left, and with the
   primitive frontier closed the certificate directly proves synthesis/control.
   The coverage-to-rank bridge
   `emittedFinsetPairingKernel_eq_bot_of_forcedEdgeCoverage`,
   `emittedFinsetPairingKernel_eq_bot_of_controlEdges_nonzeroCoverage_subset_emittedFinset`,
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_forcedEdgeCoverage`,
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_forcedEdgeCoverage`
   now connect the lab no-evader/coverage verdict to that rank certificate:
   exact forced-edge coverage, or a finite control set that meets every
   nonzero selected-boundary-zero chain and is already emitted by the
   classifier, proves the emitted red/blue pairing-kernel certificate consumed
   by the executable report route.
   The exact-shell empty-worklist specialization
   `emittedFinsetPairingKernel_eq_bot_of_remainingInteriorSupportEmpty`,
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_remainingInteriorSupportEmpty`,
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_remainingInteriorSupportEmpty`
   now proves the same emitted-rank certificate directly from the concrete
   CAP5 condition that the canonical interior-support worklist is empty.
   The report-level exact-worklist fork
   `remainingInteriorSupportEmpty_closes_or_notSynthesis_boundaryZeroEvader_and_nonempty_worklist_of_no_missingCheckerEvidence`
   makes the remaining Move-2 decision boundary explicit: with the primitive
   checker frontier closed, empty worklist closes synthesis/control, while
   failed synthesis forces a nonempty worklist and returns a genuine
   selected-boundary-zero evader plus a decreasing remaining-worklist edge.
   The executable-report exact-worklist fork
   `ofDecidableChecks_missingCheckerEvidence_or_remainingInteriorSupportEmpty_closes_or_notSynthesis_boundaryZeroEvader_and_nonempty_worklist`
   removes the raw closed-frontier handoff from that statement: the report now
   returns either a primitive checker gap or the same exact worklist fork.
   The executable-report residual scheduler fork
   `ofDecidableChecks_missingCheckerEvidence_or_residualSchedulerCoverageNoEvader_or_synthesis_or_immutableProcessedControlObstruction_of_processedControl`
   and its failure-only corollary
   `ofDecidableChecks_missingCheckerEvidence_or_residualSchedulerImmutableProcessedControlObstruction_of_notSynthesis_of_processedControl`
   now remove the raw forced-all handoff from the promoted scheduler as well:
   the report returns either a primitive checker gap or the terminal
   processed-coverage no-evader/synthesis branch, an already-closed synthesis
   branch, or a promoted residual-edge obstruction; under failed synthesis,
   only the primitive gap or the genuine residual selected-boundary-zero
   evader with immutable processed-control failure and strict residual decrease
   remains.
   The initial residual scheduler corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_initialResidualSchedulerNoEvader_or_synthesis_or_immutableProcessedControlObstruction`
   and
   `ofDecidableChecks_missingCheckerEvidence_or_initialResidualSchedulerImmutableProcessedControlObstruction_of_notSynthesis`
   remove the scheduler-side processed-state handoff altogether at the start:
   `processed = ∅` supplies processed-control automatically, so the executable
   report itself starts the promoted scheduler.  Failed synthesis now returns
   either the primitive gap or the first residual selected-boundary-zero evader
   with immutable one-edge processed-control failure, the one-edge promoted
   control update, and strict residual decrease.
   The initial residual closure layer
   `InitialResidualSchedulerImmutableProcessedControlObstruction`,
   `emittedFinsetKernelMapEvader_of_initialResidualSchedulerImmutableProcessedControlObstruction`,
   `initialResidualSchedulerImmutableProcessedControlObstruction_of_no_missingCheckerEvidence_of_notSynthesis`,
   `emittedFinsetKernelMapEvader_of_no_missingCheckerEvidence_of_notSynthesis_via_initialResidualScheduler`,
   `theorem49BoundaryRootSynthesis_of_no_missingCheckerEvidence_and_no_initialResidualSchedulerImmutableProcessedControlObstruction`,
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_initialResidualRemainingControlEdgesEmpty`,
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_initialResidualRemainingControlEdgesEmpty`
   turns that fork into a direct route decision: no primitive checker gap plus
   an initially empty residual scheduler proves theorem-4.9 synthesis with full
   selected-boundary-zero classifier control, while no primitive checker gap
   plus failed synthesis forces the named first residual evader/immutable
   processing obstruction.  That obstruction now promotes to the same unified
   emitted-kernel/remaining-map evader used by the finite F2 rank oracle, so
   the nonempty initial scheduler branch is no longer a separate branch from
   the emitted-rank/map fork.  The remaining Move-2 burden is therefore to
   prove exact CAP5 shell data empties that initial residual scheduler/emitted-
   rank certificate, or to accept the named first residual obstruction as the
   unified finite F2 evader.
   The focus-shell threshold bridge
   `sharedInteriorPair_CAP5_initialResidualRemainingControlEdges_eq_empty_iff_emittedInterior_card_ge_two`
   and
   `wheelWithInnerTriangle_CAP5_initialResidualRemainingControlEdges_eq_empty_iff_emittedInterior_card_ge_three`
   resolves that question for the two current lab focus shells: the shared
   interior-pair shell has an empty initial residual worklist exactly when both
   shared controls are emitted, and the inner-triangle wheel shell has an empty
   initial residual worklist exactly when all three spoke controls are emitted.
   The paired synthesis and contrapositive corollaries close the
   boundary-trimmed unique-certificate route from those empty worklists, while
   failed synthesis forces a genuinely nonempty initial residual worklist.  The
   remaining question is now the uniform exact CAP5 shell-data lift of these
   finite focus thresholds, not another isolated repair-packet refutation.
   The uniform scheduler bridge
   `initialResidualRemainingControlEdges_eq_empty_iff_controlEdges_subset_emittedFinset`
   now identifies the initial residual condition for any finite control set
   with the concrete fixed point that all chosen controls are already emitted.
   The report-facing corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_initialResidualInteriorSupport_subset_emittedFinset`
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_initialResidualInteriorSupport_subset_emittedFinset`
   therefore state the exact remaining shell-data handoff directly: if the
   canonical `interiorEdgeSupport` is contained in the emitted classifier
   output, then the remaining-edge certificate obligations are vacuous, the
   initial residual scheduler is empty, and the report route closes to
   synthesis/full selected-boundary-zero control except for primitive checker
   gaps.  The Move-2 lift target is now this emitted-interior-support subset,
   uniformly.
   The failure-side corollaries
   `exists_initialResidualInteriorSupportEdge_not_emitted_of_no_missingCheckerEvidence_of_notSynthesis`
   and
   `initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader_of_no_missingCheckerEvidence_of_notSynthesis`
   make the opposite side equally concrete: with the primitive checker frontier
   closed, failed theorem-4.9 synthesis forces a residual canonical
   interior-support edge outside the emitted classifier output, and returns it
   together with the unified emitted-kernel/remaining-map F2 evader.  So the
   exact shell-data handoff is now a true close-or-witness fork: prove emitted
   canonical interior-support subset, or accept the missing interior coordinate
   plus the unified finite F2 obstruction.
   The report-level wrappers
   `ofDecidableChecks_missingCheckerEvidence_or_initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader_of_notSynthesis`
   and
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_or_initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader`
   remove the remaining closed-frontier handoff from this paired obstruction:
   the executable report itself now returns primitive checker gap, synthesis,
   or the paired missing-interior-coordinate plus unified finite F2 evader.
   The packaged theorem
   `budgetMetNoEvader_boundaryZeroControl_oracle` is the assembled oracle
   surface over those case lemmas: with the primitive checker gap absent, no
   unified emitted-kernel/remaining-map evader is equivalent to theorem-4.9
   synthesis plus full selected-boundary-zero classifier control; if that
   closed result fails, the theorem returns the same precise unified evader.
   The remaining exact-shell question is therefore the no-evader certificate
   itself, not another scheduler/rank/report split.
   The direct no-evader route corollaries
   `ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   and
   `theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
   now expose the decision step in the requested form: excluding both concrete
   evader branches leaves only primitive checker gap or synthesis/control, and
   with the primitive frontier closed it directly proves synthesis/control.
   The higher edge-cap/coloring-cap
   projected-generator lab run now records this distinction explicitly: among
   65 reports there are 53 found coordinate-probe reports, 12 no-Tait-coloring
   reports, and 0 missing probe reports.
   These projected probes are supporting realization evidence, not the
   emitted-kernel rank certificate needed by the Lean oracle.  The
   pure no-target theorem underneath those refinements says failed synthesis
   already produces a genuine selected-boundary-zero evader for the enumerated
   forced edges.  The remaining crux is whether exact shell/CAP5 data reaches
   canonical remaining-interior trace-control/emitted-kernel triviality
   uniformly, or whether this
   genuine boundary-zero/vertex-Kirchhoff/path-xor trace-local evader with
   canonical red/blue pairing/map/kernel signal is the decided obstruction.

The historical trichotomy below remains useful background:

1. **Repair**: find same-embedding geometric hypotheses that (a) are
   natural for the manuscript's induction, (b) are *not* satisfied by the
   wheel/shared-interior-pair benchmarks, and (c) construct one of the four
   oracle inputs.  Everything at or below the exact shells is proven
   insufficient; candidate hypotheses must be checked against the benchmarks
   *first* (5-minute check) before building route surface (multi-day work).
2. **Non-geometric repair**: derive the new shell-wise detector obligation
   `AlgebraicNeighborhoodCancellationOracle` uniformly from the exact shell,
   or at least derive the stronger whole-closure
   `AlgebraicCancellationOracle`.  This is the formalized version of the
   memo's algebraic cancellation certificate: it is strong enough to imply
   `Theorem49ShellClaim`, it now matches the finite lab's explicit
   certificates at the right granularity, and the direct kernel-check shell
   form `AlgebraicNeighborhoodPairingKernelOracle` now packages those
   certificates before any upgrade to the detector surface.  The current wheel/shared
   benchmark families no longer refute it.
3. **Refute**: find a shell-bearing embedding where
   `Theorem49BoundaryRootSynthesis` itself fails.  The cheapest current
   candidates have now been checked computationally: the finite lab in
`scripts/4cp_lab/exp01_wheel_endpoint.py` finds the synthesis **true** on
the shell-bearing wheel and shared-interior-pair benchmarks, both for the
explicit benchmark colorings and for every Tait coloring the lab enumerates
there.  The companion detector experiment
`scripts/4cp_lab/exp02_kempe_detector.py` shows the remaining explicit
annihilator checks are tiny: radius `0` for the wheel and radius `1` for
the shared-interior-pair case.  Both exact certificates are now
kernel-checked directly in Lean: the wheel singleton radius-0 certificate, and
the shared radius-1 certificate, which even compresses there to a two-color
witness subfamily.  So the direct-counterexample lane survives only through a
different shell-bearing benchmark, or through a future Lean-computable F₂
elimination/search layer that scales beyond the wheel and shared-interior-pair
benchmarks already discharged in Lean.

## File organization

- **`Goal.lean`, `Shells.lean`, `Frontier.lean`** — the live surface (above).
- **Core theory** (reusable, Mathlib-style): `ColorAlgebra`, `FaceIncidence`,
  `PlanarFaceIncidence`, `Orthogonality`, `BoundaryVanishing`,
  `Theorem49LinearAlgebra`, the `PlanarBoundary*` family (embeddings,
  sources, annulus construction, peeling), `Theorem49KempeGeneratorSpan`,
  `Theorem49SpanningGap`.
- **Route files** (`Theorem49*Route`, `Theorem49Synthesis`,
  `Theorem49PositiveGeometricSource*`, …): the positive lane.  Heavily
  duplicated between closed-walk and successor-cycle presentations; new
  statements should go through `Shells.lean` bundles instead of extending
  these.
- **Load-bearing benchmark/obstruction files kept in the main tree** (they
  are imported by route files): `Theorem49AtMostOneNonemptyCarrierImpossibility`,
  `Theorem49ForcingInteriorEdgeObstruction`,
  `Theorem49InteriorVerticesEndpointObstruction`,
  `Theorem49PositiveGeometricSourceImpossibility`, and the four
  `Theorem49PlanarBoundaryAnnulus*Regression` keepers (these define the
  shared-interior-pair benchmark).
- **`Legacy/`**: the historical obstruction ledger plus the concrete explicit
  endpoint regression certificates.  Fully verified.  Its maximal results are
  re-exported by `Frontier.lean`; weaker shells refuted there are subsumed a
  fortiori.  Do not add new shell-obstruction wrappers there; do not build on
  it except through `Frontier`.

## Conventions going forward

- State new theorems over the `Shells.lean` bundles.  If a hypothesis package
  recurs three times, bundle it.
- No new 100+-character theorem names; the shell vocabulary exists so names
  can be short.
- A failed universal converse is one application of
  `not_forall_target_of_exists_shell_witness` to an explicit witness — do not
  write bespoke 60-line converse theorems.
- New benchmark counterexamples get their own file with the benchmark's facts
  proved once; obstruction theorems combine benchmark facts with shell
  definitions.
- Keep the tree without proof placeholders or extra trusted constants.

## Build targets

- Live surface: `lake build Mettapedia.GraphTheory.FourColor.Goal`
  (pulls in `Shells`, `Frontier`, and the route files they wrap).
- Everything incl. ledger: `lake build Mettapedia.GraphTheory.FourColorRegression`.
- Dependency audit: `python3 ../../../scripts/lean_deps.py <path>`.
