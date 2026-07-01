# FourColor Proof State

Last updated: 2026-07-01 on `fourcolor/cont-20260626`.

This file tracks the active route forks.  The Four Color Theorem is not
claimed here.

## Current Pillar-C Reset

The Ben-route status is now Pillar C, not the older CAP5/F2/six-cut route.
`GoertzelLemma814.lean` models the canonical three-cell gadget from Lemma 8.14:
internal tree `F1-F0-F2-F4-F5` with leaf `F3`, boundary stubs `B0..B7`,
inputs `B0..B3`, the finite proper-coloring state space, input-disjoint
Kempe-component switches, an indexed path certificate for `LKR_in`, and the
tree-transparency finite check for Lemma 8.15.  The lab script
`lemma814_lkr_in_lab.py` confirms the finite audit numerically with numpy and
Sympy: tau has 192 proper colorings, fixed-input fibers of size 4 or 8 when
nonempty, all fixed-input Kempe graphs connected, and the `sigmaL`/`sigmaR`
piece checks and tree transparency pass.

Lean status: Lemma 8.14 is closed by the finite certificate theorem
`lemma814_tau_lkrIn_audit`, which proves
`lemma814_tau_lkrIn_finiteCheck = true`.  The supporting row-split theorems
prove the 192-state space audit, indexed path certificate, and fixed-input
representative coherence.  The mirror invariance theorem is
`lemma814_mirror_lkrIn_same_check`.  Lemma 8.15 transparency is now closed by
the finite certificate theorem `lemma815_tau_tree_transparency_audit`, proving
`lemma815_tau_tree_transparency_finiteCheck = true`.  The audit is split into
three 64-state chunks
`tauTreeTransparencyRange_0_64_ok`,
`tauTreeTransparencyRange_64_64_ok`, and
`tauTreeTransparencyRange_128_64_ok`, covering all 192 canonical gadget
colorings and every two-color component.  The 8.15 theorem and its chunk
theorems are axiom-clean; the 8.14 theorem and mirror check remain at the
standard finite-audit footprint `[propext]`.

Lemma 8.18/Corollary 8.19 are not closed by the manuscript's Step-1
preparation argument.  The theorem
`lemma818_pointwise_lift_preparation_obstruction` is a finite, axiom-clean
`τ -> τ` obstruction to the pointwise downstream-pairing claim used in Lemma
8.18: with an upstream state `6` and downstream state `176`, the upstream
`{r,b}` component seeded at `B5` is input-disjoint and exits the interface at
`B5,B7`, but the downstream fixed-input fiber has no extension pairing the
corresponding input stubs `B1,B3` in the `{r,b}` subgraph.  This does not prove
that the two-gadget composite fails `LKR_in`; it proves that Lemma 8.18 as
written needs a stronger or different composition invariant than Lemmas 8.14
and 8.15 supply.

Gate-1 salvage audit is now favorable, but not yet a formal seal.  The lab
`lemma818_composite_lkr_gate1_lab.py` directly constructs composite fixed-input
Kempe graphs for every length-2 and length-3 word over `τ` and mirror-`τ`,
with mirror modeled as the same incidence tree and reversed ordered
input/output stubs.  The fast connectivity run reports all 12 composite words
connected in every nonempty fixed-input fiber.  The corresponding Lean model
in `GoertzelLemma814.lean` now builds and matches the lab's composite state
counts, but raw in-Lean closure search is too slow to serve as the final proof
certificate.  A generated parent-certificate prototype for the first `τ²`
word also timed out as one monolithic theorem at 2M heartbeats, even though the
same checker evaluated successfully.  The next formal step is therefore a
per-fixed-input-fiber generated certificate, or a smaller frontier automaton
certificate, not another literal repair of Ben's pointwise-preparation proof.

The chain certificate target has now been decomposed at the Lean API level.
`GoertzelLemma814.lean` defines `ChainFiberParentRow`,
`ChainFiberCertificate`, `chainFiberIndicesFrom`,
`chainFiberParentCertificateAudit`, and
`chainAllFiberParentCertificateAudit`.  A certificate row names a concrete
source state index, a parent index in the same fixed-input fiber, and the
specific input-disjoint chain Kempe move witnessing the parent edge; bounded
parent iteration must reach the canonical root of that exact fiber.  The smoke
theorem `tauSingleNormalFiber0Certificate_ok` checks the first single-`τ`
fixed-input fiber `{0,1,2,3,48,49,50,51}` against the real chain-state model
and real chain Kempe moves.  This is the intended small target for generated
per-fiber path certificates, not yet a proof of all composite `LKR_in`.
The base single-`τ` case now also has a generated all-key audit:
`tauSingleNormalAllFiberCertificateAudit_ok` checks all 81 fixed-input color
assignments, including empty fibers, in nine 9-key chunks.  The 36 nonempty
fiber certificates are generated from the Lemma 8.14 path rows and rechecked
against the serial-chain model rather than the original one-gadget checker.
The mirrored base orientation is covered as well:
`tauSingleMirrorAllFiberCertificateAudit_ok` checks the same generated local
parent rows under the mirror input order.  Thus both one-gadget base
orientations have per-fiber chain certificates; the composite representative
certificates and the all-chain induction consequence remain open.
`GoertzelLemma818CompositeCertificate.lean` now checks the generated full
`τ,τ` direct parent/path table: `ttAllFiberCertificateAudit_ok` covers all 81
fixed-input keys, with 36 nonempty fibers, 960 generated chain states, and
maximum parent depth 4.  The row checks are split down to individual direct
Kempe moves and parent-iteration facts, avoiding the failed monolithic closure
search.  This is the first complete two-gadget generated certificate table,
not the all-chain `LKR_in` theorem and not the 8.18/8.19 DFA lift.
`GoertzelLemma818TauMirrorCertificate.lean` adds the next mixed-orientation
length-2 base table: `tmAllFiberCertificateAudit_ok` checks all 81 fixed-input
keys for the `τ,mirror-τ` chain, with 36 nonempty fibers, 1152 generated chain
states, and maximum parent depth 4.  The remaining length-2 generated base
tables are `mirror-τ,τ` and `mirror-τ,mirror-τ`; those still do not replace
the frontier/DFA lift.
`GoertzelLemma818MirrorTauCertificate.lean` adds the third length-2 base
table: `mtAllFiberCertificateAudit_ok` checks all 81 fixed-input keys for the
`mirror-τ,τ` chain, with 36 nonempty fibers, 1152 generated chain states, and
maximum parent depth 4.  The only remaining length-2 generated base table is
`mirror-τ,mirror-τ`; the all-chain frontier/DFA consequence is still separate.
`GoertzelLemma818MirrorMirrorCertificate.lean` completes the length-2 base
layer: `mmAllFiberCertificateAudit_ok` checks all 81 fixed-input keys for the
`mirror-τ,mirror-τ` chain, with 36 nonempty fibers, 960 generated chain states,
and maximum parent depth 4.  All four length-2 orientation words now have
generated direct parent/path certificate tables; the all-chain frontier/DFA
consequence is still separate.
`GoertzelLemma818LengthTwoBase.lean` packages those four tables as a finite
base interface: `lengthTwoCertificateAudit_ok` proves the generated
certificate audit for any constructor of the four-word length-2 orientation
type, and `lengthTwoAllCertificateAudit_ok` checks the aggregate list.  This
is the base hook for the future DFA induction, not the induction consequence.

Gate-2 frontier-mode checkpoint, 2026-06-30: the lab evidence has stabilized
at a finite profile-mode surface, but it is not yet a Lean composition
certificate.  The archived automaton runs record 936 frontier summaries after
three saturation rounds; raw summary fibers are too coarse, but the
atom-refined fixed-input Kempe graphs are connected for every word of length
1 through 4 and the atom transition is congruent through the full length-4
surface.  The compact state key
`profile mode + frontier summary + local atom index` is transition-congruent
on the observed surface (`888192` transition cases, `56064` transition keys,
0 failures), and the profile-mode DFA closes at 20 modes with 40 transitions
in the lab (`36` observed, `4` inferred by singleton-summary transition).
The key archive reports are
`fourcolor-lemma818-frontier-atom-stabilization-20260630.json` (SHA256
`0ac0783238bf84fdaa2da6258f6104eedfa67018f70c4388dead11f2140e3d88`),
`fourcolor-lemma818-frontier-mode-atom-transition-len4-20260630.json` (SHA256
`4d8ae453b06643fd6fdc9931b6503062f7b3861217fb310b88ede904e70f5d9a`), and
`fourcolor-lemma818-frontier-profile-mode-dfa-closure-20260630.json` (SHA256
`2b1f24eb3d3939020bca6f5423b7aa7d57ddac7967f513029a76beda414d659e`).

The honest frontier is connectivity, not mode finiteness.  Targeted length-5
profile checks show the alternating words collapse back to existing singleton
modes, and the remaining representatives either collapse to existing modes or
land in two new singleton profile modes; the length-5 profile reports are
`fourcolor-lemma818-frontier-alternating-len5-light-flag-20260630.json`
(SHA256
`a45d47b19815d1d0d7e6fbcf75e7fecd85dc6d936a94c46e9162d1dfc06739f1`) and
`fourcolor-lemma818-frontier-remaining-len5-light-profiles-20260630.json`
(SHA256
`a12c8163a06dd57fc15b91811edd6ef6c84840c2f25fc0acc4529244c963913a`).
The two new singleton mode representatives now also have independent
per-fixed-input quotient-connectivity checks: `TTTTM` and `MTTTT` each have
396288 states, 336 summaries, 336 singleton atoms, 36 nonempty fixed-input
fibers, connected quotient graph in every fixed-input fiber, and 0 failures.
The reports are
`fourcolor-lemma818-frontier-new-singleton-TTTTM-quotient-20260630.json`
(SHA256
`c2e526666d3076319468d98cbbc14237d38fe72bad6851cc56f01f67492f3da1`) and
`fourcolor-lemma818-frontier-new-singleton-MTTTT-quotient-20260630.json`
(SHA256
`e4d650337c6976215ead2c6680fc2d8263e75ad454f88ec86f260eb16dcefa19`).
Archived representative evidence coverage is now formalized in Lean at the
metadata level.  Thus the finite automaton is lab-closed at the profile-mode
level with source-consistent archived connectivity witness rows for all 20
modes, including the newly discovered singleton modes, while the all-chain
`LKR_in` certificate remains open until real chain/profile certificates and
per-fixed-input path certificates discharge the semantic connectivity
consequence by small generated lemmas or a finite transition certificate.

Lean now contains the lab-facing profile-mode DFA table in
`GoertzelLemma818FrontierMode.lean`: 20 modes, two orientations, the 40-entry
total transition function, mode hashes, and representative word metadata.  The
table check theorem `tableClosedCheck_ok` proves by `rfl` that the table has
20 modes, 2 orientations, 40 transitions, and every one-step transition lands
inside the finite mode list.  The theorem `profileHashLookupCheck_ok` checks
that the 20 archived profile hashes round-trip through the hash-to-mode lookup.
The same module defines `wordMode`, the abstract fold of a nonempty orientation
word through the DFA, and proves `wordMode_inTable`: any mode returned by that
fold is one of the 20 table modes.  It also encodes the archived representative
words for every mode and proves `representativeWordsSoundCheck_ok`,
`representativeCoverageCheck_ok`, and `modeWitnessWord_sound`: every stored
representative word folds to the listed mode, and every mode has a checked
canonical representative.  The theorem `knownProfileWordHashCheck_ok` checks
the 42 archived known word/profile-hash pairs against both `wordMode` and
`modeOfProfileHash`.  The theorem `knownTransitionHashCheck_ok` checks the 40
archived source-hash/orientation/target-hash transition entries against the
hash lookup and the Lean `step` function.  `#print axioms` reports no axioms
for these table-layer theorems.  The structural closure skeleton is also now
checked: `wordMode_induction` and `wordMode_bool_induction` prove, axiom-free,
that any Prop-valued or Bool-valued invariant holding at the two initial modes
and preserved by `step` holds for the mode returned by any nonempty orientation
word.  The archived connectivity-witness layer is checked by
`archivedConnectivityCoverageCheck_ok`: the table contains the 30
length-1-through-4 atom-connectivity rows, the two length-5 singleton quotient
rows, and a source-consistent connectivity row for each of the 20 modes.
`wordMode_hasArchivedConnectivityEvidence` lifts that coverage through the DFA
to every nonempty orientation word.  This is not yet the proof that every
reachable chain profile is represented by the table's canonical representatives
or that the table entails all-chain `LKR_in`; it is evidence coverage plus the
induction hook that a generated connectivity certificate must instantiate.
Current checkpoint status: stop the open-ended sweeps.  The profile-mode
automaton is finite and Lean table-closed, and every one of the 20 modes has a
source-consistent archived connectivity witness row.  No additional mode is
currently known to lack archived connectivity evidence.  What remains
unverified is the semantic bridge from those archived quotient/atom rows to
actual chain-state fixed-input path certificates and then through
`wordMode_induction` to all-chain `LKR_in`.

Green checkpoint, 2026-07-01: this is the intended stopping point for the
Gate-2 exploration pass.  The branch records the finite 20-mode profile DFA,
its table closure, the 42 archived representative word/profile-hash checks,
the 40 transition-hash checks, the induction hook, the 30 direct
length-1-through-4 atom-connectivity rows, and the two length-5 singleton
quotient-connectivity rows.  The automaton is finite and closed at the
profile-mode metadata level.  All 20 modes have archived per-fixed-input
connectivity evidence; no mode is currently flagged as unverified at that
metadata layer.  The remaining frontier is to formalize the semantic
certificate connecting those rows to real per-fixed-input Kempe path
certificates and then derive all-chain `LKR_in`.  This checkpoint does not
claim the Four Color Theorem.
`GoertzelLemma818FrontierBaseBridge.lean` now adds the first explicit bridge
from the generated length-2 chain certificates to the frontier-mode surface:
each constructor of `LengthTwoOrientWord` is converted to the frontier word,
checked against the expected DFA mode (`TT -> mode10`, `TM -> mode18`,
`MT -> mode11`, `MM -> mode04`), and paired with both the generated
length-2 fiber certificate audit and the archived connectivity-evidence row.
The aggregate theorem `lengthTwoFrontierBaseCoverageAudit_ok` checks all four
base words.  This is still a base bridge only; the representative-word
semantic certificate and all-chain induction consequence remain open.
The same bridge now names the six frontier modes already backed by real
chain-level per-fixed-input certificates: `T -> mode07`, `M -> mode16`,
`TT -> mode10`, `TM -> mode18`, `MT -> mode11`, and `MM -> mode04`.
`baseCertifiedFrontierCoverageAudit_ok` checks those six base-certified words
against the real single/length-2 chain certificate audits, frontier word-mode
folding, and archived connectivity evidence.  The other 14 modes still need
representative-word semantic certificates before the DFA induction can imply
all-chain `LKR_in`.
`GoertzelLemma818RepresentativeTargets.lean` now names those 14 remaining
semantic targets explicitly.  `representativeTargetCoverageAudit_ok` checks
that the chosen words fold to modes
`mode00/mode01/mode02/mode03/mode05/mode06/mode08/mode09/mode12/mode13/mode14/mode15/mode17/mode19`,
that each target mode already has archived connectivity evidence, and that
none is among the six base-certified modes.  `plannedSemanticModeCoverageAudit_ok`
checks that the six certified base modes plus these 14 targets cover all 20
frontier modes.  This is still only the finite target surface; the real
per-fixed-input chain/path certificates for those target words remain open.

Gate-2 stop checkpoint, 2026-07-01: the open-ended connectivity sweeps should
remain stopped.  There is no known unverified profile mode at the archived
connectivity-evidence layer: all 20 modes have a source-consistent witness row,
the profile-mode transition table is finite and closed, and the six modes
`mode07/mode16/mode10/mode18/mode11/mode04` are already backed by real
single/length-2 chain certificate audits.  The unverified layer is semantic,
not exploratory: the remaining 14 representative modes still need real
per-fixed-input chain/path certificates, or an equivalent finite transition
certificate, before the DFA induction can imply all-chain `LKR_in`.  A
generated `TTT` light-fiber prototype confirmed that direct representative
certificates must be decomposed further: it split the `TTT` state space into
45 empty fixed-input fibers, 24 size-16 light fibers, and 12 size-512 large
fibers, but the Lean row checks still expanded too much for the default kernel
recursion budget.  That prototype is archived as failed WIP, not imported and
not part of the proof surface.  The next pass should formalize smaller
component certificates or the finite transition automaton; it should not extend
word lengths or raise kernel limits.

Second stop checkpoint, 2026-07-01: a later generated continuation for the
remaining blocks of the first `TTT` large fiber was not imported and is not
counted as proof evidence.  The checked Lean surface remains the same
semantic frontier: six base modes certified by real chain audits, `TTT`/`mode09`
light fibers certified, and rows 0 through 127 of the first `[r,r,b,b]`
size-512 fiber certified.  The finite automaton itself is still closed at the
metadata layer: 20 modes, 40 transitions, archived per-fixed-input
connectivity evidence for all modes, and no profile mode currently flagged as
missing connectivity evidence.  The open layer is semantic certification for
the rest of `mode09` and the other thirteen non-base representative modes, or
an equivalent finite transition certificate that makes those per-fixed-input
paths unnecessary as separate large tables.

Fresh-pass block2 checkpoint, 2026-07-01: the next 64 rows of that same
`[r,r,b,b]` large fiber are now restored as four 16-row chunk modules and
checked by explicit parent-path facts, not by reducing the recursive parent
iterator over the large fiber.  The checked semantic surface now covers rows
0 through 191 of this size-512 fiber.  Rows 192 through 511, the other eleven
large `TTT` fibers, and the other thirteen non-base representative modes remain
open.

Fresh-pass block3 checkpoint, 2026-07-01: rows 192 through 255 of the same
`[r,r,b,b]` large fiber are now checked as four more 16-row chunk modules.
They use the same explicit component rows, generated parent-map agreement, and
explicit bounded parent paths to root `2176`.  The checked semantic surface now
covers rows 0 through 255 of this size-512 fiber.  Rows 256 through 511, the
other eleven large `TTT` fibers, and the other thirteen non-base representative
modes remain open.

Fresh-pass block4 checkpoint, 2026-07-01: rows 256 through 319 of the same
`[r,r,b,b]` large fiber are now checked as four more 16-row chunk modules.
They use the same explicit component rows, generated parent-map agreement, and
explicit bounded parent paths to root `2176`.  The checked semantic surface now
covers rows 0 through 319 of this size-512 fiber.  Rows 320 through 511, the
other eleven large `TTT` fibers, and the other thirteen non-base representative
modes remain open.

Fresh-pass block5 checkpoint, 2026-07-01: rows 320 through 383 of the same
`[r,r,b,b]` large fiber are now checked as four more 16-row chunk modules.
The generated parent-map data was mechanically refactored into 64-entry
low/high offset blocks so high-side parent lookups normalize at default kernel
limits.  The block5 chunks still check explicit component rows, generated
parent-map agreement, and explicit bounded parent paths to root `2176`.  The
checked semantic surface now covers rows 0 through 383 of this size-512 fiber.
Rows 384 through 511, the other eleven large `TTT` fibers, and the other
thirteen non-base representative modes remain open.

Fresh-pass block6 checkpoint, 2026-07-01: rows 384 through 447 of the same
`[r,r,b,b]` large fiber are now checked as four more 16-row chunk modules.
The block6 chunks keep the same explicit component-row, generated parent-map,
and explicit bounded parent-path shape under default kernel limits.  The checked
semantic surface now covers rows 0 through 447 of this size-512 fiber.  Rows
448 through 511, the other eleven large `TTT` fibers, and the other thirteen
non-base representative modes remain open.

Fresh-pass block7 checkpoint, 2026-07-01: rows 448 through 511 of the same
`[r,r,b,b]` large fiber are now checked as four more 16-row chunk modules.
This completes the first size-512 `TTT`/`mode09` large fiber by the explicit
component-row, generated parent-map, and bounded parent-path certificate shape.
The other eleven large `TTT` fibers and the other thirteen non-base
representative modes remain open.

`GoertzelLemma818SemanticBridge.lean` now records the finite semantic handoff
for that next pass.  It maps each of the 20 profile modes to exactly one
planned semantic witness: one of the six base-certified chain words, or one of
the fourteen representative targets.  The theorem
`semanticWitnessCoverageAudit_ok` checks the witness map, representative
word-mode agreement, and frontier-word-to-chain-word agreement.  The theorem
`semanticPlanStepClosureAudit_ok` checks that this witness coverage is closed
under both DFA transitions.  The theorem
`wordMode_hasSemanticModeAudit_of_targets` is the small consequence hook: once
the fourteen target audits are supplied, every nonempty orientation word folds
to a mode with a planned semantic audit.  This is still not the all-chain
`LKR_in` theorem; it makes the remaining finite obligations explicit and keeps
the final semantic bridge separate from metadata coverage.

`GoertzelLemma818ComponentCertificate.lean` now provides the next certificate
shape for those obligations.  Instead of reducing `chainComponent`, a row
supplies the switched two-color component explicitly.  The checker verifies
that the component is made of representative chain edges in the chosen color
pair, contains the seed, is connected from the seed, is closed under adjacent
pair-colored chain edges, avoids the fixed input, and switches to the claimed
parent state.  The single-`τ` fixed-input fiber-0 smoke is rechecked in this
style: seven explicit component-switch row theorems plus a parent-depth theorem
cover the same non-root moves as the existing `tauSingleNormalFiber0Certificate`.
This is the intended small-row proof shape for the fourteen remaining
representative targets; those target certificates are still open.
`GoertzelLemma818TripleTauComponentSmoke.lean` applies that proof shape to the
first non-base representative slice: the `TTT` word
(`RepresentativeSemanticTarget.ttt`, `mode09`) and fixed-input key
`[r,r,b,r]`.  The theorem `tttFiber3ComponentCertificateAudit_ok` checks the
16-state fiber with explicit two-color component rows, source coverage,
parent-depth convergence to root `3808`, and the target/mode bookkeeping.  It
is a real chain-state component certificate slice for a non-base representative
mode, but it is not the full `TTT` target audit: the other `TTT` fibers,
including the 12 large size-512 fibers, and the other thirteen target modes
remain open.
`GoertzelLemma818TripleTauLightComponentCertificate.lean` now scales that row
shape across the light part of the same `TTT`/`mode09` representative target.
The theorem `tttLightComponentCertificateAudit_ok` checks the target/mode
bookkeeping, the 69 light fixed-input fibers, the 45 empty fibers, the 24
nonempty size-16 fibers, and all 384 light chain states by explicit
component-switch rows and parent-depth convergence.  This replaces the archived
failed direct-row prototype for the light slice: Lean no longer expands full
`chainComponent` for these rows.  It is still not the full `TTT` target audit,
because the 12 size-512 `TTT` fibers remain open, and it is not the all-chain
`LKR_in` consequence.
`GoertzelLemma818TripleTauLargeFiber4Data.lean` records the finite parent map
for this first large fiber.  The map is now split into eight 64-entry offset
matchers under the same public `tttLargeFiber4ParentOf` interface, preserving
the finite table while keeping high-side lookup certificates within default
kernel recursion limits.
`GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate.lean` starts
the large-fiber decomposition at the same granularity.  The checked fiber is the
first size-512 `TTT` fiber, fixed-input key `[r,r,b,b]`, with root `2176` and
BFS parent depth 6.  The theorem
`tttLargeFiber4Block0ComponentCertificateAudit_ok` checks the first 64 source
rows of that fiber by explicit component-switch rows, verifies that each row's
parent agrees with the generated parent map, and verifies convergence to the
root under that parent map.  This is a large-fiber block certificate, not the
full size-512 fiber audit: the other 448 rows of this fiber and the other
eleven size-512 `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate.lean` extends
the same first large fiber by another 64 rows, split into four 16-row chunk
modules.  The theorem `tttLargeFiber4Block1ComponentCertificateAudit_ok`
checks rows 64 through 127 by explicit component-switch rows, generated
parent-map agreement, and parent-depth convergence from local 16-source lists.
Thus the first 128 rows of the `[r,r,b,b]` size-512 fiber are now checked; the
remaining 384 rows of this fiber and the other eleven size-512 `TTT` fibers
remain open.
`GoertzelLemma818TripleTauLargeFiber4Block2ComponentCertificate.lean` extends
the same fiber by a third 64-row block, again split into four 16-row chunk
modules.  The theorem `tttLargeFiber4Block2ComponentCertificateAudit_ok`
checks rows 128 through 191 by explicit component-switch rows, generated
parent-map agreement, and explicit bounded parent paths to root `2176`.
Thus rows 0 through 191 of the `[r,r,b,b]` size-512 fiber are now checked; the
remaining 320 rows of this fiber and the other eleven size-512 `TTT` fibers
remain open.
`GoertzelLemma818TripleTauLargeFiber4Block3ComponentCertificate.lean` extends
the same fiber by a fourth 64-row block, again split into four 16-row chunk
modules.  The theorem `tttLargeFiber4Block3ComponentCertificateAudit_ok`
checks rows 192 through 255 by explicit component-switch rows, generated
parent-map agreement, and explicit bounded parent paths to root `2176`.
Thus rows 0 through 255 of the `[r,r,b,b]` size-512 fiber are now checked; the
remaining 256 rows of this fiber and the other eleven size-512 `TTT` fibers
remain open.
`GoertzelLemma818TripleTauLargeFiber4Block4ComponentCertificate.lean` extends
the same fiber by a fifth 64-row block, split into four 16-row chunk modules.
The theorem `tttLargeFiber4Block4ComponentCertificateAudit_ok` checks rows
256 through 319 by explicit component-switch rows, generated parent-map
agreement, and explicit bounded parent paths to root `2176`.  Thus rows 0
through 319 of the `[r,r,b,b]` size-512 fiber are now checked; the remaining
192 rows of this fiber and the other eleven size-512 `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber4Block5ComponentCertificate.lean` extends
the same fiber by a sixth 64-row block, split into four 16-row chunk modules.
The theorem `tttLargeFiber4Block5ComponentCertificateAudit_ok` checks rows
320 through 383 by explicit component-switch rows, generated parent-map
agreement, and explicit bounded parent paths to root `2176`.  Thus rows 0
through 383 of the `[r,r,b,b]` size-512 fiber are now checked; the remaining
128 rows of this fiber and the other eleven size-512 `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber4Block6ComponentCertificate.lean` extends
the same fiber by a seventh 64-row block, split into four 16-row chunk modules.
The theorem `tttLargeFiber4Block6ComponentCertificateAudit_ok` checks rows
384 through 447 by explicit component-switch rows, generated parent-map
agreement, and explicit bounded parent paths to root `2176`.  Thus rows 0
through 447 of the `[r,r,b,b]` size-512 fiber are now checked; the remaining
64 rows of this fiber and the other eleven size-512 `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber4Block7ComponentCertificate.lean` completes
the same fiber with an eighth 64-row block, split into four 16-row chunk
modules.  The theorem `tttLargeFiber4Block7ComponentCertificateAudit_ok`
checks rows 448 through 511 by explicit component-switch rows, generated
parent-map agreement, and explicit bounded parent paths to root `2176`.  Thus
all 512 rows of the `[r,r,b,b]` size-512 fiber are now checked; the other eleven
size-512 `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber4Certificate.lean` is the aggregate surface
for that completed first large fiber.  The theorem
`tttLargeFiber4ComponentCertificateAudit_ok` combines target/mode bookkeeping,
the fiber count audit, and all eight 64-row block audits into one checked
certificate for the `[r,r,b,b]` size-512 fiber.  It is still one fixed-input
large-fiber certificate, not the full `TTT` target audit.
`GoertzelLemma818TripleTauLargeFiber8Data.lean` and
`GoertzelLemma818TripleTauLargeFiber8Block0ComponentCertificate.lean`
start the second large `TTT` fixed-input fiber, key `[r,r,p,p]`.  The data
module records the 512-state fiber ranges `4368..4623` and `6000..6255`, root
`4368`, max parent depth 6, and the generated finite parent map.  The chunk
theorems are aggregated by `tttLargeFiber8Block0ComponentCertificateAudit_ok`,
which checks rows 0 through 63 by explicit component-switch rows, parent-map
agreement, and explicit bounded parent paths.  This is the first 64-row block
of that fiber, not the full second large-fiber audit.
`GoertzelLemma818TripleTauLargeFiber8Block1ComponentCertificate.lean` extends
the same second large `TTT` fiber by another four 16-row chunks.  The theorem
`tttLargeFiber8Block1ComponentCertificateAudit_ok` checks rows 64 through 127
by the same explicit component rows, parent-map agreement, and bounded parent
paths to root `4368`.  Thus rows 0 through 127 of `[r,r,p,p]` are now checked;
the remaining 384 rows of that fiber and the other ten large `TTT` fibers
remain open.
`GoertzelLemma818TripleTauLargeFiber8Block2ComponentCertificate.lean` adds the
next four 16-row chunks for that fiber.  The theorem
`tttLargeFiber8Block2ComponentCertificateAudit_ok` checks rows 128 through 191
by explicit component rows, parent-map agreement, and bounded parent paths to
root `4368`.  Thus rows 0 through 191 of `[r,r,p,p]` are now checked; the
remaining 320 rows of that fiber and the other ten large `TTT` fibers remain
open.
`GoertzelLemma818TripleTauLargeFiber8Block3ComponentCertificate.lean` adds the
next four 16-row chunks for the same fiber.  The theorem
`tttLargeFiber8Block3ComponentCertificateAudit_ok` checks rows 192 through 255
by explicit component rows, parent-map agreement, and bounded parent paths to
root `4368`.  Thus rows 0 through 255 of `[r,r,p,p]` are now checked; the
remaining 256 rows of that fiber and the other ten large `TTT` fibers remain
open.
`GoertzelLemma818TripleTauLargeFiber8Block4ComponentCertificate.lean` adds the
next four 16-row chunks for the same fiber.  The theorem
`tttLargeFiber8Block4ComponentCertificateAudit_ok` checks rows 256 through 319
by explicit component rows, parent-map agreement, and bounded parent paths to
root `4368`.  Thus rows 0 through 319 of `[r,r,p,p]` are now checked; the
remaining 192 rows of that fiber and the other ten large `TTT` fibers remain
open.
`GoertzelLemma818TripleTauLargeFiber8Block5ComponentCertificate.lean` adds the
next four 16-row chunks for the same fiber.  The theorem
`tttLargeFiber8Block5ComponentCertificateAudit_ok` checks rows 320 through 383
by explicit component rows, parent-map agreement, and bounded parent paths to
root `4368`.  Thus rows 0 through 383 of `[r,r,p,p]` are now checked; the
remaining 128 rows of that fiber and the other ten large `TTT` fibers remain
open.
`GoertzelLemma818TripleTauLargeFiber8Block6ComponentCertificate.lean` adds the
next four 16-row chunks for the same fiber.  The theorem
`tttLargeFiber8Block6ComponentCertificateAudit_ok` checks rows 384 through 447
by explicit component rows, parent-map agreement, and bounded parent paths to
root `4368`.  Thus rows 0 through 447 of `[r,r,p,p]` are now checked; the
remaining 64 rows of that fiber and the other ten large `TTT` fibers remain
open.
`GoertzelLemma818TripleTauLargeFiber8Block7ComponentCertificate.lean` adds the
last four 16-row chunks for the same fiber.  The theorem
`tttLargeFiber8Block7ComponentCertificateAudit_ok` checks rows 448 through 511
by explicit component rows, parent-map agreement, and bounded parent paths to
root `4368`.  Thus all 512 rows of `[r,r,p,p]` are now checked; the other ten
large `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber8Certificate.lean` aggregates the eight
block audits with the target/mode and count checks into
`tttLargeFiber8ComponentCertificateAudit_ok`, the downstream dependency point
for this completed fixed-input fiber.
`GoertzelLemma818TripleTauLargeFiber10Data.lean` and
`GoertzelLemma818TripleTauLargeFiber10Block0ComponentCertificate.lean` start
the third large `TTT` fixed-input fiber, key `[r,b,r,b]`.  The data module
records ranges `2448..2703` and `4096..4351`, root `2448`, and max parent
depth `6`.  The theorem `tttLargeFiber10Block0ComponentCertificateAudit_ok`
checks rows 0 through 63 by four 16-row chunk modules, explicit component
rows, parent-map agreement, and bounded parent paths to root `2448`.  Thus the
first 64 rows of `[r,b,r,b]` are checked; the remaining 448 rows of that fiber
and the other nine large `TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber10Block1ComponentCertificate.lean`
continues the same fiber with rows 64 through 127.  The theorem
`tttLargeFiber10Block1ComponentCertificateAudit_ok` checks those rows by four
16-row chunk modules, explicit component rows, parent-map agreement, and
bounded parent paths to root `2448`.  Thus rows 0 through 127 of `[r,b,r,b]`
are checked; the remaining 384 rows of that fiber and the other nine large
`TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber10Block2ComponentCertificate.lean`
continues the same fiber with rows 128 through 191.  The theorem
`tttLargeFiber10Block2ComponentCertificateAudit_ok` checks those rows by four
16-row chunk modules, explicit component rows, parent-map agreement, and
bounded parent paths to root `2448`.  Thus rows 0 through 191 of `[r,b,r,b]`
are checked; the remaining 320 rows of that fiber and the other nine large
`TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber10Block3ComponentCertificate.lean`
continues the same fiber with rows 192 through 255.  The theorem
`tttLargeFiber10Block3ComponentCertificateAudit_ok` checks those rows by four
16-row chunk modules, explicit component rows, parent-map agreement, and
bounded parent paths to root `2448`.  Thus rows 0 through 255 of `[r,b,r,b]`
are checked; the remaining 256 rows of that fiber and the other nine large
`TTT` fibers remain open.
`GoertzelLemma818TripleTauLargeFiber10Block4ComponentCertificate.lean`,
`GoertzelLemma818TripleTauLargeFiber10Block5ComponentCertificate.lean`,
`GoertzelLemma818TripleTauLargeFiber10Block6ComponentCertificate.lean`, and
`GoertzelLemma818TripleTauLargeFiber10Block7ComponentCertificate.lean`
complete rows 256 through 511 of the same fiber.  The theorem
`tttLargeFiber10ComponentCertificateAudit_ok` in
`GoertzelLemma818TripleTauLargeFiber10Certificate.lean` aggregates all eight
blocks with the representative-mode and count audits.  The third size-512
`TTT`/`mode09` large fiber `[r,b,r,b]` is now fully checked; the other nine
large `TTT` fibers remain open.

Checkpoint stop status, 2026-07-01: the exploratory Gate-2 connectivity sweeps
are stopped.  The finite mode set is not the open question anymore: Lean records
a 20-mode profile DFA, 40 closed transitions, 42 representative word/hash
checks, 30 direct length-1-through-4 atom-connectivity rows, and the two
length-5 singleton quotient-connectivity rows.  Every one of the 20 modes has
archived per-fixed-input connectivity evidence at that metadata layer, and no
mode is presently flagged as lacking such evidence.  The closure that is still
unproved is semantic: only six modes are currently backed by real single or
length-2 chain-level parent/path certificates
(`mode07/mode16/mode10/mode18/mode11/mode04`).  The other fourteen modes
(`mode00/mode01/mode02/mode03/mode05/mode06/mode08/mode09/mode12/mode13/mode14/mode15/mode17/mode19`)
still need compact per-fixed-input chain/component certificates, or an
equivalent finite transition certificate, before `wordMode_induction` can yield
all-chain `LKR_in`.  The first non-base target, `mode09`, now has its `TTT`
light fibers certified and the first three large `TTT` fibers fully certified,
but not the remaining large `TTT` work.  This checkpoint is
therefore a finite-mode/table-closure plus partial target-certificate
checkpoint, not a completed Lemma 8.18/8.19 lift and not a Four Color Theorem
claim.

Immediate halt checkpoint, 2026-07-01: no longer run broader word-length or
representative sweeps from this context.  The generated blocks for the rest of
the first large `TTT` fiber were produced as WIP, and blocks 4, 5, 6, and 7
have since been restored and checked in the fresh 16-row chunk style.  The
green branch now keeps the checked block 0 theorem plus four-chunk replacements
for blocks 1, 2, 3, 4, 5, 6, and 7.
The status split is therefore precise:
all 20 profile modes have metadata/quotient connectivity evidence; six modes
have full base chain certificates; `mode09` has the light `TTT` fibers plus the
first three large `TTT` fibers certified; and the remaining semantic
certificates are still open for the other nine large `TTT` fibers and for
`mode00/mode01/mode02/mode03/mode05/mode06/mode08/mode12/mode13/mode14/mode15/mode17/mode19`.
The 16-row chunk shape with explicit parent paths is viable through block 7.
The next pass should continue only as small explicit parent-path/component
chunks or replace the remaining large-fiber proof with a finite transition
certificate, then feed those audits through `GoertzelLemma818SemanticBridge.lean`.

Final Gate-2 exploration stop, 2026-07-01: the finite-mode finding is now the
checkpoint, not an instruction to keep sweeping.  The profile layer is a checked
finite 20-mode, 40-transition table with representative/hash coverage, 30
length-1-through-4 atom-connectivity rows, two length-5 singleton quotient rows,
and archived per-fixed-input connectivity evidence for every mode.  Thus no
profile mode is currently listed as connectivity-unverified at the metadata
layer.  What is not closed is the semantic lift from those archived rows to
actual chain-state `LKR_in`: six base modes have real chain certificates,
`mode09` has its light `TTT` fibers, the first large `[r,r,b,b]` fiber
certified, the second large `[r,r,p,p]` fiber certified, and the third large
`[r,b,r,b]` fiber certified.  The remaining semantic work is
the other nine large `TTT` fibers, plus
`mode00/mode01/mode02/mode03/mode05/mode06/mode08/mode12/mode13/mode14/mode15/mode17/mode19`.
The next pass should formalize this stabilized finite surface by compact
per-fixed-input chain/component certificates or an equivalent finite transition
invariant.  It should not extend representative lengths or raise kernel limits.

Fresh finite-surface formalization delta, 2026-07-01:
`GoertzelLemma818TripleTauTargetProgress.lean` now aggregates the checked
`TTT`/`mode09` target progress into the theorem
`tttPartialTargetCertificateAudit_ok`.  The audit ties the `mode09` semantic
witness to `RepresentativeSemanticTarget.ttt`, checks the light-fiber theorem
and the three completed large-fiber theorems, verifies the completed-fiber
count split of 1,920 certified states versus 4,608 states still in named large
fibers, and now also checks the first 16-row slice of the next large fiber
`[r,p,r,p]` by `tttLargeFiber20FirstChunkProgressAudit_ok`.  With that slice,
1,936 `TTT` states have explicit target-surface certificates and 4,592 states
remain in the large-fiber layer.  This is a structured partial target
certificate, not a completed `TTT` audit and not the all-chain Lemma 8.18/8.19
lift.

The CAP5/F2, GP(12,2), dodecahedral six-cut, and related files below are
exploratory audits of a divergent F2-additivity route.  They are retained for
negative evidence and infrastructure, but they are not Ben's actual route and
should not be promoted as a counterexample or as a Four Color Theorem claim.

## Consolidated Verdict

The section below records the older CAP5/F2 exploratory verdict and is
superseded for Ben-route planning by the Pillar-C reset above.

As of the checkpoint after `08cd9ed6`, stop treating additional GP(12,2)
adapter slices as make-or-break work.  The make-or-break decision for the
current finite CAP5/F2 route is already banked at `cb729b3a`: the first
formable cyclic-five/Tait survivor, GP(12,2), is a wide Gate-2 BREAK under the
checked finite criterion
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty`.
The later GP12 route-input adapter and two-row certificate slice are useful
upside evidence only and do not change that verdict.

The generic six-cut meta-barrier is not proved.  The non-boundary six-cut
degree of freedom remains open.  Therefore the consolidated status is:
decided current-route wide BREAK, six-cut residual honestly open, no 4CT claim,
and no route-derived coloring payoff.

Consolidation verification: focused `CAP5RouteVerdict` build SHA256
`7b6ae89e8bfa82e8cc7df6070d84fd71e2ca1a6172f02db3ee5c9e2212d119c8`;
FourColor umbrella build SHA256
`737deefdb55e3f567d1a23d0caf36854be06e510a68be13d3eb6e0f39d18b99d`;
axiom audit driver/log SHA256
`b0110815b9229f6956455e7ad0e6940e15986836dff08631fb58b46b3204623c` /
`c599bbefab7d583e1d737e4edc5056bb57e984e54076e1b6821af0451e903b7e`,
baseline `[propext, Classical.choice, Quot.sound]`.

## Fork State

| Fork | State | PLN STV | ITV | Progress |
|---|---|---:|---:|---:|
| Whole CAP5/F2 route verdict | `CAP5RouteVerdict.lean` now packages the route into the single Lean theorem `cap5F2Route_irreducibleBarrier`, plus the closed-frontier no-gap form `cap5F2Route_irreducibleBarrier_of_noGap`.  The verdict is an irreducible barrier, not a 4CT claim and not a positive-canary sufficient condition: under the standard cyclic-five finite F2 route data, Lean returns either a concrete primitive portal/cycle checker gap from the executable CAP5 report, or the closed-frontier statement that absence of the two concrete target/off-target F2 evaders is exactly equivalent to theorem-4.9 synthesis plus full selected-boundary-zero classifier control.  The unified emitted-kernel/remaining-map obstruction is now named as `CAP5F2UnifiedKernelMapEvader`; under `¬ CAP5PrimitiveCheckerGap`, Lean proves no such evader iff the route is closed, and existence of such an evader iff the closed route endpoint fails.  In that same closed-frontier branch, the CAP5/Jordan geometric separator repair is impossible by the already formalized cyclic-cut obstruction.  The module also records the primitive Gate-1 parity barrier: `noGap_forall_boundaryEdge_crosses` forces all five CAP5 boundary edges to cross under no-gap, and `cap5PrimitiveCheckerGap_of_boundaryEdge_odd_closed_walk` shows any five-edge boundary support covering an odd closed walk is Gate-1 blocked.  The remaining open crux is therefore precisely the actual-side primitive checker frontier plus the single named unified no-evader predicate on candidates not already excluded by this parity barrier; adding more scheduler, rank, or report forks would not change the route decision. | `<0.97,0.95>` | `[0.92,0.97]` | 100% verdict layer |
| Route payoff audit and finite gate | `CAP5RoutePayoff.lean` no longer claims that route closure yields `G.EdgeColorable 4`: that payoff was vacuous because the route root already has type `G.EdgeColoring Color`.  The non-vacuous route endpoint is now `CAP5RouteClosedSynthesisPayoff`, which extracts only `Theorem49BoundaryRootSynthesis emb C₀` and selected-boundary-zero classifier control from `CAP5F2RouteClosed`.  A genuine coloring payoff remains blocked until the route is refactored around a raw edge-labeling/properness object, or an additional bridge proves properness/nonzero colorability from synthesis rather than from the type of `C₀`.  The finite pre-RREF input is still `CAP5FiniteNoGapRouteInput`; with actual exceptional/cyclic side data and `CAP5F2NoUnifiedKernelMapEvader`, `CAP5FiniteNoGapRouteInput.routeClosed_of_noUnifiedKernelMapEvader` proves `CAP5F2RouteClosed`.  `F2KernelCertificate.lean` adds the checked finite left-inverse certificate `F2LeftInverseKernelCertificate`, and `CAP5RoutePayoff.lean` also consumes the exact empty-remaining finite certificate through `CAP5FiniteNoGapRouteInput.routeClosed_of_remainingControlEdges_eq_empty`.  The same file now records the generic honest-boundary no-input corollaries `CAP5FiniteNoGapRouteInput.false_of_boundaryEdge_odd_closed_walk` and `CAP5FiniteRouteClosedWitness.false_of_boundaryEdge_odd_closed_walk`: any finite route input or route-closed witness whose five CAP5 boundary edges cover an odd closed walk is impossible before Gate 2.  It also records the fixed-embedding formability obstruction `CAP5FiniteNoGapRouteInput.redInterior_mem_projectedColoringGeneratorSubspace`, `CAP5FiniteNoGapRouteInput.blueInterior_mem_projectedColoringGeneratorSubspace`, and the red/blue missing-probe contradiction corollaries: every interior-support edge is either emitted or remaining, so one missing interior red/blue projected-generator coordinate already refutes `CAP5FiniteNoGapRouteInput`.  `CAP5WheelRouteData.lean` fixes one concrete exceptional wheel boundary/component-cover core and proves that exact five-edge boundary is Gate-1 blocked by `wheelCAP5PrimitiveCheckerGap`, so no `CAP5FiniteNoGapRouteInput` or `CAP5FiniteRouteClosedWitness` exists for that core.  The strict incidence lab supersedes the earlier one-control prism MAKE: deriving `selectedBoundarySupport` and `interiorEdgeSupport` from the face incidence data makes the prism 3,840/3,840 `BREAK_evader`, and the prism also fails cyclic-five.  The cyclic-five/Tait dodecahedral six-cut lab candidate is Gate-1-positive and exact strict F2 row reduction gives 532 no-gap sides, 1,021,440 route cases, all `BREAK_evader`; the distinguished side has a unit red-scalar evader on `dod0_1`.  `CAP5DodecahedralRouteData.lean` now records the concrete dodecahedral graph, face embedding, Tait coloring, exceptional CAP5 core, side/cut data, and checked strict F2 evader certificate (`dodecahedralStrictF2KernelEvaderCertificate`: emitted rows `0x20000000,0x400`, rank 2, kernel dimension 28, unit red-scalar on `dod0_1`).  The actual-route lab then tried to promote that same side through the projected generator surface and failed before Gate 2: the full edge-Kempe closure has 6 colorings, the projected face-generator span has rank 42 in the 60-dimensional chain space, and none of the 60 red/blue single-coordinate route probes lies in that span.  Therefore the dodecahedral side is not a formable `CAP5FiniteNoGapRouteInput`; its raw emitted-coordinate matrix has a `BREAK_evader`, but no Lean `CAP5FiniteUnifiedKernelMapEvaderWitness` can honestly be built for this side. | `<0.87,0.95>` | `[0.73,0.89]` | finite-evidence/current-surface six-cut barriers added; generic six-cut meta-barrier not proven; non-boundary six-cut DOF remains open |
| Geometric CAP5/Jordan repair | The old packet-refutation lane has been consolidated for the source-bound canonical/one-collar part: every closed-walk exact shell structurally blocks the canonical witness choice and every one-collar collar/previous-boundary witness repair by the same two-interior-edge face obstruction. The side-cut lane has two structural obstructions now: any finite support containing an odd closed walk cannot be realized by a single vertex-side cyclic separator, and any CAP5/Jordan exceptional candidate realized as cyclic-cut data produces a forbidden cyclic edge cut of size at most four in a cyclically five-edge-connected graph. The generated residual surface is now classified and decision-shaped: under cyclic five-edge-connectivity every generated node is either missing primitive checker evidence or emits a concrete outside-crossing edge outside candidate support; at report level, the missing frontier is empty exactly when every latent has the primitive portal/cycle checker evidence needed to enter the realized separator-repair class, while a nonempty frontier is precisely failed checker prerequisites. The report-level geometric decision theorem now says that after the one-collar/canonical obstruction, a CAP5/Jordan report either fails those primitive repair prerequisites or the completed frontier is forced-all and every compatible exceptional cyclic-separator realization is impossible by the same size-at-most-four edge-cut obstruction. Remaining work is to connect exact shell data to the completed-prerequisite side when the route wants more than refuting the repair class. | `<0.66,0.78>` | `[0.51,0.73]` | 88% |
| Algebraic F2 cancellation oracle | Lab finds no top-level all-interior evader on 65 records, no declared-forced evader on the 38 declared-forced rows (36 forcing-tagged records), and no all-interior vertex-Kirchhoff failure on all 65 records; the vertex-failure crux survives on the 36 forcing records. Lean now proves the route-facing classifier-control iff/no-evader contract, including the full selected-boundary-zero version: emitted CAP5 coordinates control every selected-boundary-zero chain iff no nonzero selected-boundary-zero chain evades all enumerated forced edges. The completed-checker no-evader handoff now also returns full boundary-zero classifier control together with theorem-4.9 synthesis. The executable report bridge now consumes the generator verdict `forcedCounterexampleLatents = all`: under cyclic five-edge-connectivity that verdict closes the primitive missing-evidence frontier, so the report-forced-all branch feeds directly into full boundary-zero no-evader control, the empty-worklist subset certificate, and the target-controlled synthesis-or-genuine-evader fork. The empty-worklist subset certificate is now the actual no-evader branch too: if the forced-all report has no remaining canonical interior-support worklist, Lean proves there is no nonzero selected-boundary-zero evader and then closes synthesis plus full selected-boundary-zero classifier control. The forced-all finite scheduler fork packages the remaining exact-shell obligation: either that empty-worklist no-evader/full-control branch holds, or there is a concrete remaining interior-support edge whose erasure strictly decreases the finite worklist. The forced-all residual scheduler fork now strengthens the failure side: if synthesis fails under the forced-all report, Lean returns the complete checker histogram, forced-bin detector payload, a genuine selected-boundary-zero evader, a traced remaining interior-support edge in the residual worklist, and a strict residual decrease after recording that edge as processed. The residual scheduler transition now also proves that the chosen edge is not controlled by the immutable classifier output and returns the exact one-edge emitted/control update needed to insert it into the processed scheduler state. The terminal residual scheduler theorem closes the success side: if the explicit residual interior-support worklist is exhausted while the processed-control invariant holds, Lean proves no selected-boundary-zero evader exists and closes theorem-4.9 synthesis plus full selected-boundary-zero classifier control. The failed-terminal scheduler decision now connects the two sides: under forced-all and processed-control, failed synthesis cannot have an exhausted residual worklist, and Lean returns a genuine selected-boundary-zero evader plus the next residual edge, immutable-control failure for that edge, the one-edge emitted/control update, and strict residual decrease. The immutable-scheduler obstruction now proves that the same returned edge cannot be silently inserted into the processed state under the original classifier output: processing it is invalid unless the scheduler promotes new emitted/control information, or the returned boundary-zero chain is accepted as the obstruction. The route-facing residual scheduler decision now packages the live finite state as terminal no-evader/synthesis, already-closed synthesis, or a promoted one-edge obstruction with immutable processing ruled out and strict residual decrease. The initial residual closure layer now names the first scheduler obstruction, proves that no primitive checker gap plus failed synthesis forces that obstruction, and proves that no primitive checker gap plus an initially empty residual scheduler closes theorem-4.9 synthesis and full selected-boundary-zero classifier control. The terminal-coverage and trace-control forms sharpen that state: processed coverage is the semantic terminal invariant, canonical remaining-interior trace-control is equivalent to absence of a selected-boundary-zero evader, and trace-control failure returns a concrete trace edge where the evader is nonzero and, given the canonical red/blue remaining-edge certificates, a nonzero pairing against the canonical single-coordinate family. The remaining-family map oracle now sharpens this again: every genuine selected-boundary-zero evader has nonzero image under the canonical remaining-edge family-pairing map; conversely, emitted classifier zeros plus zero image under that map force the boundary-zero chain to be zero. The exact split proves no map-detected evader iff no selected-boundary-zero evader, and under forced-all the route is theorem-4.9 synthesis plus full selected-boundary-zero classifier control or a concrete map-detected evader. The emitted-kernel bridge identifies the lab-facing finite rank certificate on immutable emitted forced-edge coordinates with the same no-evader oracle. The new emitted-kernel/map equivalence proves the two failure languages coincide: every nontrivial emitted-kernel witness has nonzero remaining-family map image, and every map-detected evader lies in the emitted kernel. The forced-all rank split now returns one concrete witness carrying both certificates. The failed-synthesis corollary removes the success branch entirely: under forced-all, if theorem-4.9 synthesis fails, Lean returns that same unified emitted-kernel/remaining-map evader directly. The exact forced-all oracle equivalence now proves that absence of this unified evader is equivalent to theorem-4.9 synthesis plus full selected-boundary-zero classifier control. The emitted-rank exact oracle now proves the lab-facing finite F2 kernel certificate itself is equivalent to theorem-4.9 synthesis plus full selected-boundary-zero classifier control under forced-all; the report-closed emitted-rank theorem removes that raw handoff by deriving forced-all from an empty executable missing-evidence frontier, and the report fork now states either primitive portal/cycle evidence is missing or this rank certificate is exactly equivalent to synthesis/control. The stronger report-level trace fork now removes the same raw handoff from the trace-control split: the executable report returns a primitive checker gap, theorem-4.9 synthesis with full selected-boundary-zero control, or a genuine trace-local selected-boundary-zero evader with nonzero canonical remaining-family pairing. The failure-only report trace theorem now removes the success side under `¬ Theorem49BoundaryRootSynthesis`: a failed route returns a primitive checker gap or that genuine trace-local evader directly. The failure-only report kernel/map theorem now makes the same failed route lab-facing: the executable report returns the primitive checker gap or the unified emitted-kernel/remaining-map evader carrying kernel membership and nonzero canonical remaining-map image. The report-level kernel/map split and no-gap/no-evader closure corollary turn this around: if the executable report has no primitive checker gap and no unified emitted-kernel/remaining-map evader, Lean proves theorem-4.9 synthesis plus full selected-boundary-zero classifier control. The forced-all F2 oracle is also packaged as a direct route-facing split: either no-evader closes synthesis plus full selected-boundary-zero classifier control, or Lean returns an actual nonzero selected-boundary-zero evader. The same report-forced-all interface is now split into its two decision halves: target control plus absence of the concrete theorem-4.9 boundary-vertex Kirchhoff evader yields synthesis and target coverage, while target control plus failed synthesis returns that genuine evader and a decreasing remaining-worklist edge. The forced-all branch now also exposes the pure F2 failure fork without target control: failed synthesis itself returns a nonzero selected-boundary-zero chain vanishing on every enumerated forced edge plus a decreasing remaining interior-support worklist edge. Its stronger canonical path-xor payload form returns the detector payload, a selected-boundary-zero chain, a concrete non-forced remaining interior edge where the chain is nonzero, a strict worklist decrease, and a nonzero canonical red/blue family pairing. Lean also proves the target-dimension fork theorem below-bound classifier implies genuine target evader, the target-control/off-target bridge, the vertex-Kirchhoff failure bridge, the row-span/subset certificate bridge, and the exact binary fork theorem. The empty canonical interior-support worklist proves the exact row-span/subset certificate itself and rules out the concrete vertex-Kirchhoff evader branch. The all-interior/empty-worklist success side proves there is no odd closed walk in ambient interior support, while odd-worklist witnesses do not block synthesis once the concrete evader is excluded. The closed-frontier target/off-target rank-certificate theorem now states the lab-facing emitted kernel certificate itself is equivalent to absence of both target and off-target report evaders; synthesis/control is recovered from the same rank certificate rather than bundled into the certificate predicate. The emitted-rank route-close theorem now consumes that rank certificate directly: the executable report returns only primitive checker gap or synthesis/control, and with a closed primitive frontier the same certificate proves theorem-4.9 synthesis plus full selected-boundary-zero classifier control. The coverage-to-rank bridge now removes one more handoff: exact forced-edge coverage, or a concrete finite control set that meets every nonzero selected-boundary-zero chain and is contained in the emitted classifier output, proves the emitted red/blue pairing-kernel certificate itself; therefore the report route can consume the lab no-evader/coverage verdict as the rank certificate. The empty-worklist rank close now specializes this to exact CAP5 shell data: if the canonical interior-support worklist is empty, Lean proves the emitted pairing kernel is trivial, the executable report has only primitive checker gap or synthesis/control left, and with a closed primitive frontier the empty worklist directly proves synthesis plus full selected-boundary-zero classifier control. The report-level interior-gap wrapper now removes the remaining closed-frontier handoff from the paired failure branch: the executable report returns primitive checker gap, theorem-4.9 synthesis, or a residual canonical interior-support coordinate outside the immutable emitted classifier output together with the unified emitted-kernel/remaining-map evader. The remaining burden is now sharper: prove uniform exact CAP5 data emits every canonical interior-support coordinate and closes the no-evader branch, or accept the paired missing interior coordinate plus the genuine unified finite F2 obstruction. | `<0.94,0.95>` | `[0.89,0.94]` | 99% |

Route-verdict delta: `CAP5RouteVerdict.lean` adds the compact certificate bundle
`CAP5F2RouteCertificate`, the named residual predicates
`CAP5PrimitiveCheckerGap`, `CAP5F2NoTargetOffTargetEvader`,
`CAP5F2UnifiedKernelMapEvader`, `CAP5F2NoUnifiedKernelMapEvader`, and
`CAP5F2RouteClosed`, and the top-level theorem
`cap5F2Route_irreducibleBarrier`.  The no-gap theorem
`cap5F2Route_irreducibleBarrier_of_noGap` eliminates the checker-gap branch
once exact side data proves `¬ CAP5PrimitiveCheckerGap`.  The unified-evader
theorems
`cap5F2NoUnifiedKernelMapEvader_iff_routeClosed_of_noGap` and
`cap5F2UnifiedKernelMapEvader_exists_iff_not_routeClosed_of_noGap` pin the
remaining algebraic question directly: under no gap, no unified evader is
exactly route closure, and a unified evader exists exactly when that closed
endpoint fails.  This is the route verdict, not a goes-through theorem with a
positive coloring canary.  Current whole-route verdict estimate is PLN STV
`<0.97,0.95>`, ITV `[0.92,0.97]`, progress `100%` for the route-verdict layer
and no claim of 4CT.

Route-payoff correction and finite-input delta: `CAP5RoutePayoff.lean` now retracts
the former route-closure-to-`EdgeColorable 4` payoff as vacuous: `C₀` already has type
`G.EdgeColoring Color`, so that conclusion did not factor through route closure.
The non-vacuous endpoint is `CAP5RouteClosedSynthesisPayoff`, which extracts
theorem-4.9 synthesis and selected-boundary-zero classifier control from
`CAP5F2RouteClosed`.  The same file also proves
`CAP5DecidableCheckerEvidence.noPrimitiveGap_of_noPrimitiveGapByFiniteCheck`
and exposes `CAP5FiniteNoGapRouteInput`.  This names the exact object still
missing before the finite F2 question can be checked on a concrete side: a
closed executable primitive-checker report, the concrete forced-edge
classifier, and red/blue single-coordinate witnesses for every emitted and
remaining control edge.  `CAP5FiniteNoGapRouteInput.toRouteCertificate` turns
that object into the route certificate consumed by the existing unified-evader
oracle.  `CAP5FiniteNoGapRouteInput.routeClosed_of_noUnifiedKernelMapEvader`
is the MAKE gate: with actual exceptional/cyclic side data and
`CAP5F2NoUnifiedKernelMapEvader`, Lean closes `CAP5F2RouteClosed`;
`CAP5FiniteNoGapRouteInput.toClosedWitness_of_noUnifiedKernelMapEvader` then
packages the finite route-closed witness.  The BREAK gate is now named as
`CAP5FiniteUnifiedKernelMapEvaderWitness`, a concrete unified emitted-kernel/
remaining-map evader for the certificate induced by the finite no-gap input.
No concrete actual-side instance, checked unified RREF/no-evader certificate, or
route-derived coloring payoff is claimed by this delta.

RREF-shaped finite gate update: `F2KernelCertificate.lean` introduces
`F2LeftInverseKernelCertificate`, a finite basis-and-matrix certificate whose
checked product equation reconstructs a left inverse and proves
`LinearMap.ker f = ⊥`.  `CAP5RoutePayoff.lean` now proves
`cap5F2NoUnifiedKernelMapEvader_of_emittedFinsetPairingKernel_eq_bot`, so a
checked bottom emitted-pairing kernel certificate directly excludes the unified
emitted-kernel/remaining-map evader.  At the finite-input surface,
`CAP5FiniteNoGapRouteInput.noMissingCheckerEvidence` exposes the closed
primitive frontier in the exact report vocabulary, and
`CAP5FiniteNoGapRouteInput.routeClosed_of_emittedFinsetPairingKernel_eq_bot`
plus
`CAP5FiniteNoGapRouteInput.toClosedWitness_of_emittedFinsetPairingKernel_eq_bot`
turn such a checked emitted-kernel certificate, together with the required
actual exceptional/cyclic side data, into `CAP5F2RouteClosed` and the finite
closed witness.  The new left-inverse wrappers
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_of_emittedFinsetPairingLeftInverseCertificate`,
`CAP5FiniteNoGapRouteInput.routeClosed_of_emittedFinsetPairingLeftInverseCertificate`,
and
`CAP5FiniteNoGapRouteInput.toClosedWitness_of_emittedFinsetPairingLeftInverseCertificate`
show how a generated finite RREF/kernel certificate is consumed.  This is the
certificate-shaped bridge for Gate 2.  The BREAK side now also has the small
constructor
`CAP5FiniteNoGapRouteInput.exists_unifiedKernelMapEvader_of_boundaryZeroChain`
and wrapper
`CAP5FiniteNoGapRouteInput.toUnifiedKernelMapEvaderWitness_of_boundaryZeroChain`:
a selected-boundary-zero chain that vanishes on emitted edges and is nonzero on
one remaining control edge is promoted to the named unified kernel-map evader
for the induced finite input.  The unit-coordinate specialization
`CAP5FiniteNoGapRouteInput.exists_unifiedKernelMapEvader_of_mem_remainingControlEdges`
now proves that any nonempty `remainingControlEdges` set already gives such an
evader, because a red unit vector on a remaining interior edge is boundary-zero,
vanishes on all emitted edges, and is detected by the remaining map.  The exact
current finite Gate-2 criterion is
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty`:
for a checked finite no-gap input, the no-unified-kernel-map-evader side holds
iff the classifier leaves no remaining interior controls.  The equivalent
coverage form is now also explicit:
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset`.
Thus the current finite Gate-2 surface is MAKE exactly when the Boolean CAP5
classifier emits the entire canonical `interiorEdgeSupport`.  The corollaries
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_exists_interiorEdgeSupport_not_emitted`,
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_emittedInterior_card_lt_interiorEdgeSupport_card`,
and
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_emittedFinset_card_lt_interiorEdgeSupport_card`
package the same obstruction in witness and cardinality forms.

Fixed-embedding formability update: `CAP5FiniteNoGapRouteInput` now exposes the
necessary membership condition directly.  The theorems
`CAP5FiniteNoGapRouteInput.redInterior_mem_projectedColoringGeneratorSubspace`
and
`CAP5FiniteNoGapRouteInput.blueInterior_mem_projectedColoringGeneratorSubspace`
prove that every edge in `interiorEdgeSupport emb.faceBoundary emb.faces` must
have both red and blue single-coordinate probes in
`projectedColoringGeneratorSubspace emb colorings`.  The corollaries
`CAP5FiniteNoGapRouteInput.false_of_missing_interior_red_probe` and
`CAP5FiniteNoGapRouteInput.false_of_missing_interior_blue_probe` turn any one
missing interior probe into `False`.  This is the formal reason that the
dodecahedral projected-generator membership failure is an input-formability
blocker, independent of which sidecase emits a given interior edge.

Lab-first finite Gate-2 verdict update: the numpy/sympy-pinned all-static run
recorded in `fourcolor-cap5-f2-all-static-verdict-20260629.json` built the
current CAP5 forced-edge classifier matrix over F2 for all eight static
benchmark JSONs and ran exact mod-2 row reduction before any further Lean
packaging.  The current Lean surface contains one concrete component-cover
core (`wheelCAP5ComponentCoverCore`) and zero concrete positive
`CAP5FiniteNoGapRouteInput` instances.  Seven static benchmarks have zero
Gate-1 no-gap sides.  The only Gate-1-positive static benchmark is
chained-diamonds, with 32 no-gap sides and 368,640 route cases, all
`BREAK_evader`; Lean proves
`not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph`, so that
regression case cannot be promoted to an actual Tait-route BREAK certificate.

Strict incidence Gate-2 verdict update: the later run recorded in
`fourcolor-cap5-strict-gate2-incidence-verdict-20260629.json` derives
`selectedBoundarySupport` and `interiorEdgeSupport` from the same face
incidence convention used by `PlaneEmbeddingWithBoundary`, then runs exact F2
row reduction on the emitted/remaining map.  This supersedes the earlier
manual one-control prism MAKE: under the prism's own face list,
`selectedBoundarySupport = empty` and all 18 edges are incidence-two interior
edges, so the two Gate-1 no-gap sides give 3,840/3,840 `BREAK_evader`; the
separate cyclic-cut audit also shows the prism has nine cyclic edge cuts of
size four, so it cannot satisfy `CyclicallyFiveEdgeConnected`.  The same strict
run builds a dodecahedral six-cut candidate from `networkx.dodecahedral_graph`;
it is cubic, brute-force Tait-colorable, cyclically five-edge-connected
(no cyclic edge cut of size at most four), and Gate-1-positive.  Exact F2
row reduction gives 532 no-gap sides and 1,021,440 route cases, all
`BREAK_evader`.  On the distinguished side
`{0,1,2,3,4,19}`, with boundary slots
`dod0_10, dod1_8, dod2_6, dod4_5, dod4_17`, the
`p0Inside_p4Outside` case emits `dod18_19, dod4_17`, leaves 28 remaining
interior controls, has scalar rank 2 and kernel dimension 28, and the unit
red-scalar chain on `dod0_1` is a concrete unified kernel-map evader: it is
boundary-zero, vanishes on the emitted edges, and is detected by the remaining
map at `dod0_1`.

`CAP5DodecahedralRouteData.lean` now encodes the dodecahedral graph,
face-boundary embedding, Tait coloring, exceptional component-cover core,
distinguished side/cut data, and the checked strict witness
`dodecahedralStrictF2KernelEvaderCertificate`: the emitted row words are
`0x20000000` and `0x400`, the RREF row words are `0x400` and `0x20000000`,
the scalar rank is 2, the scalar kernel dimension is 28, and the unit
red-scalar on `dod0_1` is boundary-zero, vanishes on emitted edges, and is
detected on the remaining controls.  No full Lean
`CAP5FiniteUnifiedKernelMapEvaderWitness` is claimed.  The follow-up actual
route lab `fourcolor-dodeca-actual-route-f2-lab-20260629.json` and the
purpose-built forced-classifier matrix run
`fourcolor-dodeca-forced-classifier-matrix-lab-20260629.json` decide why:
for the same Gate-1-positive side, the projected face-generator span over the
full edge-Kempe closure has rank 42 out of 60, and all 60 red/blue
single-coordinate route probes required by `CAP5FiniteNoGapRouteInput` are
missing.  The four raw coordinate classifier matrices are all `BREAK_evader`
with the unit `dod0_1` raw evader; their emitted ranks are 6, 4, 4, and 4
over the 60-dimensional red/blue coordinate domain.  This raw BREAK is not a
formal CAP5 finite-route BREAK, because the required projected-generator
membership hypotheses fail before the Lean route family exists.  The
one-face-punctured repair was also checked in
`fourcolor-dodeca-punctured-route-f2-lab-20260629.json`: omitting each of the
12 pentagonal faces makes a genuine selected-boundary support and lowers the
projected-generator rank to 38 on the 50-dimensional selected-boundary-zero
domain, but all 48 omitted-face/sidecase combinations still fail formability,
with 50, 52, or 54 missing route probes; all raw matrices still have a unit
remaining-coordinate evader.  The next finite task is therefore either a
different Gate-1-positive Tait/cyclic-five candidate whose projected generator
span supplies the route probes, or a generic barrier showing this
single-coordinate membership surface cannot be satisfied on genuine
candidates; it is not to package this dodecahedral side as a route input.
Fresh reruns
`fourcolor-dodeca-forced-classifier-matrix-lab-rerun-20260629.json` and
`fourcolor-dodeca-punctured-route-f2-lab-rerun-20260629.json` reproduce the
same finite answers: `INVALID_ROUTE_INPUT_missing_projected_generator_memberships`
for the closed embedding and `NO_FORMABLE_PUNCTURED_DODECA_ROUTE_INPUT` for
the 48 punctured cases.

Small cubic/Tait formability filter: the graph-generic lab
`fourcolor-small-cubic-tait-route-formability-dodeca-kempeclasses-lab-20260629.json`
partitions all 60 dodecahedral Tait colorings into 10 Kempe classes of size 6.
The full union of all Tait classes spans all interior red/blue coordinate
probes, but each individual Kempe class misses every required interior probe
on the closed embedding and on each one-face puncture.  Since the route input
only permits `colorings ⊆ G.EdgeKempeClosure C₀`, this rules out the
dodecahedral graph across all root Tait colorings and all one-face-punctured
embeddings tested, not just the previously pinned root coloring.  The wider
known-family run
`fourcolor-small-cubic-tait-route-formability-known20-capped-lab-20260629.json`
checks 22 known small cubic planar graphs through 20 vertices, including
generalized Petersen variants.  Its formable Kempe-class cases are only the
tetrahedral graph or cyclic-five failures; the only genuine Tait cyclic-five
case up to isomorphism is the dodecahedral graph, and it has no formable Kempe
class.  Scope: this is still finite search evidence and a dodeca-wide
Kempe-class barrier, not the required generic meta-barrier for all legitimate
CAP5 instances.

GP(12,2) finite Gate-2 verdict: the cyclic-first extension of the same
formability filter through 24 vertices found a genuine cyclic-five/Tait
survivor, `generalized_petersen_12_2`, with a closed formable Kempe class.
The follow-up actual Gate-2 lab
`fourcolor-gp12-cap5-gate2-verdict-lab-20260629.json` builds the CAP5
forced-edge classifier matrix for the first five-edge cyclic cut
`e0_1,e2_14,e3_4,e13_23,e15_17`, using the closed embedding where the
selected-boundary support is empty and all 36 graph edges are interior.  The
chosen Kempe class has 96 colorings and generator rank 72/72, so every
emitted/remaining red-blue coordinate probe required by
`CAP5FiniteNoGapRouteInput` is present.  Exact numpy RREF cross-checked by
SymPy `DomainMatrix` over `GF(2)` gives `BREAK_unified_kernel_map_evader` in
all four CAP5 side cases: ranks are 2, 2, 4, and 2; kernel dimensions are 70,
70, 68, and 70; and explicit unit red-coordinate evaders are recorded
(`e0_1` in three sidecases, `e0_11` when `e0_1` is emitted).  Therefore this
first formable cyclic-five/Tait candidate is not a MAKE certificate: Gate 2
decides BREAK for this no-gap cut.  The Lean-side reason is now generic for the
current finite route surface: by
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_remainingControlEdges_eq_empty`,
MAKE is possible exactly when `remainingControlEdges = empty`; the GP(12,2)
lab has 35, 35, 34, and 35 remaining controls in the four sidecases, so each
sidecase is a checked BREAK.  Equivalently, by
`CAP5FiniteNoGapRouteInput.noUnifiedKernelMapEvader_iff_interiorEdgeSupport_subset_emittedFinset`,
the current route can only MAKE if the forced-edge classifier emits all 36
interior-support edges; GP(12,2) emits only 1, 1, 2, and 1 interior edges in
the four sidecases.  Evidence: lab script SHA256
`bb78dd9377f740361f2dc6531c84596ab0d62a11f04444c74f6a5b68e5617e1f`, JSON
SHA256 `977f7dfa7b1c28b72bd3badcb31e7020d39ba1a0bdb72bc42e87cf01752127fe`,
log SHA256 `d5b52ebc6b19e6eec2f95bb22cd11590663023e6055f57626d7ab325df516ba8`.
`CAP5GP12RouteData.lean` now records the concrete GP(12,2) graph, closed
embedding, Tait coloring, exceptional CAP5 component-cover core, the selected
five-edge side cut, and four checked sidecase evader certificates:
`gp12P0InsideP4OutsideKernelEvaderCertificate`,
`gp12P0OutsideP4InsideKernelEvaderCertificate`,
`gp12P0InsideP4InsideKernelEvaderCertificate`, and
`gp12P0OutsideP4OutsideKernelEvaderCertificate`.  Each certificate packages the
lab rank/kernel-dimension pair plus a unit red boundary-zero chain that vanishes
on the emitted edges and is detected on a remaining interior control edge.
The same file now also proves the concrete GP(12,2) five-cut is Gate-1 closed:
`gp12FiveCutSide_noPrimitiveCheckerGap` discharges the primitive checker gap
from the five boundary-slot crossing facts plus explicit selected-side and
complement-side cycle witnesses.  This removes the Lean handoff for the
no-gap part of the candidate.  A graph-specific `CAP5FiniteNoGapRouteInput`
is still not claimed, because the projected-generator red/blue coordinate
witnesses reported by the lab are not yet packaged as Lean membership
certificates.
The membership gap is now finite and explicit rather than exploratory:
`fourcolor-gp12-membership-certificate-lab-20260629.json` verifies all 72
closed-embedding interior red/blue coordinate probes in the chosen GP(12,2)
Kempe-class projected-generator span, with generator rank 72/72, SymPy GF(2)
rank cross-check 72/72, 72 used generator rows, and target-combination sizes
between 2 and 42.  The lab script SHA256 is
`2615eefc5c4a09faf556e00a17b769a2bde6dff7cb843f5619b0a5182fede9be`;
the JSON SHA256 is
`b96c76cb4660003371a3cd1902b162b53585d086ad2043dca9229f73754e761d`.
The companion path artifact
`fourcolor-gp12-kempe-path-certificate-lab-20260629.json` verifies that the
11 coloring IDs used by those generator rows are reachable from the Lean
`gp12TaitEdgeColoring` inside the chosen class: the Lean base is coloring ID 5,
the maximum recorded path depth is 4, the paths use 15 distinct coloring IDs,
and replaying every recorded switch reaches the target coloring.  The script
SHA256 is
`574553f65496cc7babe6ef1153700014a3766bb4a4a14a330df48d11c67a8aac`;
the JSON SHA256 is
`77276a587f35964baa88342b53a28d9e5e09d055209d1496fd1099e6f26fb139`.
Lean also now has the route-input adapter:
`CAP5DecidableCheckerEvidence.noPrimitiveGapByFiniteCheck_of_noPrimitiveGap`,
`CAP5FiniteNoGapRouteInput.ofNoPrimitiveGap`,
`gp12FiveCutSideCheckerEvidence`,
`gp12FiveCutSide_noPrimitiveGapByFiniteCheck`, and
`gp12FiniteNoGapRouteInput_of_allCoordinateMemberships`.  The specialized
adapter `gp12FiniteNoGapRouteInput_of_closureCoordinateMemberships` can take
`colorings` to be the full `EdgeKempeClosure gp12TaitEdgeColoring`, so the
route-input surface itself no longer needs a separate finite coloring-set
subset proof.  The remaining GP(12,2) route-input packaging obligation is the
72 projected-generator finite-sum memberships in that closure subspace; no full
route input is claimed yet.  Lean now has the finite-sum landing lemmas
`finset_sum_projectedFaceGenerator_mem_projectedColoringGeneratorSubspace` and
`single_mem_projectedColoringGeneratorSubspace_of_finset_sum_projectedFaceGenerator_eq`.
`CAP5GP12RouteData.lean` also checks the first concrete two-row lab certificate:
rows 26 and 194, both on face 8 with pair `blue_purple`, sum to the red
single-coordinate probe on `gp12_e8_20`.  The theorem
`gp12_e8_20_red_mem_projectedColoringGeneratorSubspace_of_routeCertColorings_mem_closure`
therefore reduces that one target to the two remaining Kempe-closure facts for
route-certificate colorings 0 and 4.  This is a certificate-slice check, not a
full all-coordinate package.  Smoke file
`fourcolor-gp12-two-row-certificate-smoke-20260629.lean` has SHA256
`79b6b90c1842f4f923e7d6da3c51e7125ecc8646de0709251f69af7358ecd435`.
Verification for this two-row route-certificate increment: focused
`CAP5GP12RouteData` build SHA256
`c72439a459caa6fb401efba52bbeb04c71f9ec9e481631b98b49b40adeac09e3`;
FourColor umbrella build SHA256
`b1828374afcbde99b5c3d02b8ceb52e98ba519fb6dd90728168b5bfa5399f6f7`;
axiom audit driver/log SHA256
`3a878f943ba33d7c2522db0304e56360cdcee99f8b1727e832763c863f561222` /
`faf81cb4f15a4517e0f56ed58aaf36b7ebfc0baa07e71ad02e921d44db8c7987`,
baseline `[propext, Classical.choice, Quot.sound]`.  This does not upgrade the
six-cut residual:
the generic six-cut meta-barrier is not proven, and the non-boundary six-cut
degree of freedom remains open.  Verification for this closure-set adapter
increment: focused `CAP5GP12RouteData` build SHA256
`c5cf0251289caeb631efa958cbc2e78f3960812f36b3f680878a845e8cf96870`;
FourColor umbrella build SHA256
`af99f08c3c25acf21c284845e1f3b84ac7cb9f357dabf99089a4dcf73de4bbbe`;
axiom audit driver/log SHA256
`8c2907f04d6c54ee3e173a7cfd331c0da24c33e86bdb529c931187c2e7ec7cf1` /
`37b88abc5bf1563500e2a736d493cf9073a00e54396ce8d7e0c4f5d55de909be`,
baseline `[propext, Classical.choice, Quot.sound]`.
Additional verification for this GP(12,2) Gate-1 no-gap increment: focused
`CAP5GP12RouteData` build SHA256
`6a0465c7b5b2500101e4e7afa74c8c43c4c7738ca0afa47bc06c75850ab83360`;
FourColor umbrella build SHA256
`1c6dbe74bdaa401f5655b468a78884784eda313c787a725987421e8c0a2e2961`;
axiom audit driver/log SHA256
`79f27c6c5494e9c06b955c2c322e839a7d768b1f4d45803cbd7bd5a2a12601dd` /
`e1db9e764ef2a54b6c3470e18adc175d631bc5ee83988349f7bbb4b5b55cfcaa`,
baseline `[propext, Classical.choice, Quot.sound]`.
Verification: focused
`CAP5RoutePayoff` build SHA256
`3e54951880633f264897c516d9840130917f59156877eb6b6dd41f1cf949b851`;
FourColor umbrella build SHA256
`def9c35c8fb4e7449068f0a2accf0c91eb8100e4e57b60619aaf22a34c80d131`;
axiom audit driver SHA256
`233b955ba5d1520821bab6e6f78e00d471f30d624fc52c5f9c12b324e913b904`;
axiom audit log SHA256
`f08686366bec3466f2eec3e4d07e1fb6ba49551419af841ae4186400bd206f05`,
baseline `[propext, Classical.choice, Quot.sound]`.
The coverage/cardinality corollaries were then audited separately: focused
`CAP5RoutePayoff` build SHA256
`2bb2c379ec80f8ad97a0ee14371cfa29a7266fb8a1d358e08c54d8e73c4f874f`;
FourColor umbrella build SHA256
`ca7e78d853e6e52ba309aa4eb8b0baf105f99f8813b5bf91525ee20931b25c52`;
axiom audit driver SHA256
`fe18d015520a114029127aeaf42511a7e4693389c9baf8e77c2426fbc07b543c`;
axiom audit log SHA256
`2e6788ec7ffd6ae6dbd396500e57b9ea756d0a34646755fac758b20b8ad48c3c`,
baseline `[propext, Classical.choice, Quot.sound]`.
The same current-route-surface obstruction is now also stated geometrically:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_noncrossing_interiorEdgeSupport`
and
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sameSide_interiorEdgeSupport`
prove that any canonical interior-support edge whose endpoints stay on one
vertex side cannot be emitted by the CAP5 forced-edge classifier and therefore
forces a unified kernel-map evader.  Thus a MAKE run for the present finite
surface would need every interior-support edge to cross the selected side.
The side-bipartition requirement is now named directly by
`CAP5FiniteNoGapRouteInput.interiorEdgeSupport_edges_cross_of_noUnifiedKernelMapEvader`
and
`CAP5FiniteNoGapRouteInput.interiorEdgeSupport_edges_cross_of_routeClosed`:
no-evader, and route closure under the usual exceptional/cyclic equivalence,
force the selected route side to cut every canonical interior-support edge.
This is a generic obstruction for the current classifier/input surface, not a
route-independent refutation of every possible future repair.
The same pressure is now packaged in two stronger current-surface forms.
First,
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport`
proves that if Gate 1's selected-side cycle is wholly supported by canonical
interior edges, then no no-evader certificate can exist: no-evader would force
one of that side-internal cycle's own edges to cross the selected side.  The
all-interior specialization
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_forall_mem_interiorEdgeSupport`
and the route-closed form
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_forall_mem_interiorEdgeSupport`
therefore rule out the closed/all-interior current finite surface even when
the interior graph is bipartite.  Focused `CAP5RoutePayoff` build SHA256
`4ebb17291eadc7fdfa20a925dd9ce713dfe0769bcedfa9513f3e36981ad4bbc4`.
Second, the odd-specialized pressure is still available as an
odd-interior-walk obstruction:
`CAP5FiniteNoGapRouteInput.edgeCrossesVertexSide_of_noUnifiedKernelMapEvader_of_mem_interiorEdgeSupport`,
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_interiorEdgeSupport_odd_closed_walk`,
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_interiorEdgeSupport_odd_closed_walk`,
`CAP5FiniteNoGapRouteInput.no_interiorEdgeSupport_odd_closed_walk_of_noUnifiedKernelMapEvader`,
and
`CAP5FiniteNoGapRouteInput.no_interiorEdgeSupport_odd_closed_walk_of_routeClosed`
prove that no-evader would force every interior-support edge to cross one
vertex side, so an odd closed walk inside the canonical interior support
forbids both the no-evader certificate and, under the usual exceptional/cyclic
route equivalence, route closure.  `CAP5GP12RouteData.lean` now routes its
graph-specific obstruction through the all-interior theorem: because every
GP(12,2) edge is interior in the closed embedding,
`gp12_not_noUnifiedKernelMapEvader_of_finiteNoGapRouteInput` rules out
no-evader for any finite no-gap GP12 route input, for every side and every
`p0/p4` sidecase; `gp12_not_routeClosed_of_finiteNoGapRouteInput` gives the
corresponding route-closed obstruction when cyclic-five connectivity is
supplied.  The face-0 5-cycle `0-1-2-14-12-0` remains recorded as an odd-cycle
special case, but GP12 no longer depends on odd parity.  This removes the
sidecase emitted-set equality dependency for GP12's current-surface Gate-2
BREAK, while remaining conditional on the present finite route input/classifier
surface rather than a repair-independent meta-barrier.  Prior verification:
focused `CAP5RoutePayoff` build SHA256
`4ba71936046ffcbe56af1b281b0ffd5c32b9c25c7d95acbaa39f0225a8e9ed93`;
focused `CAP5GP12RouteData` build SHA256
`2218bdab2ff586615c68280ae97b7839c66fa64822a01f0567dbb10b6b0e5082`;
FourColor umbrella SHA256
`5e9bd78b573fbfe4ac9ec9d80d70db706da56dffb08d2e67b47bcdcd51c1e07d`;
axiom audit driver SHA256
`de85fe0a4e9418255cbe84fe0257899fcaba734fdc096a7346180bf9b85b91ef`;
axiom audit log SHA256
`d840b6dfd5b523987e455e18708756dd1ca18b761232530ac908743919241cd5`,
baseline `[propext, Classical.choice, Quot.sound]`.
The GP12 all-interior rewrite focused build SHA256 is
`0428e629dc3fe6a9b56af418efacd69aaf4a88d6fbc0db26de64de1f6e4a3946`.
Final verification for the side-cycle/all-interior increment: axiom audit
driver SHA256
`275258792b1d337e665fe36b151d644b2e20c1ec5344da2c83bd02e2396ea6f2`;
axiom audit log SHA256
`afe9cfe8a01ab5cfa77ee3c6ca6a14f04f55223d3e9ffc833c5fb8f7e728b409`,
baseline `[propext, Classical.choice, Quot.sound]`; FourColor umbrella build
SHA256
`be8496df88da4efab22699fc57e0810c00bdbaf01ddc372e9d16e3e3170acaab`.
`git diff --check`, the touched Lean proof-token scan, and the public diff
leak scan are clean.
The side-cycle obstruction now also has a non-interior crossing form:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_nonInterior_edges_cross`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_nonInterior_edges_cross`
show that if every edge outside canonical interior support already crosses the
selected route side, then the current finite route surface cannot be no-evader
or route-closed.  The boundary-slot corollaries
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_nonInterior_subset_boundaryEdge`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_nonInterior_subset_boundaryEdge`
specialize this to the case where every non-interior graph edge is one of the
five CAP5 boundary slots; no-gap forces those slots to cross, while Gate 1 also
supplies a side-contained cycle.  Thus any surviving repair of the current
surface must expose a selected-side cycle edge outside canonical interior
support that is not merely a no-gap boundary slot.  This is a stronger current
classifier/input-surface obstruction, not a repair-independent B1
meta-barrier.  Verification: focused `CAP5RoutePayoff` build SHA256
`baf83bc864536339ace652630fe76b3e599db14aa5f3d291ab6b9340a4d72732`;
focused `CAP5GP12RouteData` build SHA256
`693bd616b3420f260a081b7dfc12cace892414788ffdc5b5a3e449b37bddbfa2`;
FourColor umbrella build SHA256
`6423fcb114a3354125db4ce80e2a57eef6a5b4db6246f4b1758923f5fa2fe00e`;
axiom audit driver/log SHA256
`7f081459a669e1d1e34925a146d0237555f67c491209ae962f4cf0f726515382` /
`ac507e5c9c1061c160d3d7758765dbe4c49aa1e6f180da0d546e320d89bd2049`,
baseline `[propext, Classical.choice, Quot.sound]`.
The local side-cycle version is now checked too:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_sideCycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`
need only the Gate-1 selected-side cycle itself to be covered by canonical
interior support or the five CAP5 boundary slots.  This is the six-cut
checkpoint status: the generic six-cut meta-barrier is not proven.  The
evidence is finite plus current classifier/input-surface Lean obstruction; the
non-boundary six-cut degree of freedom remains honestly open.  Verification:
focused `CAP5RoutePayoff` build SHA256
`9f93d299da21e27eb3492abfdd0312b1c96ced1475b2994989638ae5917032f5`;
focused `CAP5GP12RouteData` build SHA256
`b6e618c3603acc54be5a54deed1bfd502c196ba8e62216e4f416951191968069`;
FourColor umbrella build SHA256
`ce461cfe7aa93c85d50a752bf7d19405286fc8474c3d3fcb1aaf2140ee13a8e5`;
axiom audit driver/log SHA256
`252079c06d2416bd393f457ab8b57be8b5211106658a5bc721b1bcb3b8ad733e` /
`3ecc5bc92ce68601cf1b945fb15ce54f45bc2f9e00ce5138be4973d1121de5c0`,
baseline `[propext, Classical.choice, Quot.sound]`.
The obstruction is now also available from one explicit covered cycle, not
only from the particular Gate-1 cycle returned by the no-gap package:
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`
and
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_cycle_edges_subset_interiorEdgeSupport_or_boundaryEdge`.
Thus a current-surface survivor must avoid even a single side-contained cycle
whose edges lie in canonical interior support or among the five CAP5 boundary
slots; every selected-side cycle must use some non-interior non-boundary-slot
edge.  This still does not prove the generic six-cut meta-barrier, but it
narrows the non-boundary DOF to an explicit graph-side cycle-escape condition.
Verification: focused `CAP5RoutePayoff` build SHA256
`d18b4d66459dd04dfcbda08c9aef4279530ded9a05b5242eb2fa3cfc39de365d`;
focused `CAP5GP12RouteData` build SHA256
`98a2ec8a3513ce8348aeacd3f96fe7f8b6907a51365476956f12d52588eb6a38`;
FourColor umbrella build SHA256
`6e72fb11a40bb6894da320174c0b887e40b60c1d589b2e5dec5821bd5207dd4e`;
axiom audit driver/log SHA256
`9025abf124771a09382dd56560a9a83e4c17d2d63410ca45754d2d4720d75cc4` /
`ba6559862ad00a3993086afa49144ff51b919c3759aeb4f35b3e0fdb06dae284`,
baseline `[propext, Classical.choice, Quot.sound]`.
The finite dodeca audit
`fourcolor-dodeca-explicit-covered-cycle-audit-20260629.json` then checks this
condition against the archived strict and one-face-punctured dodecahedral
six-cut rows.  It finds all 4 closed strict sidecases have a covered side
cycle.  Among the 48 punctured rows, 24 have a covered side cycle and 24 escape
because the omitted face is one of faces `0..5`, so the archived
selected-side pentagon uses a non-interior non-boundary-slot edge.  All 48
punctured rows, including the 24 escape rows, remain invalid route inputs by
projected-generator membership failure.  Audit SHA256
`fd1b7ce900538396200206b66dee682f63c56b4002cd1550442977e5e46ef734`.
The side-bipartition audit of the archived known/generalized-Petersen sweep
through 24 vertices gives finite evidence for why the current surface keeps
stalling: among cyclic-five/Tait route-relevant Kempe-formable embeddings, the
only graph is `generalized_petersen_12_2`, with 15 closed/punctured embeddings,
and all 15 have non-bipartite canonical interior support.  Even the cyclic-five
full-Tait upper-bound formable embeddings have zero bipartite-interior
survivors.  Evidence:
`fourcolor-small-cubic-formability-bipartite-interior-audit-20260629.log`
SHA256 `5e654ecb29cb59261e74d28269a4f73e130e8d9b267b7c3bc74b1ba010d3faaa`;
source sweep SHA256
`06ac2ac0ba4626119c6bbce7396a79974bdf81bc35402d1d33e5e8a3882bd1c6`.
Scope: this is still a finite audit, not the required generic meta-barrier.
The older archive artifacts with apparent route-case verdicts were also
validity-audited before promotion: `spoke-cut-prism-6` is Tait/cubic and had an
old all-MAKE lab abstraction, but fails cyclic-five via nine size-four cyclic
cuts; `split-chained-diamonds` is Tait-colorable under backtracking and had an
old all-BREAK abstraction, but it is disconnected and not connected cubic
3-regular.  Evidence:
`fourcolor-valid-cap5-archive-candidate-validity-audit-20260629.json` SHA256
`3ab3a792466d092d81af761b5c841e7138b241b01880a25b6e0f9b2ff5edc3c6`.
Neither is an objective-A valid CAP5/Tait/cyclic-five input.

The current-surface obstruction also now separates active portal edges from
emitted forced edges.  The theorem
`CAP5FiniteNoGapRouteInput.not_noUnifiedKernelMapEvader_of_activePortal_interiorEdgeSupport`
proves that if a sidecase-active portal boundary edge lies in canonical
interior support, then it cannot be emitted by the finite forced-edge
classifier and therefore gives a unified kernel-map evader.  The route-closed
form
`CAP5FiniteNoGapRouteInput.not_routeClosed_of_activePortal_interiorEdgeSupport`
uses the usual exceptional/cyclic no-evader equivalence to rule out
`CAP5F2RouteClosed` from the same hypothesis.  Focused `CAP5RoutePayoff`
build SHA256
`582e5065827594125f1da8bd6a68be437d42fbc5a503569c46ed26c357a4a760`.
This is a current finite classifier/input-surface theorem, not a claim about
all possible repaired route encodings.

To avoid hiding an annular repair gap, a new two-face annulus audit checked the
known NetworkX cubic planar/Tait/cyclic-five graphs through 24 vertices, all
two-face omissions, and all five-edge cyclic two-component cuts.  It found
three graph families in scope (`dodecahedral`, `generalized_petersen_10_2`,
and `generalized_petersen_12_2`), 223 annular surface rows of interest, 223
full-Tait formable annular upper-bound surfaces, 91 Kempe-formable annular
surfaces, zero side-bipartition-valid side rows, and zero side rows that could
fit any sidecase emitted portal-complement under any ordering of the five
boundary edges.  Evidence:
`fourcolor-two-face-annulus-current-surface-audit-20260629.json` SHA256
`1016cde08d7f2aec705488118bf7c12ee714290b24a6a54328f8970073266077`;
run log SHA256
`2efd5b38fb16788a4d6edcc7148af1d8dbc258fcb8805dbcddbccdd4ae5afc4b`.
This widens the finite evidence to legitimate two-boundary annular embeddings,
but it is still not the B1 generic repair-robust meta-barrier.
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

Boundary-cycle Gate-1 repair audit: the lab
`fourcolor-dodeca-boundary-cycle-gate1-lab-20260629.json` checks the natural
repair of the dodecahedral candidate where each pentagonal face, rather than a
five-of-six cut support, is used as the five CAP5 boundary edges.  It enumerates
all `2^20` vertex-side masks for all 12 pentagonal faces and finds zero masks
crossing all five boundary edges, hence zero Gate-1 no-gap sides.  The JSON SHA
is `9102525b04fc5c89d91c7cc8d97be4b3afae78681f5f3e7139cf65f14a7045cd`;
the run log SHA is
`eb4178027bf419711a4ade66a7825ade1d0b5c714d2d02364a2556c3281410bd`;
the ignored lab script SHA is
`f56d4cc62d7897245cbfb59be4175b4d4f2fcb89938ebbc8edebf1d704f42a4c`.
Lean promotes the generic reason in `CAP5RouteVerdict.lean`:
`cap5PrimitiveCheckerGap_of_boundaryEdge_odd_closed_walk` says that if the five
boundary edges cover an odd closed walk, no vertex-side cut can cross all of
them, so the primitive checker gap is forced.  `CAP5RoutePayoff.lean` now
packages the finite-input consequence as
`CAP5FiniteNoGapRouteInput.false_of_boundaryEdge_odd_closed_walk` and
`CAP5FiniteRouteClosedWitness.false_of_boundaryEdge_odd_closed_walk`, ruling
out both the no-gap input and route-closed witness for any such honest odd
boundary.  Scope: this is a genuine Gate-1 barrier for honest odd CAP5
boundary cycles; it does not by itself
refute non-boundary cut-style reformulations.

Geometric table delta: the latest report-level decision theorem reduces the
primitive missing branch to failed portal/cycle prerequisites for the
CAP5/Jordan separator-repair class.  If those prerequisites are present, the
completed report branch is forced-all and the realized exceptional separator is
blocked by the same cyclic-five small-cut obstruction.  The new completed-
prerequisite wrapper
`closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction` packages this
as one fundamental obstruction: no source-bound canonical/one-collar repair,
forced-all report output, and no CAP5/Jordan exceptional cyclic-separator
repair realization under cyclic five-edge-connectivity.

Algebraic-F2 table delta: the latest initial residual closure layer names the
first scheduler obstruction and removes three remaining handoffs.  First,
`residualRemainingControlEdges ... ∅ = ∅` is now proved equivalent to the
empty immutable remaining-control worklist, so an initially empty residual
scheduler closes theorem-4.9 synthesis plus full selected-boundary-zero
classifier control, modulo only the primitive checker gap.  Second, once that
primitive gap is absent, failed synthesis forces the named first residual
obstruction: a genuine selected-boundary-zero evader, a concrete residual edge
where it is nonzero, immutable one-edge processed-control failure, the promoted
one-edge control update, and strict residual decrease.  Third, that named
obstruction now promotes to the unified emitted-kernel/remaining-map evader,
so the first residual scheduler failure is not a separate branch from the
finite F2 rank/map oracle.  Accepting it is accepting a genuine emitted-kernel
evader with nonzero canonical remaining-family map image; excluding the
unified evader closes synthesis/control through the existing no-gap
no-evader theorem, and excluding the named scheduler obstruction still closes
synthesis.  Current Algebraic-F2 estimate is PLN STV `<0.91,0.95>`, ITV
`[0.86,0.91]`, progress `99%`.

Packaged oracle delta: the case-lemma surface is now assembled into
`CAP5TransportedEdgeComponentCoverCore.budgetMetNoEvader_boundaryZeroControl_oracle`.
With the primitive portal/cycle checker gap absent, this single theorem states
that absence of the unified emitted-kernel/remaining-map evader is equivalent
to theorem-4.9 synthesis plus full selected-boundary-zero classifier control;
if that closed result fails, the theorem returns the same precise nonzero
selected-boundary-zero evader with forced-edge vanishing, emitted-kernel
membership, and nonzero canonical remaining-family map image.  The same
existential is now recorded as `CAP5F2UnifiedKernelMapEvader` in
`CAP5RouteVerdict.lean`, so the barrier is no longer an unnamed long formula:
exact CAP5 shell data must prove `CAP5F2NoUnifiedKernelMapEvader` for the
actual closed side, or accept the returned witness as the obstruction.  Current
Algebraic-F2 estimate is PLN STV `<0.95,0.96>`, ITV `[0.91,0.95]`, progress
`100%` for the oracle-packaging layer; exact CAP5 shell data still must supply
the no-evader side or accept the returned evader.

Target/rank decomposition delta: the emitted-rank certificate is now connected
to the theorem-4.9 target fork without going through prose.  Lean proves that
absence of a full selected-boundary-zero evader is equivalent to target
classifier control plus absence of the concrete off-target boundary-vertex
Kirchhoff evader, and therefore that the emitted-edge pairing kernel is trivial
exactly when that target/off-target oracle is closed.  The failure side is now
concrete too: under theorem-4.9 target classifier control, a nontrivial
emitted-edge pairing kernel returns a selected-boundary-zero evader that
vanishes on every enumerated forced edge, lies in the emitted kernel, is
detected by the canonical remaining-family map, and fails Kirchhoff at a named
theorem-4.9 boundary vertex.

Target-controlled rank-decision delta: after theorem-4.9 target classifier
control is assumed, the finite emitted-edge rank certificate is now exactly
the absence of that off-target boundary-vertex Kirchhoff evader.  Lean also
packages the binary decision form: either the emitted-edge kernel closes, or
the returned witness carries forced-edge vanishing, emitted-kernel membership,
nonzero canonical remaining-map image, and the concrete boundary-vertex
Kirchhoff failure.

Unconditional rank-failure split delta: the target-control hypothesis is no
longer needed to interpret emitted-rank failure.  Lean proves that a nontrivial
emitted-edge pairing kernel returns either a nonzero theorem-4.9 target chain
vanishing on every enumerated forced edge, or the off-target selected-boundary-
zero evader with emitted-kernel membership, nonzero canonical remaining-map
image, and a theorem-4.9 boundary-vertex Kirchhoff failure.  The corresponding
decision theorem packages the local finite F2 verdict as kernel close, target
evader, or off-target kernel/map/vertex-failure evader.

Report-level target/off-target rank split delta: the executable CAP5 report now
carries that same split.  Lean proves the report branch is a primitive checker
gap, emitted-rank close with theorem-4.9 synthesis and full selected-boundary-
zero control, a theorem-4.9 target evader vanishing on every enumerated forced
edge, or the off-target emitted-kernel/remaining-map evader with a concrete
boundary-vertex Kirchhoff failure.  Under `¬ Theorem49BoundaryRootSynthesis`,
the emitted-rank close branch is eliminated, leaving only primitive checker gap
or target/off-target evader.

Closed-frontier target/off-target no-evader delta: with the primitive checker
frontier already closed, Lean now proves emitted-rank close plus theorem-4.9
synthesis and full selected-boundary-zero classifier control is equivalent to
the absence of both target-side theorem-4.9 evaders and the concrete
off-target emitted-kernel/remaining-map boundary-vertex Kirchhoff evader.  The
report-level no-evader side is therefore stated in the same target/off-target
vocabulary returned by the failure branch, rather than only through the older
unified-kernel predicate.

Closed-frontier target/off-target rank-certificate delta: Lean now removes the
extra bundled-success wording from that closed frontier.  The emitted-edge
pairing kernel is trivial iff both concrete report evaders are absent;
theorem-4.9 synthesis and full selected-boundary-zero classifier control are recovered
from the same rank certificate.  This makes the finite lab target exactly the
target/off-target no-evader predicate.

Emitted-rank route-close delta: Lean now consumes the lab-facing rank
certificate directly in the report route.  If the emitted-edge pairing kernel
is trivial, the executable report returns only primitive checker gap or
theorem-4.9 synthesis with full selected-boundary-zero classifier control.  If
the primitive checker frontier is closed, the same rank certificate proves
synthesis/control outright.

Report-route target/off-target no-evader conclusion delta: Lean now exposes the
surviving F2 oracle in the direct route form requested by the decide goal.  If
the target-side theorem-4.9 evader and the off-target emitted-kernel/
remaining-map Kirchhoff evader are both absent, the executable CAP5 report
returns either a primitive checker gap or theorem-4.9 synthesis with full
selected-boundary-zero classifier control.  If the primitive checker frontier
is closed too, the no-evader hypotheses directly prove synthesis/control.

Trace-F2 delta: the same report-closed handoff now reaches the stronger
trace-control split.  The executable report returns a primitive checker gap,
or else the closed frontier yields either theorem-4.9 synthesis with full
selected-boundary-zero control or a genuine selected-boundary-zero evader with
a concrete remaining trace edge and nonzero canonical red/blue family pairing.
With `¬ Theorem49BoundaryRootSynthesis`, Lean eliminates the success side and
returns exactly a primitive checker gap or that trace-local evader.
The same failure-only report surface now also returns the lab-facing unified
emitted-kernel/remaining-map evader, carrying emitted-kernel membership and
nonzero canonical remaining-map image.

## Latest Move-1 Evidence

- Focused geometric build archived locally as
  `fourcolor-move1-one-collar-obstruction-focused-build-20260628.log`.
- Dependency replay repair build archived locally as
  `fourcolor-move1-one-collar-obstruction-dependency-build-20260628.log`.
- New Lean theorem surface:
  `not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell`,
  `not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell`, and
  `not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell`.
  These package the shared geometric obstruction: a closed-walk exact shell
  already forces a face with two distinct interior-support edges, while the
  canonical one-collar witness/collar surfaces can carry at most one such edge
  on that face.  This retires the source-bound canonical and one-collar
  positive-collar repair packet family as one structural theorem family,
  rather than as isolated benchmark failures.
- Side-cut focused build archived locally as
  `fourcolor-move1-odd-sidecut-frontier-focused-build-20260628.log`.
- Validation lab JSON archived locally as
  `fourcolor-move1-odd-sidecut-lab-20260628.json`; the rerun contains 65
  benchmark signatures, 65 projected-generator certificate reports, and 80
  rejected counterexample exports, with empty stderr.
- Axiom audit archived locally as
  `fourcolor-move1-odd-sidecut-axiom-audit-20260628.log`; the new theorem
  constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move1-odd-sidecut-full-build-20260628.log` with 5900 jobs.
- New side-cut theorem surface:
  `not_exists_sideCut_crosses_closed_odd_walk_subset`,
  `not_exists_exceptionalAnnulusCrossingOutsideEdge_of_closed_odd_walk_subset`,
  `closedWalkExactShell_oneCollar_and_oddSideCut_obstruction`, and
  `closedWalkExactShell_oneCollar_and_CAP5OddSideCut_obstruction`.
  These package the two-band triangle failure as a general odd-closed-walk
  cyclic-separator obstruction: no single side predicate can make every edge
  in a finite support cross if that support contains an odd closed walk, and
  the CAP5 outside-crossing normal form cannot repair that.
- Repair-removal focused build archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-focused-build-20260629.log`.
- Validation lab JSON archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-lab-20260629.json`; the rerun
  contains 65 benchmark signatures, 65 projected-generator certificate
  reports/files, 80 mined survivor packets, and 80 rejected counterexample
  exports, with empty stderr.
- Axiom audit archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-axiom-audit-20260629.log`; the
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move1-cyclic-repair-obstruction-full-build-20260629.log` with
  5900 jobs.
- New repair-removal theorem surface:
  `CAP5ExceptionalCyclicSeparatorRepairRealization`,
  `not_CAP5ExceptionalCyclicSeparatorRepairRealization_of_cyclicallyFiveEdgeConnected`,
  and
  `closedWalkExactShell_oneCollar_and_CAP5CyclicSeparatorRepair_obstruction`.
  These expose the fundamental small-cut obstruction for the CAP5/Jordan
  exceptional cyclic-separator surface: realizing even one compatible
  exceptional candidate as cyclic-cut data yields a cyclic edge cut of size at
  most four, hence is incompatible with cyclic five-edge-connectivity; the
  wrapper packages this with the exact-shell one-collar/canonical obstruction.
- Residual-classifier focused build archived locally as
  `fourcolor-move1-residual-classifier-focused-build-20260629.log`.
- Validation lab JSON archived locally as
  `fourcolor-move1-residual-classifier-lab-20260629.json`; the rerun contains
  65 benchmark signatures, 65 projected-generator certificate reports/files,
  80 mined survivor packets, and 80 rejected counterexample exports, with
  empty stderr.
- Axiom audit archived locally as
  `fourcolor-move1-residual-classifier-axiom-audit-20260629.log`; the new
  theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- New residual-classifier theorem surface:
  `closedWalkExactShell_oneCollar_and_CAP5GeneratorNode_residualClassifier`
  and
  `closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_residualClassifier`.
  These prove that a generated CAP5 separator node in a cyclically
  five-edge-connected graph cannot hide as a latent repair: it is missing
  primitive checker evidence or emits the outside-crossing edge outside its
  candidate support.  At report level, the 16-latent finite generator forces
  every counterexample latent exactly when the missing-evidence frontier is
  empty; otherwise Lean returns a concrete latent with missing checker
  evidence.  This is still a classifier, not the final Move-1 closure.
- Report-level geometric repair decision focused builds are archived locally as
  `fourcolor-move1-report-decision-focused-build-20260629.log`.
- New report-decision theorem surfaces:
  `CAP5ExceptionalAnnulusGeneratorReport.missingCheckerEvidenceLatents_eq_nil_iff_all_checker_evidence`,
  `CAP5ExceptionalAnnulusGeneratorReport.missingCheckerEvidenceLatents_ne_nil_iff_exists_failed_checker_evidence`,
  and
  `closedWalkExactShell_oneCollar_and_CAP5GeneratorReport_geometricRepairDecision`.
  These prove that the primitive missing branch is exactly failure of the
  portal/cycle prerequisites for the realized CAP5/Jordan separator-repair
  class.  If the primitive frontier is complete, the report is forced-all and
  the completed repair branch is blocked by the cyclic-five small-cut
  obstruction.
- New completed-prerequisite geometric obstruction surface:
  `closedWalkExactShell_CAP5Jordan_fundamentalRepairObstruction`.
  This removes the last report fork from the completed CAP5/Jordan repair
  branch: assuming the primitive missing-evidence frontier is empty, cyclic
  five-edge-connectivity forces all generated latents into the counterexample
  bin and forbids the exceptional cyclic-separator repair realization by the
  single size-at-most-four cyclic-cut obstruction, while the closed-walk shell
  still blocks the source-bound canonical and one-collar repairs by the
  two-interior-edge face obstruction.
- Remaining Move-1 burden: if the route insists that exact shell data supplies
  all primitive portal/cycle prerequisites, prove that handoff explicitly;
  otherwise the CAP5/Jordan geometric repair class is now reduced to failed
  prerequisites or the realized small-cut obstruction.

## Latest Move-2 Evidence

- Lab command archived locally as
  `fourcolor-move2-f2-oracle-validation-lab-20260628.log`.
- JSON snapshot archived locally as
  `fourcolor-move2-f2-oracle-validation-lab-20260628.json`.
- Result summary: 65 records; no top-level all-interior, declared-forced, or
  all-forcing F2 evader flags; crux report keeps the algebraic-F2 implication
  alive and rejects the outside-crossing geometric crux on generated two-band
  annuli.
- Lean theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.forcedEdgeBoundaryTargetCoverage_iff_no_targetEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_no_evader_of_no_missing_finsetControl`.
- Follow-up lab rerun archived locally as
  `fourcolor-move2-interior-frontier-validation-lab-20260628.log`.
- New Lean frontier:
  `CAP5TransportedEdgeComponentCoverCore.interiorSupportForced_synthesis_and_boundaryTargetCoverage`
  and
  `CAP5TransportedEdgeComponentCoverCore.interiorSupportForced_or_remainingEdge`.
  If the closed primitive checker enumerates every ambient interior-support
  edge as forced, synthesis and target coverage follow; otherwise the
  canonical worklist exposes a concrete remaining interior-support edge.
- Empty-worklist lab rerun archived locally as
  `fourcolor-move2-empty-worklist-validation-lab-20260628.log`.
- Executable certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_synthesis_and_targetCoverage`
  and
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_report_synthesis_and_targetCoverage`.
  An empty canonical interior-support worklist plus the closed primitive
  checker report now directly yields synthesis and target coverage.
- Closed-report failure-frontier focused build archived locally as
  `fourcolor-move2-evader-frontier-focused-build-20260628.log`.
- New Lean frontier:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`.
  With an empty executable checker report, failed synthesis now carries both a
  genuine selected-boundary-zero evader for the enumerated forced edges and a
  concrete remaining interior-support edge whose erasure decreases the finite
  worklist.
- Classifier no-evader lab rerun archived locally as
  `fourcolor-move2-classifier-noevader-lab-20260628.json`; exported 65
  projected-generator certificate files and 80 rejected counterexample files.
  In the record signatures, `f2_all_interior_boundary_zero_only_no_evader` and
  `f2_all_interior_boundary_zero_plus_kirchhoff_no_evader` are true on all 65
  records, while the declared-forced variants are true on the 36 records with
  nonempty forcing interior edges.  The algebraic-F2 cruxes
  `forcing_edges_to_f2_all_interior_boundary_zero_control` and
  `forcing_edges_to_f2_all_interior_boundary_zero_kirchhoff_control` still
  survive with support 36 and purified support 18.
- Route-facing classifier theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.enumeratedExceptionalAnnulusForcedEdgeClassifierBoundaryZeroControl_iff_no_boundaryZeroEvader`,
  `CAP5TransportedEdgeComponentCoverCore.enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryTargetClassifierControl_iff_no_targetEvader`.
  These prove that the emitted classifier coordinates control the full
  selected-boundary-zero carrier, any chosen boundary-zero Kirchhoff target, or
  the theorem-4.9 boundary target exactly when no nonzero chain in the
  corresponding carrier evades every enumerated CAP5 forced edge.
- Full boundary-zero no-evader closure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_no_missing_finsetControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl`.
  These are the direct Move-2 no-evader/classifier-controls-boundary-zero step:
  a closed CAP5 checker plus absence of a nonzero selected-boundary-zero evader
  yields theorem-4.9 synthesis and proves that emitted CAP5 coordinates control
  the entire selected-boundary-zero subspace.
- Target-dimension fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_theorem49BoundaryTargetEvader_of_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_lt`
  and
  `CAP5TransportedEdgeComponentCoverCore.edge_card_le_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_of_no_targetEvader`.
  These prove that an underdimensioned classifier produces a genuine nonzero
  `W0(H)` evader, while any no-evader CAP5 classifier must meet the
  boundary-zero plus theorem-4.9 Kirchhoff target dimension lower bound.
- Off-target bridge theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_offTargetBoundaryZeroEvader_of_no_missing_finsetControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.offTargetBoundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`.
  These prove that target classifier control closes the completed checker once
  off-target boundary-zero evaders are excluded, and conversely any failed
  closed checker under target control exposes exactly such an off-target
  evader plus the decreasing interior-support worklist edge.
- Vertex-Kirchhoff failure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget`,
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl`,
  and
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`.
  These refine the off-target branch to a concrete failed Kirchhoff equation at
  a theorem-4.9 boundary vertex: under target classifier control, a failed
  closed checker exposes a forced-edge-vanishing boundary-zero chain with
  nonzero `vertexKirchhoffSum` at that vertex and the decreasing worklist edge.
- Vertex-failure lab rerun archived locally as
  `fourcolor-move2-subset-certificate-lab-20260628.json`; exported 65
  projected-generator certificate files and 80 rejected counterexample files.
  The new
  `f2_all_interior_boundary_zero_kirchhoff_failure_absent` signature is true
  on all 65 records; the crux packet
  `forcing_edges_to_f2_all_interior_boundary_zero_kirchhoff_failure_absent`
  survives with support 36 and purified support 18.  The focus rows still
  expose smaller-control failure witnesses, e.g. single-spoke/single-shared
  controls produce a nonzero theorem-4.9 boundary-vertex Kirchhoff image.
- Row-span/subset certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`,
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl`.
  These make the remaining exact-shell proof obligation a row-span/subset
  certificate: every boundary-zero chain vanishing on the enumerated forced
  edges must lie in the theorem-4.9 boundary target; failure of that certificate
  is already a genuine vertex-Kirchhoff evader.
- Exact F2 fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl_of_no_missing_finsetControl`.
  These package the surviving algebraic oracle as a binary machine-checked
  decision: the subset certificate closes the target-controlled checker, and
  failure of that certificate is already the concrete evader branch.
- Empty-worklist subset-certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty`,
  `CAP5TransportedEdgeComponentCoverCore.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_interiorEdgeSupport_subset_enumeratedForcedEdges`,
  `CAP5TransportedEdgeComponentCoverCore.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty`,
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_remainingInteriorSupportEmpty`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_remainingInteriorSupportEmpty_of_no_missing_finsetControl`.
  These prove the exact subset certificate on the executable empty-worklist
  shell and collapse the binary F2 fork to synthesis plus target coverage under
  target classifier control and a closed checker.
- Odd-worklist focused build archived locally as
  `fourcolor-move2-odd-worklist-focused-build-20260628.log`.
- Odd-interior worklist theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport`
  and
  `CAP5TransportedEdgeComponentCoverCore.not_remainingInteriorSupportEmpty_of_closed_walk_odd_length_in_interiorSupport`.
  These prove that an odd closed walk supported by ambient interior-support
  edges refutes the executable empty-worklist branch for any Boolean CAP5
  forced-edge classifier: some interior-support edge remains unemitted, and
  erasing it strictly decreases the canonical worklist.
- Target-controlled odd-worklist fork focused build archived locally as
  `fourcolor-move2-target-odd-fork-focused-build-20260628.log`.
- Axiom audit archived locally as
  `fourcolor-move2-target-odd-fork-axiom-audit-20260628.log`; the two new
  theorem constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-target-odd-fork-strict-scans-20260628.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-target-odd-fork-full-build-20260628.log` with 5900 jobs.
- Target-controlled odd-worklist lab rerun archived locally as
  `fourcolor-move2-target-odd-fork-lab-20260628.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator
  certificate reports/files, 80 mined survivor packets, and 80 rejected
  counterexample exports.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- New target-controlled executable fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_oddInteriorWorklistEdge_of_closed_walk_odd_length_in_interiorSupport`.
  These consolidate the active F2 route surface: under target classifier
  control and an empty checker report, the executable fork is synthesis plus
  target coverage, or a concrete forced-edge-vanishing boundary-zero evader
  with nonzero theorem-4.9 boundary-vertex Kirchhoff sum and a decreasing
  remaining worklist edge.  If an odd closed walk lies in ambient interior
  support, the same theorem also exposes the remaining worklist edge
  unconditionally, so the exact shell cannot claim the empty-worklist subset
  certificate on that support.
- Empty-worklist no-odd focused build archived locally as
  `fourcolor-move2-empty-worklist-noodd-focused-build-20260628.log`.
- Axiom audit archived locally as
  `fourcolor-move2-empty-worklist-noodd-axiom-audit-20260628.log`; the three
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-empty-worklist-noodd-strict-scans-20260628.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-empty-worklist-noodd-full-build-20260628.log` with 5900
  jobs.
- Empty-worklist no-odd lab rerun archived locally as
  `fourcolor-move2-empty-worklist-noodd-lab-20260628.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate reports/files, 80 mined survivor packets, and 80 rejected
  counterexample exports.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- New success-branch odd-obstruction exclusion theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges`,
  `CAP5TransportedEdgeComponentCoverCore.interiorSupportForced_synthesis_and_boundaryTargetCoverage_and_no_closed_odd_walk`, and
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_synthesis_and_targetCoverage_and_no_closed_odd_walk`.
  These prove that the all-interior forced-edge/subset side excludes the odd
  closed-walk obstruction directly: if every ambient interior-support edge is
  enumerated as forced, there is no odd closed walk in ambient interior support.
  Consequently an empty canonical interior-support worklist reaches synthesis
  plus target coverage and simultaneously certifies that the odd-interior
  worklist obstruction is absent.
- New odd-interior no-evader closure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_and_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`.
  This proves that an odd closed walk can still leave the canonical
  interior-support worklist nonempty while the target-controlled no-evader
  branch closes theorem-4.9 synthesis and target coverage.  Therefore the odd
  worklist is only a measure/witness obstruction to the empty-worklist proof
  path, not a substitute for the genuine vertex-Kirchhoff evader branch.
- Report-forced-all lab rerun archived locally as
  `fourcolor-move2-report-forcedall-lab-20260629.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator certificate
  files, and 80 rejected counterexample exports.  The all-interior no-evader
  and vertex-Kirchhoff-failure-absent signatures are true on all 65 records;
  the declared-forced variants are true on the 36 forcing records.
- Report-forced-all focused detector build archived locally as
  `fourcolor-move2-report-forcedall-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-report-forcedall-axiom-audit-20260629.log`; the three new
  theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-report-forcedall-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-forcedall-full-build-20260629.log` with 5900 jobs.
- New report-forced-all theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_noEvader_of_forcedAllLatents`,
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorEmpty_synthesis_and_targetCoverage_of_forcedAllLatents`, and
  `CAP5TransportedEdgeComponentCoverCore.targetControlledSynthesis_or_evader_of_forcedAllLatents`.
  These replace the raw executable premise `missingCheckerEvidenceLatents = []`
  with the report verdict `forcedCounterexampleLatents = all`: if the
  generator forces all 16 latents under cyclic five-edge-connectivity, the
  branch feeds directly into the full selected-boundary-zero no-evader closure,
  the empty-worklist subset-certificate closure, or the target-controlled
  synthesis-versus-genuine-vertex-Kirchhoff-evader fork.
- Forced-all evader-fork lab rerun archived locally as
  `fourcolor-move2-forcedall-evaderfork-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Forced-all evader-fork focused detector build archived locally as
  `fourcolor-move2-forcedall-evaderfork-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-evaderfork-axiom-audit-20260629.log`; the two new
  theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-evaderfork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-evaderfork-full-build-20260629.log` with 5900
  jobs.
- New forced-all fork-half theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.targetControlledSynthesis_of_noEvader_of_forcedAllLatents`
  and
  `CAP5TransportedEdgeComponentCoverCore.targetControlledEvader_of_notSynthesis_of_forcedAllLatents`.
  These remove the last ambiguity in the report-forced-all target-controlled
  interface: under target classifier control, absence of the concrete
  theorem-4.9 boundary-vertex Kirchhoff evader proves synthesis plus target
  coverage, while failed synthesis proves the evader exists and carries a
  decreasing remaining-worklist edge.  This is an interface decision, not yet
  the exact-shell proof of the no-evader/subset side.
- Forced-all payload-fork lab rerun archived locally as
  `fourcolor-move2-forcedall-payloadfork-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Forced-all payload-fork focused detector build archived locally as
  `fourcolor-move2-forcedall-payloadfork-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-payloadfork-axiom-audit-20260629.log`; the two
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-payloadfork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-payloadfork-full-build-20260629.log` with 5900
  jobs.
- New forced-all canonical payload theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.canonicalPayloadEvader_of_notSynthesis_of_forcedAllLatents`
  and
  `CAP5TransportedEdgeComponentCoverCore.synthesis_or_canonicalPayloadEvader_of_forcedAllLatents`.
  These sharpen the forced-all failure side from an existential evader into
  the finite path-xor artifact the lab is meant to return: detector payload,
  boundary-zero chain, non-forced remaining interior edge with nonzero chain
  value, strict worklist decrease, and nonzero canonical red/blue family
  pairing.  This still leaves the exact-shell no-evader/subset derivation open.
- Forced-all pure-evader lab rerun archived locally as
  `fourcolor-move2-forcedall-pureevader-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Forced-all pure-evader focused detector build archived locally as
  `fourcolor-move2-forcedall-pureevader-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-pureevader-axiom-audit-20260629.log`; the two
  new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-pureevader-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-pureevader-full-build-20260629.log` with 5900
  jobs.
- New forced-all pure-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_notSynthesis_of_forcedAllLatents`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`.
  These state the F2 fork at the no-target level: once the report forces all
  latents, failed synthesis is already a genuine selected-boundary-zero evader
  for the enumerated forced edges, with the decreasing worklist edge attached.
  Target-control and canonical payload theorems are now refinements of this
  pure evader branch.
- Forced-all oracle-fork focused detector build archived locally as
  `fourcolor-move2-forcedall-oraclefork-focused-build-20260629.log`.
- Forced-all oracle-fork lab rerun archived locally as
  `fourcolor-move2-forcedall-oraclefork-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-oraclefork-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-oraclefork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-oraclefork-full-build-20260629.log` with 5900
  jobs.
- New forced-all oracle theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroEvader_of_forcedAllLatents`.
  This packages the F2 oracle itself: under the executable forced-all report,
  either no-evader closes theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control, or there is a concrete nonzero selected-boundary-zero
  evader for the enumerated forced edges.  The exact-shell task remains to
  prove which side uniform CAP5/Jordan shell data supplies.
- Empty-worklist no-evader lab rerun archived locally as
  `fourcolor-move2-emptyworklist-noevader-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Empty-worklist no-evader focused detector build archived locally as
  `fourcolor-move2-emptyworklist-noevader-focused-build-20260629.log`.
- Axiom audit archived locally as
  `fourcolor-move2-emptyworklist-noevader-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-emptyworklist-noevader-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-emptyworklist-noevader-full-build-20260629.log` with 5900
  jobs.
- New empty-worklist no-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents`.
  This upgrades the forced-all empty-worklist/subset certificate: empty
  canonical interior-support worklist now proves the actual no-evader verdict,
  theorem-4.9 synthesis, and full selected-boundary-zero classifier control.
  The remaining algebraic task is to prove uniform exact CAP5/Jordan shell data
  reaches this empty-worklist branch, or to formalize the evader/worklist
  alternative.
- Forced-all scheduler focused detector build archived locally as
  `fourcolor-move2-forcedall-scheduler-focused-build-20260629.log`.
- Forced-all scheduler lab rerun archived locally as
  `fourcolor-move2-forcedall-scheduler-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-scheduler-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-scheduler-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-scheduler-full-build-20260629.log` with 5900
  jobs.
- New forced-all scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_or_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_forcedAllLatents`.
  This packages the residual finite obligation after the executable forced-all
  report: either the empty canonical interior-support worklist gives
  no-evader/synthesis/full-control, or a concrete remaining interior-support
  edge is available with strict erasure decrease.  Uniform exact shell data now
  has to prove the left side or use the returned edge to drive the scheduler.
- Forced-all residual-scheduler focused detector build archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-focused-build-20260629.log`.
- Forced-all residual-scheduler lab rerun archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-lab-20260629.json`; stderr is
  empty, and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-residual-scheduler-full-build-20260629.log` with
  5900 jobs.
- New forced-all residual-scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlTraceEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_finsetControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_forcedAllResidualSchedulerPayloadEvader_of_forcedAllLatents`.
  These strengthen the failure side from a bare remaining-edge erasure witness
  into a processed-state scheduler payload: complete `(0, 0, 16)` checker
  histogram, forced-bin detector, selected-boundary-zero evader, traced
  remaining interior-support edge, residual-worklist membership, strict
  residual decrease after `insert e processed`, strict canonical erasure
  decrease, and nonzero canonical red/blue family pairing.
- Forced-all residual-transition focused detector build archived locally as
  `fourcolor-move2-forcedall-residual-transition-focused-build-20260629.log`.
- Forced-all residual-transition lab rerun archived locally as
  `fourcolor-move2-forcedall-residual-transition-lab-20260629.json`; stderr is
  empty, and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, and 80 rejected counterexample exports.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced variants are true on the 36
  forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-forcedall-residual-transition-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-forcedall-residual-transition-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-forcedall-residual-transition-full-build-20260629.log` with
  5900 jobs.
- New forced-all residual-transition theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_or_forcedAllResidualSchedulerTransitionEvader_of_forcedAllLatents_of_processedControl`.
  This strengthens the scheduler failure branch again: under a processed-edge
  zero invariant, failed synthesis returns the same selected-boundary-zero
  evader and residual decrease, plus a proof that the selected edge is not
  controlled by the immutable classifier output and the exact one-edge
  emitted/control update needed to insert it into the processed state.
- Terminal residual scheduler focused detector build archived locally as
  `fourcolor-move2-residual-terminal-focused-build-20260629.log`.
- Terminal residual scheduler lab rerun archived locally as
  `fourcolor-move2-residual-terminal-lab-20260629.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator certificate
  files, and 80 rejected counterexample exports.  The all-interior no-evader
  and vertex-Kirchhoff-failure-absent signatures are true on all 65 records;
  the declared-forced variants are true on the 36 forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-residual-terminal-axiom-audit-20260629.log`; the two new
  theorem constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-residual-terminal-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-residual-terminal-full-build-20260629.log` with 5900 jobs.
- New terminal residual scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_of_residualRemainingInteriorSupportEmpty_of_processedControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.residualRemainingInteriorEmpty_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents_of_processedControl`.
  These close the success endpoint for the finite scheduler: residual
  exhaustion plus the processed-control invariant proves no selected-boundary-zero
  evader exists, and under the forced-all report yields theorem-4.9 synthesis
  with full selected-boundary-zero classifier control.
- Failed-terminal scheduler focused detector build archived locally as
  `fourcolor-move2-failed-terminal-step-focused-build-20260629.log`.
- Failed-terminal scheduler lab rerun archived locally as
  `fourcolor-move2-failed-terminal-step-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, 80 rejected counterexample exports, 80 mined rejections,
  and 80 mined survivors.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-failed-terminal-step-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-failed-terminal-step-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-failed-terminal-step-full-build-20260629.log` with 5900
  jobs.
- New failed-terminal scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_residualSchedulerStep_of_notSynthesis_of_forcedAllLatents_of_processedControl`.
  This combines the terminal theorem and the residual transition into the
  decision form needed by the scheduler: under forced-all and the
  processed-control invariant, failed synthesis implies the residual worklist
  is nonempty and returns a genuine selected-boundary-zero evader, the next
  residual edge, proof that the edge is not controlled by the immutable
  classifier output, the one-edge emitted/control update, and strict residual
  decrease.
- Immutable-scheduler obstruction focused detector build archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-focused-build-20260629.log`.
- Immutable-scheduler obstruction lab rerun archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-lab-20260629.json`; stderr
  is empty, and the run contains 65 benchmark signatures, 65
  projected-generator certificate files, 80 rejected counterexample exports,
  80 mined rejections, and 80 mined survivors.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- Axiom audit archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-immutable-scheduler-obstruction-full-build-20260629.log`
  with 5900 jobs.
- New immutable-scheduler obstruction theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_and_immutableProcessedControlObstruction_of_notSynthesis_of_forcedAllLatents_of_processedControl`.
  This lifts the lower-level immutable-processed obstruction to the
  route-facing forced-all branch: the residual edge returned by failed
  synthesis cannot be inserted into `processed` using the original classifier
  output.  The scheduler must add the one-edge emitted/control update or keep
  the evading boundary-zero chain as the genuine obstruction.
- Residual scheduler route-decision focused detector build archived locally as
  `fourcolor-move2-residual-scheduler-route-decision-focused-build-20260629.log`.
- Residual scheduler route-decision lab rerun archived locally as
  `fourcolor-move2-residual-scheduler-route-decision-lab-20260629.json`;
  stderr is empty, and the run contains 65 benchmark signatures, 65
  projected-generator certificate files, 80 rejected counterexample exports,
  80 mined rejections, and 80 mined survivors.  The all-interior no-evader and
  vertex-Kirchhoff-failure-absent signatures are true on all 65 records; the
  declared-forced variants are true on the 36 forcing records.
- New residual scheduler route-decision theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.residualSchedulerTerminalNoEvader_or_synthesis_or_immutableProcessedControlObstruction_of_forcedAllLatents_of_processedControl`.
  This packages the finite scheduler state: terminal residual exhaustion closes
  no-evader/synthesis/control, synthesis may already be closed before terminal
  exhaustion, and the remaining branch returns a genuine evader plus the next
  promoted edge with immutable processing ruled out and strict residual
  decrease.
- Terminal-coverage scheduler focused detector build archived locally as
  `fourcolor-move2-terminal-coverage-focused-build-20260629.log`.
- Terminal-coverage scheduler lab rerun archived locally as
  `fourcolor-move2-terminal-coverage-lab-20260629.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator certificate
  files, 80 mined rejections, and 80 mined survivors.  The all-interior
  no-evader and vertex-Kirchhoff-failure-absent signatures are true on all 65
  records; the declared-forced boundary-zero variants are true on the 38
  declared-forced rows in this run.
- Axiom audit archived locally as
  `fourcolor-move2-terminal-coverage-axiom-audit-20260629.log`; the two new
  theorem constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-terminal-coverage-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-terminal-coverage-full-build-20260629.log` with 5900 jobs.
- New terminal-coverage scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportCovered_noEvader_and_synthesis_and_boundaryZeroControl_of_forcedAllLatents_of_processedControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.residualSchedulerCoverageNoEvader_or_synthesis_or_immutableProcessedControlObstruction_of_forcedAllLatents_of_processedControl`.
  These restate the scheduler success and route-decision endpoints using the
  semantic invariant that `processed` covers every original remaining control
  edge, rather than the implementation detail that the residual finset is
  empty.  This keeps the promoted finite scheduler focused on the real
  invariant: prove coverage and close no-evader/synthesis/control, or accept
  the genuine evader plus promoted-edge obstruction returned by the route.
  Current Algebraic-F2 estimate: PLN STV `<0.69,0.84>`, ITV `[0.58,0.74]`,
  progress `93%`.
- Trace-control fork focused detector build archived locally as
  `fourcolor-move2-trace-control-fork-focused-build-20260629.log`.
- Trace-control fork lab rerun archived locally as
  `fourcolor-move2-trace-control-fork-lab-20260629.json`; stderr is empty, and
  the run contains 65 benchmark signatures, 65 projected-generator certificate
  files, 80 mined rejections, and 80 mined survivors.  The all-interior
  no-evader and vertex-Kirchhoff-failure-absent signatures are true on all 65
  records; the declared-forced boundary-zero variants are true on the 38
  declared-forced rows in this run.
- Axiom audit archived locally as
  `fourcolor-move2-trace-control-fork-axiom-audit-20260629.log`; the three new
  theorem constants depend only on `[propext, Classical.choice, Quot.sound]`.
- Strict diff/proof-marker/leak scans archived locally as
  `fourcolor-move2-trace-control-fork-strict-scans-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-trace-control-fork-full-build-20260629.log` with 5900 jobs.
- New trace-control F2 theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportTraceControl_iff_no_boundaryZeroEvader`,
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroTraceEvader_of_not_remainingInteriorSupportTraceControl`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroTraceEvader_of_forcedAllLatents`.
  These make the finite scheduler's algebraic fork exact: canonical
  remaining-interior trace-control is equivalent to no selected-boundary-zero
  evader, and under the forced-all report the route either closes theorem-4.9
  synthesis plus full selected-boundary-zero classifier control or returns a
  genuine evader together with a concrete trace edge where it is nonzero.
  Current Algebraic-F2 estimate: PLN STV `<0.70,0.85>`, ITV `[0.60,0.75]`,
  progress `94%`.
- Trace-pairing obstruction focused detector build archived locally as
  `fourcolor-move2-trace-pairing-obstruction-focused-build-20260629.log`.
- Trace-pairing obstruction lab rerun archived locally as
  `fourcolor-move2-trace-pairing-obstruction-lab-20260629.json`; stderr is
  empty, and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, 80 mined rejections, and 80 mined survivors.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced boundary-zero variants are true
  on the 38 declared-forced rows in this run.
- Axiom audit archived locally as
  `fourcolor-move2-trace-pairing-obstruction-axiom-audit-20260629.log`; the two
  new theorem constants depend only on `[propext, Classical.choice,
  Quot.sound]`.
- New trace-pairing obstruction theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroTraceEvader_and_canonicalFamilyPairing_ne_zero_of_not_remainingInteriorSupportTraceControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroTraceEvader_canonicalFamilyPairing_ne_zero_of_forcedAllLatents`.
  These strengthen the exact trace-control fork: failure of trace-control now
  returns a genuine selected-boundary-zero evader, a concrete canonical
  remaining trace edge where it is nonzero, proof that the same edge is in the
  canonical remaining-control worklist, and a nonzero pairing against the
  canonical red/blue single-coordinate family generated by the remaining-edge
  certificates.  Current Algebraic-F2 estimate: PLN STV `<0.71,0.85>`, ITV
  `[0.60,0.75]`, progress `95%`.
- Remaining-family map oracle focused detector build archived locally as
  `fourcolor-move2-remaining-family-map-oracle-focused-build-20260629.log`.
- Remaining-family map oracle lab rerun archived locally as
  `fourcolor-move2-remaining-family-map-oracle-lab-20260629.json`; stderr is
  empty, and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, 80 mined rejections, and 80 mined survivors.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced boundary-zero variants are true
  on the 38 declared-forced rows in this run.
- Axiom audit archived locally as
  `fourcolor-move2-remaining-family-map-oracle-axiom-audit-20260629.log`; the
  three new theorem constants depend only on `[propext, Classical.choice,
  Quot.sound]`.
- New remaining-family map oracle theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.boundaryZeroEvader_remainingControlFamilyPairingMap_ne_zero`,
  `CAP5TransportedEdgeComponentCoverCore.eq_zero_of_emittedFinset_vanishes_and_remainingControlFamilyPairingMap_eq_zero`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_remainingControlFamilyPairingMapEvader_of_forcedAllLatents`.
  These prove that every genuine selected-boundary-zero evader has nonzero
  image under the canonical remaining-edge family-pairing map, while emitted
  classifier zeros plus zero image under that map force the boundary-zero chain
  to vanish.  Under the forced-all report, no map-detected evader is therefore
  enough to close theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control.  Current Algebraic-F2 estimate: PLN STV `<0.72,0.86>`,
  ITV `[0.62,0.76]`, progress `96%`.
- Exact map-oracle split focused detector build archived locally as
  `fourcolor-move2-map-oracle-exact-split-focused-build-20260629.log`.
- Exact map-oracle split lab rerun archived locally as
  `fourcolor-move2-map-oracle-exact-split-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, 80 mined rejections, and 80 mined survivors.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced boundary-zero variants are true
  on the 38 declared-forced rows in this run.
- Axiom audit archived locally as
  `fourcolor-move2-map-oracle-exact-split-axiom-audit-20260629.log`; the two
  new theorem constants depend only on `[propext, Classical.choice,
  Quot.sound]`.
- New exact map-oracle split theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_remainingControlFamilyPairingMapEvader_iff_no_boundaryZeroEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_remainingControlFamilyPairingMapEvader_of_forcedAllLatents`.
  These prove that absence of a map-detected evader is exactly absence of a
  selected-boundary-zero evader, and package the forced-all route as a binary
  split: theorem-4.9 synthesis plus full selected-boundary-zero classifier
  control, or a concrete nonzero selected-boundary-zero chain whose image under
  the canonical remaining-edge family-pairing map is nonzero.  Current
  Algebraic-F2 estimate: PLN STV `<0.73,0.86>`, ITV `[0.63,0.76]`, progress
  `97%`.
- Emitted-kernel bridge focused detector build archived locally as
  `fourcolor-move2-emitted-kernel-bridge-focused-build-20260629.log`.
- Emitted-kernel bridge lab rerun archived locally as
  `fourcolor-move2-emitted-kernel-bridge-lab-20260629.json`; stderr is empty,
  and the run contains 65 benchmark signatures, 65 projected-generator
  certificate files, 80 mined rejections, and 80 mined survivors.  The
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures are
  true on all 65 records; the declared-forced boundary-zero variants are true
  on the 38 declared-forced rows in this run.
- Emitted-kernel bridge axiom audit archived locally as
  `fourcolor-move2-emitted-kernel-bridge-axiom-audit-20260629.log`; the three
  new theorem constants depend only on `[propext, Classical.choice,
  Quot.sound]`.
- Strict proof-marker/leak/diff scans archived locally as
  `fourcolor-move2-emitted-kernel-bridge-strict-scans-20260629.log`.
- Full build rerun archived locally as
  `fourcolor-move2-emitted-kernel-bridge-full-build-rerun2-20260629.log`; it
  completed `lake -f lakefile.lean build Mettapedia` with 5900 jobs.  Two
  earlier full-build attempts in this checkpoint exposed stale external-package
  `.olean` prerequisites and were superseded by this green rerun.
- New emitted-kernel theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_no_boundaryZeroEvader`,
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_emittedFinsetPairingKernel_eq_bot_of_forcedAllLatents`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_emittedFinsetKernelEvader_of_forcedAllLatents`.
  These connect the lab-facing finite rank certificate to the route directly:
  the canonical red/blue pairing kernel on the immutable emitted forced-edge
  coordinates is trivial iff there is no nonzero selected-boundary-zero chain
  vanishing on every enumerated forced edge.  Under the forced-all report that
  kernel certificate closes theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control; failure returns a concrete nonzero selected-boundary-zero
  kernel witness vanishing on every enumerated forced edge.  Current
  Algebraic-F2 estimate: PLN STV `<0.74,0.87>`, ITV `[0.64,0.77]`, progress
  `98%`.
- Emitted-kernel/map equivalence focused detector build archived locally as
  `fourcolor-move2-emitted-kernel-map-equivalence-focused-build-20260629.log`.
- Emitted-kernel/map equivalence lab rerun archived locally as
  `fourcolor-move2-emitted-kernel-map-equivalence-lab-20260629.json`; stderr
  is empty.  The rerun contains 65 benchmark records, 65 projected-generator
  certificate records, and the same no-evader/vertex-Kirchhoff-failure-absent
  signatures as the emitted-kernel bridge run.
- Emitted-kernel/map equivalence axiom audit archived locally as
  `fourcolor-move2-emitted-kernel-map-equivalence-axiom-audit-20260629.log`;
  the two new theorem constants depend only on `[propext, Classical.choice,
  Quot.sound]`.
- Strict proof-marker/leak/diff scans archived locally as
  `fourcolor-move2-emitted-kernel-map-equivalence-strict-scans-20260629.log`.
- Full build archived locally as
  `fourcolor-move2-emitted-kernel-map-equivalence-full-build-20260629.log`;
  it completed `lake -f lakefile.lean build Mettapedia` with 5900 jobs.
- New emitted-kernel/map theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetKernelEvader_iff_remainingControlFamilyPairingMapEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_or_emittedFinsetKernelMapEvader_of_forcedAllLatents`.
  These prove that the emitted-kernel obstruction and remaining-family map
  obstruction are the same genuine selected-boundary-zero evader.  Under the
  forced-all report, the rank-check fork now returns synthesis/control or one
  concrete nonzero chain carrying both emitted-kernel membership and nonzero
  remaining-map image.  Current Algebraic-F2 estimate: PLN STV `<0.75,0.88>`,
  ITV `[0.66,0.78]`, progress `99%`.
- Failed-synthesis kernel/map evader focused detector build archived locally as
  `fourcolor-move2-not-synthesis-kernel-map-evader-focused-build-20260629.log`.
- Failed-synthesis kernel/map evader lab rerun archived locally as
  `fourcolor-move2-not-synthesis-kernel-map-evader-lab-20260629.json`; stderr
  is empty.  The rerun contains 65 benchmark records, 65 projected-generator
  certificate records, 80 mined survivors, and 80 rejected candidates; the
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures remain
  true on all 65 records, with declared-forced signatures true on the 38
  eligible rows.
- Failed-synthesis kernel/map evader axiom audit archived locally as
  `fourcolor-move2-not-synthesis-kernel-map-evader-axiom-audit-20260629.log`;
  the new theorem constant depends only on `[propext, Classical.choice,
  Quot.sound]`.
- Strict proof-marker/leak/diff scans archived locally as
  `fourcolor-move2-not-synthesis-kernel-map-evader-strict-scans-20260629.log`.
- Full build archived locally as
  `fourcolor-move2-not-synthesis-kernel-map-evader-full-build-20260629.log`;
  it completed `lake -f lakefile.lean build Mettapedia` with 5900 jobs.
- New failed-synthesis theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetKernelMapEvader_of_notSynthesis_of_forcedAllLatents`.
  This removes the success side from the forced-all rank fork under
  `¬ Theorem49BoundaryRootSynthesis`: failed synthesis now directly returns a
  genuine selected-boundary-zero evader carrying emitted-kernel membership and
  nonzero remaining-family map image.  Current Algebraic-F2 estimate: PLN STV
  `<0.76,0.89>`, ITV `[0.68,0.79]`, progress `99%`.
- Kernel/map oracle iff focused detector build archived locally as
  `fourcolor-move2-kernel-map-oracle-iff-focused-build-20260629.log`.
- Kernel/map oracle iff lab rerun archived locally as
  `fourcolor-move2-kernel-map-oracle-iff-lab-20260629.json`; stderr is empty.
  The rerun contains 65 benchmark records, 65 projected-generator certificate
  records, 80 mined survivors, and 80 rejected candidates; the all-interior
  no-evader and vertex-Kirchhoff-failure-absent signatures remain true on all
  65 records, with declared-forced signatures true on the 38 eligible rows.
- Kernel/map oracle iff axiom audit archived locally as
  `fourcolor-move2-kernel-map-oracle-iff-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict proof-marker/leak/diff scans archived locally as
  `fourcolor-move2-kernel-map-oracle-iff-strict-scans-20260629.log`.
- Full build archived locally as
  `fourcolor-move2-kernel-map-oracle-iff-full-build-20260629.log`; it completed
  `lake -f lakefile.lean build Mettapedia` with 5900 jobs.
- New exact kernel/map oracle theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_emittedFinsetKernelMapEvader_iff_theorem49Synthesis_and_boundaryZeroControl_of_forcedAllLatents`.
  Under the forced-all report, absence of the unified finite F2 evader is now
  equivalent to theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control.  Current Algebraic-F2 estimate: PLN STV `<0.77,0.90>`,
  ITV `[0.69,0.79]`, progress `99%`.
- Emitted-rank oracle iff focused detector build archived locally as
  `fourcolor-move2-emitted-rank-oracle-iff-focused-build-20260629.log`.
- Emitted-rank oracle iff lab rerun archived locally as
  `fourcolor-move2-emitted-rank-oracle-iff-lab-20260629.json`; stderr is
  empty.  The rerun contains 65 benchmark records, 65 projected-generator
  certificate records, 80 mined survivors, and 80 rejected candidates; the
  all-interior no-evader and vertex-Kirchhoff-failure-absent signatures remain
  true on all 65 records, with declared-forced signatures true on the 38
  eligible rows.
- Emitted-rank oracle iff axiom audit archived locally as
  `fourcolor-move2-emitted-rank-oracle-iff-axiom-audit-20260629.log`; the new
  theorem constant depends only on `[propext, Classical.choice, Quot.sound]`.
- Strict proof-marker/leak/diff scans archived locally as
  `fourcolor-move2-emitted-rank-oracle-iff-strict-scans-20260629.log`.
- Full build archived locally as
  `fourcolor-move2-emitted-rank-oracle-iff-full-build-20260629.log`; it
  completed `lake -f lakefile.lean build Mettapedia` with 5900 jobs.
- New exact emitted-rank oracle theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_theorem49Synthesis_and_boundaryZeroControl_of_forcedAllLatents`.
  Under the forced-all report, the finite F2 emitted-edge pairing kernel is
  trivial iff theorem-4.9 synthesis plus full selected-boundary-zero classifier
  control holds.  Current Algebraic-F2 estimate: PLN STV `<0.78,0.91>`, ITV
  `[0.71,0.80]`, progress `99%`.
- Report-closed emitted-rank focused build archived locally as
  `fourcolor-move2-report-closed-emitted-rank-focused-build-20260629.log`.
- Report-closed emitted-rank lab rerun archived locally as
  `fourcolor-move2-report-closed-emitted-rank-lab-20260629.json`; stderr is
  empty.  The rerun contains 65 benchmark records, 65 projected-generator
  certificate records, 80 mined survivors, and 80 rejected candidates; the
  crux report still shows the all-interior/declared-forced no-evader rows as
  synthesis/no-evader on the live F2 focus rows.
- Report-closed emitted-rank axiom audit archived locally as
  `fourcolor-move2-report-closed-emitted-rank-axiom-audit-20260629.log`;
  both new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Strict proof-marker/leak/diff scans archived locally as
  `fourcolor-move2-report-closed-emitted-rank-strict-scans-20260629.log`.
- Full build archived locally as
  `fourcolor-move2-report-closed-emitted-rank-full-build-20260629.log`; it
  completed `lake -f lakefile.lean build Mettapedia` with 5900 jobs.
- New report-closed emitted-rank theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_theorem49Synthesis_and_boundaryZeroControl_of_missingCheckerEvidenceLatents_eq_nil`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetPairingKernel_eq_bot_iff_theorem49Synthesis_and_boundaryZeroControl`.
  These remove the raw `forcedCounterexampleLatents = all` premise from the
  public rank-oracle surface: the executable report either returns a primitive
  portal/cycle checker gap, or its closed missing-evidence frontier supplies
  forced-all and the emitted-edge pairing kernel is trivial iff theorem-4.9
  synthesis plus full selected-boundary-zero classifier control holds.  Current
  Algebraic-F2 estimate: PLN STV `<0.79,0.92>`, ITV `[0.73,0.81]`, progress
  `99%`.
- New report-closed trace-evader theorem surfaces:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_or_boundaryZeroTraceEvader_canonicalFamilyPairing_ne_zero`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_boundaryZeroTraceEvader_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis`.
  This removes the raw `forcedCounterexampleLatents = all` premise from the
  stronger trace-control fork: the executable report now returns a primitive
  portal/cycle checker gap, theorem-4.9 synthesis with full
  selected-boundary-zero classifier control, or a genuine trace-local
  boundary-zero evader with nonzero canonical remaining-family pairing; under
  failed theorem-4.9 synthesis, the success branch is eliminated and the report
  returns only the primitive gap or the trace-local evader.
  Current Algebraic-F2 estimate remains PLN STV `<0.79,0.92>`, ITV
  `[0.73,0.81]`, progress `99%`.
- New report-closed kernel/map failure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetKernelMapEvader_of_not_theorem49BoundaryRootSynthesis`.
  Under failed theorem-4.9 synthesis, the executable report now returns a
  primitive portal/cycle checker gap or the unified finite F2 obstruction: a
  nonzero selected-boundary-zero evader in the immutable emitted-edge pairing
  kernel with nonzero image under the canonical remaining-family map.  Current
  Algebraic-F2 estimate remains PLN STV `<0.79,0.92>`, ITV `[0.73,0.81]`,
  progress `99%`.
- New report-closed kernel/map split and no-gap/no-evader closure surfaces:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_or_emittedFinsetKernelMapEvader`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_no_emittedFinsetKernelMapEvader`.
  These turn the failure branch around: if the executable report has no
  primitive portal/cycle checker gap and no unified emitted-kernel/remaining-map
  evader, Lean proves theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control.  Current Algebraic-F2 estimate remains PLN STV
  `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- New report-closed exact kernel/map oracle surfaces:
  `CAP5TransportedEdgeComponentCoverCore.no_emittedFinsetKernelMapEvader_iff_theorem49Synthesis_and_boundaryZeroControl_of_missingCheckerEvidenceLatents_eq_nil`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_no_emittedFinsetKernelMapEvader_iff_theorem49Synthesis_and_boundaryZeroControl`.
  These strengthen the no-gap/no-evader closure into the exact report-level
  F2 decision: once the primitive missing-evidence frontier is closed, absence
  of the unified emitted-kernel/remaining-map evader is equivalent to
  theorem-4.9 synthesis plus full selected-boundary-zero classifier control;
  the executable report returns a primitive checker gap or that exact iff.
  Current Algebraic-F2 estimate remains PLN STV `<0.79,0.92>`, ITV
  `[0.73,0.81]`, progress `99%`.
- New report-closed emitted-rank/no-unified-evader equivalence surfaces:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_no_emittedFinsetKernelMapEvader_of_missingCheckerEvidenceLatents_eq_nil`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetPairingKernel_eq_bot_iff_no_emittedFinsetKernelMapEvader`.
  These connect the lab-facing finite rank certificate directly to the
  obstruction branch: after a closed primitive frontier, the emitted-edge
  pairing kernel is trivial iff there is no unified emitted-kernel/remaining-map
  evader; the executable report returns a primitive checker gap or that exact
  finite F2 equivalence.  Current Algebraic-F2 estimate remains PLN STV
  `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- New report-level emitted-rank trichotomy surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_or_emittedFinsetKernelMapEvader`.
  The finite rank verdict now decides the executable Move-2 branch directly:
  the report has a primitive checker gap, or the emitted-edge kernel is
  trivial and theorem-4.9 synthesis with full selected-boundary-zero control
  follows, or rank failure returns the unified emitted-kernel/remaining-map
  evader as the obstruction.  Current Algebraic-F2 estimate remains PLN STV
  `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- Target/rank decomposition focused detector build archived locally as
  `fourcolor-move2-target-rank-decomposition-focused-build-20260629.log`.
- Target/rank decomposition validation lab rerun archived locally as
  `fourcolor-move2-target-rank-decomposition-lab-20260629.json`; stderr is
  empty.  It preserves the edge-40/color-1M projected-generator counts: 65
  reports split as 53 found, 12 no-Tait-coloring, and 0 missing; 740 color
  probes split as 454 found, 286 no-Tait-coloring, and 0 missing.
- Target/rank decomposition trusted-constant audit archived locally as
  `fourcolor-move2-target-rank-decomposition-axiom-audit-20260629.log`; the
  two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-target-rank-decomposition-full-build-20260629.log`; it
  completed with 5900 jobs.
- New target/rank decomposition theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.no_boundaryZeroEvader_iff_theorem49BoundaryTargetClassifierControl_and_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`
  and
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_theorem49BoundaryTargetClassifierControl_and_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure`.
  These make the surviving algebraic fork more exact: the finite emitted-edge
  rank certificate is equivalent not only to the full no-evader oracle, but to
  theorem-4.9 target classifier control plus exclusion of the concrete
  off-target boundary-vertex Kirchhoff evader.  Current Algebraic-F2 estimate
  remains PLN STV `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- Target-controlled kernel-evader focused detector build archived locally as
  `fourcolor-move2-target-controlled-kernel-evader-focused-build-20260629.log`.
- Target-controlled kernel-evader validation lab rerun archived locally as
  `fourcolor-move2-target-controlled-kernel-evader-lab-20260629.json`;
  stderr is empty.  It preserves the edge-40/color-1M projected-generator
  counts: 65 reports split as 53 found and 12 no-Tait-coloring; 740 color
  probes split as 454 found and 286 no-Tait-coloring, with 0 missing color
  probes.
- Target-controlled kernel-evader trusted-constant audit archived locally as
  `fourcolor-move2-target-controlled-kernel-evader-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-target-controlled-kernel-evader-full-build-20260629.log`;
  it completed with 5900 jobs.
- New target-controlled kernel-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_emittedFinsetPairingKernel_eq_bot_of_theorem49BoundaryTargetClassifierControl`.
  This closes the other half of the target/rank split: after theorem-4.9
  target classifier control is known, emitted-rank failure is no longer an
  abstract linear-algebra defect.  Lean returns the genuine
  selected-boundary-zero evader carrying emitted-kernel membership, nonzero
  canonical remaining-map image, and a concrete theorem-4.9 boundary-vertex
  Kirchhoff failure.  Current Algebraic-F2 estimate remains PLN STV
  `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- Target-controlled rank-decision focused detector build archived locally as
  `fourcolor-move2-target-controlled-rank-decision-focused-build-20260629.log`.
- Target-controlled rank-decision validation lab rerun archived locally as
  `fourcolor-move2-target-controlled-rank-decision-lab-20260629.json`;
  stderr is empty.  It preserves the edge-40/color-1M projected-generator
  counts: 65 reports split as 53 found and 12 no-Tait-coloring; 740 color
  probes split as 454 found and 286 no-Tait-coloring, with 0 missing color
  probes.
- Target-controlled rank-decision trusted-constant audit archived locally as
  `fourcolor-move2-target-controlled-rank-decision-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-target-controlled-rank-decision-full-build-20260629.log`;
  it completed with 5900 jobs.
- New target-controlled rank-decision theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl`.
  These turn the target-controlled algebraic fork into an exact local
  decision: after target control, emitted-rank triviality is equivalent to
  excluding the concrete off-target Kirchhoff evader, and rank failure returns
  that evader with emitted-kernel and remaining-map certificates.  Current
  Algebraic-F2 estimate remains PLN STV `<0.79,0.92>`, ITV `[0.73,0.81]`,
  progress `99%`.
- Unconditional rank-failure split focused detector build archived locally as
  `fourcolor-move2-unconditional-rank-evader-split-focused-build-20260629.log`.
- Unconditional rank-failure split validation lab rerun archived locally as
  `fourcolor-move2-unconditional-rank-evader-split-lab-20260629.json`;
  stderr is empty.  It preserves the edge-40/color-1M projected-generator
  counts: 65 reports split as 53 found and 12 no-Tait-coloring; 740 color
  probes split as 454 found and 286 no-Tait-coloring, with 0 missing color
  probes.
- Unconditional rank-failure split trusted-constant audit archived locally as
  `fourcolor-move2-unconditional-rank-evader-split-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-unconditional-rank-evader-split-full-build-20260629.log`;
  it completed with 5900 jobs.
- New unconditional rank-failure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_emittedFinsetPairingKernel_eq_bot`
  and
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`.
  These remove the target-control side condition from the finite-rank failure
  branch: a failed emitted-rank certificate now returns either a nonzero
  theorem-4.9 target chain vanishing on every enumerated forced edge or the
  off-target kernel/map/vertex-failure evader.  Current Algebraic-F2 estimate
  remains PLN STV `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- Report target/off-target rank split focused detector build archived locally
  as
  `fourcolor-move2-report-target-offtarget-rank-split-focused-build-20260629.log`.
- Report target/off-target rank split validation lab rerun archived locally as
  `fourcolor-move2-report-target-offtarget-rank-split-lab-20260629.json`;
  stderr is empty.  It preserves the edge-40/color-1M projected-generator
  counts: 65 reports split as 53 found and 12 no-Tait-coloring; 740 color
  probes split as 454 found and 286 no-Tait-coloring, with 0 missing color
  probes.
- Report target/off-target rank split trusted-constant audit archived locally
  as
  `fourcolor-move2-report-target-offtarget-rank-split-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-target-offtarget-rank-split-full-build-20260629.log`;
  it completed with 5900 jobs.
- New report target/off-target rank theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49BoundaryTargetEvader_or_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_theorem49BoundaryRootSynthesis`.
  These lift the target/off-target rank-failure split to the executable report:
  primitive checker gap, rank close with synthesis/control, target evader, or
  off-target kernel/map/vertex-failure evader; under failed synthesis only the
  primitive-gap or evader branches remain.  Current Algebraic-F2 estimate
  remains PLN STV `<0.79,0.92>`, ITV `[0.73,0.81]`, progress `99%`.
- New closed-frontier target/off-target no-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_and_theorem49Synthesis_and_boundaryZeroControl_iff_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missingCheckerEvidence`.
  With the primitive checker frontier closed, Lean now proves emitted-rank close
  with synthesis/control is equivalent to absence of both target-side and
  off-target report evaders.  Current Algebraic-F2 estimate is PLN STV
  `<0.80,0.93>`, ITV `[0.74,0.81]`, progress `99%`.
- Closed-frontier target/off-target no-evader focused detector build archived
  locally as
  `fourcolor-move2-report-target-offtarget-noevader-iff-focused-build-20260629.log`.
- Closed-frontier target/off-target no-evader validation lab rerun archived
  locally as
  `fourcolor-move2-report-target-offtarget-noevader-iff-lab-20260629.json`;
  stderr is empty.  The edge-40/color-1M projected-generator counts remain:
  65 reports split as 53 found and 12 no-Tait-coloring; 740 color probes split
  as 454 found and 286 no-Tait-coloring, with 0 missing color probes.
- Closed-frontier target/off-target no-evader trusted-constant audit archived
  locally as
  `fourcolor-move2-report-target-offtarget-noevader-iff-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-target-offtarget-noevader-iff-full-build-20260629.log`;
  it completed with 5900 jobs.
- New route-facing target/off-target no-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure`.
  The first theorem proves that excluding both concrete target/off-target
  evader branches leaves only primitive checker gap or synthesis/control in
  the executable report.  The second theorem closes the route under a closed
  primitive frontier.  The lab was rerun first as
  `fourcolor-move2-report-target-offtarget-noevader-route-lab-20260629.json`;
  stderr is empty and the edge-40/color-1M projected-generator counts remain:
  65 reports split as 53 found and 12 no-Tait-coloring; 740 color probes split
  as 454 found and 286 no-Tait-coloring, with 0 missing color probes.  Current
  Algebraic-F2 estimate is PLN STV `<0.81,0.93>`, ITV `[0.75,0.82]`, progress
  `99%`.
- New closed-frontier target/off-target rank-certificate theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_iff_no_theorem49BoundaryTargetEvader_and_no_emittedFinsetKernelMapEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missingCheckerEvidence`.
  It proves that, once the primitive checker frontier is closed, the emitted
  F2 pairing kernel certificate itself is equivalent to absence of both
  concrete target/off-target report evaders.  The lab was rerun as
  `fourcolor-move2-target-offtarget-rank-cert-iff-lab-20260629.json`; stderr
  is empty and the edge-40/color-1M projected-generator counts remain:
  65 reports split as 53 found and 12 no-Tait-coloring; 740 color probes split
  as 454 found and 286 no-Tait-coloring, with 0 missing color probes.  Current
  Algebraic-F2 estimate is PLN STV `<0.82,0.94>`, ITV `[0.77,0.83]`, progress
  `99%`.
- Closed-frontier target/off-target rank-certificate focused detector build
  archived locally as
  `fourcolor-move2-target-offtarget-rank-cert-iff-focused-build-20260629.log`.
- Closed-frontier target/off-target rank-certificate trusted-constant audit
  archived locally as
  `fourcolor-move2-target-offtarget-rank-cert-iff-axiom-audit-20260629.log`;
  the new theorem constant depends only on
  `[propext, Classical.choice, Quot.sound]`.
- New emitted-rank route-close theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_emittedFinsetPairingKernel_eq_bot`
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_emittedFinsetPairingKernel_eq_bot`.
  These prove that the emitted F2 rank certificate leaves only primitive
  checker gap or synthesis/control in the executable report, and closes
  synthesis/control outright when the primitive checker frontier is closed.  The
  lab was rerun as
  `fourcolor-move2-emitted-rank-route-close-lab-20260629.json`; stderr is empty
  and the edge-40/color-1M projected-generator counts remain: 65 reports split
  as 53 found and 12 no-Tait-coloring; 740 color probes split as 454 found and
  286 no-Tait-coloring, with 0 missing color probes.  Current Algebraic-F2
  estimate is PLN STV `<0.83,0.94>`, ITV `[0.78,0.84]`, progress `99%`.
- Emitted-rank route-close focused detector build archived locally as
  `fourcolor-move2-emitted-rank-route-close-focused-build-20260629.log`.
- Emitted-rank route-close trusted-constant audit archived locally as
  `fourcolor-move2-emitted-rank-route-close-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- New coverage-to-rank bridge theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_of_forcedEdgeCoverage`,
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_of_controlEdges_nonzeroCoverage_subset_emittedFinset`,
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_forcedEdgeCoverage`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_forcedEdgeCoverage`.
  These prove that an exact forced-edge coverage/no-evader verdict, or a
  concrete finite control-set coverage certificate contained in the emitted
  classifier output, supplies the emitted red/blue pairing-kernel rank
  certificate consumed by the report route.  The executable report therefore
  has only primitive checker gap or synthesis/control left under coverage, and
  with the primitive frontier closed coverage directly proves synthesis plus
  full selected-boundary-zero classifier control.  The lab was rerun as
  `fourcolor-move2-coverage-rank-bridge-lab-20260629.json`; stderr is empty and
  the edge-40/color-1M projected-generator counts remain: 65 reports split as
  53 found and 12 no-Tait-coloring; 740 color probes split as 454 found and
  286 no-Tait-coloring, with 0 missing color probes.  Current Algebraic-F2
  estimate is PLN STV `<0.84,0.95>`, ITV `[0.80,0.85]`, progress `99%`.
- Coverage-to-rank bridge focused detector build archived locally as
  `fourcolor-move2-coverage-rank-bridge-focused-build-20260629.log`.
- Coverage-to-rank bridge trusted-constant audit archived locally as
  `fourcolor-move2-coverage-rank-bridge-axiom-audit-20260629.log`.
- New empty-worklist rank-close theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetPairingKernel_eq_bot_of_remainingInteriorSupportEmpty`,
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_remainingInteriorSupportEmpty`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_remainingInteriorSupportEmpty`.
  These specialize the coverage-to-rank bridge to the exact CAP5 shell
  condition that the canonical interior-support worklist is empty: Lean proves
  the emitted red/blue pairing-kernel certificate, the executable
  primitive-gap-or-synthesis/control report route, and the closed-frontier
  synthesis plus full selected-boundary-zero classifier-control conclusion.
  The lab was rerun as
  `fourcolor-move2-empty-worklist-rank-close-lab-20260629.json`; stderr is
  empty and the edge-40/color-1M projected-generator counts remain: 65 reports
  split as 53 found and 12 no-Tait-coloring; 740 color probes split as 454
  found and 286 no-Tait-coloring, with 0 missing color probes.  Current
  Algebraic-F2 estimate is PLN STV `<0.85,0.95>`, ITV `[0.81,0.86]`, progress
  `99%`.
- Empty-worklist rank-close focused detector build archived locally as
  `fourcolor-move2-empty-worklist-rank-close-focused-build-20260629.log`.
- Empty-worklist rank-close trusted-constant audit archived locally as
  `fourcolor-move2-empty-worklist-rank-close-axiom-audit-20260629.log`.
- New exact-worklist fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.remainingInteriorSupportEmpty_closes_or_notSynthesis_boundaryZeroEvader_and_nonempty_worklist_of_no_missingCheckerEvidence`.
  This packages the current Move-2 decision boundary at report level: with the
  primitive checker frontier closed, an empty canonical interior-support
  worklist closes theorem-4.9 synthesis plus full selected-boundary-zero
  classifier control, while failed synthesis forces the worklist to be nonempty
  and returns a genuine selected-boundary-zero evader vanishing on all
  enumerated forced edges plus a decreasing remaining-worklist edge.  Current
  Algebraic-F2 estimate is PLN STV `<0.86,0.95>`, ITV `[0.82,0.87]`, progress
  `99%`.  The lab was rerun as
  `fourcolor-move2-exact-worklist-fork-lab-20260629.json`; stderr is empty and
  the edge-40/color-1M projected-generator counts remain: 65 reports split as
  53 found and 12 no-Tait-coloring; 740 color probes split as 454 found and 286
  no-Tait-coloring, with 0 missing color probes.
- Exact-worklist fork focused detector build archived locally as
  `fourcolor-move2-exact-worklist-fork-focused-build-20260629.log`.
- Exact-worklist fork trusted-constant audit archived locally as
  `fourcolor-move2-exact-worklist-fork-axiom-audit-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-exact-worklist-fork-full-build-20260629.log`; it completed
  with 5900 jobs.
- New executable-report exact-worklist fork theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_remainingInteriorSupportEmpty_closes_or_notSynthesis_boundaryZeroEvader_and_nonempty_worklist`.
  This removes the raw closed-frontier handoff from the exact-worklist fork:
  the decidable CAP5 report returns either a primitive checker gap or the same
  exact worklist decision surface.  In the closed branch, empty canonical
  interior-support worklist closes synthesis/control, while failed synthesis
  forces a nonempty worklist and returns a genuine selected-boundary-zero evader
  plus a decreasing remaining-worklist edge.  Current Algebraic-F2 estimate is
  PLN STV `<0.87,0.95>`, ITV `[0.83,0.88]`, progress `99%`.  The lab was rerun
  as `fourcolor-move2-report-exact-worklist-fork-lab-20260629.json`; stderr is
  empty and the edge-40/color-1M projected-generator counts remain: 65 reports
  split as 53 found and 12 no-Tait-coloring; 740 color probes split as 454
  found and 286 no-Tait-coloring, with 0 missing color probes.
- Report-level exact-worklist fork focused detector build archived locally as
  `fourcolor-move2-report-exact-worklist-fork-focused-build-20260629.log`.
- Report-level exact-worklist fork trusted-constant audit archived locally as
  `fourcolor-move2-report-exact-worklist-fork-axiom-audit-20260629.log`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-exact-worklist-fork-full-build-20260629.log`; it
  completed with 5900 jobs.
- New report-level residual scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_residualSchedulerCoverageNoEvader_or_synthesis_or_immutableProcessedControlObstruction_of_processedControl`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_residualSchedulerImmutableProcessedControlObstruction_of_notSynthesis_of_processedControl`.
  These remove the raw forced-all handoff from the promoted residual scheduler:
  the executable report returns either a primitive checker gap or the terminal
  processed-coverage no-evader/synthesis branch, an already-closed synthesis
  branch, or a promoted residual-edge obstruction.  On the failed synthesis
  side, Lean returns only the primitive checker gap or the genuine
  selected-boundary-zero residual evader with immutable processed-control
  failure, the one-edge promoted control update, and strict residual decrease.
  Current Algebraic-F2 estimate is PLN STV `<0.88,0.95>`, ITV `[0.84,0.89]`,
  progress `99%`.  The lab was rerun as
  `fourcolor-move2-report-residual-scheduler-fork-lab-20260629.json`; stderr
  is empty and the edge-40/color-1M projected-generator counts remain:
  65 reports split as 53 found and 12 no-Tait-coloring; 740 color probes split
  as 454 found and 286 no-Tait-coloring, with 0 missing color probes.
- Report-level residual scheduler focused detector build archived locally as
  `fourcolor-move2-report-residual-scheduler-fork-focused-build-20260629.log`.
- Report-level residual scheduler trusted-constant audit archived locally as
  `fourcolor-move2-report-residual-scheduler-fork-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-residual-scheduler-fork-full-build-20260629.log`;
  it completed with 5900 jobs.
- New initial residual scheduler theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_initialResidualSchedulerNoEvader_or_synthesis_or_immutableProcessedControlObstruction`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_initialResidualSchedulerImmutableProcessedControlObstruction_of_notSynthesis`.
  These remove the scheduler-side processed-state hypothesis from the report
  fork by instantiating `processed = ∅` and proving processed-control
  internally.  The executable report now starts the promoted scheduler itself:
  primitive checker gap, empty initial worklist no-evader/synthesis,
  already-closed synthesis, or a promoted first residual-edge obstruction.
  On the failed synthesis side, only the primitive gap or the genuine first
  residual selected-boundary-zero evader remains, with immutable one-edge
  processed-control failure, the one-edge promoted control update, and strict
  residual decrease.  Current Algebraic-F2 estimate is PLN STV `<0.90,0.95>`,
  ITV `[0.86,0.91]`, progress `99%`.  The lab was rerun as
  `fourcolor-move2-report-initial-residual-scheduler-lab-20260629.json`;
  stderr is empty and the edge-40/color-1M projected-generator counts remain:
  65 reports split as 53 found and 12 no-Tait-coloring; 740 color probes split
  as 454 found and 286 no-Tait-coloring, with 0 missing color probes.
- Initial residual scheduler focused detector build archived locally as
  `fourcolor-move2-report-initial-residual-scheduler-focused-build-20260629.log`.
- Initial residual scheduler trusted-constant audit archived locally as
  `fourcolor-move2-report-initial-residual-scheduler-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-initial-residual-scheduler-full-build-20260629.log`;
  it completed with 5900 jobs.
- New initial residual closure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.InitialResidualSchedulerImmutableProcessedControlObstruction`,
  `CAP5TransportedEdgeComponentCoverCore.initialResidualSchedulerImmutableProcessedControlObstruction_of_no_missingCheckerEvidence_of_notSynthesis`,
  `CAP5TransportedEdgeComponentCoverCore.theorem49BoundaryRootSynthesis_of_no_missingCheckerEvidence_and_no_initialResidualSchedulerImmutableProcessedControlObstruction`,
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_initialResidualRemainingControlEdgesEmpty`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_initialResidualRemainingControlEdgesEmpty`.
  The finite worklist bridge
  `EnumeratedExceptionalAnnulusForcedEdgeClassifier.residualRemainingControlEdges_empty_processed_eq_empty_iff_remainingControlEdges_eq_empty`
  proves that the initial residual scheduler is empty exactly when the
  canonical immutable remaining-control worklist is empty.  Thus the executable
  report has a full-control no-evader closure from an initially empty residual
  scheduler, while no primitive checker gap plus failed synthesis is now forced
  to accept the named first residual evader/immutable-processing obstruction.
  Current Algebraic-F2 estimate is PLN STV `<0.90,0.95>`, ITV `[0.86,0.91]`,
  progress `99%`.  The lab was rerun as
  `fourcolor-move2-initial-residual-closure-lab-20260629.json`; stderr is
  empty and the edge-40/color-1M projected-generator counts remain: 65 reports
  split as 53 found and 12 no-Tait-coloring; 740 color probes split as
  454 found and 286 no-Tait-coloring, with 0 missing color probes.
- Initial residual closure focused detector build archived locally as
  `fourcolor-move2-initial-residual-closure-focused-build-20260629.log`.
- Initial residual closure trusted-constant audit archived locally as
  `fourcolor-move2-initial-residual-closure-axiom-audit-20260629.log`;
  the new theorem constants and worklist bridge depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-initial-residual-closure-full-build-20260629.log`;
  it completed with 5900 jobs.
- New initial residual unified-evader theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetKernelMapEvader_of_initialResidualSchedulerImmutableProcessedControlObstruction`
  and
  `CAP5TransportedEdgeComponentCoverCore.emittedFinsetKernelMapEvader_of_no_missingCheckerEvidence_of_notSynthesis_via_initialResidualScheduler`.
  Lean now proves the named first residual scheduler obstruction is the same
  surviving finite F2 obstruction used by the emitted-rank/map oracle: it
  returns a nonzero selected-boundary-zero chain vanishing on every enumerated
  forced edge, membership in the immutable emitted-edge pairing kernel, and
  nonzero image under the canonical remaining-family pairing map.  Thus under
  a closed primitive checker frontier, failed theorem-4.9 synthesis via the
  initial scheduler no longer leaves a scheduler-local branch; it returns the
  unified emitted-kernel/remaining-map evader directly.  Current Algebraic-F2
  estimate is PLN STV `<0.91,0.95>`, ITV `[0.86,0.91]`, progress `99%`.
  The validation lab was rerun as
  `fourcolor-move2-initial-residual-unified-evader-lab-20260629.json`; stderr
  is empty, and the projected-generator summary has 65 reports split as
  53 found and 12 no-Tait-coloring, 726 color probes split as 458 found and
  268 no-Tait-coloring, with 0 missing reports, 0 missing color probes, and
  0 truncations.
  Focused detector build archived locally as
  `fourcolor-move2-initial-residual-unified-evader-focused-build-20260629.log`.
  Trusted-constant audit archived locally as
  `fourcolor-move2-initial-residual-unified-evader-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
  Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-initial-residual-unified-evader-full-build-20260629.log`;
  it completed with 5900 jobs.  Strict current-diff proof-marker, leak, and
  whitespace scans are archived under the same
  `fourcolor-move2-initial-residual-unified-evader-*20260629.log` prefix and
  are empty.
- New focus-shell initial residual threshold theorem surface:
  `sharedInteriorPair_CAP5_initialResidualRemainingControlEdges_eq_empty_iff_emittedInterior_card_ge_two`,
  `wheelWithInnerTriangle_CAP5_initialResidualRemainingControlEdges_eq_empty_iff_emittedInterior_card_ge_three`,
  `sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_initialResidualRemainingControlEdges_eq_empty_uniqueCertificates_boundaryTrimmed`,
  `wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_initialResidualRemainingControlEdges_eq_empty_uniqueCertificates_boundaryTrimmed`,
  `sharedInteriorPair_CAP5_initialResidualRemainingControlEdges_ne_empty_of_not_theorem49BoundaryRootSynthesis_uniqueCertificates_boundaryTrimmed`,
  and
  `wheelWithInnerTriangle_CAP5_initialResidualRemainingControlEdges_ne_empty_of_not_theorem49BoundaryRootSynthesis_uniqueCertificates_boundaryTrimmed`.
  These prove the initial residual scheduler is empty exactly at the finite F2
  focus-shell thresholds already certified by the lab: both shared interior
  controls for `sharedInteriorPair`, and all three spokes for
  `wheelWithInnerTriangle`.  Empty initial residual now closes the
  boundary-trimmed unique-certificate synthesis route for those shells, while
  failed synthesis forces a genuinely nonempty initial residual worklist.  This
  moves the Move-2 burden from isolated repair packets to the uniform CAP5
  shell-data question: lift these exact focus thresholds uniformly, or accept
  the unified finite F2 evader already returned by the fork.  Current
  Algebraic-F2 estimate is PLN STV `<0.92,0.95>`, ITV `[0.87,0.92]`, progress
  `99%`.  Focused detector build archived locally as
  `fourcolor-move2-focus-initial-residual-threshold-focused-build-20260629.log`.
  Trusted-constant audit archived locally as
  `fourcolor-move2-focus-initial-residual-threshold-axiom-audit-20260629.log`;
  the six new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.  The seeded validation lab rerun
  is archived as
  `fourcolor-move2-focus-initial-residual-threshold-lab-20260629.json`;
  stderr is empty, and the projected-generator summary has 65 reports split as
  54 found and 11 no-Tait-coloring, 700 color probes split as 456 found and
  244 no-Tait-coloring, 0 missing color probes, and 0 truncations.  The two
  focus rows both return found red/blue certificates on all target controls:
  `shared-interior-pair` targets `sip01`/`sip12`, and
  `wheel-with-inner-triangle` targets `wit01`/`wit02`/`wit03`.
  Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-focus-initial-residual-threshold-full-build-20260629.log`;
  it completed with 5900 jobs.  Strict current-diff proof-marker, leak, and
  whitespace scans are archived under the same
  `fourcolor-move2-focus-initial-residual-threshold-*20260629.log` prefix and
  are empty.
- New uniform initial-residual subset bridge:
  `CAP5TransportedEdgeComponentCoverCore.EnumeratedExceptionalAnnulusForcedEdgeClassifier.remainingControlEdges_eq_empty_iff_controlEdges_subset_emittedFinset`,
  `CAP5TransportedEdgeComponentCoverCore.EnumeratedExceptionalAnnulusForcedEdgeClassifier.initialResidualRemainingControlEdges_eq_empty_iff_controlEdges_subset_emittedFinset`,
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_and_boundaryZeroControl_of_initialResidualInteriorSupport_subset_emittedFinset`,
  and
  `CAP5TransportedEdgeComponentCoverCore.theorem49Synthesis_and_boundaryZeroControl_of_no_missingCheckerEvidence_and_initialResidualInteriorSupport_subset_emittedFinset`.
  Lean now proves the scheduler start condition is exactly the fixed point
  `controlEdges ⊆ classifier.emittedFinset` for any finite control set.  The
  report-level no-evader route consumes the canonical exact-shell obligation
  directly: if `interiorEdgeSupport emb.faceBoundary emb.faces` is contained
  in the emitted classifier output, the remaining-edge red/blue obligations
  are vacuous, the initial residual scheduler is empty, and the executable
  report leaves only primitive checker gap or theorem-4.9 synthesis with full
  selected-boundary-zero classifier control.  With the primitive checker
  frontier closed, that subset condition alone closes synthesis/control.  This
  is the uniform lift point for the focus-shell thresholds; the remaining
  Move-2 burden is to prove exact CAP5 shell data supplies this emitted
  interior-support subset, or accept the unified finite F2 evader already
  isolated by the failure branch.  Current Algebraic-F2 estimate is PLN STV
  `<0.93,0.95>`, ITV `[0.88,0.93]`, progress `99%`.  Focused detector build
  archived locally as
  `fourcolor-move2-uniform-initial-residual-subset-focused-build-20260629.log`.
  Trusted-constant audit archived locally as
  `fourcolor-move2-uniform-initial-residual-subset-axiom-audit-20260629.log`;
  the four new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.  The seeded validation lab rerun
  is archived as
  `fourcolor-move2-uniform-initial-residual-subset-lab-20260629.json`;
  stderr is empty, and the projected-generator summary has 65 reports split as
  54 found and 11 no-Tait-coloring, 700 color probes split as 456 found and
  244 no-Tait-coloring, 0 missing color probes, and 0 truncations.  Full
  `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-uniform-initial-residual-subset-full-build-20260629.log`;
  it completed with 5900 jobs.  Strict current-diff proof-marker, leak, and
  whitespace scans are archived under the same
  `fourcolor-move2-uniform-initial-residual-subset-*20260629.log` prefix and
  are empty.
- New emitted-interior-support failure theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.exists_initialResidualInteriorSupportEdge_not_emitted_of_no_missingCheckerEvidence_of_notSynthesis`
  and
  `CAP5TransportedEdgeComponentCoverCore.initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader_of_no_missingCheckerEvidence_of_notSynthesis`.
  Lean now proves the contrapositive of the uniform subset close in the
  closed primitive frontier: failed theorem-4.9 synthesis forces a concrete
  canonical interior-support edge in the initial residual worklist and outside
  the immutable emitted classifier output.  The paired failure theorem returns
  that exact emitted-interior-support gap together with the unified finite F2
  obstruction: a nonzero selected-boundary-zero chain vanishing on every
  enumerated forced edge, lying in the emitted pairing kernel, and having
  nonzero canonical remaining-family map image.  Thus the remaining Move-2
  branch is now a clean fork: prove the emitted canonical interior-support
  subset and close synthesis/control, or accept a named missing interior
  coordinate plus the unified evader.  Current Algebraic-F2 estimate remains
  PLN STV `<0.93,0.95>`, ITV `[0.88,0.93]`, progress `99%`.  Focused detector
  build archived locally as
  `fourcolor-move2-interior-subset-gap-evader-focused-build-20260629.log`.
  Trusted-constant audit archived locally as
  `fourcolor-move2-interior-subset-gap-evader-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.  The seeded validation lab rerun
  is archived as
  `fourcolor-move2-interior-subset-gap-evader-lab-20260629.json`; stderr is
  empty, and the projected-generator summary has 65 reports split as 54 found
  and 11 no-Tait-coloring, 700 color probes split as 456 found and
  244 no-Tait-coloring, 0 missing color probes, and 0 truncations.
  Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-interior-subset-gap-evader-full-build-20260629.log`; it
  completed with 5900 jobs.  Strict current-diff proof-marker, leak, and
  whitespace scans are archived under the same
  `fourcolor-move2-interior-subset-gap-evader-*20260629.log` prefix and are
  empty.
- New report-level interior-gap/evader fork surface:
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader_of_notSynthesis`
  and
  `CAP5TransportedEdgeComponentCoverCore.ofDecidableChecks_missingCheckerEvidence_or_theorem49Synthesis_or_initialResidualInteriorSupportGap_and_emittedFinsetKernelMapEvader`.
  These remove the closed-frontier handoff from the paired
  emitted-interior-support obstruction.  Under failed theorem-4.9 synthesis,
  the executable report now returns either the primitive portal/cycle checker
  gap or the paired finite F2 obstruction directly: a residual canonical
  interior-support coordinate outside the immutable emitted classifier output
  plus the unified emitted-kernel/remaining-map evader.  With the success
  branch retained, the same report-level fork is exactly primitive checker
  gap, theorem-4.9 synthesis, or that paired obstruction.  Current
  Algebraic-F2 estimate is PLN STV `<0.94,0.95>`, ITV `[0.89,0.94]`,
  progress `99%`.  Focused detector build archived locally as
  `fourcolor-move2-report-interior-gap-evader-fork-focused-build-20260629.log`.
  The seeded validation lab rerun is archived as
  `fourcolor-move2-report-interior-gap-evader-fork-lab-20260629.json`; stderr
  is empty, and the projected-generator summary has 65 reports split as
  54 found and 11 no-Tait-coloring, 700 color probes split as 456 found and
  244 no-Tait-coloring, 0 missing color probes, and 0 truncations.
- New packaged oracle theorem surface:
  `CAP5TransportedEdgeComponentCoverCore.budgetMetNoEvader_boundaryZeroControl_oracle`.
  This assembles the committed rank/map/trace/scheduler case lemmas into one
  closed-frontier statement: no unified emitted-kernel/remaining-map evader
  iff theorem-4.9 synthesis plus full selected-boundary-zero classifier
  control, and failure of that closed result returns the same precise unified
  evader.  Focused build archived locally as
  `fourcolor-fresh-oracle-package-focused-build-20260629.log`; trusted-
  constant audit archived locally as
  `fourcolor-fresh-oracle-package-axiom-audit-20260629.log`, with both new
  theorem constants depending only on `[propext, Classical.choice,
  Quot.sound]`.  Strict current-diff, added Lean proof-marker, and added leak
  scans are archived under the `fourcolor-fresh-oracle-package-*20260629.log`
  prefix and are empty.  Full `lake -f lakefile.lean build Mettapedia`
  archived locally as
  `fourcolor-fresh-oracle-package-full-build-20260629.log`; it completed with
  5900 jobs.
- Report-route target/off-target no-evader focused detector build archived
  locally as
  `fourcolor-move2-report-target-offtarget-noevader-route-focused-build-20260629.log`.
- Report-route target/off-target no-evader trusted-constant audit archived
  locally as
  `fourcolor-move2-report-target-offtarget-noevader-route-axiom-audit-20260629.log`;
  the two new theorem constants depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake -f lakefile.lean build Mettapedia` archived locally as
  `fourcolor-move2-report-target-offtarget-noevader-route-full-build-20260629.log`;
  it completed with 5900 jobs.
- Projected-generator edge-40/color-1M lab rerun archived locally as
  `fourcolor-move2-projected-generator-edge40-color1m-lab-20260629.json`;
  stderr is empty.  With the edge cap raised to 40 and the coloring cap raised
  to 1000000, the 65 generated/benchmark projected-coordinate probe reports
  split as 53 `found`, 12 `no_tait_coloring`, and 0 `missing`; the 740 color
  probes split as 454 `found`, 286 `no_tait_coloring`, and 0 `missing`.  This
  removes both the previous edge-limit skip artifact and the later 100000-bound
  truncation artifact, but still does not certify the emitted-kernel/no-evader
  branch.  Move 2 therefore remains: prove canonical
  trace-control/emitted-kernel triviality from exact shell data or formalize
  the genuine unified evader already returned by the Lean fork.  This older
  projected-generator lab state is now subsumed by the report-level rank,
  exact-worklist, and residual-scheduler forks above; the current
  Algebraic-F2 estimate is PLN STV `<0.94,0.95>`, ITV `[0.89,0.94]`,
  progress `99%`.
- Route-verdict checker-frontier sharpening:
  `cap5PrimitiveCheckerGap_iff_missingCheckerEvidenceLatents_ne_nil`,
  `no_cap5PrimitiveCheckerGap_iff_missingCheckerEvidenceLatents_eq_nil`,
  `noGap_portalsCross_allLatents`,
  `cap5PrimitiveCheckerGap_of_no_selectedSideCycle`,
  `cap5PrimitiveCheckerGap_of_no_complementarySideCycle`, and
  `noGap_forces_sideCycles`.  These prove that the route-level primitive
  checker gap is exactly the executable 16-latent missing-evidence report, and
  that closing the gap already entails all portal crossings plus both
  graph-side cycle witnesses.  Conversely, failure of either side-cycle
  witness immediately inhabits the primitive checker gap.  This is the current
  proof-level reason the barrier cannot be restated as an unconditional
  closure from the existing hypotheses alone: the exact CAP5 class must still
  prove those portal/cycle facts and decide the target/off-target F2 evader
  set, or accept the formal gap/evader alternatives.  Focused verification:
  `lake -f lakefile.lean build Mettapedia.GraphTheory.FourColor.CAP5RouteVerdict`
  completed successfully with the repo's existing upstream deprecation/linter
  warnings only.  Trusted-constant audit for these six theorem constants
  reports only `[propext, Classical.choice, Quot.sound]`; current-diff proof
  marker, leak, whitespace, and `git diff --check` scans are clean.  Full
  `lake -f lakefile.lean build Mettapedia` completed successfully with
  5900 jobs and only pre-existing warnings outside this checkpoint.
- No-gap oracle side-condition discharge:
  `noGap_portalsCross_matchingCandidate`,
  `CAP5F2RouteCertificate.ofNoGap`, and
  `budgetMetNoEvader_boundaryZeroControl_oracle_of_noGap`.  These remove the
  old separate portal-crossing, two-side-cycle, and no-missing-checker
  arguments from the budget oracle once `¬ CAP5PrimitiveCheckerGap` is known.
  The portal transport is now broad enough for the oracle: any candidate with
  the selected `ofPortalSides p0 p4` side case has the same finite portal set
  as the corresponding canonical latent, so no-gap supplies the portal premise
  for that candidate.  Lean also proves `cap5PrimitiveCheckerGap_falseSide`
  and `not_forall_no_cap5PrimitiveCheckerGap_allSides`, showing that a
  completely side-uniform no-gap theorem is false because the constant-empty
  side has no selected-side cycle.  The remaining side-condition seam is
  therefore localized: exact CAP5 shell data must prove that its actual side
  is not such a degenerate side and closes `CAP5PrimitiveCheckerGap`.  The
  unified emitted-kernel/remaining-map evader set is now named by
  `CAP5F2UnifiedKernelMapEvader`: under no gap, Lean proves no such evader iff
  `CAP5F2RouteClosed`, and proves existence of such an evader iff route closure
  fails.  Focused
  `CAP5RouteVerdict`, FourColor aggregate, and full `Mettapedia` builds all
  pass; trusted-constant audit for the five new headline constants reports
  only `[propext, Classical.choice, Quot.sound]`, and current-diff proof
  marker, leak, whitespace, and `git diff --check` scans are clean.
- Route payoff audit:
  `CAP5RoutePayoff.lean` removes the closed-route coloring payoff
  `cap5RouteClosedColoringPayoff_of_routeClosed` as vacuous, because the root
  `C₀` already has type `G.EdgeColoring Color`.  The replacement
  `cap5RouteClosedSynthesisPayoff_of_routeClosed` extracts only the route-native
  consequences of `CAP5F2RouteClosed`: theorem-4.9 synthesis and full emitted
  selected-boundary-zero control.  The exact Tait bridge obligation
  `CAP5RouteClosedRootTaitBridge`, the finite witness bundle
  `CAP5FiniteRouteClosedWitness`, and the wheel canary names
  `WheelCAP5RoutePayoff.wheelColoringCanary` and
  `WheelCAP5RoutePayoff.WheelCAP5FiniteRouteClosedCanary` remain, but the wheel
  coloring canary is independent of the CAP5 route.  `CAP5WheelRouteData.lean`
  now also proves that its concrete five-edge wheel boundary has
  `CAP5PrimitiveCheckerGap` for every side, via the triangle parity obstruction
  on `wit12`, `wit23`, and `wit31`; hence no `CAP5FiniteNoGapRouteInput` or
  `CAP5FiniteRouteClosedWitness` exists for that exact core.  A genuine route coloring
  payoff now requires a raw edge-labeling/properness bridge or a route-type
  refactor; it is not claimed here.  Focused verification:
  `lake -f lakefile.lean build Mettapedia.GraphTheory.FourColor.CAP5RoutePayoff`
  completed successfully; the FourColor aggregate build completed successfully;
  full `lake -f lakefile.lean build Mettapedia` completed successfully with
  5900 jobs and only pre-existing warnings outside this checkpoint.  Trusted
  constants for the seven new headline constants report only
  `[propext, Classical.choice, Quot.sound]`; current-diff whitespace and proof
  marker scans are clean.

## Remaining Completion Requirements

- Move 1: prove the remaining exact-shell handoff into the primitive
  portal/cycle prerequisites.  The route-level checker lemmas now show that a
  missing selected-side or complementary-side cycle directly inhabits
  `CAP5PrimitiveCheckerGap`, and the no-gap oracle wrapper now derives the
  broad portal premise automatically from no-gap.  This handoff must therefore
  prove the exact CAP5 side has both cycle witnesses and closes
  `CAP5PrimitiveCheckerGap`, rather than try to clear a report flag for all
  possible side predicates.  The
  completed-prerequisite
  branch is now blocked by the cyclic-five small-cut repair-removal
  obstruction.
- Move 2: decide `CAP5F2NoUnifiedKernelMapEvader` for the actual no-gap route
  certificate.  Under the current Lean theorem surface, this is exactly the
  same as deciding `CAP5F2RouteClosed`; a checked
  `F2LeftInverseKernelCertificate` for the actual emitted-pairing map is now a
  sufficient MAKE certificate.  If the check fails, Lean must return a genuine
  `CAP5F2UnifiedKernelMapEvader` with forced-edge vanishing, emitted-kernel
  membership, and nonzero canonical remaining-family map image.  Do not
  reopen trace/rank/scheduler sub-forks unless they directly prove this named
  predicate or construct this named witness.
- Before any public checkpoint: strict proof-marker scan, trusted-constant audit for new
  theorems, validation lab rerun, full `lake -f lakefile.lean build
  Mettapedia`, and push only to `origin/fourcolor/cont-20260626`.
