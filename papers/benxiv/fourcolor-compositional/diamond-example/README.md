# The diamond family: actual graphs and both colouring branches

Configurations 1, 2 and 4 in the classical catalogue share an internal diamond.
Two boundary-triangle insertions relate their complete embedded graphs:

```text
configuration 1  ── insert in a boundary triangle ──▶  configuration 2
configuration 2  ── insert in a boundary triangle ──▶  configuration 4
```

These correspondences, their boundary orders and their complete colouring
semantics are kernel-checked. A shared joint-profile certificate now supplies
repair for all three cores. The complete proof uses its configuration-2 and
configuration-4 repairs and retains the general split transfer from 2 to 1.
The three original certificate dependencies are absent. The common profile
explanation still has finite cover obligations; a uniform extension to a
broader class of cores and its geometric coverage remain open.

## The local law

Start with a triangle on vertices `a`, `b`, `c`. Delete the edge `a-b` and
insert a fresh vertex joined to all three. Every target four-colouring belongs
to exactly one of two branches:

| Endpoint colours | Data that reconstruct the target colouring |
| --- | --- |
| `a` and `b` differ | A colouring of the old graph. The new vertex receives the unique fourth colour. |
| `a` and `b` agree | A colouring of the graph with `a` and `b` contracted, together with a new colour distinct from the merged vertex and `c`. |

The second branch has two choices for the new colour. The
[general alternatives theorem][alternatives] gives a bijection of actual
colouring witnesses, valid under any additional condition on the resulting
colouring. A proof using only the first branch discards legitimate target
colourings.

## The connection to the catalogue

[ExecutableConfiguration][executable] gives explicit inverses to the reference
hypermap operations and proves equality with the reference decoder for every
program in its `R`, `U`, `Y`, `H` fragment. A proved dart bijection numbers the
result. [DiamondConfigurations][configurations] then checks all three
permutations of configurations 1, 2 and 4 against compact finite tables.

The correspondence retains the actual cyclic geometry. For each configuration,
the file proves that the named graph vertices are exactly the hypermap's face
classes, that graph adjacency is exactly incidence across a map edge, and that
the listed boundary is the reference ring. It also identifies the complete
face orbits used to read cyclic neighbour lists. The two ring orientations are
exposed separately, including the orientation consumed by classical
reducibility. The four internal vertices in each graph are proved to form the
same diamond, a complete four-vertex graph with one edge removed.

[DiamondInsertion][insertions] proves graph isomorphisms for both insertions,
locates the inner triangle opposite the chosen boundary edge, and verifies the
changes to every cyclic neighbour list and to the outer ring. With zero-based
vertex names, the triangles are `(0,1,6)` for `1 → 2` and `(4,5,9)` for `2 → 4`.

Its `referenceAlternatives12` and `referenceAlternatives24` instantiate the
general two-branch law and produce colourings of the actual reference
hypermaps. Their composite, `referenceAlternatives14`, describes every colouring
of configuration 4 exactly once. The equivalence preserves arbitrary predicates
on the resulting colouring, so a surrounding boundary constraint can be imposed
without losing information.

## One interior-elimination law

[DiamondBoundaryElimination][elimination] proves a single equivalence for a
diamond attached to any boundary graph, over any colour alphabet. A summary
contains a proper boundary colouring, two distinct centre colours, and a colour
for each tip that avoids both centres and all its boundary neighbours. It
reconstructs an actual full colouring; eliminating that colouring returns the
same summary. Every predicate on the joint boundary assignment is preserved.

This is the relevant boundary-elimination principle: retain the shared centre
choice before solving the two tip constraints. Independent tests that forget
which centre pair was used cannot substitute for this joint witness.

[DiamondBoundarySummary][summary] gives an arbitrary-length fan model and
checks its literal instances:

| Configuration | Insertions at the two centres | Boundary length |
| --- | --- | --- |
| 1 | `(0,0)` | 6 |
| 2 | `(1,0)` | 7 |
| 4 | `(1,1)` | 8 |

The graph isomorphisms and ordered ring identities connect the same summary
to each reference reducibility boundary. Reconstruction for configuration 4
also supplies a compatible GSLT insertion history. The joint repair below now
constructs all its terminal witnesses through this common law; the complete
endpoint audit requires that dependency.

The uniform result here is exact colouring semantics. It applies to the fan
graphs at every length, but does not prove them reducible. The remaining family
claim must show that justified contract traces meet the ordinary summary
relation under every permitted exterior constraint.

## The specified contractions

[DiamondContract][contracts] also identifies the actual classical contracts,
using the same zero-based graph coordinates:

| Configuration | Selected edges |
| --- | --- |
| 1 | `6–7` |
| 2 | `10–7` |
| 4 | `4–10–6` and `0–8–2` (four edges in two paths) |

For configuration 4 these are exactly the two old triangle sides `a–c` and
`c–b` at each insertion. The theorem `referenceContract_insertions` proves
this correspondence through the actual insertion maps. Contract colourings
identify all three old triangle corners on each path. This differs from the
ordinary equal-endpoint branch above, where `a` and `b` agree and `c` differs.

The executable decoder now retains the ordered kernel edges for every
construction program in its fragment and proves equality with the reference
enumeration. The selected darts are then checked in the finite coordinates.
The general [contract transport theorem][contract-transport] preserves actual
colouring witnesses: selected edges have equal endpoint colours, every other
edge has different endpoint colours, and the colouring remains constant on
each face. For all three configurations, `contractTrace001`,
`contractTrace002` and `contractTrace004` identify precisely the boundary
traces consumed by classical reducibility.

## The joint boundary condition

[DiamondJointContract][joint] eliminates the contracted interior exactly. In
the forward boundary order, every contract colouring has the form

\[
[A,X,A,Y,B,Z,B,W],
\]

where `A ≠ B`, `X ≠ A`, `Z ≠ B`, and each of `Y,W` differs from both `A,B`.
Conversely, every such assignment reconstructs an actual contract colouring.
The two remaining interior colours are `A + B + W` and `A + B + Y`, with
addition in the Klein four-group. The boundary theorem is an equivalence of
existence statements with explicit reconstruction in the return direction.

The inequality `A ≠ B` comes from the edge joining the two insertion
triangles' contracted corners. It retains a relation between the pieces when
their interiors are eliminated. This is a concrete constraint analogue of
preserving a boundary response under elimination.

[DiamondKempeBoundary][obstruction] proves that either side-edge contraction
alone fails the Kempe trace-repair obligation. Each admits an actual contract
colouring with the eight-edge trace `[1,1,1,1,1,1,1,1]`. That trace is outside
the Kempe coclosure of the complete ordinary colouring relation, including
both insertion branches. The proof uses the reference's verified specification
of the converged Kempe checker and a kernel computation on this small ring.
The joint contract excludes that trace. These statements concern abstract
Kempe-closed predicates; they do not assert a realizable planar exterior
blocking an actual colouring.

An independent [finite probe][joint-probe] finds 243 traces for either single
contract, of which 75 fail the coclosure test; all 108 joint-contract traces
pass. The joint formula has 432 boundary assignments and 18 edge-trace classes
under permutation of the three nonzero colours. These counts are independently
replayed program evidence. The positive joint repair implication is now also
proved in Lean, as described below.

The probe also tests repeated insertions on the same two original triangles.
The rule that keeps contracting their original side edges fails at two
insertions on one side, and at two on one side plus one on the other. This
rules out iterating that specified rule without additional hypotheses or a
different contract. It does not rule out a different reduction for those
graphs. At configuration 2 the tested two-side contract differs from the
catalogue's specified one-edge contract. Any extension must retain the coupling
between insertions and prove its new contract conditions.

A subsequent [contract-family probe][contract-family-probe] tests every
off-ring contract of one to four edges on the first longer fan: two insertions
on one side and none on the other. It retains the oriented faces during each
insertion. There are 997 node-simple edge sets; two four-edge sets fail the
model's triad condition. Each of the remaining 995 has an explicit contract
colouring whose boundary trace belongs to one shared, 882-word Kempe-closed
predicate disjoint from all 468 ordinary traces. The saved witnesses are
rechecked on the original graph, and corrupted witnesses, missing contracts,
chromograms and face data are rejected.

These are independently replayed program certificates. The identification of
the general contract-shape model with Lean's `ValidContract` is still a formal
obligation. The closed predicate is not asserted to be an actual planar
exterior. Within the tested model, merely changing the contract, or asking
the exterior to meet every tested contract language, leaves that same abstract
obstruction available. An unrestricted fan extension therefore needs stronger
exterior information or a different reduction principle. The shared profile certificate below now covers zero or one insertion on each
side, including configurations 1, 2 and 4. It does not repair this longer fan.

## Testing a different strict replacement

The [disk-replacement probe][disk-probe] tests a different operation: erase the
four interior vertices, retain all eight distinct boundary vertices in their
cyclic order, and fill the hole with a triangulated disk having fewer interior
vertices. This supplies concrete candidate smaller graphs without choosing
another contraction of the original interior.

| Interior vertices in the replacement | Generated disk candidates |
| --- | ---: |
| 0 | 132 |
| 1 | 1,287 |
| 2 | 10,296 |
| 3 | 78,936 |

Every one of the 90,651 candidates has a proper colouring whose trace belongs
to the 921-word abstract Kempe-closed obstruction for configuration 4. The same
experiment on the first longer fan uses its 882-word obstruction and again
finds a witness for every candidate. The two target obstructions are different;
within each target, one fixed predicate works for the whole tested collection.
The individual colourings can differ between replacements.

Writing `P` for the target's ordinary boundary support and `R` for a candidate
replacement, the result has the form

```
Q is Kempe-closed,    Q ∩ P = ∅,
for every tested R,   Q ∩ support(R) ≠ ∅.
```

Consequently, merely requiring the exterior relation to meet each of these
replacement supports separately cannot prove repair. This does not address a
joint relation between the choices for different replacements. It also does
not refute the existing successful contraction: that contraction identifies
boundary vertices and retains the cross-insertion inequality described above.

The [replay program][disk-script] checks each actual colouring, Euler
characteristic, boundary incidences and vertex links. A second implementation
checks closure of each generated collection under diagonal flips. Twelve
corrupted-evidence controls are rejected; both original four-interior-vertex
disks correctly have no colouring in their own obstruction. The report stores
deterministic hashes of all candidate and witness streams, regenerated by the
program. The enumeration is the full flip component of one stacked seed at
each size, modulo interior relabelling. Its identification with **all** embedded
disks is not proved here. These results are program evidence, not a Lean
theorem or a realizable planar exterior, and earn no compression credit.

A separate direct-transfer test collapses two distinct edge colours in the
configuration-4 repair relation. It reaches 240 of 546 proper seven-port traces,
compared with 234 from ordinary colourings alone. That direct transfer is
insufficient to supply configuration 2's full repair; further seven-port Kempe
steps remain possible. The next common core argument must therefore add a
repair mechanism beyond this collapse, while retaining the coupling that made
configuration 4 work.

## Joint-profile descent across the three cores

For a fixed boundary colouring, write `L₀, L₁, L₂, L₃` for the colours
available at the four interior vertices. The centres must receive distinct
colours `a ∈ L₀` and `b ∈ L₂`; each tip must receive a colour in its own list
outside `{a,b}`. The same pair `(a,b)` constrains both tips. This is the joint
relation retained by [DiamondProfile][profile], and its terminal solver
constructs an actual interior witness through the general summary.

The [shared certificate][profile-certificate] ranks the four lists jointly,
forgetting colour names and allowing exchanges of the centres or of the tips.
It also retains boundary length: dropping that information did not support
the candidate descent. The generated finite data contain 92 ranked profile
types, including 51 terminal types and 41 nonterminal types. There are 236
trace representatives and 291 answer references, with at most six strict
rank decreases before a terminal. This measures proof descent, not physical
Kempe-chain swaps.

| Core | Proper boundary traces | Traces covered by the profile certificate | Required input |
| --- | ---: | ---: | --- |
| Configuration 1 | 183 | 183 | Every proper zero-sum six-port trace |
| Configuration 2 | 546 | 546 | Every proper zero-sum seven-port trace |
| Configuration 4 | 1,641 | 684 | All 108 traces permitted by the joint contract |

For each nonterminal representative the kernel checks an answer for **every**
matching exterior chromogram, with strict descent in the shared profile rank.
The [single-chord exchange law][chord] now supplies that coverage for 71 of the
100 nonterminal representatives:

1. Choose a boundary edge and a pair of colours to exchange. Ignore the ports
   carrying the fixed third edge colour.
2. Its exterior chord must end at a port of the opposite parity in the remaining
   cyclic order: the active ports between its two ends are paired internally.
3. Exchanging the two ends preserves that same exterior chromogram. If every
   possible partner gives a lower-ranked joint profile, one structural argument
   supplies the repair step for every exterior.

This theorem holds at arbitrary boundary length and uses no finite chromogram
checker or configuration data. The concrete consumers still check the ranks
and target references of all possible partners.

The [coupled mask law][chord-masks] handles another 24 representatives:

1. Eliminate the ports carrying the fixed third colour, retaining the cyclic
   order of the six active ports. A mask records which endpoints to exchange.
2. A single finite planar lemma supplies two disjoint chords between cyclically
   consecutive active ports. For each possible ear pair, the application must
   offer an accepted exchange of either chord or both together.
3. The general mask-transport theorem preserves the **same** exterior
   chromogram and reinserts all fixed ports. The accepted joint answer has a
   lower profile rank and eventually reconstructs an actual interior colouring.

The transport theorem has no boundary-length bound. The two-ear fact used here
is kernel checked once for all balanced Boolean bracket words on **six active
ports**; this certificate makes no claim for an arbitrary active-port count.
Each application retains nine disjoint-ear pair classifications, 216 in total.
These are separate from the finite ranks and answer references.

The [joint-anchor projection][anchor-projection] handles the last five cases:

1. Give both ends of each exterior chord the same label. An anchor observes
   the complete mask of its chord. Retain those masks jointly, including when
   two anchors observe the same chord; discard all other chord identities.
2. Two exteriors with the same projected signature offer the same exchanges
   of one selected chord or the union of two. A general induction proves that
   every such mask preserves the original exterior. The proof works at any
   active-port count, with fixed-colour ports reinserted by mask transport.
3. Classify the joint signatures of the chosen anchors. In the five concrete
   eight-active-port cases, each class has an accepted answer whose joint
   profile is terminal. The interior solver reconstructs the actual colouring.

With ports numbered from one, anchors `(1,2)` have seven signatures, `(1,5)`
have ten, and `(1,2,3)` have ten. The five consumers use respectively two, two,
and one instances of those patterns: **44 finite classifications remain**.
The classifier generates balanced unsigned skeletons and identifies equal
projections; enumeration has not disappeared. The 14 eight-port skeletons
are reduced to the seven or ten distinctions observed by each anchor pattern.

| Core | Nonterminal representatives | Single chord | Coupled ears | Joint anchors | Original covers remaining |
| --- | ---: | ---: | ---: | ---: | ---: |
| Configuration 1 | 15 | 11 | 4 | 0 | 0 |
| Configuration 2 | 52 | 45 | 7 | 0 | 0 |
| Configuration 4 | 33 | 15 | 13 | 5 | 0 |

The consumer counts are kernel checked in `structural_counts`, `coupled_counts`
and `anchor_counts`. `zero_terminal` verifies that zero strategy is used only
for genuine terminal witnesses. The local repair no longer calls the original
`coversRec` checker or its soundness theorem. Finite ranks, partner targets,
216 ear-pair classifications and 44 joint-anchor classifications remain.
This removes no additional whole configuration certificate. Answer references
increase from 289 to 291, with at most five per representative; no size,
runtime or net primitive-check reduction is claimed. The longer-fan obstruction
remains unaffected. All three kinds of step compose through the shared rank.

There is a concrete coupled example in `coupled_example`. On the boundary
trace `22231123`, take the disjoint cyclic ears at ports 2–3 and 8–1, with ports
numbered from one. The checked chromogram pairs those ears and ports 4–7:

| Exchange | Resulting trace | Shared profile rank |
| --- | --- | ---: |
| Neither | `22231123` | 2 |
| Ports 2–3 | `23331123` | 0 |
| Ports 8–1 | `32231122` | 0 |
| Both | `33331122` | 1, with a genuine interior-colouring witness |

Rank zero means the trace is outside this ranked certificate, not that no
colouring or other repair exists. The combined exchange retains the original
chromogram and reaches a terminal interior witness. Its two choices must be
evaluated together.

[Input coverage][profile-inputs] verifies the actual required domains. The
[graph consumers][profile-reduction] then reconstruct literal graph colourings,
transport the ordered rings, and validate the reference contracts. The complete
proof supplies strict reduction and classical geometric coverage.

This is a bounded profile explanation of three core shapes, using a general
single-chord law, a six-active-port coupled rule and general joint-anchor
projection. The ranked-certificate principle is reused from the reference
proof; the projected classification and rank data remain finite. Repair for these inputs can
descend using this particular joint observable and can reconstruct genuine
colourings. Boundary length separates the three shapes, so the rank table does
not by itself prove a law independent of ring size. It also does not assert
that these are all repairable eight-port traces.

The [twenty-five-root audit][profile-audit] excludes the original configuration 1,
2 and 4 certificates, the former diamond repair bodies, global Kempe fixed-point
computations, `coversRec` and its soundness theorem, and the complete theorem
from the new local proofs. The complete
endpoint audit requires the replacement proofs. All 633 configurations remain;
630 original certificate dependencies are retained. No reduction in certificate
bytes or kernel time is claimed. [Measurements][profile-measurements] record
those costs separately from the dependency replacement.

## A base repair shared through boundary splitting

For a Kempe-closed exterior relation `Q`, define its split relation by

```
Split(Q) = { a :: b :: t | a ≠ 0, b ≠ 0, a ≠ b, Q((a+b) :: t) }.
```

Addition is the Klein four-group operation. [KempeBoundarySplit][split-law]
proves that `Split(Q)` is Kempe-closed at every boundary length. Its chromogram
transformation lifts the original matching constraint, and every resulting
answer collapses to a valid original answer. Keeping the two colours together
is essential: their sum is the colour seen by the old exterior.

Suppose a larger piece repairs every proper zero-sum trace, and each successful
split colouring reconstructs in the smaller piece. The theorem
`repairs_collapse` then transfers repair to the smaller piece for every
Kempe-closed exterior. This is a uniform implication with explicit hypotheses;
it neither assumes all target colourings lie in the old-graph branch nor
claims that arbitrary insertion preserves reducibility in the forward direction.

[DiamondSplitRepair][split-repair] established the original consumer using
configuration 2's reference certificate. The current
[profile consumer][profile-reduction] retains its reconstruction argument:

1. Configuration 2's joint-profile certificate covers all 546 proper
   seven-port traces and supplies the base repair.
2. In an actual configuration-2 colouring, the first two edge colours are
   `a = k(0)+k(1)` and `b = k(1)+k(2)`. The split relation enforces `a ≠ b`,
   hence `k(0) ≠ k(2)`. Deleting vertex 1 and restoring the old boundary edge
   therefore gives a genuine configuration-1 colouring. Its trace begins
   with `a+b`; the other ports and their order are retained exactly.
3. The reference contract of configuration 1 is valid and every contract trace
   is proper. The transferred repair therefore establishes its reducibility.
   The complete assembly consumes this result through the existing embedded
   contraction and reconstruction theorem, without its old `Bulk.Cfg000` proof.

The direction matters: graph construction is `1 → 2`, while this repair proof
transfers `2 → 1`. Configuration 2 remains the base, now supplied by the shared profile law. Configuration 4's
joint contract can identify the old endpoints, giving two equal edge colours;
that is outside the split relation above. Its coupled repair remains necessary.

## The earlier coupled boundary repair

[DiamondBoundaryRepair][boundary-repair] proves a law for any predicate on
eight-edge traces that contains twenty-three specified terminal patterns.
Every admissible joint trace is in its Kempe coclosure: every Kempe-closed
exterior predicate containing that trace meets the terminal predicate.
The law imports no configuration or configuration certificate.

First translate and permute three distinct vertex colours to `0,1,2`.
The remaining choices give eighteen normalized trace types. Twelve already
have ordinary colourings. Ten repair states handle the remaining six types
and their intermediate answers:

| Proof level | Input words | Answer levels |
| --- | --- | --- |
| 1 | `11123312`, `11213321`, `11232223`, `11233323` | Ordinary colourings |
| 2 | `11213123`, `11231213` | Ordinary colourings or level 1 |
| 3 | `11213132`, `11231312` | Ordinary colourings or level 2 |
| 4 | `11231132` | Ordinary colourings or level 3 |
| 5 | `11231123` | Ordinary colourings or level 4 |

Each state answers **every** matching chromogram, after an allowed colour
permutation. [KempeAnswerComposition][answers] composes these answers using
the reference's proved matching-cover specification. The five levels measure
proof dependency depth, not a bound on the number of physical Kempe-chain swaps.

[DiamondJointRepair][joint-repair] checks the boundary and four-vertex interior
conditions for each terminal pattern, then reconstructs a literal twelve-vertex
colouring through the common summary. The resulting colouring separates the
endpoints of every actual map edge. Exact contract
elimination supplies the input condition. The theorem `reducible` combines
this repair implication with the proved geometric contract conditions.
`compatible_history` also supplies the chosen colouring's GSLT history through
the two insertion alternatives.

This was the first configuration-4 replacement. The current
[complete range][family-range] instead consumes the shared profile repair and
split transfer described above. The earlier theorem remains available as a
smaller, independently checked explanation of the joint contract's 18 input
types. Shared reference modules still load old declarations; runtime and
artifact-size savings are not claimed.

## One repair through an unbounded family of ear contexts

[DiamondEarFamily][ear-family] supplies a further compositional result for all
three cores. A triangular ear adds a fresh vertex adjacent to the first two
boundary vertices **while retaining their edge**. Repeating this operation at
the first boundary edge produces a precisely defined family of any length.
It is a different operation from the triangle subdivision studied above.

1. **Actual graphs and exact semantics.** [BoundaryEarRepair][ear-graph]
   proves that the new boundary relation is exactly the joint split: two
   distinct nonzero edge colours replace their sum. Both directions construct
   genuine graph colourings, preserving every old vertex colour.
2. **Repair through the context.** [KempeBoundaryMerge][ear-merge] proves that
   existentially joining the two ports preserves Kempe-closed exterior
   relations. Its chord surgery retains their correlation. This lets the
   core's repair work against every compatible exterior after an ear is added.
3. **Arbitrary repetition and reconstruction.** [BoundaryEarGSLT][ear-gslt]
   composes the law along any finite route of these ear operations. The result
   supplies a matching colouring and every intermediate colouring witness.
   An `n`-ear member has exactly `n` additional vertices, so erasing a nonempty
   ear sequence strictly decreases size. Admissible starting relations are
   proved nonempty at every length.

This is a common **context law**, with the three existing core repairs as
consumers. It adds no per-ear repair certificate. The configuration-4 input
retains its full coupled contract relation. Support and actual colouring
witnesses are proved; equal colouring counts and an executable sequence of
physical Kempe swaps are not asserted.

The theorem does not replace the three cores by one core argument. It also
does not establish embedded-map recognition, a new valid contraction for longer
fans, or geometric coverage. The formal operation constructs simple graphs
with ordered boundaries; using it as a specific embedded disk operation needs
the corresponding embedding bridge. The completed theorem retains 633 catalogue
entries and 630 original certificate dependencies. The ear-family consumers
still use the earlier core proofs; connecting them to the new profile proofs
is separate from the complete endpoint integration.

The [12-root audit][ear-audit] checks the generic law's independence from the
catalogue, the actual graph consumers, compatible histories, and strict size
decrease. [Measurements][ear-measurements] distinguish this family result from
certificate compression. An [independent finite replay][ear-probe] checks
4,652 chromograms and the first three ears on each literal diamond graph.

## Compatible histories

[DiamondInsertionGSLT][routes] interprets this reconstruction as a GSLT route.
Its initial state is the full tree of colouring alternatives. The first step
assembles a configuration-2 colouring when that branch is used; the second
assembles a reference configuration-4 colouring. The contracted alternative at
the second step is retained as its own source of witnesses.

`supported_iff` identifies the route's output exactly, and `every_coloring`
recovers a compatible history from every final reference colouring.
`viable_iff` retains any terminal observation. This is an account of the whole
reconstruction tree; it does not require every final colouring to descend from
an old configuration-1 colouring alone.

`constructed` supplies one complete successful history from an explicit,
kernel-checked configuration-1 colouring, including the actual reference-map
colouring produced at its end.

## Scope and remaining work

Three original reference certificate dependencies are replaced, while all 633
catalogue entries remain. The shared finite profile certificate supplies
configuration 2 and configuration 4; configuration 1 inherits repair through
the general split law. The profile certificate also proves configuration 1's
repair directly. A structural theorem that removes further finite cover
obligations, a valid broader core reduction and geometric coverage remain the
research tasks. The negative longer-fan and disk-replacement results continue
to constrain any proposed extension.

The
[geometry audit][audit] checks 28 roots; the [contract audit][contract-audit]
checks another 13. Both exclude classical certificate and complete theorem
dependencies. The [joint boundary audit][joint-audit] adds nine roots for the
elimination and obstruction results, with the same exclusions. The new
[repair audit][repair-audit] checks eight roots, excluding both existing
configuration certificates and global Kempe fixed-point computations.
The [summary audit][summary-audit] checks eleven roots linking the generic
witness equivalence to all three reference rings and the GSLT history.
The [geometry record][measurements], [contract record][contract-measurements]
and [joint boundary record][joint-measurements] retain source hashes, artifact
hashes and kernel/frontend costs. The [repair measurements][repair-measurements]
record the integrated replacement. Run
`lake build kernelConfigurationFamilies` in the classical package after
preparing its dependencies as described in the [package guide][package].
The [summary measurements][summary-measurements] record the subsequent common-law
integration, which itself replaced no additional certificate. The
[split measurements][split-measurements] record the later transfer and the
additional dependency it replaces. The eight-root [split audit][split-audit]
requires configuration 2's base proof, verifies witness reconstruction and
excludes configuration 1's original certificate.

[alternatives]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryTriangleAlternatives.lean
[elimination]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DiamondBoundaryElimination.lean
[summary]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondBoundarySummary.lean
[summary-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondBoundarySummaryAudit.lean
[summary-measurements]: ../../../../tools/fourcolor/classical/diamond-summary-measurements.json
[boundary-repair]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondBoundaryRepair.lean
[answers]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeAnswerComposition.lean
[joint-repair]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondJointRepair.lean
[family-range]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondFamilyReducibility.lean
[complete-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/CompleteAudit.lean
[repair-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondJointRepairAudit.lean
[repair-measurements]: ../../../../tools/fourcolor/classical/diamond-joint-repair-measurements.json
[executable]: ../../../../lean/fourcolor-classical/MettapediaFourColor/ExecutableConfiguration.lean
[configurations]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondConfigurations.lean
[insertions]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondInsertion.lean
[routes]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondInsertionGSLT.lean
[audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondInsertionAudit.lean
[contracts]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondContract.lean
[contract-transport]: ../../../../lean/fourcolor-classical/MettapediaFourColor/ConfigurationContract.lean
[joint]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondJointContract.lean
[obstruction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondKempeBoundary.lean
[joint-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondKempeBoundaryAudit.lean
[joint-probe]: ../../../../tools/fourcolor/classical/diamond-joint-repair-probe.json
[contract-family-probe]: ../../../../tools/fourcolor/classical/diamond-contract-family-probe.json
[disk-probe]: ../../../../tools/fourcolor/classical/diamond-disk-replacement-probe.json
[disk-script]: ../../../../tools/fourcolor/classical/probe_diamond_disk_replacements.py
[joint-measurements]: ../../../../tools/fourcolor/classical/diamond-joint-boundary-measurements.json
[contract-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondContractAudit.lean
[contract-measurements]: ../../../../tools/fourcolor/classical/diamond-contract-measurements.json
[measurements]: ../../../../tools/fourcolor/classical/diamond-geometry-measurements.json
[package]: ../../../../lean/fourcolor-classical/README.md
[split-law]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeBoundarySplit.lean
[split-repair]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondSplitRepair.lean
[split-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondSplitRepairAudit.lean
[split-measurements]: ../../../../tools/fourcolor/classical/diamond-split-measurements.json
[ear-family]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondEarFamily.lean
[ear-graph]: ../../../../lean/fourcolor-classical/MettapediaFourColor/BoundaryEarRepair.lean
[ear-merge]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeBoundaryMerge.lean
[ear-gslt]: ../../../../lean/fourcolor-classical/MettapediaFourColor/BoundaryEarGSLT.lean
[ear-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondEarFamilyAudit.lean
[ear-measurements]: ../../../../tools/fourcolor/classical/diamond-ear-measurements.json
[ear-probe]: ../../../../tools/fourcolor/classical/diamond-ear-probe.json

[profile]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondProfile.lean
[profile-certificate]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondProfileCertificate.lean
[profile-inputs]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondProfileFamilyRepair.lean
[profile-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondProfileReducibility.lean
[profile-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondProfileAudit.lean
[profile-measurements]: ../../../../tools/fourcolor/classical/diamond-profile-measurements.json
[chord]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeChordExchange.lean
[chord-masks]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeChordMasks.lean
[anchor-projection]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeAnchorProjection.lean
