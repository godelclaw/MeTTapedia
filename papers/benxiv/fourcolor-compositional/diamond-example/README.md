# The diamond family: actual graphs and both colouring branches

Configurations 1, 2 and 4 in the classical catalogue share an internal diamond.
Two boundary-triangle insertions relate their complete embedded graphs:

```text
configuration 1  ── insert in a boundary triangle ──▶  configuration 2
configuration 2  ── insert in a boundary triangle ──▶  configuration 4
```

These correspondences, their boundary orders and their complete colouring
semantics are now kernel-checked. The coupled boundary law now proves
configuration 4 reducible and replaces its original certificate dependency
in the complete proof. A general boundary-split law also transfers
configuration 2's repair to configuration 1. Their two obligations now share
one base certificate. A common rule also covering configuration 4, and a
justified broader family, remain the next steps.

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
exterior information or a different reduction principle. The next positive
target remains a common structural law for zero or one insertion on each side,
which includes configurations 1, 2 and 4.

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

[DiamondSplitRepair][split-repair] supplies the concrete consumer:

1. Configuration 2's existing rank planes cover all 546 proper seven-port
   traces. Its verified checker supplies the base repair.
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
transfers `2 → 1`. Configuration 2 remains the retained base. Configuration 4's
joint contract can identify the old endpoints, giving two equal edge colours;
that is outside the split relation above. Its coupled repair remains necessary.

## From the coupled boundary law to reducibility

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

[DiamondFamilyReducibility][family-range] inserts this result into the full
633-case range. The [complete endpoint audit][complete-audit] requires the new
law and the split transfer, and rejects every dependency on the original
`Bulk.Cfg000` and `Bulk.Cfg003` certificates. The other 631 reference
certificate dependencies remain. Shared reference modules still load the
old declarations; runtime and artifact-size savings
are not claimed.

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

Two reference certificate dependencies are replaced, while all 633 catalogue
entries remain. Configuration 2 supplies its own obligation and configuration
1's through a uniform transfer; configuration 4 uses the coupled law.
This does not yet give one rule replacing the checks for all three configurations,
or a valid contraction rule for arbitrarily long insertion fans. Those are
separate family and geometric coverage tasks.

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
[joint-measurements]: ../../../../tools/fourcolor/classical/diamond-joint-boundary-measurements.json
[contract-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondContractAudit.lean
[contract-measurements]: ../../../../tools/fourcolor/classical/diamond-contract-measurements.json
[measurements]: ../../../../tools/fourcolor/classical/diamond-geometry-measurements.json
[package]: ../../../../lean/fourcolor-classical/README.md
[split-law]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeBoundarySplit.lean
[split-repair]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondSplitRepair.lean
[split-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondSplitRepairAudit.lean
[split-measurements]: ../../../../tools/fourcolor/classical/diamond-split-measurements.json
