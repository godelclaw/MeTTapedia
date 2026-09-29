# The diamond family: actual graphs and both colouring branches

Configurations 1, 2 and 4 in the classical catalogue share an internal diamond.
Two boundary-triangle insertions relate their complete embedded graphs:

```text
configuration 1  ── insert in a boundary triangle ──▶  configuration 2
configuration 2  ── insert in a boundary triangle ──▶  configuration 4
```

These correspondences, their boundary orders and their complete colouring
semantics are now kernel-checked. This realizes one of the local insertion
ideas in the compositional programme. The remaining task is to use the family
semantics to prove reducibility and replace independent catalogue checks.

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
under permutation of the three nonzero colours. These counts and the positive
joint repair test are program evidence, separate from the Lean elimination
and obstruction theorems.

The probe also tests repeated insertions on the same two original triangles.
The rule that keeps contracting their original side edges fails at two
insertions on one side, and at two on one side plus one on the other. This
rules out iterating that specified rule without additional hypotheses or a
different contract. It does not rule out a different reduction for those
graphs. At configuration 2 the tested two-side contract differs from the
catalogue's specified one-edge contract. The next family argument must retain
the coupling between insertions and establish the joint Kempe implication.
The existing classical certificate already proves configuration 4 reducible;
the open task is to replace that certificate with the family argument.

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

## What remains

The missing implication is reducibility transport: every contract boundary
trace must lie in the Kempe coclosure of the ordinary boundary traces. The
ordinary traces include both colouring branches. The geometry, specified
contracts and both kinds of trace now have a proved connection to that exact
reference obligation. The family proof must establish this Kempe implication
before it can replace any existing reducibility certificate.

No reducibility certificate has been removed, and the complete Four Colour
assembly still uses all 633 catalogue entries. The
[geometry audit][audit] checks 28 roots; the [contract audit][contract-audit]
checks another 13. Both exclude classical certificate and complete theorem
dependencies. The [joint boundary audit][joint-audit] adds nine roots for the
elimination and obstruction results, with the same exclusions.
The [geometry record][measurements], [contract record][contract-measurements]
and [joint boundary record][joint-measurements] retain source hashes, artifact
hashes and kernel/frontend costs. Run
`lake build kernelConfigurationFamilies` in the classical package after
preparing its dependencies as described in the [package guide][package].

[alternatives]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryTriangleAlternatives.lean
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
[joint-measurements]: ../../../../tools/fourcolor/classical/diamond-joint-boundary-measurements.json
[contract-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondContractAudit.lean
[contract-measurements]: ../../../../tools/fourcolor/classical/diamond-contract-measurements.json
[measurements]: ../../../../tools/fourcolor/classical/diamond-geometry-measurements.json
[package]: ../../../../lean/fourcolor-classical/README.md
