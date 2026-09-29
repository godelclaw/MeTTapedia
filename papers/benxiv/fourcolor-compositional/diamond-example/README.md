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

The missing implication is reducibility transport. The two-branch language must
meet the appropriate exterior Kempe-closure obligation, with the specified
contraction retained for configuration 4. Geometry and complete colouring
semantics now have a proved connection to that exact reference problem.
Configuration 4's classical certificate specifies its own contract, whose
edge correspondence must also be proved.

No reducibility certificate has been removed, and the complete Four Colour
assembly still uses all 633 catalogue entries. The
[audit][audit] checks 28 roots and excludes classical certificate and complete
theorem dependencies. The [measurement record][measurements] records source
hashes, artifact hashes and kernel/frontend costs. Run
`lake build kernelConfigurationFamilies` in the classical package after
preparing its dependencies as described in the [package guide][package].

[alternatives]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryTriangleAlternatives.lean
[executable]: ../../../../lean/fourcolor-classical/MettapediaFourColor/ExecutableConfiguration.lean
[configurations]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondConfigurations.lean
[insertions]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondInsertion.lean
[routes]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondInsertionGSLT.lean
[audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondInsertionAudit.lean
[measurements]: ../../../../tools/fourcolor/classical/diamond-geometry-measurements.json
[package]: ../../../../lean/fourcolor-classical/README.md
