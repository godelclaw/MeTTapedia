# Compositional graph semantics in GSLT

This Lean library connects graph representations, operational paths and actual
colouring witnesses. It includes seven entry points and their source dependency
closure, with an axiom audit. It does not assert the Four Colour Theorem.

## Start here

- [Graph representation overview](Mettapedia/GraphTheory/Representation/README.md):
  edge lists, adjacency matrices, adjacency rows, neighbour sets, incidence
  matrices and compressed sparse rows.
- [Representation GSLT](Mettapedia/GraphTheory/Representation/RepresentationGSLT.lean):
  graph-preserving conversions and their paths.
- [Colouring transport](Mettapedia/GraphTheory/Representation/ColoringTransport.lean):
  conversions preserve actual colourings, prescribed boundary values and counts.
- [Relational route semantics](Mettapedia/GSLT/Core/RelationalRouteSemantics.lean):
  compatible witnesses compose along routes; certified replacements preserve them.
- [Cubic construction semantics](Mettapedia/GraphTheory/FourColor/VertexConstructionGSLT.lean):
  route acceptance is equivalent to colouring the decoded graph piece.
- [Source construction semantics](Mettapedia/GraphTheory/FourColor/SourceConstructionGSLT.lean):
  transport between construction presentations with their physical meanings.
- [MeTTaIL premise application](Mettapedia/OSLF/MeTTaIL/PremiseRouteSemantics.lean):
  the same replacement theorem preserves compatible premise answers.

An adjacency matrix records which vertices are joined. A colouring-transfer
matrix records which boundary colourings a piece permits. These are different
interpretations. The representation conversions here preserve simple-graph
meaning; embedding order and individual multigraph edges need additional data.
Compatible witnesses may be selected along a construction path. No theorem
requires every partial colouring to survive every operation.

## Build

Use the pinned Lean toolchain and Mathlib revision:

```sh
lake exe cache get
lake build GSLTGraphAudit
```

The audit rejects any axiom other than `propext`, `Classical.choice` and
`Quot.sound` among the imported public library declarations. The source manifest
records the included module hashes. Generated build artifacts are not included.

## Attribution

The Mettapedia sources retain the repository's MIT licence and their original
headers. The representation modules credit their origin in the linked overview.
The required `Foundation` modules come from FormalizedFormalLogic/Foundation
and its Lean 4.34 compatibility port at revision
`6769009b4ca6006aefcf4176e0c7297a108a28df`; their Apache-2.0 licence is retained in
`LICENSES/Foundation-Apache-2.0.txt`. They are an unchanged dependency subset,
not a new implementation of that library. Mathematical source credits remain
in the individual modules.
