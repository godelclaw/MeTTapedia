# Graph representations and their operational semantics

Six layouts share one `SimpleGraph (Fin n)` meaning, and each has its own
observers. Conversion functions construct target data and prove that the graph
meaning is preserved. The representation GSLT records routes of these
conversions; the lookup GSLTs expose the primitive work of individual queries.

| Layout | Data and principal observation |
| --- | --- |
| Edge list | Ordered edge occurrences; linear adjacency scan |
| Adjacency matrix | Symmetric Boolean cells; one-cell adjacency lookup |
| Adjacency rows | Ordered neighbor lists; scan of the selected row |
| Neighbor finite sets | Finite neighbor sets; abstract membership operation |
| Incidence matrix | Vertex/edge columns; one-cell incidence lookup and column scan for adjacency |
| CSR | Packed neighbor rows with offsets; traversal of the selected slice |

`Basic` sets up the common operational vocabulary and `Transformations`
constructs the conversions. `RepresentationGSLT.convertPath` gives a route from
any supported layout to any selected layout through an adjacency matrix.
`MatrixBridge` connects operational matrices to Mathlib's `Matrix` and
`SimpleGraph.adjMatrix`; `MatrixSemantics` adds relabelling and algorithmic
semantics, and `SliceSemantics` places the layouts in Mathlib's category of
meanings.

## Transport along conversions

[`SemanticTransport`](SemanticTransport.lean) transports every proposition
about the denoted graph through a total conversion, for example
Hamiltonicity, connectivity, bipartiteness and acyclicity.
[`SemanticInvariant`](SemanticInvariant.lean) packages graph meaning and matrix
answers as GSLT semantic invariants, with negative controls for layout names
and query phases.

[`ColoringTransport`](ColoringTransport.lean) transports actual proper vertex
colorings. Each vertex keeps its assigned color. The equivalence also preserves
prescribed colors at named boundary vertices, hence boundary support and
finite coloring counts. Transports compose and do not depend on the chosen
conversion history. `liftPath` constructs all intermediate coloring witnesses
along each chosen representation route, starting from an explicitly supplied
coloring, using the generic relational route semantics of
`GSLT/Core/RelationalRouteSemantics`.

[`MatrixOperationalTranslation`](MatrixOperationalTranslation.lean) packages
graph-matrix lookup into raw-matrix lookup as a `CoveredTranslation`: source
steps map forward and every target step leaving an encoded state has a source
lift. Linear scanning and single-cell lookup have different primitive step
shapes; `no_scan_to_matrix_step_translation` rules out mapping every scan step
to exactly one matrix lookup step. The graph conversions and their complete
query answers remain valid.

These are contracts for simple-graph meaning. The edge-list denotation forgets
loops, multiplicity and occurrence order, so it cannot serve as an exact
multigraph or embedding representation without additional data. Cyclic orders
are enrichments rather than interchangeable layouts (see
[`RotationSystem`](RotationSystem.lean)); individual edge colorings and map
operations need their own adapters. Adjacency matrices here record edges. A
matrix recording which boundary colorings a graph piece permits is a different
interpretation and needs its own contract. No theorem here supplies an initial
coloring.

## Further modules

- Resource accounts: `CostModel`, `CostedRepresentationGSLT`,
  `EdgeListToMatrixCost`, `MultiView`.
- Occurrence-by-occurrence materialization: `EdgeListToMatrixGSLT`,
  `EdgeListToMatrixLanguageDef`, `EdgeListToMatrixModule`.
- Revision, query and world models: `RevisionQuery`, `RevisionPortfolio`,
  `SemanticRevisionGSLT`, `WorldModelGSLT`, `MigrationExamples`.
- Other graph structures and views: `Hypergraph`, `Metagraph`,
  `HigherGraphSemanticGSLT`, `DistinctionBridge` (OSLF distinction graphs),
  `FrontierAffine` (graph frontiers as ordered affine actions).

`Mettapedia.GraphTheory.Representation` imports all of these.
`SurfaceLanguage`, a compositional surface language for representations, is
not part of that umbrella. From the Lean project directory, the coloring and
operational contracts build with

```bash
lake build Mettapedia.GraphTheory.Representation.ColoringTransport Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation
```
