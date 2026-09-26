# Graph representations and their operational semantics

The six layouts here have a common `SimpleGraph (Fin n)` meaning and their own
observers. Conversion functions construct target data and prove that graph
meaning is preserved. The representation GSLT records routes of these
conversions; the lookup GSLTs expose the primitive work of individual queries.

| Layout | Data and principal observation |
| --- | --- |
| Edge list | Ordered edge occurrences; linear adjacency scan |
| Adjacency matrix | Symmetric Boolean cells; one-cell adjacency lookup |
| Adjacency rows | Ordered neighbour lists; scan of the selected row |
| Neighbour finite sets | Finite neighbour sets; abstract membership operation |
| Incidence matrix | Vertex/edge columns; one-cell incidence lookup and column scan for adjacency |
| CSR | Packed neighbour rows with offsets; traversal of the selected slice |

`Transformations` constructs the conversions. `RepresentationGSLT.convertPath`
gives a route from any supported layout to any selected layout through an
adjacency matrix. `MatrixBridge` connects operational matrices to Mathlib's
`Matrix` and `SimpleGraph.adjMatrix`.

## Colouring and execution contracts

[`ColoringTransport`](ColoringTransport.lean) transports actual proper vertex
colourings. Each vertex keeps its assigned colour. The equivalence also
preserves prescribed colours at named boundary vertices, hence boundary support
and finite colouring counts. Transports compose and do not depend on the chosen
conversion history. `liftPath` constructs all intermediate colouring witnesses
along each chosen representation route, starting from an explicitly supplied
colouring, using the generic relational-route semantics.

[`MatrixOperationalTranslation`](MatrixOperationalTranslation.lean) packages
graph-matrix lookup into raw-matrix lookup as a `CoveredTranslation`: source
steps map forward and every target step leaving an encoded state has a source
lift. Linear scanning and single-cell lookup have different primitive step
shapes; `no_scan_to_matrix_step_translation` rules out mapping every scan step
to exactly one matrix lookup step. The graph conversions and their complete
query answers remain valid.

These are contracts for simple-graph meaning. The edge-list denotation forgets
loops, multiplicity and occurrence order. It cannot be used as an exact
multigraph or embedding representation without additional data. Cyclic orders,
individual Tait-coloured edges, and hypermap operations require their own
adapters. Adjacency matrices here record edges; the boundary transfer matrices
in the Four Colour library record colouring counts. No theorem here supplies
an initial colouring or proves the Four Colour Theorem.

## Source and validation

`Basic`, the six layout modules, `Transformations`, `RepresentationGSLT`, and
`MatrixBridge` were imported unchanged from
[`zariuq/MeTTapedia` at `cfe595631d96125f37e9860f5ac34d16884ed444`](https://github.com/zariuq/MeTTapedia/tree/cfe595631d96125f37e9860f5ac34d16884ed444/lean/mettapedia/Mettapedia/GraphTheory/Representation).
They use the repository's MIT license and were checked with the local toolchain.
The colouring transport and packaged operational contracts are subsequent
additions. From the Lean project directory, build their complete dependency set
with:

```bash
lake build Mettapedia.GraphTheory.Representation.ColoringTransport Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation
```
