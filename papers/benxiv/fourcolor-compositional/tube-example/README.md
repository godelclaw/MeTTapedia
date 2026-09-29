# One boundary certificate for an infinite tube family

For the literal zigzag tube with five ordered ports at **each** end, every
tube of at least four rings has exactly the boundary-colouring relation of
the four-ring tube. A tube with five or more rings can therefore be shortened
inside any closed sewing context, with reconstruction preserving every
exterior edge colour. If the original map is connected, bridgeless,
spherical and cubic with cyclic vertex rotations, so is the replacement.

The same certificate applies to every marked tube in any finite GSLT chain,
including chains with arbitrary other open pieces between the tubes. The
chain is realized by actual graph gluing, and its compatible route witnesses
are equivalent to actual colourings of that graph.

This is a completed instance of the corridor mechanism in the compositional
programme. The finite width-five certificate already existed; the new result
connects it to the newer literal replacement theorem and to normalization of
whole construction families. No classical configuration check is removed.

## 1. Check one equality with its full boundary meaning

Let `R` be the relation between the two ordered colour words admitted by one
literal ring. There are `3^5 = 243` nonzero words at each end. The existing
[`five_ring_stabilizes`][certificate] checks the finite equality

\[
R^5 = R^4.
\]

The check uses the Lean kernel. [`accepts_iff_testBit`][decoder] proves that
the table means actual ring colourings. The new
[`mem_iterate_singleton_iff_transfer`][normalization] connects its iterated
reachable sets to compatible sequences of those colourings. Words containing
a zero colour are rejected on both sides, so the final equality covers the
entire formal boundary type.

Ordered words are retained. This is not a test using only colour counts or a
claim that all words can connect to all others.

## 2. Propagate the certificate and reconstruct the physical graph

Composing the equality with another ring gives `R^6 = R^5 = R^4`.
Induction proves the same for every larger length. Thus, writing `T_l` for
the physical tube of `l` rings,

\[
\operatorname{support}(T_l)
 = \operatorname{support}(T_{\min(l,4)}) \qquad (l\geq1).
\]

[`five_tube_normalize`][normalization] proves this formula. In the Lean
definition `tube 5 n`, the parameter `n` counts rings after the first, so
the normal form is `tube 5 (min n 3)`.

[`strict_five_tube_reduction`][normalization] combines it with the existing
geometric replacement theorems. Every ring has ten vertices. A tube with
`l > 4` rings loses exactly `10(l−4)` vertices when shortened. The seam
matching is retained, as are the closed map's required geometric properties.
`reconstructFiveTube_isTait` restores a proper colouring of the longer tube;
`reconstructFiveTube_exterior` proves pointwise preservation of all exterior
edge colours, including edges sewn to its boundary.

The uniform theorem for arbitrary circumference `k ≥ 3` gives a sufficient
normal form of `2k(k−1)` rings. At circumference five, this integration of
the earlier finite certificate improves that physical normal form from
forty rings to four: 400 tube vertices become 40. Minimality of the four-ring
threshold is not asserted.

## 3. Compose the replacements across a whole family

The generic [`BoundaryReduction`][generic] packages a local replacement and
maps of colouring witnesses in both directions. Its `forwardRoute` and
`backwardRoute` compose those maps, retaining every shared seam word.
`boundary_predicate_iff` preserves any predicate on the two outer states;
`in_context_iff` preserves compatibility with arbitrary initial and final
routes.

[`ZigzagTubeBoundaryGSLT`][operational] supplies a concrete consumer. Its
events retain actual open pieces and marked five-port tubes. For example,
for every intermediate piece `P` and every pair of positive lengths,

```text
T_l ; P ; T_m    →    T_min(l,4) ; P ; T_min(m,4)
```

preserves exactly the admitted outer colour words. The theorem covers any
finite number of marked tubes and intervening pieces. `Chain.witnessEquiv`
connects the route to literal serial gluing, and
`Chain.normalize_boundary_iff` proves preservation under an arbitrary test
of the outer boundary. That test can require compatibility with a fixed
exterior. Interior colourings can change, and their numbers need not agree.

This is the relational counterpart of [linear boundary elimination][kron]:
retain exactly what the surrounding system can observe after eliminating
interior variables. The linear theorem uses an invertible interior operator
and retains its forcing contribution. The colouring theorem instead retains
a relation and reconstructible witnesses; it uses no matrix inverse and
does not import the linear module.

## Recognizing compatible seams in actual graphs

The [geometric seam theorem][seam] removes a coordinate assumption from the
embedded-row argument. Suppose two consecutive zigzag rows have their actual
ambient vertex rotations, and every face crossing their common seam is a
hexagon. Their complete boundary maps construct a permutation `s` pairing the
first row's output ports with the next row's input ports. The theorem proves

\[
s(i+1)=s(i)+1, \qquad s(i)=i+s(0).
\]

Each row supplies a three-step arc of the ambient face permutation. Combining
the two arcs with the six-step return around the intervening hexagon forces
the successor equation. Induction around the cyclic index set gives the
translation. This proof works at every positive width and does not enumerate
permutations. Reindexing by this one offset gives exactly the usual two-ring
colouring relation, including reconstruction of actual side colourings.

The [chain theorem][hex-chain] accumulates these offsets through any number of
rows. The [whole-strip assembly][hex-assembly] now proves that the recognized
chain is the literal serial tube: every original strip vertex and dart is
accounted for, with internal edge mates, vertex rotations and both ordered
interfaces preserved.

The [exterior-sewing theorem][exterior] cuts out precisely those vertices.
Its complete port bijection and dart/vertex equivalences identify the sewn
map with the original one. [Exact structural transport][transport] preserves
cubicity, connectedness, bridgelessness and the quotient-face Euler equation.
The exterior may be disconnected; no separate connected-shore premise is
needed. The [closed-witness bridge][closed-witness] reconstructs actual edge
colourings while retaining every exterior edge colour.

Consequently, [physical reduction of the recognized strip][hex-reduction]
consumes the earlier four-ring certificate. For a strip with `l ≥ 5` rows it
removes exactly `10(l−4)` vertices, stays in the original bridgeless spherical
cubic map class, and restores a genuine colouring of the original graph from
one of the smaller graph. `hexagonal_five_length_le_four` excludes such a
strip from a graph-backed vertex-minimal counterexample. This improves the
previous [coarse shore-splice bound][hex-exclusion] from 446,403 to four rows.
The four-ring threshold is sufficient; its optimality is not claimed.

The facial adapter derives row orientation from the original face incidences
and alternating retained degrees, then consumes this reduction directly in
`FacialCycleChord.chain_length_le_four`. Suitable alternating-row supply,
complete interfaces, and control of width remain geometric tasks. An unmarked
band or a large hexagonal patch alone does not provide them.

An [independent dart-permutation probe][seam-probe] checks all 5,912 seam
permutations at widths two through seven. Exactly the cyclic translations
give hexagonal seam faces throughout. Its closed five-port example has two
rows capped by pentagons: 30 vertices, 45 edges, twelve pentagonal faces and
five hexagonal faces. A shift by two ports retains these counts and a checked
Tait colouring. A noncyclic control instead has an 18-sided seam face and
Euler characteristic zero; it is a toroidal example, not a planar
counterexample. These examples are program checks, separate from the general
Lean proofs.

A second [strip probe][strip-probe] checks exact dart and rotation relabelling
for selected three-, five- and seven-row capped strips, including nonzero
accumulated seam shifts. It reconstructs colourings of the five- and seven-row
maps from a four-row map while fixing all 20 exterior edge colours. The maps
have respectively 60 and 80 vertices before replacement and 50 afterwards.
These are independent finite program checks, not Lean certificates.

The expanded [geometric audit][hex-audit] requires both the actual
facial-recognition and four-ring reduction consumers, and rejects classical
`FourColor` dependencies. The [strip measurement record][strip-measurements]
separates these proofs from the reused finite five-port stabilization
certificate and the earlier [seam checkpoint][hex-measurements]. No
configuration or certificate is removed by this geometric result.

## Constructing a row from its surrounding faces

The [collar theorem][collar] starts with one recognized row, rather than an
assumed sequence of rows. Let `pᵢ` be its actual output darts. The ambient
edge reversal `α` and vertex rotation `ρ` determine the candidate new vertices:

```
xᵢ = α(pᵢ)          incoming dart at the first new vertex
yᵢ = α(ρ(xᵢ))      dart at the next vertex of the exterior face
```

Hexagonal face closure forces the second new edge to end at the next
`x`-vertex. The [noncollision theorem][collar-noncollision] proves that all
`2k` candidate vertices are distinct. Its argument has three parts:

1. The old complete boundary prevents candidate vertices from returning into
   the old side.
2. The cubic star excludes identifications between two `x`-vertices or between
   two `y`-vertices.
3. An identification between an `x`- and a `y`-vertex propagates in opposite
   directions around their cyclic indices. Decreasing the index gap reaches
   equal or adjacent positions, forcing an edge to equal its own reverse.

This works for every positive width. It uses the given oriented row and
hexagonal seam faces; no additional planarity or connectivity hypothesis is
needed for noncollision. With new output-port faces of length five or six,
`hexagonalNextRow` constructs the complete oriented slab. It derives
chordlessness and both boundary maps; input labels agree with the previous
output labels. `hexagonalNextRow_support` composes the exact joint relation
with genuine interior colouring witnesses. The earlier exact successor
criterion remains available, with its injectivity condition now discharged.

The [progression theorem][collar-progress] connects this geometric construction
to termination and the four-ring physical reduction. In any finite cubic map
with pentagonal/hexagonal faces, successive rows reach an actual pentagonal
seam; the vertex count gives a coarse upper bound on extensions. In a least
counterexample, a supplied five-port row reaches such a seam within three
successful extensions. A fourth extension would construct a reducible five-row
tube. A reduction at the pentagonal stop is still required, as are initial-row
supply, changing-width mechanisms and coverage of other face sizes.

The [independent collar probe][collar-probe] examines all 574 simple ten-cycles,
in both orientations, across seven explicit spherical cubic maps. It finds
48 oriented alternating rows: 28 have hexagonal collars and yield complete
successor rows; 20 meet pentagonal faces immediately. The [growth probe][collar-growth]
follows all 48 recognized starts to actual pentagonal seams, checking both
complete boundaries, orientation and ten fresh vertices at every extension.
The longest history has six extensions. This finite-map check does not assume
minimal-counterexample status, which is required for the sharper bound of
three. The 80- and 180-vertex Goldberg examples have no alternating ten-cycle.
These are finite program checks, separate from the general Lean theorems.
The [current measurement record][noncollision-measurements] separates
noncollision, finite termination, physical reduction and remaining coverage.
The [earlier collar record][collar-measurements] retains its checkpoint data.

## Scope and verification

This establishes an infinite family reduction from the corridor idea,
independently of the classical Four Colour theorem. It does not establish
that every large relevant map contains such a tube, that arbitrary linked
bands are literal zigzag tubes, or that unbounded interfaces have finitely
many behaviours. Coverage remains a separate obligation in the proposed
short proof.

The [audit][audit] checks eight roots and their required dependencies, with
12,276 declarations in the combined closure. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no classical `FourColor` namespace
dependency is permitted. The [measurement record][measurements] records
source and artifact hashes and the successful build. The tube theorem itself
removes no classical configuration certificate. The [current proof ledger](../README.md#compression-achieved-and-the-next-proof-obligation)
records the complete assembly's certificate dependencies, including subsequent
diamond-family replacements.

From `lean/mettapedia`, the gate is:

```sh
lake build FourColorLane Mettapedia.GraphTheory.FourColor.ResearchCheckpoint
```

[certificate]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/GoertzelV24FiveTubeExclusion.lean
[decoder]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagRingTable.lean
[normalization]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagTubeFiniteNormalization.lean
[generic]: ../../../../lean/mettapedia/Mettapedia/GSLT/Core/BoundaryCertificateComposition.lean
[operational]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagTubeBoundaryGSLT.lean
[kron]: https://github.com/zariuq/MeTTapedia/blob/main/lean/mettapedia/Mettapedia/GSLT/Dynamics/LinearBoundaryReduction.lean
[audit]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagTubeBoundaryAudit.lean
[measurements]: ../../../../tools/fourcolor/classical/five-tube-normalization-measurements.json
[seam]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalSlabSeam.lean
[hex-chain]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalTubeChain.lean
[hex-exclusion]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalTubeExclusion.lean
[hex-audit]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalTubeAudit.lean
[hex-measurements]: ../../../../tools/fourcolor/classical/hexagonal-seam-measurements.json
[seam-probe]: ../../../../tools/fourcolor/classical/hexagonal-seam-probe.json
[hex-assembly]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalTubeAssembly.lean
[exterior]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/SlabExterior.lean
[transport]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/RotationSystemExactTransport.lean
[closed-witness]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OpenTangleClosedWitness.lean
[hex-reduction]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalTubeReduction.lean
[strip-probe]: ../../../../tools/fourcolor/classical/hexagonal-strip-probe.json
[strip-measurements]: ../../../../tools/fourcolor/classical/hexagonal-strip-measurements.json
[collar]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalCollar.lean
[collar-progress]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalCollarProgress.lean
[collar-probe]: ../../../../tools/fourcolor/classical/hexagonal-collar-probe.json
[collar-measurements]: ../../../../tools/fourcolor/classical/hexagonal-collar-measurements.json

[collar-noncollision]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalCollarNoncollision.lean
[collar-growth]: ../../../../tools/fourcolor/classical/hexagonal-collar-growth-probe.json
[noncollision-measurements]: ../../../../tools/fourcolor/classical/hexagonal-collar-noncollision-measurements.json
