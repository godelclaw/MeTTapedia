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
rows. In the resulting coordinates, accepted words are exactly the iterated
ring relation. The [physical consumer][hex-exclusion] combines this fact with
the existing strict shore splice: for five-port rows, a graph-backed
vertex-minimal counterexample cannot have more than **446,403** such rows,
under the stated good-inner-side and connected-shore hypotheses. The bound is
unchanged; the improvement is that seam alignment follows from face geometry.
The facial adapter constructs the row's rotation compatibility from its
original face incidences and alternating retained degrees.

This does not yet recognize an entire strip as the literal sewn tube used in
the four-ring replacement above. Supplying the alternating rows, their
complete interfaces and the end-shore conditions remains a geometric task.
An unmarked band or a large hexagonal patch alone does not provide them.

An [independent dart-permutation probe][seam-probe] checks all 5,912 seam
permutations at widths two through seven. Exactly the cyclic translations
give hexagonal seam faces throughout. Its closed five-port example has two
rows capped by pentagons: 30 vertices, 45 edges, twelve pentagonal faces and
five hexagonal faces. A shift by two ports retains these counts and a checked
Tait colouring. A noncyclic control instead has an 18-sided seam face and
Euler characteristic zero; it is a toroidal example, not a planar
counterexample. These examples are program checks, separate from the general
Lean proofs.

The [geometric audit][hex-audit] checks twelve roots and 23,144 dependency
declarations, requires the actual facial-recognition, support and strict-splice
consumers, and rejects classical `FourColor` dependencies. The [measurement
record][hex-measurements] separates the new proof costs from the reused finite
five-port stabilization certificate. No configuration or certificate is
removed by this geometric result.

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
