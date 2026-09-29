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
`FacialCycleChord.chain_length_le_four`. The initial-row recognition below now
constructs the interfaces from a simple alternating cycle. Supply of such
cycles and control of width remain geometric tasks. An unmarked band or a
large hexagonal patch alone does not provide them.

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

## Recognizing the initial row

The [recognition theorem][alternating-recognition] takes a simple cyclic vertex
order of length `2k`, with `k ≥ 2`, in an actual bridgeless spherical cubic
graph. Its turns alternate in the original rotation system. These local
conditions determine a facial side: [the cycle-walk bridge][cycle-walk]
constructs the actual simple closed walk and its exact edge set, and spherical
separation supplies both connected facial shores. The alternating retained
degrees are then proved from the local turns. If the faces at the unused
ports have size five or six, the existing geometric argument excludes chords
and constructs both complete ordered interfaces.

No shore, chordlessness assertion or boundary bijection is supplied separately.
The resulting row has the original vertices and darts. `row_support` gives
the exact joint colouring relation with genuine interior witnesses. In the
all-face-5/6 class, `recognized_pentagonWithin` feeds the earlier finite growth
theorem; at width five, `recognized_pentagonWithin_three` consumes physical
four-ring reduction under the minimal-counterexample hypothesis.

The [independent orbit probe][alternating-probe] enumerates every state of the
dart/turn-phase permutation in twelve explicit maps, with no cycle-length
cutoff. It finds 468 simple oriented rows and checks 1,082 successful collar
extensions; all 468 histories reach pentagonal seams. For Goldberg `GP(n,0)`,
tested at `n = 1,...,8`, there are `12n` simple oriented rows of width `5n`.
Thus the earlier examples without alternating ten-cycles do have wider rows:
width ten for `GP(2,0)` and width fifteen for `GP(3,0)`.

Eight other orbits in the capped-strip examples repeat a vertex. Finite
permutation closure therefore does not itself establish simplicity. The
Goldberg pattern is finite program evidence, not an all-frequency Lean
theorem. No universal supply theorem or effective wider-row reduction is
claimed. The [measurement record][alternating-measurements] records the
recognition audit and its physical consumer. Catalogue and certificate
savings from this step are zero.

## When the alternating walk crosses itself

The [simple-lobe theorem][lobes] starts from any dart and either turn phase.
Finiteness supplies a returning segment; choosing a shortest positive return
prevents an internal vertex repetition. Nonbacktracking excludes lengths one
and two. The result is an actual simple closed walk of length between three
and the ambient vertex count. Its darts are a contiguous part of the original
trajectory, and `internal_transition` preserves every internal operation and
its phase. The closing transition is unrestricted.

`exists_separating_lobe` applies spherical separation to this actual walk.
It constructs two connected facial shores and proves that precisely the
walk's edges separate them. It assumes no supplied simple orbit, facial side
or cut. It does not yet give the alternating degree pattern or complete row
contract used by the four-ring reduction.

This distinction matters in small examples. The [finite replay][lobe-probe]
checks 137 explicit fullerene rotations on 20 through 42 vertices; 30 have
no simple complete alternating orbit. One 30-vertex example has four directed
dart/phase orbits, of lengths 68, 22, 68 and 22, each with an explicit repeated
vertex. Its 164,220 edge subsets of sizes one through four contain no cyclic
cut. A Tait colouring is recorded as well: this is an obstruction to the
simple-orbit supply assertion, not a counterexample to colourability or to
a stronger minimal-counterexample hypothesis.

That example contains an eleven-edge simple lobe. Its internal turns
alternate and its facial shores contain five and seven pentagons. The
associated turn/curvature calculation is a program check here, not a new
Lean curvature theorem. Zigzag self-intersections and the curvature of
patches bounded by zigzag arcs are studied by
[Deza and Dutour](https://arxiv.org/abs/math/0212352). The next task is to
derive an exact joint boundary contract for the marked closing transition,
then prove a reduction with genuine colouring reconstruction. A lobe alone
does not discharge that task or bound its width uniformly.

The [measurement record][lobe-measurements] separates the general Lean
extraction and separation theorems from the finite replay. No additional
classical certificate dependency or catalogue entry is removed.

## The information a cycle contraction must retain

The [marked cycle theorem][cycle-seam] supplies one part of the missing
contract. For a cycle boundary word `w`, let `C(w, s)` mean that an actual
Tait colouring exists with colour `s` on the incoming edge at vertex zero.
If all ports are nonzero and `w₀ ≠ w₁`, then

```text
C((w₀,w₁,w₂,...), s)  ↔  s ≠ w₀ ∧ C((w₀+w₁,w₂,...), s).
```

Addition is in the Klein colour group. Contracting the two ports erases the
edge between them. Its reconstructed colour is forced to be `s+w₀`, which
explains the guard `s ≠ w₀`. This is a single theorem for every cycle length
at least three, using literal `CycleCap` tangles and actual colouring
witnesses. `spokes_collapse` proves that taking boundary colours commutes
with the contraction; `marked_contract_iff` supplies the exact validity
conditions and inverse witness construction. Any additional predicate on
the retained seam can be composed with the same law.

The guard cannot be discarded. The word `(red,blue,red,blue)` is not accepted
by the four-cycle. Its contracted word `(purple,red,blue)` is accepted by the
triangle, with the forbidden seam colour `red`. Both claims are proved in
Lean. Thus retaining an answer about separate support is too weak for this
reconstruction; the seam and boundary choice must remain related.

The [independent replay][cycle-seam-probe] checks all 6,534 marked cases for
nonzero words of lengths three through seven whose first two ports differ.
It also restricts the recorded actual C30 colouring to its eleven-edge lobe
and checks all five rotations where the first two port colours differ.
Those lobe checks are program evidence. The literal cap theorem does not
establish an embedding equivalence: the lobe's ports occur on both sides,
whereas the cap uses its specified rotation. A formal adapter retaining
this placement, an operation on the exterior, and strict reduction within
the target map class remain required. No catalogue certificate is removed.
The [measurement record][cycle-seam-measurements] records the proof audit.

## From one seam to a joint patch repair

The equal-port branch suggests deleting the two vertices at an odd lobe's
exceptional seam. Joining their two cycle ends and their two exterior ends
decreases the whole map by two vertices. Reconstruction requires different
colours on the two new edges. The [seam replay][seam-repair-probe] checks this
operation with two independent colouring and physical-switch implementations.
Of 103 tested odd seams, 83 admit repair from every smaller colouring and
20 have trapped classes. For the displayed C30 lobe, the smaller graph has
228 colourings in one Kempe class; 96 reconstruct directly, and every other
one reaches those in at most two switches. The first failure has successful
alternative lobes. These are finite program results, and they refute arbitrary
seam repair rather than the existence of a successful decomposition.

A larger joint interface gives a positive theorem. Combine the eleven-edge
lobe with the pentagon on its five-port shore. The resulting cubic patch
has sixteen internal vertices and six external ports. Its dual disk has
twelve vertices, six on the boundary. An independent [patch replay][patch-probe]
checks the primal/dual colouring correspondence and recognizes this same disk,
including its ordered ring and triangles, in all 29 sampled eleven-lobe cases.

For the literal dual graph, [PentagonalLobePatch][patch] proves:

```text
Q is Kempe-closed, and contains a proper zero-sum six-port word
  → some genuine colouring of the disk has its boundary trace in Q.
```

The successful trace is one shared choice for the disk and exterior. The
proof has 22 explicit terminal colourings and nine finite answer-cover checks,
composed through the reference's proved chromogram rule. Independent enumeration
finds 132 supported words among 183 admissible words; the unsupported set
shrinks as 51 → 6 → 0. These two closure rounds are not a bound of two physical
Kempe switches. All fourteen ordered six-leaf tree replacements fail direct
support inclusion, which explains the need to permit exterior recolouring.

The [four-root audit][patch-audit] checks 3,347 dependency declarations,
requires actual graph witnesses and cover soundness, and excludes configuration
certificates and the complete theorem. Only the three standard axioms occur.
This is a boundary repair theorem for one concrete patch, with arbitrary
Kempe-closed exteriors. Formal embedded recognition, strict replacement and
geometric coverage remain open. It adds no catalogue or certificate savings.
The [measurement record][patch-measurements] separates these claims.

The [literal tangle adapter][patch-tangle] now proves the next reconstruction
step. It retains sixteen cubic vertices, twenty-one internal edges, six
boundary half-edges and the cyclic order at every vertex. Differences of
adjacent face colours produce proper nonzero colours on the actual darts.
Taking the six boundary colours commutes exactly with taking the disk trace.
`compatible_darts` retains a genuine exterior colouring and matches all six
ports simultaneously; `sewn_colorable` uses the existing sewing theorem to
colour the resulting closed rotation system.

The [tangle audit][patch-tangle-audit] checks this reconstruction separately
from the finite boundary repair. The replay checks every literal dart and
rotation against the extracted C30 patch; general recognition remains open.

The [physical boundary bridge][physical-boundary] now discharges the closure
hypothesis from physical noncrossing. A proper exterior colouring determines
one matching of its active boundary ports. The translation retains that
matching and both endpoint colours. Every chromogram answer reconstructs as
a simultaneous switch of whole components of the same exterior. The
trace-difference lemma works at every length; the matching-to-chromogram codec
is verified at six ports. This transfers a common mathematical argument
between the physical and reference representations, with explicit witnesses.

The embedded consumer derives reference closure for a spherical six-port
cyclic bond boundary with connected opposite shore, under the existing map
hypotheses. Cubic incidence supplies the zero-sum equation. The resulting
[physical repair theorem][physical-repair] has the form:

```text
one proper exterior colouring + cubicity + physical noncrossing
  → a genuine colouring of the sewn sixteen-vertex patch and exterior.
```

The exterior colouring may change; existence and actual reconstruction are
proved, while counting and executable-history equivalences are unclaimed.
The [seven-root audit][physical-audit] checks 21,333 dependency declarations,
only the three standard axioms, and no catalogue certificate or complete
Four Colour theorem.

The [tree replay][tree-probe] tests a smaller-map operation: remove all sixteen
patch vertices and insert an ordered cubic tree with six ports and four
internal vertices. All fourteen tree shapes succeed geometrically on all
29 supplied patches, giving 406 simple, connected, bridgeless spherical cubic
maps with twelve fewer vertices. All tested exteriors have Kempe-closed
supports. On C30, every smaller tree replacement has genuine colourings whose
boundary words lie in that same exterior support. These are finite program
checks, retained separately in the [physical measurement record][physical-measurements].

The [tree geometry theorem][tree-geometry] now proves one of these replacements
in every connected exterior. The chosen tree is the path `0--1--2--3`, with
six boundary ports distributed as `2,1,1,2`. Its first-return permutation is
exactly the patch's cyclic successor. The patch has seven open face cycles;
the tree has one. Their common open Euler contribution is four. Thus six
whole-map faces disappear while exterior cofaciality is preserved.

Bridge-freedom has a reusable reason. In a bridgeless source, both sides of
any exterior bridge reach a boundary port. The replacement is connected and
has a port at every vertex, so the exterior and tree reconnect each other's
potential cuts. Together with the inherited cubic rotations and exact Euler
calculation, this preserves the entire connected bridgeless spherical cubic
class. The theorem permits parallel edges; simplicity was checked only in the
finite examples.

The [strict reduction theorem][tree-reduction] joins geometry and colouring:

```text
source = sixteen-vertex patch sewn to a connected exterior
  → replace the patch by the four-vertex tree: twelve fewer total vertices
  → a colouring of the smaller map restricts to a genuine exterior colouring
  → physical noncrossing enables joint repair
  → a genuine colouring of the source map.
```

`colorable_of_smallerColorable` consumes vertex minimality to supply the smaller
colouring. This is one argument for arbitrary compatible exteriors, with the
physical noncrossing hypothesis stated explicitly. It preserves colouring
existence and reconstructs actual witnesses; no equality of colouring counts
or executable-history equivalence is claimed. The [dependency audit][tree-audit]
requires both the geometric and reconstruction chains and excludes complete
Four Colour endpoints and catalogue reducibility certificates.

This advances the reduction part of the lobe mechanism. The next missing
geometric theorem must recognize this literal patch and its ordered exterior
inside an independently specified family of alternating lobes, and derive
physical noncrossing through the existing cyclic-bond boundary theorem.
Coverage of the relevant stopping configurations remains open. The
[tree measurement record][tree-measurements] credits no additional original
configuration-certificate savings; the 22 terminal witnesses and nine
answer-cover checks remain.

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
[cycle-walk]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CycleFrameWalk.lean
[alternating-recognition]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/AlternatingCycleRecognition.lean
[alternating-probe]: ../../../../tools/fourcolor/classical/alternating-cycle-probe.json
[alternating-measurements]: ../../../../tools/fourcolor/classical/alternating-cycle-measurements.json
[lobes]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/AlternatingWalkLobes.lean
[cycle-seam]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CycleSeamTransfer.lean
[cycle-seam-probe]: ../../../../tools/fourcolor/classical/cycle-seam-probe.json
[cycle-seam-measurements]: ../../../../tools/fourcolor/classical/cycle-seam-measurements.json
[lobe-probe]: ../../../../tools/fourcolor/classical/alternating-lobe-probe.json
[lobe-measurements]: ../../../../tools/fourcolor/classical/alternating-lobe-measurements.json
[seam-repair-probe]: ../../../../tools/fourcolor/classical/lobe-seam-repair-probe.json
[patch]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobePatch.lean
[patch-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobePatchAudit.lean
[patch-probe]: ../../../../tools/fourcolor/classical/pentagonal-lobe-patch-probe.json
[patch-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-patch-measurements.json
[patch-tangle]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTangle.lean
[patch-tangle-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTangleAudit.lean
[physical-boundary]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PhysicalKempeBoundary.lean
[physical-repair]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobePhysicalRepair.lean
[physical-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobePhysicalRepairAudit.lean
[tree-probe]: ../../../../tools/fourcolor/classical/pentagonal-lobe-tree-probe.json
[physical-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-physical-measurements.json

[tree-geometry]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTreeGeometry.lean
[tree-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTreeReduction.lean
[tree-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTreeReductionAudit.lean
[tree-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-tree-measurements.json
