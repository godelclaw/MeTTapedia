# Compositional reductions for tube families

The strongest current reduction allows a cyclic change of seam matching.
At every circumference `k ≥ 2`, any recognized tube with at least three rows
can lose two rows: exactly `4k` vertices disappear. The smaller map remains
connected, bridgeless, spherical and cubic, and each of its colourings
reconstructs while fixing all exterior edge colours. See the
[two-row deletion](#two-row-deletion-with-a-cyclic-seam-shift) below.
This theorem uses the complementary-ring algebra, with no finite colouring
certificate. The earlier exact-support normalization remains useful when
the original seam matching and both directions of transport are required.

## Exact support with the original seam

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

The [embedded reduction][embedded-reduction] now removes the explicit
noncrossing premise for an actual recognized occurrence. Recognition consists
of bijections of the sixteen vertices, forty-two internal darts and six ports
with a literal vertex shore, together with the exact edge and rotation laws.
It contains no colouring or repair assertion. The source is a connected
bridgeless spherical cubic simple graph with two-sided faces and a connected
exterior.

The patch's internal connectedness is proved from its actual edges. Its
computed return order transports through the recognition isomorphism. The
planar bond theorem gives the opposite cyclic order on the actual exterior;
reflection preserves the six-port crossing predicate. The physical separator
theorem therefore supplies noncrossing. Dual connectedness is also derived
from the source. Exact reassembly then identifies the repaired colouring
with a colouring of the original graph:

```text
local dart/vertex/port recognition + connected exterior
  → opposite boundary order, derived from spherical geometry
  → physical Kempe compatibility, derived from the common component matching
  → twelve-vertex reduction and reconstruction of the original graph.
```

`Embedded.not_in_minimal_counterexample` consumes this chain. It applies one
argument to every recognized occurrence satisfying the geometric hypotheses.
The [audit][embedded-audit] checks that the reconstruction, geometric
transport and physical separator really occur in the dependency closure,
without complete Four Colour endpoints or catalogue certificates.

The [distinct-attachment consumer][attachments] replaces the connected-exterior
premise with six distinct vertices at the exterior ends of the cut edges,
under cyclic edge-connectivity at least four. Minimality already supplies
that cut bound. The argument is a general finite graph law: with at most one
outgoing edge per vertex, a cubic component cannot be a tree. Two exterior
components would therefore contain cycles and consume at least four disjoint
boundary edges each. Six ports cannot supply them. The resulting theorem
feeds directly into the same twelve-vertex reduction and reconstruction.

The [independent test][attachments-probe] checks distinct attachments in all
29 extracted patches. It also checks two limits of the general graph law:
eight distinct ports can support two components, and six ports can fail if
attachment vertices repeat. These are finite program checks; the general
connectivity theorem and its reduction consumer have a separate
[kernel audit][attachments-audit].

The [minimal-exterior theorem][minimal-exterior] removes the distinctness
premise for the intended minimal-counterexample argument. Its stronger
six-port count uses the cycle inside the removed patch. Every exterior
component needs at least three outgoing edges. A component containing an
edge needs at least four, because a connected cubic side behind at most
three edges is either cyclic or a single vertex. Two such components would
need at least seven ports. Cubic incidence supplies an internal edge as soon
as the exterior has more than two vertices.

Euler and minimum face size give at least twenty ambient vertices, so at
least four remain outside this sixteen-vertex patch. Minimality supplies the
face-size and cyclic-cut bounds. Thus exact local recognition now suffices:

```text
recognized sixteen-vertex patch in a vertex-minimal counterexample
  → at least four exterior vertices and a cycle inside the patch
  → connected exterior, with repeated attachment endpoints allowed
  → strict twelve-vertex reduction and genuine colouring reconstruction
  → contradiction to minimality.
```

`Embedded.not_in_minimal_counterexample_of_recognition` consumes this entire
chain, with no exterior root, connectedness or endpoint injection supplied
separately. The [audit][minimal-exterior-audit] checks eleven roots and excludes
complete Four Colour endpoints and catalogue certificates. The reusable
[six-port theorem][six-port-connectivity] needs no embedding or colouring;
the [twenty-vertex bound][vertex-lower-bound] counts actual quotient faces.

The cycle, spoke-order and full recognition results below now construct the
required isomorphism from independently specified two-cycle incidence and
outer turns. The 29 program-recognized examples do not prove general supply.
Coverage of the relevant stopping configurations remains open. The
[measurement record][minimal-exterior-measurements] credits no
additional original configuration-certificate savings; the 22 terminal
witnesses, nine answer-cover checks and one shared matching codec remain.
Counts and executable recolouring histories are not asserted equivalent.

## Recognizing a cycle from its graph incidence

The [cycle-incidence construction][cycle-incidence] now starts with ordinary
graph data: a cyclic list of distinct vertices, its cycle edges, and one
adjacent outside vertex at each position. Outside vertices need not be
distinct. Cubicity proves that these are all the neighbours, constructs
the complete retained dart carrier and ordered ports, and proves every
internal edge reversal. The cycle itself supplies shore connectedness.
No local rotation or tangle-isomorphism field is an input.

The [orientation law][cycle-orientation] has a short uniform proof. Give
each directed cycle edge its side mark, and give each port the mark selected
by its local three-dart rotation. Face traversal preserves this mark.
All ports on one open face must therefore have the same local orientation.
This works at every cycle length. A connected complement in a spherical map
supplies cofaciality through the existing planar-bond Euler theorem.

`CubicCycleIncidence.Frame.uniform_geometry` combines these results. One
global reversal choice determines both the actual source rotations and the
exact port return: predecessor in one orientation, successor in the other.
The first return is proved through the actual two-step face path, including
the absence of an intervening boundary hit. This is a precise instance of
transporting graph incidence into an operational boundary summary while
retaining the choice on which both representations depend.

For the inner pentagon, this replaces a potential enumeration of 32 local
rotation assignments with the uniform law. The separate attachment-order
argument is now proved below. The [bounded experiment][spoke-order-probe]
fixes the outer lobe and tests all 120 spoke assignments and 32 inner rotation
choices. Of 3,840 combinations, ten have the seven open faces required of
this connected spherical shore. All ten become the literal patch after
relabelling the inner vertices by their spokes. The enumeration is program
evidence; the following theorem derives its order constraint directly from
actual spherical source geometry.

The [kernel audit][cycle-recognition-audit] checks nine roots and 20,865
dependency declarations, allowing only `propext`, `Classical.choice` and
`Quot.sound`. It requires both the graph-incidence construction and the
planar-bond/first-return chain, and excludes complete Four Colour endpoints
and catalogue certificates. The [receipt][cycle-recognition-measurements]
records source and artifact fingerprints. This is one uniform recognition
law, with no additional original certificate removed and no assertion of
colour-count or executable-history equivalence. The next geometric task is
to assemble the recognized incidence and attachment order into the full
patch isomorphism and consume the existing twelve-vertex strict reduction.

## Forcing the pentagon's spoke order

The [spoke-order theorem][lobe-spoke-order] starts with two disjoint graph
cycles: an eleven-cycle and a five-cycle. The five inner spokes meet outer
positions 1, 3, 5, 7 and 9 in an arbitrary bijective order. The outer vertex
turns alternate, with the two adjacent outward positions at the closing
seam. No inner rotation, cyclic matching or tangle isomorphism is assumed.
The source is a connected spherical cubic simple graph with cyclic vertex
rotations and two-sided faces.

First, [spoke connectivity][cycle-spoke-connectivity] proves that all exterior
attachment vertices reaching one connected outer set forces the entire
complement to be connected. The proof is ordinary graph theory and works
for cycles of every length. Here the eleven-cycle supplies that connected
outer set, so the inner-cycle orientation theorem applies without a separate
complement hypothesis or distinct exterior attachment vertices.

Next, trace the actual face path through that complement. The return moves
from attachment `j` to `j - 1`. It takes three face steps across each ordinary
gap and four across the closing gap. The proof checks that no intermediate
dart is a boundary hit. Opposite planar-bond boundary orders then give

```text
inner return: i → i + 1 or i - 1
outer return: j → j - 1
spoke matching σ: σ(i ± 1) = σ(i) + 1
```

An induction valid for any cyclic interface length turns the last equation
into `σ(i) = σ(0) + i` or `σ(i) = σ(0) - i`. Crucially, the same orientation
witness controls this formula and all actual inner vertex rotations. Thus
one argument rules out the other attachment/rotation combinations without
enumerating 120 permutations and 32 turn assignments. It applies to every
ambient graph satisfying these local incidence and embedding hypotheses.

The [eight-root audit][lobe-spoke-order-audit] checks 21,053 dependency
declarations, permits only the three standard axioms, and excludes complete
Four Colour endpoints and original catalogue certificates. The
[receipt][lobe-spoke-order-measurements] records exact source and artifact
fingerprints. The final module build took 5.1 seconds and its audit 5.6 seconds;
these include elaboration and kernel checking.

This settles the attachment-order component. The full sixteen-vertex tangle
isomorphism and its strict-reduction consumer are now constructed below.
Deriving the stated two-cycle arrangement from a general stopping lobe and
proving coverage remain separate obligations.
The complete proof retains 633 configurations and 630 original certificates;
this result removes no additional certificate and makes no assertion about
preserving colouring counts or executable recolouring histories.

## Reducing the actual two-cycle family

[PentagonalLobeRecognition][lobe-recognition] completes the geometric chain
for the specified pentagon-plus-eleven-cycle arrangement. The graph input
consists of two disjoint cycles, an arbitrary bijective matching of the five
inner spokes to outer positions 1, 3, 5, 7 and 9, and the alternating outer
turns. The ambient map is connected, spherical and cubic, with cyclic vertex
rotations and two-sided faces. No inner rotation, cyclic matching, connected
exterior or tangle isomorphism is supplied.

The construction labels each inner vertex by its actual outer attachment.
The previously derived orientation is used for both its adjacent vertices
and its three-dart rotation. Cubic neighbour exhaustiveness proves that the
six remaining outer spokes leave the entire patch. It also proves that the
coordinate map covers every actual dart at every retained vertex. A
[kernel-checked codec][lobe-coordinates] identifies these two cyclic lists
with the existing literal patch, preserving all vertices, edge reversals,
rotations and exposed half-edges. The general [dart-recognition constructor][dart-recognition]
then supplies the exact open-tangle isomorphism. The same witness is retained
through every representation change.

```text
two cycles + five spoke attachments + outer turns
  → spherical geometry forces one joint inner order and orientation
  → exact correspondence of 16 vertices, 48 darts and 6 ports
  → actual patch-to-exterior sewing and compatible recolouring
  → replacement by a four-vertex tree, reducing the whole map by 12 vertices.
```

`strict_reduction_of_geometry` proves the final step under minimum face size
five and cyclic edge-connectivity at least four. It constructs a smaller
map in the bridgeless spherical cubic class and reconstructs an original-map
colouring from a smaller-map colouring. All replacement vertices are counted.
Exterior attachments may repeat. `not_in_minimal_counterexample` obtains the
face-size and cut bounds from minimality and excludes this actual family.
The reconstruction may recolour the exterior; it retains compatible joint
choices throughout.

This is one local geometric shape in arbitrary qualifying surrounding maps.
It completes its recognition and reduction obligations, without proving an
unbounded family of distinct local cores or occurrence in every stopping
lobe. The proof still uses the existing 22 terminal colourings, nine finite
answer-cover checks and one shared six-port matching codec. The new literal
coordinate tables certify a representation change, not additional colouring
cases. No further original configuration certificate or catalogue entry is
removed: the complete proof still has 633 configurations and 630 original
certificates. Existence reconstruction is proved; no new count-preservation
or executable recolouring-history theorem is claimed.

The [audit][lobe-recognition-audit] checks twelve roots and 26,523 dependency
declarations, allowing only `propext`, `Classical.choice` and `Quot.sound`.
It requires the geometric-order, exact-dart, exterior-connectivity, strict-size
and colouring-reconstruction chains. Complete Four Colour endpoints,
original catalogue certificates and diamond reducibility are excluded.
The [receipt][lobe-recognition-measurements] records source and artifact hashes.
The final recognition module took 3.6 seconds and its audit 6.5 seconds,
including elaboration and kernel checking. From `lean/fourcolor-classical`:

```sh
lake build MettapediaFourColor.PentagonalLobeRecognitionAudit
```

The next geometric question is which stopping-lobe conditions force this
arrangement, or a larger family with a similarly reconstructible reduction.
Existing alternating-walk extraction retains the closing transition but
does not yet supply the enclosed pentagon and its five attachments.

## Constructing the lobe from its neighbouring faces

The [facial construction][corona-geometry] starts from a rooted pentagon
with four pentagonal neighbours and one hexagonal neighbour. The hexagon
lies across the chosen root edge. Crossing the third edge at each central
vertex reaches five outer attachment vertices. Following the neighbouring
faces connects consecutive attachments: each pentagon contributes a path
of two edges, and the hexagon contributes a path of three edges. Together
these form the eleven-position boundary, including its longer closing gap.

The underlying [traversal law][corona-traversal] applies at every central
cycle length: a neighbouring face of period `n + 3` supplies an `n`-step
outer arc. It uses actual edge reversals and vertex rotations. For this
six-face pattern, the [incidence construction][corona-incidence] derives
both cycles, their spoke matching and all alternating outer turns. The
input supplies no outer cycle frame, rotation equations or patch isomorphism.

The sixteen traced vertices are now proved **distinct**.
[Exact dart transport][corona-immersion] interprets a partial sixteen-vertex
diagram in the original graph, preserving each local slot, vertex rotation
and internal edge reversal. This construction assumes no global vertex
injectivity. If two vertices coincided, their incident darts would agree in
one of three relative phases. Applying the same operations to both darts
preserves that agreement. The [general separation theorem][dart-separation]
shows that reaching distinct local slots, a loop, duplicate incident darts
or a triangle contradicts the actual graph's local laws and triangle-freeness.

The [finite check][corona-separation] covers all `16 × 15 × 3 = 720` ordered
collision/phase cases in at most six simultaneous operations. Its soundness
applies uniformly to every actual realization, independently of the exterior's
size. [Noncollision][corona-noncollision] supplies triangle-freeness from
cyclic-five connectivity and more than four vertices, or directly from
minimality. This is exact transport of operations and their joint state;
independently projecting the two darts would lose the equality being tested.
The 720 cases are geometric checks, with the partial edge-involution law
checked separately. They are counted apart from colouring certificates.

[Chord exclusion][corona-chord] also derives the absence of extra outer edges.
The [actual consumer][corona-reduction] therefore performs the strict reduction
from the six face lengths, with genuine colouring reconstruction.
Its ambient source is a bridgeless spherical cubic simple graph with cyclic
rotations and two-sided faces, minimum face size five and cyclic-five edge
connectivity. The minimal-counterexample consumer derives these ambient
conditions from minimality. Repeated exterior attachment vertices are allowed.

The chord argument uses the information retained at the boundary. Before
assuming inducedness, [cubic dart counting][corona-boundary] places every
outgoing edge at one of six outer positions. An extra chord uses two distinct
positions, leaving at most four outward edges. The retained patch contains
the central pentagon. Minimality gives at least twenty vertices in the whole
graph, hence at least four outside this sixteen-vertex patch. If that exterior
were a forest, cubic degree counting would require at least six outward edges.
It therefore contains a cycle, giving a cyclic cut of at most four edges,
contrary to cyclic-five connectivity.

The reusable [boundary theorem][cyclic-five-boundary] needs only three
exterior vertices and no exterior connectedness assumption. Thus the local
chord theorem already holds at ambient size nineteen under its stated
cubic and cyclic-connectivity hypotheses. This replaces one geometric
recognition premise with a general argument; it introduces no new colouring
certificate and claims no new catalogue saving.

```text
central pentagon + four pentagonal neighbours + one hexagonal neighbour
  → actual facial arcs of lengths 2,2,2,2,3
  → exact dart transport + separation prove sixteen distinct vertices
  → two cycles and their joint rotation/attachment data
  → cubic port count + cyclic connectivity exclude outer chords
  → exact six-port semantics and compatible colouring repair
  → four-vertex replacement; twelve fewer vertices in the whole map.
```

The [independent replay][corona-probe] checks all 1,644 pentagons in the 137
recorded maps. It finds 76 matching faces across 29 maps; every traced patch
has the required distinct vertices and induced boundary. All 29 previously
selected lobe instances are recovered. This finds additional occurrences
in the same maps, not additional map coverage. The census remains independent
program evidence. The general noncollision theorem is established separately
by the Lean realization and separation argument.

The [twelve-root audit][corona-audit] checks 26,708 dependency declarations,
using only `propext`, `Classical.choice` and `Quot.sound`. It requires the
finite separation check, its soundness and actual dart realization, derived
noncollision, chord exclusion, strict whole-map decrease and colouring
reconstruction.
Complete Four Colour endpoints, original catalogue certificates and diamond
reducibility are excluded. The [receipt][corona-measurements] records source
and artifact hashes. The separation check took 25 seconds, the strengthened
reduction 2.8 seconds and its audit 7 seconds, including elaboration and kernel checking. From
`lean/fourcolor-classical`:

```sh
lake build MettapediaFourColor.PentagonalCoronaFaceReductionAudit
```

The [local chord replay][corona-chord-probe] checks fourteen possible extra
chords in the literal patch, confirming four remaining outward darts in
each case. The exterior and minimality argument is a separate Lean proof.
The [pair-transport replay][corona-separation-probe] independently checks all
720 collision/phase cases and records deterministic witness statistics.
Allowing terminal paths of length one separates 652 cases; length two
separates 712; triangle-freeness handles the remaining eight. These figures
describe this search, not a proof that every alternative argument needs
triangle-freeness.

No additional colouring enumeration is introduced. The 22 terminal witnesses,
nine answer-cover checks, one six-port matching codec, 633 catalogue
configurations and 630 original configuration certificates remain. The local
recognition chain is complete for this pattern in arbitrary qualifying
exteriors. Next: extend the joint repair to other face patterns or longer
lobes, and integrate further certificate replacements. Face traversal alone
does not supply their colouring repair or prove global coverage.

## Scope and verification

The tube result establishes an infinite family reduction from the corridor idea,
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

## Using a smaller shared core

The neighbouring-face construction contains a smaller piece: the central
pentagon and just three consecutive pentagonal neighbours. Their twelve
vertices form the cubic dual of the diamond configuration already handled
by the joint-profile proof. The other two neighbouring face lengths do not
enter this core. The [new theorem][diamond-face-reduction] therefore applies
more broadly than the earlier pentagon-with-four-pentagons-and-a-hexagon result.

```text
central pentagon + three consecutive pentagonal neighbours
  → twelve actual vertices and six actual boundary darts
  → the existing diamond graph and its ordered boundary observation
  → shared joint-profile repair with compatible exterior witnesses
  → four-vertex tree; eight fewer vertices in the whole map.
```

Recognition is proved from face lengths and ambient normal form. The partial
diagram has 396 ordered collision/phase cases. Shared operations separate
392 using triangle-freeness; the remaining four would close genuine
four-cycles. Cyclic-five connectivity and the source-size bound exclude both
short cycles. A [general boundary law][partial-dart-boundary] then proves
that all six missing reversals are genuine ports: the cut has size at least
five and at most six, and the cubic degree identity makes its size even.
No unrecorded internal edge remains. The literal coordinate map preserves
all vertices, internal reversals, rotations and ordered ports.

The [colouring bridge][diamond-tangle] turns the existing diamond colourings
into genuine interior witnesses, preserving their entire boundary word.
Physical Kempe closure provides a compatible exterior witness. The
[shared reduction law][six-port-replacement] proves preservation of the
bridgeless spherical cubic class and counts all four introduced vertices.
Exterior attachment endpoints may coincide. The theorem concerns existence
and reconstruction; it does not assert preservation of colouring counts or
provide an executable sequence of Kempe swaps.

This choice of interface matters. The independent tests for full coronas
with exceptional neighbour length six, seven and eight found:

| Outer ports | Realized words | Words in the remaining closed obstruction |
| --- | ---: | ---: |
| 6 | 132 | 0 |
| 7 | 282 | 0 |
| 8 | 576 | 600 |

The last row refutes the tested full-repair statement against arbitrary
abstract Kempe-closed exterior predicates. It is not a constructed planar
exterior counterexample. Five of 132 tested eight-port tree contracts avoid
the obstruction. More directly, the proved smaller-core reduction uses the
inner six-port interface. Minimality supplies a colouring of its actual
smaller map; the omitted neighbouring faces belong to the exterior and may
be recoloured along with it. This implements the freedom to choose a
successful decomposition and compatible witnesses.

The [dependency audit][diamond-face-audit] checks 18 roots and 27,238
declarations. For the earlier corona exclusion, the new route avoids its
22 separate terminal-colouring checks and nine answer-cover checks by
reusing the integrated diamond profile. It adds no colouring certificate.
The old reduction with a decrease of twelve remains separately available;
the broader reduction has a decrease of eight. All 633 catalogue entries
and 630 original certificate dependencies remain. This is sharing at one
local application, not a new reduction of the complete catalogue.

The [independent replay][diamond-probe] checks 458 rooted occurrences,
representing 318 central faces and 229 vertex subsets across 75 of the same
137 recorded maps. The earlier pattern covered 76 central faces in 29 maps.
The mathematical theorem has no exterior-size bound, but its local core is
fixed. Neither this census nor the theorem proves that every target contains
such a core. Coverage of graphs with more widely separated pentagons remains
an explicit task. The [receipt][diamond-measurements] records source and
artifact hashes, checks, scope and unchanged complete-assembly counts.

## Recognizing the mixed diamond

The next member of the shared diamond family now has an actual geometric
interpretation. Start with a pentagonal face and three consecutive neighbours
of lengths five, six, five. The remaining two neighbour lengths are unrestricted.
This is the thirteen-vertex, seven-port dual of configuration 2, whose abstract
repair already uses the same joint-profile law as configurations 1 and 4.

[MixedDiamondFaceRecognition][mixed-recognition] constructs the occurrence
from those face lengths and the ambient normal form. It follows real darts,
preserves rotations and reversals, and proves all thirteen positions distinct.
The common dart-separation argument handles 464 of the 468 ordered
vertex/phase cases under triangle-freeness. One four-edge path, transported
in both directions, resolves the four remaining cases using absence of
four-cycles. Minimality supplies both girth restrictions.

Odd boundary width adds a geometric obligation. With seven possible ports,
a hidden internal chord could leave five actual outgoing edges. Cut parity
does not rule that out. [The seven-port boundary law][seven-boundary] uses
internal-six connectivity: every cyclic five-cut has a shore of at most five
vertices. Here both shores have at least six, so that hidden cut is impossible.
Every unpaired dart really reaches the exterior. No distinctness assumption
on the exterior attachment vertices is added.

The representation change preserves the information repair needs. The
[colouring isomorphism][colouring-isomorphism] sends a whole interior
assignment to the actual region, reads back each boundary colour, and has an
inverse recovering the original assignment. The
[arbitrary-width context theorem][open-repair] then glues two compatible
whole assignments. The recognized region inherits the existing
`DiamondProfileReducibility.repair002`, with no new colour certificate.
This is an exact transfer of a successful argument between representations.

The remaining obligations are visible in the statements:

| Step | Status |
| --- | --- |
| Four actual face lengths give the full thirteen-vertex occurrence | Proved under the stated ambient normal form; minimality supplies that form |
| The joint boundary observation transports the existing repair | Proved, retaining genuine whole-shore colouring witnesses |
| Compatible interior and exterior assignments reconstruct the original map | Proved from one initial exterior colouring; actual physical closure is now derived |
| The actual seven-port exterior has that closure | Proved by the arbitrary-width matching codec and actual cyclic boundary geometry |
| A valid strict replacement and whole-map decrease | Proved below: thirteen removed, five introduced, net eight; the smaller map supplies the initial exterior colouring |
| The known local patterns cover the intended source class | Open |

The [audit][mixed-audit] checks 21 roots and 27,512 dependency declarations,
using only `propext`, `Classical.choice` and `Quot.sound`. It excludes complete
Four Colour endpoints, original catalogue certificates and superseded
independent repairs. The existing six-port face reductions also pass their
audits after the generic transport extension. The
[measurement record][mixed-measurements] separates this recognition from
strict reduction and catalogue compression: totals remain 633 configurations
and 630 original certificate dependencies.

An [independent replay][mixed-probe] verifies the literal tables, ordered dual
correspondence, all collision traces and actual face traversals. In the same
137 fixtures it finds 1,059 rooted occurrences on 792 central faces in 130
maps; every occurrence has seven outgoing ports. The census does not
establish normal form or universal coverage. The assignment bijection concerns exact
representation changes; it asserts neither count preservation under graph
reduction nor an executable Kempe history.

[mixed-recognition]: ../../../../lean/fourcolor-classical/MettapediaFourColor/MixedDiamondFaceRecognition.lean
[seven-boundary]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PartialCubicDartSevenBoundary.lean
[colouring-isomorphism]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OpenTangleIsomorphismColoring.lean
[open-repair]: ../../../../lean/fourcolor-classical/MettapediaFourColor/OpenTangleKempeRepair.lean
[mixed-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/MixedDiamondFaceRecognitionAudit.lean
[mixed-measurements]: ../../../../tools/fourcolor/classical/mixed-diamond-measurements.json
[mixed-probe]: ../../../../tools/fourcolor/classical/mixed-diamond-probe.json

[certificate]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/GoertzelV24FiveTubeExclusion.lean
[corona-traversal]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/FacialCoronaTraversal.lean
[corona-geometry]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaGeometry.lean
[corona-incidence]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaIncidence.lean
[corona-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalCoronaFaceReduction.lean
[corona-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalCoronaFaceReductionAudit.lean
[corona-probe]: ../../../../tools/fourcolor/classical/pentagonal-corona-probe.json
[corona-measurements]: ../../../../tools/fourcolor/classical/pentagonal-corona-noncollision-measurements.json
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

[embedded-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeEmbeddedReduction.lean
[embedded-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeEmbeddedReductionAudit.lean
[embedded-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-embedded-measurements.json

[attachments]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeDistinctAttachments.lean
[attachments-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeDistinctAttachmentsAudit.lean
[attachments-probe]: ../../../../tools/fourcolor/classical/matching-boundary-connectivity-probe.json
[attachments-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-attachments-measurements.json

[minimal-exterior]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeMinimalExterior.lean
[minimal-exterior-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeMinimalExteriorAudit.lean
[cycle-incidence]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CubicCycleIncidence.lean
[cycle-orientation]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CycleBoundaryOrientation.lean
[cycle-recognition-audit]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CycleBoundaryRecognitionAudit.lean
[cycle-recognition-measurements]: ../../../../tools/fourcolor/classical/cycle-boundary-recognition-measurements.json
[spoke-order-probe]: ../../../../tools/fourcolor/classical/lobe-spoke-order-probe.json
[minimal-exterior-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-minimal-exterior-measurements.json
[six-port-connectivity]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/SixPortBoundaryConnectivity.lean
[vertex-lower-bound]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/SphericalVertexLowerBound.lean

[cycle-spoke-connectivity]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CycleSpokeConnectivity.lean
[lobe-spoke-order]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ElevenLobeSpokeOrder.lean
[lobe-spoke-order-audit]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ElevenLobeSpokeOrderAudit.lean
[lobe-spoke-order-measurements]: ../../../../tools/fourcolor/classical/eleven-lobe-spoke-order-measurements.json

[lobe-recognition]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeRecognition.lean
[lobe-coordinates]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeCoordinates.lean
[dart-recognition]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OpenTangleDartRecognition.lean
[lobe-recognition-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeRecognitionAudit.lean
[lobe-recognition-measurements]: ../../../../tools/fourcolor/classical/pentagonal-lobe-recognition-measurements.json

[corona-boundary]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaBoundary.lean
[corona-chord]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaChordExclusion.lean
[cyclic-five-boundary]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CyclicFiveBoundary.lean
[corona-chord-probe]: ../../../../tools/fourcolor/classical/pentagonal_corona_chord_probe.py
[dart-separation]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PartialCubicDartSeparation.lean
[corona-immersion]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaImmersion.lean
[corona-separation]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaSeparationCheck.lean
[corona-noncollision]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalCoronaNoncollision.lean
[corona-separation-probe]: ../../../../tools/fourcolor/classical/pentagonal_corona_separation_probe.py

[diamond-face-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalDiamondFaceReduction.lean
[diamond-tangle]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalDiamondTangle.lean
[diamond-face-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/PentagonalDiamondFaceReductionAudit.lean
[partial-dart-boundary]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PartialCubicDartBoundary.lean
[six-port-replacement]: ../../../../lean/fourcolor-classical/MettapediaFourColor/SixPortTreeReplacement.lean
[diamond-probe]: ../../../../tools/fourcolor/classical/pentagonal-diamond-probe.json
[diamond-measurements]: ../../../../tools/fourcolor/classical/pentagonal-diamond-measurements.json


## Uniform boundary reconstruction

The [matching translation][uniform-codec] now works at every finite width.
Scan the ordered ports: a fixed port is skipped, the first end of a pair
opens a stack entry, and its second end closes that entry. Noncrossing
ensures that a closing endpoint meets the top open pair.
The [literal stack law][uniform-stack] proves these transitions
for arbitrary involutions, and the parser proof preserves the endpoint
colour relation.

This retains the coupling that made the diamond repair successful. Every
accepted answer differs from the original colouring by switches of complete
original pairs. The proof never chooses a new matching for each answer.
[Physical switching][uniform-closure] reconstructs a genuine colouring of
the whole exterior. Thus the representation change preserves both the joint
boundary observation and the interior witnesses needed for sewing.

The [actual mixed-diamond consumer][mixed-closure] supplies the geometric
hypotheses. The recognized core has one boundary-return cycle. In a
cyclically five-edge-connected cubic graph, a component with a cycle needs
at least five outgoing ports; another component needs at least three.
Seven ports and at least six exterior vertices therefore force connectivity.
No distinctness condition on exterior attachment vertices is used. Planarity
then gives the opposite exterior order and noncrossing of its actual
bichromatic components. The generic proof applies directly at width seven.

The [dependency audit][uniform-audit] requires the stack theorem, physical
component switches, planar separation, actual occurrence and shared
configuration-2 repair. It excludes the old finite matching and arc
translations, original catalogue certificates and complete Four Colour
endpoints. The earlier six-port consumer now uses the same uniform codec.
The [measurement record][uniform-measurements] keeps this replacement of
finite classifications separate from catalogue counts: 633 configurations
and 630 original configuration certificates still remain.

The [bounded replay][uniform-probe] checks all noncrossing involutions through
width eight, including 127 at width seven and 323 at width eight. For each
chromogram it compares the complete answer set with simultaneous switches
of whole original pairs. It also checks cyclic arc witnesses through width
sixteen and the literal mixed diamond's boundary-return geometry. These
program checks are independent finite evidence; the Lean theorem covers
arbitrary widths.

The next result completes the replacement step: the five-vertex path
preserves the ambient class and supplies the initial exterior colouring by
restriction from the smaller map. This uses the closure proved here;
closure alone does not give colourability. No global coverage, colour-count
preservation under reduction, or executable recolouring-history theorem is
inferred.

[uniform-codec]: ../../../../lean/fourcolor-classical/MettapediaFourColor/KempeMatchingChromogram.lean
[uniform-stack]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/NoncrossingMatchingStack.lean
[uniform-closure]: ../../../../lean/fourcolor-classical/MettapediaFourColor/OpenTangleKempeClosure.lean
[mixed-closure]: ../../../../lean/fourcolor-classical/MettapediaFourColor/MixedDiamondExteriorClosure.lean
[uniform-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/MixedDiamondExteriorClosureAudit.lean
[uniform-measurements]: ../../../../tools/fourcolor/classical/uniform-kempe-measurements.json
[uniform-probe]: ../../../../tools/fourcolor/classical/uniform-matching-probe.json


## Strict reduction of the mixed diamond

The [actual face-pattern theorem][mixed-reduction] completes a second
geometric application of the shared diamond repair. A central pentagon has
a hexagonal neighbour flanked by two pentagons; the other two neighbouring
face lengths are unrestricted. In the stated connected bridgeless spherical
cubic normal form, this recognizes the thirteen-vertex, seven-port piece.
The ambient assumptions are minimum face size five, cubic-dual internal-six
connectivity and two-sided orbit faces. Minimal-counterexample normal form
supplies all of them.

The replacement is the [five-vertex path][seven-tree]. Each vertex has a
boundary port and each endpoint has two. Its seven ordered face returns
are the same cyclic permutation as the old piece's. Although the interiors
have different face counts, both have Euler mass four. Consequently they
contribute the same Euler characteristic in every fixed exterior.

[One map-preservation theorem][replacement-class] combines that exact boundary
calculation with connectedness, boundary-essentiality and cubic cyclic
rotations. It now serves both the six-port and seven-port reductions. The
exterior's connectedness is proved from the actual geometry; its attachment
vertices need not be distinct. Every seam edge keeps its own identity.

The colouring argument then follows the compositional plan:

```text
13-vertex interior + actual exterior
                 |
        replace interior by 5-vertex path
                 |
        smaller valid map: 8 fewer vertices
                 |
        restrict a colouring to the exterior
                 |
        shared joint repair and physical Kempe switches
                 |
        compatible witnesses colour the original map
```

The strict-reduction theorem proves the last implication for any colouring
of the smaller map. In a vertex-minimal counterexample, minimality supplies
that colouring and yields a contradiction. No initial exterior colouring is
assumed in the exclusion theorem. The exterior may be arbitrarily large;
the local core and boundary width are fixed.

The [dependency audit][mixed-reduction-audit] checks fourteen roots and 28,102
declarations, using only `propext`, `Classical.choice` and `Quot.sound`.
It requires actual recognition, the smaller-map geometry, complete vertex
counting, physical closure, shared `repair002` and genuine witness gluing.
It excludes complete Four Colour endpoints, original configuration
certificates and the superseded finite matching translations.

The [independent geometric replay][mixed-reduction-probe] reads the exact
Lean tables and checks all fourteen dihedral sewings to a five-vertex
exterior. The seven reflected seams are spherical; the other orientation
has Euler characteristic minus four. Replacement preserves Euler
characteristic, connectedness and bridge-freedom in all fourteen tests, with
an eighteen-to-ten vertex decrease. These are bounded geometric controls;
the Lean theorem establishes the reduction in every qualifying exterior.

The [measurement record][mixed-reduction-measurements] credits a completed
local strict reduction and a shared geometric proof. It introduces no new
colouring certificate and removes no additional catalogue dependency:
633 configurations and 630 original certificates remain. The next family
and coverage work must explain which stopping lobes supply these patterns,
or provide a sound replacement for the lobes they do not cover.

[mixed-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/MixedDiamondFaceReduction.lean
[seven-tree]: ../../../../lean/fourcolor-classical/MettapediaFourColor/SevenPortTree.lean
[replacement-class]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OpenTangleReplacementClass.lean
[mixed-reduction-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/MixedDiamondFaceReductionAudit.lean
[mixed-reduction-probe]: ../../../../tools/fourcolor/classical/mixed-diamond-reduction-probe.json
[mixed-reduction-measurements]: ../../../../tools/fourcolor/classical/mixed-diamond-reduction-measurements.json

## The coupled eight-port wiring

Configuration 4 exposes why the boundary contract matters. Its proved repair
starts with a **joint contraction colouring**. A smaller piece must supply
that contract; an arbitrary proper eight-port word is insufficient.

Eliminating the contracted interior gives this wiring:

```text
0 ── 1                          4 ── 5

2 ─┐                            ┌─ 6
   ●────── shared colour ────────●
3 ─┘                            └─ 7
```

There are two vertices and seven edges, including the two free wires.
Writing the eight boundary colours as `c₀,…,c₇`, the joint relation says
that all are nonzero and

```text
c₀ = c₁,     c₄ = c₅,     c₂ + c₃ = c₆ + c₇ ≠ 0.
```

Addition is in the Klein four-group. The last common value is the central
edge colour. Each insertion alone only requires its own sum to be nonzero;
the joint law requires the sums to agree. The kernel-checked example
`[1,1,1,2,1,1,1,3]` passes the two separate tests and fails the joint one.
Independent enumeration gives 108 valid joint words and 216 additional
spurious words after forgetting the coupling.

This is exact boundary elimination with reconstruction. Given the wiring
colours, choose one face colour as zero and recover the other face colours
by addition. Conversely a joint contract colouring supplies every wiring
edge colour. [DiamondCoupledWiring][coupled-wiring] proves both directions
and feeds the result to the already integrated shared diamond repair.

[DiamondCoupledWiringRotation][coupled-rotation] constructs the actual graph
in an arbitrary exterior, retaining all exterior darts and vertex rotations.
It requires the endpoints of each free wire to be distinct. The
[witness theorem][coupled-witness] restricts a genuine graph colouring to
the complete exterior assignment and all wiring edges, and glues matching
witnesses back. Its GSLT consumer retains a compatible history through both
insertions. Existence and genuine reconstruction are proved; equality of
colouring counts or executable recolouring histories is not asserted.

[JointDiamondTangle][joint-tangle] identifies the original fourteen-vertex
piece with the reference darts, internal edge flips, cyclic rotations and
adjacent face labels. The theorem `colorable_of_wiring` reconstructs that
piece from a colouring of the smaller wired graph, assuming the exterior's
Kempe closure. The whole-map count includes both introduced vertices:
`(|exterior| + 2) + 12 = |exterior| + 14`.

At an exact embedded occurrence, the formerly assumed exterior conditions
are now derived. [JointDiamondOccurrence][joint-occurrence] transports one
of the core's hexagons as six distinct actual face darts. Minimum face length
five and Euler counting then force more than twenty ambient vertices, leaving
at least seven vertices outside the fourteen-vertex core.

The [eight-port connectivity law][eight-port-connectivity] explains why this
is enough. Seven cubic vertices behind eight ports force a cycle. A cyclic
component consumes at least five ports; any other
component consumes at least three. A disconnected side behind eight ports
can therefore only have a cyclic component and an isolated point. Internal-six
connectivity bounds that cyclic component by five vertices when the other
shore is large. Seven exterior vertices exclude this split. Attachments may
repeat; no distinct-endpoint assumption is used for exterior connectivity.

Connected shores in the spherical embedding have opposite cyclic boundary
orders. The existing arbitrary-width matching theorem then reconstructs
physical Kempe answers on this eight-port exterior. Finally, each proposed
free wire joins two ports whose core vertices are adjacent. Identifying its
exterior endpoints would create a triangle, excluded by normal form.

[JointDiamondWiredOccurrence][joint-wired-occurrence] combines these facts
with exact boundary-coordinate transport. Its `colorable_of_actual_wiring`
reconstructs a colouring of the actual original graph from a colouring of
the actual wiring. Its whole-map count is twelve fewer vertices, including
both new vertices. Wire separation and exterior closure are conclusions.
The occurrence itself is supplied as an exact isomorphism with a vertex
shore, preserving every internal edge, rotation and boundary dart.

The wiring's class preservation is now proved in
[JointDiamondOccurrenceReduction][joint-reduction]. This closes the strict
reduction at every supplied exact occurrence under the stated normal form.
The occurrence must still be constructed from the intended neighbouring
face lengths. Planarity and bridge-freedom alone do not suffice: the
[independent replay][coupled-probe] finds planar bridgeless originals whose
disconnected exterior acquires a bridge after replacement. Those originals
have triangular faces, excluded by the intended minimal-counterexample
normal form.

The [actual-occurrence replay][joint-occurrence-probe] checks all 15,864
rooted darts in the saved 137 fullerene rotations. It finds 1,424 rooted
occurrences, representing 712 vertex subsets in 126 maps. Every exterior
is connected, and every wired graph is connected, bridgeless, loop-free
and spherical with twelve fewer vertices. These finite checks support the
operation; they do not certify internal-six connectivity of the fixtures
or prove coverage. The new Lean theorem establishes preservation for arbitrary
qualifying exteriors, independently of this census.

The new bridge argument explains why the coupling also matters geometrically.
The wiring has three port blocks: `{0,1}`, `{4,5}` and `{2,3,6,7}`. A potential
bridge can only separate whole blocks when the exterior is connected.
For either free-wire block, extending the putative cut through two old core
vertices would give a cut of at most three edges with at least three vertices
on each side. Cyclic-five connectivity excludes it.

The four-port block needs **two extensions of the same exterior cut**. One
puts four old vertices on the selected side; the other puts ten there. Both
add four crossing edges. Including the putative exterior bridge gives at
most five edges, so internal-six connectivity forces a shore of at most five
vertices. The four-vertex extension forces at most one selected exterior
vertex. The ten-vertex extension forces at most one unselected exterior
vertex. The exterior has at least seven vertices, contradicting both bounds
together. [JointDiamondCutLifting][joint-cut-lifting] proves this argument
with exterior size and vertex assignments left arbitrary. The constant-port
and complementary-block cases are covered too.

The face calculation retains all eight ports and all six new vertex darts,
so both free wires are counted. The exact exterior return is the inverse
eight-cycle. A generic [port-return face theorem][port-face-count] and the
[wiring's face theorem][wiring-faces] give:

| Whole-map quantity | Decrease |
| --- | --- |
| Vertices | 14 removed, 2 added: 12 |
| Edges | 18 |
| Faces | 6 |
| Euler characteristic | `12 − 18 + 6 = 0` |

Exterior vertex rotations are unchanged; the two new vertices are cubic.
The resulting map is connected, bridgeless and spherical. Thus the chain is
now complete for a supplied occurrence:

```text
exact embedded joint diamond + ambient normal form
  → actual smaller coupled wiring in the same map class
  → smaller-map colouring from minimality
  → shared joint repair with genuine exterior witnesses
  → original-map colouring
```

This is Ben's proposed boundary mechanism working in a concrete strict
reduction: keep the shared choice, reduce the interior, and reconstruct
compatible witnesses. It handles arbitrary qualifying exteriors around this
fixed core. It does not yet establish an unbounded family of distinct cores,
preservation of colouring counts, or executable recolouring histories.

The [audit and measurements][coupled-measurements] cover the actual witness
chain and exclude the former configuration-specific repair certificate.
This advances the geometric implementation of the existing shared proof;
the complete baseline still retains 633 configurations and 630 original
configuration certificates. No additional certificate saving or global
coverage is credited.

The earlier [actual-occurrence audit][joint-occurrence-measurements] checks twenty
roots and 23,910 dependency declarations with standard axioms only. It
requires the hexagon, eight-port cut argument, physical Kempe matching,
exact coordinate transport, joint repair and genuine whole-map gluing.
The former configuration certificates and complete Four Colour endpoints
are absent from these theorem dependencies.

The [strict-reduction audit and measurements][joint-reduction-measurements]
check 28 roots and 28,002 dependency declarations with the same standard-axiom
restriction. Required dependencies include actual source-cut transport, both
cut extensions, complete seam face counting, strict decrease, joint repair
and the minimal-counterexample consumer. The independent
[finite geometry replay][joint-class-probe] checks all 1,024 binary seam
assignments, the four old-shore extensions and the face corrections.
No additional colouring certificate is introduced.

Recognition now starts from the four face lengths: two adjacent hexagons,
flanked by two pentagons that each touch both. The [actual traversal][joint-face-geometry]
constructs all seventeen internal edges and forty-two incident darts from
four face periods. This is a geometric interpretation before vertex
distinctness or absence of additional edges is assumed.

The [distinctness theorem][joint-distinct] supplies fourteen distinct vertices
under girth, cyclic five-edge connectivity and an ambient size of at least
seventeen; the normal form supplies these conditions. Joint dart transport
separates most positions. The exceptional identification would make the two
flanking pentagons share their outer edge. Transport fixes the slot phase
and consumes four candidate ports. Twelve vertices remain distinct, leaving
a cyclic shore behind at most four edges, which cyclic-five connectivity
excludes. This is a geometric use of the same principle as the colouring
repair: keep the relation between the two sides while applying operations.

The [complete recognizer and strict-reduction consumer][joint-clearance] now give:

```text
four face lengths + spherical normal form
  → fourteen distinct vertices and all internal operations
  → connected core and connected exterior
  → all eight candidate ports leave the core
  → exact ordered occurrence
  → strict twelve-vertex reduction and actual colouring reconstruction
```

The outgoing-port assertion is proved. Suppose one candidate returns to the
core. Its reversed dart must be another candidate: injectivity and the
recorded edge pairs exclude every internal slot. This consumes two of the
eight candidates. The [general boundary-completion theorem][boundary-completion]
uses cubic parity and cyclic five-edge connectivity to show that all six
remaining candidates genuinely leave. The same theorem applies to any
injectively realized even-sized partial cubic diagram satisfying its size
and cut hypotheses.

The geometry now retains the cyclic order of those six ports. The original
piece's forty-two darts carry one fixed boundary-arc map. Joining ports
`p` and `q` creates a cyclic-interval label invariant under every step of
the completed face permutation. Ports on opposite sides have different
labels, so they cannot share a face orbit. Girth excludes short chords;
this [single chord argument][joint-chord] handles every remaining pair.
It uses a forty-two-character arc map, without separate stored orbit tables
for each chord.

This literal computation is connected to the actual graph by a proved
permutation conjugacy. The real capped edge flip follows the added chord
and fixes the six exposed darts; vertex rotations commute with the same
coordinate map. On the other hand, the core and its exterior are both
connected, so spherical planar-bond geometry puts all exposed ports on
one capped face. The two conclusions contradict each other. This proves
`BoundaryClear` and removes it as a premise of the final recognizer.

The resulting operation handles every occurrence of this face pattern
in an arbitrary qualifying exterior. It removes fourteen vertices,
introduces two, preserves the connected bridgeless spherical cubic class,
and reconstructs genuine colourings through the shared seam choice.
A vertex-minimal counterexample therefore cannot contain this pattern.
The local face pattern remains an explicit hypothesis; broader families,
geometric supply and global coverage remain open. Colouring counts and
executable-history equivalence are not asserted.

The [independent replay][joint-clearance-probe] tests all 2,688 combinations
of chord choices and dart steps against the cyclic-interval law. It also
replays 15,864 rooted darts in 137 saved maps: all 1,424 matching four-face
patterns have the recognized ports and admit the physical reduction.
Fixture internal-six connectivity is not certified by this replay. These
program checks accompany the universal geometric theorem; they are not
its proof.

The [clearance audit][joint-clearance-audit] checks eighteen roots and 28,530
dependency declarations with only `propext`, `Classical.choice` and
`Quot.sound`. It requires the actual face transport, planar bond, six-port
saturation, strict reduction and smaller-map minimality. Complete Four
Colour endpoints, original configuration certificates and superseded
independent repairs are excluded. The [receipt][joint-clearance-measurements]
records the exact scope and validation. The earlier conditional
[recognition receipt][joint-face-measurements] remains a historical checkpoint.
No additional catalogue entry or original colouring certificate is removed.

[joint-occurrence]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondOccurrence.lean
[joint-wired-occurrence]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondWiredOccurrence.lean
[eight-port-connectivity]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/EightPortBoundaryConnectivity.lean
[joint-occurrence-probe]: ../../../../tools/fourcolor/classical/joint-diamond-occurrence-probe.json
[joint-occurrence-measurements]: ../../../../tools/fourcolor/classical/joint-diamond-occurrence-measurements.json
[joint-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondOccurrenceReduction.lean
[joint-cut-lifting]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondCutLifting.lean
[port-face-count]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OpenTanglePortFaceCount.lean
[wiring-faces]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiringFaces.lean
[joint-reduction-measurements]: ../../../../tools/fourcolor/classical/joint-diamond-reduction-measurements.json
[joint-class-probe]: ../../../../tools/fourcolor/classical/joint-diamond-class-probe.json
[joint-face-geometry]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/JointDiamondGeometry.lean
[joint-distinct]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/JointDiamondDistinct.lean
[joint-face-reduction]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondFaceReduction.lean
[joint-face-probe]: ../../../../tools/fourcolor/classical/joint-diamond-face-probe.json
[joint-face-measurements]: ../../../../tools/fourcolor/classical/joint-diamond-face-measurements.json

[coupled-wiring]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiring.lean
[coupled-rotation]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiringRotation.lean
[coupled-witness]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiringWitness.lean
[joint-tangle]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondTangle.lean
[coupled-probe]: ../../../../tools/fourcolor/classical/coupled-wiring-probe.json
[coupled-measurements]: ../../../../tools/fourcolor/classical/coupled-wiring-measurements.json

[boundary-completion]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PartialCubicDartBoundaryCompletion.lean
[joint-chord]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondChord.lean
[joint-clearance]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondFaceClearance.lean
[joint-clearance-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondClearanceAudit.lean
[joint-clearance-probe]: ../../../../tools/fourcolor/classical/joint-diamond-clearance-probe.json
[joint-clearance-measurements]: ../../../../tools/fourcolor/classical/joint-diamond-clearance-measurements.json

## Geometric supply from pentagonal neighbour density

The three diamond reductions now have one common supply argument. It uses
the actual cyclic positions of neighbouring pentagonal faces. Incidences
are counted separately, preserving information that a set of neighbour
names could lose.

Mark each position of a five- or six-sided face when the face across that
edge is a pentagon. Any three marked positions include two separated by
exactly one position. The intervening edge therefore has a pentagon at
each flank. If all face lengths are five or six, its incident faces select
one of the completed reductions:

| Incident face lengths | Existing core | Replacement | Net vertices removed |
| --- | --- | --- | --- |
| 5, 5 | Twelve vertices, six ports | Four-vertex tree | 8 |
| 5, 6 | Thirteen vertices, seven ports | Five-vertex path | 8 |
| 6, 6 | Fourteen vertices, eight ports | Coupled wiring with two vertices | 12 |

[`classify_flanked`][diamond-supply] proves the exact reversal and rebasing
of the actual dart into the existing face-pattern hypotheses. Each physical
reduction retains the joint colouring relation its reconstruction needs;
choosing a representation does not introduce an independent choice of
colours. The existing normal-form hypotheses supply the recognized pieces,
compatible exterior, preserved map class and strict size decrease.

The same local observation gives a coverage bound. If no diamond occurs,
every face has at most two pentagonal incidences. A spherical cubic
all-five/six map has twelve pentagons, hence sixty such incidences. Writing
`F` and `V` for the numbers of faces and vertices, double counting and Euler
give

\[
60 \leq 2F = V+4, \qquad V\geq56.
\]

[`of_card_lt_fiftysix`][diamond-supply] therefore produces an actual root
and one of the three face patterns below 56 vertices. This proof uses
orbit incidence and the cubic Euler identity; it does not enumerate maps.
`not_in_minimal` consumes all three physical reductions.
`fiftysix_le_vertices_of_fullerene_minimal` states the resulting bound in
the existing fullerene class, deriving the boundary-edge/dart-length
correspondence from the actual two-sided embedding. Three pentagonal
incidences at any face are also excluded from an all-five/six minimal
counterexample, regardless of its size.

The [independent replay][diamond-supply-probe] checks all dart/phase starts
in 137 saved maps and three larger controls. Every one of the 1,489 odd
closing seams in the small maps lies in a recognized diamond core. The
scanner independently compares the flanked-edge criterion with all three
original face predicates; multiple predicates at a root are retained.
One even ten-vertex row is disjoint from every diamond in its map, where
row continuation or another choice is needed. Goldberg GP(2,0), GP(3,0)
and GP(4,0), with 80, 180 and 320 vertices, have no diamond of these three
types anywhere. Their extracted lobes are alternating rows of lengths
20, 30 and 40. These are finite observations; the fixture census does not
certify internal-six connectivity or minimality.

The [dependency audit][diamond-supply-audit] checks the actual incidence,
geometric transport and three reduction branches. Original configuration
certificates, superseded independent diamond repairs and complete Four
Colour endpoints are excluded. The [measurement record][diamond-supply-measurements]
records the kernel build and source/artifact hashes. The only new finite
checks concern the 32 and 64 binary position patterns at lengths five and
six; no new colouring certificate is introduced.

This is a shared coverage argument for the stated class. The complete
assembly still retains 633 catalogue entries and 630 original certificate
dependencies. Larger sparse all-five/six maps, other face sizes and global
coverage require further mechanisms. Existence of colouring witnesses is
the semantic conclusion used here; neither colouring counts nor execution
history equivalence is inferred.

[diamond-supply]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondGeometricSupply.lean
[diamond-supply-audit]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondGeometricSupplyAudit.lean
[diamond-supply-probe]: ../../../../tools/fourcolor/classical/diamond-supply-probe.json
[diamond-supply-measurements]: ../../../../tools/fourcolor/classical/diamond-supply-measurements.json


## Two-row deletion with a cyclic seam shift

The [new reduction][twist-reduction] uses a freedom that the exact-support
normalization did not: change the port matching when building the smaller
map. It is a uniform law for every circumference `k ≥ 2` and every tube of
at least three rows. Delete two rows and move the right attachment by one
cyclic port. Every colouring of that smaller graph reconstructs a colouring
of the original. No finite ring-stabilization certificate is used.

The colouring argument is short. Write `R(x,y)` for a genuine ring colouring,
and `s` for the cyclic shift of a boundary word. The existing complementary
cursor and rotation laws give

```text
R(x,y)  →  R(y,s(x))  →  R(s(x),s(y)).
```

These three witnesses compose because their middle words agree. Thus a
single ring can be reconstructed as three, with output `s(y)`. For a longer
tube the same operation acts on its final ring. The shorter tube's new port
`i` denotes its original port `i+1`, so the word observed by the fixed exterior
is exactly the word reconstructed by the longer tube. This is a directed
support inclusion. An equivalence of supports, preservation of colouring
counts, or an executable Kempe history is not claimed.

The geometric proof uses the same joint observations as the colour proof.
A tube's face return advances the left boundary and retreats the right
boundary. The cyclic reattachment commutes with these permutations. Boundary
reindexing also retains the open Euler mass, the interior edge graph and all
vertex rotations. Consequently the existing replacement theorems preserve
Euler characteristic, connectedness, bridge-freedom and cubicity in every
fixed exterior, including disconnected exteriors. No vertices are introduced
outside the tube. Removing two rows decreases the total vertex count by
exactly `4k`.

The [embedded consumer][twist-embedded] starts with actual recognized rows.
Their hexagonal seam faces supply the coordinate offsets; whole-strip
assembly and the exact exterior identify the physical operation. It proves
`Tube.hexagonal_length_le_two`: a graph-backed vertex-minimal Tait
counterexample contains at most two rows in any such tube, at any width
`k ≥ 2`. This improves the earlier width-five bound of four rows. It does
not assert a smaller threshold for exact support with the original matching.

Combining the reduction with the already proved collar construction gives
`ZigzagSlab.pentagonWithin_one`. In an all-five/six minimal counterexample,
any supplied oriented row meets a pentagonal seam immediately or after one
successful hexagonal extension. Arbitrarily large width therefore does not permit a
long constant-width corridor at this stage. Supplying a suitable row and
repairing the pentagonal transition are still necessary.

The [GSLT consumer][twist-gslt] uses the existing event language and directed
replacement cells. Genuine colouring witnesses lift through arbitrary
prefix and suffix routes while retaining both shared boundary assignments.
Every predicate on the outer observations survives this reconstruction.
The cell uses existential witness selection; it adds no claim about runtime
or the number of colourings.

The [independent replay][twist-probe] checks all 87,390 ring colourings at
widths two through eight. It also physically performs the operation in two
sparse Goldberg controls which contain none of the three recognized diamond
cores. GP(3,0) has a three-row width-15 tube: 180 vertices become 120.
GP(4,0) has a four-row width-20 tube: 320 become 240. Both reduced rotations
are spherical, connected, cubic and bridgeless; explicit smaller colourings
reconstruct with all exterior edge colours fixed. GP(2,0) reaches its
pentagonal stop after only two rows, so it remains outside this reduction.
These are finite examples, separate from the general theorem.

The [audit][twist-audit] checks thirteen roots and 12,297 dependency
declarations, with only the three standard axioms. It excludes the classical
Four Colour theorem, finite tube stabilization certificates and long-length
mixing bounds. The [measurement receipt][twist-measurements] records the
checks and scope. The complete classical assembly remains at 633 catalogue
entries and 630 original configuration certificate dependencies. This new
geometric reduction has not replaced another certificate in those endpoints.

[twist-reduction]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagTubeTwistReduction.lean
[twist-embedded]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HexagonalTubeTwistReduction.lean
[twist-gslt]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagTubeTwistGSLT.lean
[twist-audit]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ZigzagTubeTwistAudit.lean
[twist-probe]: ../../../../tools/fourcolor/classical/twisted-tube-probe.json
[twist-measurements]: ../../../../tools/fourcolor/classical/twisted-tube-measurements.json


## A joint colouring law for padded cycle caps

The two-row tube reduction leaves a concrete short control: the 80-vertex
Goldberg GP(2,0) map. A pentagon and its surrounding layers form a
40-vertex hemisphere. Its colouring problem belongs to an unbounded family:
three concentric cycles of lengths `m`, `3m` and `4m`, with two outward
ports per sector. There are `8m` vertices and `2m` boundary ports.
[`PaddedCycleCapTangle`](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapTangle.lean)
retains every internal edge, cyclic vertex star and outer port.

The smaller piece is the cycle with `2m` vertices. The
[kernel-checked reconstruction](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapSource.lean)
proves: for every `m ≥ 2`, every **nonconstant** boundary word admitted by
that smaller cycle is admitted by the padded cap. The source is an actual
cycle colouring. The target is an actual colouring of all `8m` vertices.
The result is directed support inclusion on the stated domain; colouring
counts and executable recolouring histories are separate questions.

The proof keeps three radial seam colours together. If `s_i` is the
smaller cycle's incoming edge colour and `a_i,b_i` its two consecutive
boundary letters, the shared choices `q_i` need satisfy only

```text
q_i ≠ 0,       q_i ≠ q_(i-1),       q_i ≠ a_i.
```

Set the inner and middle radial colours both equal to `q_i`. The
[sector formula](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapColouring.lean)
then reconstructs all eight vertex constraints using addition in the Klein
four group. A nonconstant source boundary forces the forbidden letters
`a_i` to vary. The [cyclic avoidance law](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CyclicColourAvoidance.lean)
cuts at two different forbidden letters, makes successive compatible
choices, and proves that the final edge closes. This one argument covers
all sector counts. Only elementary arithmetic on the four-element colour
group uses finite decision; no list of cap configurations or boundary words
supplies the family theorem.

The [context theorem](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapContext.lean)
reconstructs inside any fixed sewn exterior when the supplied smaller
colouring has a nonconstant interface. Every exterior dart retains its
colour. The GSLT cell carries the guard explicitly, and horizontal composition
retains both seam words and the actual exterior witnesses. Boundary
reindexing connects the sector coordinates to the smaller cycle's ordered
ports. This is a concrete instance of transporting one argument between
representations without forgetting the joint choices needed for gluing.
The whole-map vertex count differs by exactly `6m`; no outside vertices
are added by the operation.

The geometric part is now proved uniformly. The literal cap has `3m+2`
open faces: one central face, two hexagons and one pentagon per sector,
and one outer face. The smaller cycle has two open faces. Both have open
Euler contribution four and the same return to the preceding boundary
port. Their interiors are connected and bridgeless. For the cap, a cut of
size at most one must be constant around each of its three cycles; at
least two radial edges between consecutive cycles force those constants
to agree. The existing joint-boundary replacement theorems then prove
[map-class preservation](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapReplacement.lean)
in every exterior, including disconnected ones.

For **every even `m ≥ 2`**, the colouring guard can now be removed as well.
When all forbidden letters agree, alternate the other two colours around
the inner cycle. Evenness closes that final edge. When they vary, use the
same earlier cyclic avoidance law. Thus
[`strict_even_reduction`](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapEven.lean)
is a complete strict reduction scheme for an unbounded family: all smaller
colourings reconstruct, the spherical cubic connected bridgeless class is
preserved, and exactly `6m` vertices disappear. The GSLT cell acts on the
entire smaller colouring relation and preserves its shared interface words
under horizontal composition. It does not assert equality of colouring
counts or a certified executable recolouring history.

[Exact representation transport](../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapTransport.lean)
requires dart and vertex equivalences preserving edge mates, incidence and
rotation. It transfers the strict reduction to the represented ambient
graph and excludes such an even cap from a vertex-minimal counterexample.
This is the relevant TransWeave obligation in explicit form: the geometric
operations and reconstruction use the same representation change. Supplying
these equivalences from a broader face pattern remains a recognition problem.

The [independent replay](../../../../tools/fourcolor/classical/padded-cap-probe.json)
checks 87,348 nonconstant source colourings at sector counts 2 through 8,
plus all 24 constant source colourings at the four tested even widths.
For GP(2,0), it checks an orientation-preserving correspondence of the
literal cap with the actual hemisphere. Replacing that hemisphere by a
10-cycle takes 80 vertices to 50. The smaller rotation is connected,
bridgeless, spherical and cubic; one genuine smaller colouring reconstructs
while fixing all 120 exterior darts. The saved rotations, correspondence
and colourings are replayable with
[`padded_cap_probe.py`](../../../../tools/fourcolor/classical/padded_cap_probe.py).
These are finite program checks, separate from the general Lean theorem.

The [geometry replay](../../../../tools/fourcolor/classical/padded-cap-geometry-probe.json)
checks literal sewing at sector counts 2 through 20, retaining parallel
edge identities at width two. Its even-width example is a 96-vertex map
with twelve pentagons and 38 hexagons. Replacing one 48-vertex cap by its
12-cycle gives 60 vertices. A genuine colouring reconstructs while fixing
all 144 exterior darts. This gives a concrete member in the all-five/six
setting; the replay is program evidence, not a general recognition theorem.

At odd widths, the guard cannot simply be dropped. Exhaustive support checks at `m=3`
and `m=5` find exactly three smaller-cycle words missing from the padded
cap: the three monochromatic words. At `m=4` the checked inclusion has no
exceptions. These finite obstructions identify the repair obligation: change
a constant interface through a justified exterior Kempe operation, or use
another compatible smaller construction. Opposite parity alone is insufficient:
switching ports 0 and 3 of six constant-1 ports gives `[2,1,1,2,1,1]`, which
admits no cycle colouring. This also occurs in the noncrossing matching
`[(0,3),(1,2),(4,5)]`. The adjacent-component law below repairs that failure.

The even family reduction is complete on its stated domain. Its relation
to Ben's proposed uniform explanation is concrete: one law replaces all
width-specific colouring checks for this family, and joint interface data
lets the law act in arbitrary contexts. The odd family now has the coupled
repair below on its connected-exterior geometric domain. Recognition in
broader residual maps, disconnected odd-width exteriors and eventual coverage
remain open.
The finite GP(2,0) example does not certify those universal statements or
establish minimality.
The [audit receipt](../../../../tools/fourcolor/classical/padded-cap-measurements.json)
records 26 checked dependency roots spanning 12,182 declarations, standard axioms only, and the
absence of the complete classical theorem and finite tube-stabilization
certificates. All 633 catalogue entries and 630 original configuration
certificate dependencies remain; this checkpoint replaces no further
certificate in the complete assembly.

## Repairing a constant cap boundary

The [physical repair][cap-physical] reconstructs at every sector count
`m ≥ 2`, including odd widths, when the actual exterior component matching
is noncrossing in the cap's ordered ports. It retains both pieces together.
For a nonconstant boundary, apply the earlier cap law. For a constant
boundary, choose one actual bichromatic exterior component joining adjacent
ports and switch the whole component. Renaming the two smaller cycle colours
first aligns their shared edge with the intended new boundary colour; changing
that edge then changes exactly the same two ports. Both pieces remain properly
coloured with one common, now nonconstant, boundary word. The cap law applies
and reconstructs the original sewn graph.

An [adjacent-pair theorem][matching-ear] supplies that component at every
boundary width. Choose a shortest chord of the physical perfect matching.
If it contains an interior port, noncrossing puts that port's mate inside
as well and gives a shorter chord. Thus a shortest chord joins consecutive
ports. The [physical component switch][constant-repair] preserves an actual
exterior colouring. No table of matching shapes or cap boundary words is used.

The [embedded consumer][cap-physical-geometry] discharges noncrossing from
spherical geometry. An exact local isomorphism identifies the cap's vertices,
internal edge mates, cyclic stars and boundary ports with an actual vertex
shore. Its preceding-port return and the opposite complementary-shore orders
determine the exterior coordinates. The cap's connectivity follows from the
isomorphism; **exterior connectivity remains explicit**. The spherical
separator theorem supplies noncrossing for every physical exterior colouring.
Replacing this recognized cap preserves the connected bridgeless spherical
cubic class, removes exactly `6m` vertices and reconstructs an ambient
colouring. A vertex-minimal counterexample therefore has no such occurrence.
Recognition from a broader face pattern and universal coverage are additional
obligations.

The GSLT map in [the repair module][cap-physical] acts on actual closed-map
colouring witnesses. The cap and its exterior are one joint witness, so the
component switch may change exterior colours. Horizontal composition preserves
separate surrounding GSLT witnesses and outer observations. This is the precise
compositional domain of this cell. The earlier even-width cell still fixes
every cap-exterior colour in arbitrary exteriors, including disconnected ones.
Neither map establishes equality of colouring counts or a certified executable
recolouring history.

The [independent replay][cap-physical-probe] checks 476 noncrossing matchings
at 6, 10 and 14 ports and 12,000 adjacent-pair colour choices. It also checks
84 literal closed-map repairs: all six ordered colour pairs at sector counts
2 through 15. In the pentagonal-sector example, a 50-vertex cap/cycle sewing
reduces to a 20-vertex smaller map. One actual exterior component changes
four dart colours, and cap reconstruction retains that repaired exterior.
The rotations, vertex stars, edge agreement and strict whole-map counts are
checked directly. These finite examples are program evidence; they are not
Lean certificates of the fixtures or a normal-form coverage result.

The [audit][cap-physical-audit] checks the physical switch, geometric order,
strict reduction, minimality and GSLT consumers. Its [receipt][cap-physical-measurements]
records 14 roots and 23,078 dependency declarations, with only the three
standard axioms. The complete classical theorem and finite tube-stabilization
certificates are absent from these proofs. This broadens a uniform family;
it removes no further catalogue entry or original certificate dependency
from the complete assembly. Those counts remain 633 and 630.

[cap-physical]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapPhysicalRepair.lean
[matching-ear]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/Compositional/NoncrossingMatchingEar.lean
[constant-repair]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/Compositional/ConstantBoundaryKempeRepair.lean
[cap-physical-geometry]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapPhysicalGeometry.lean
[cap-physical-probe]: ../../../../tools/fourcolor/classical/padded-cap-physical-probe.json
[cap-physical-audit]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapPhysicalAudit.lean
[cap-physical-measurements]: ../../../../tools/fourcolor/classical/padded-cap-physical-measurements.json

## Recognizing caps from their faces

The [face trace][cap-face-trace] now constructs the cap's actual dart and
vertex coordinates from one central `m`-face, an inner hexagonal collar,
and a second collar with one hexagon and one pentagon per sector. Face
closure proves every internal edge reversal; the actual cubic rotations
give the three darts at each vertex. The family parameter is unrestricted
apart from `m ≥ 2` in the reduction consumer.

The remaining boundary has `2m` ports. Between successive ports the trace
gives a three-step face arc. A [general short-face law][short-face-ports]
proves that these ports cannot connect to each other when their actual
outward faces have length five or six and their two-step predecessors are
separate from all ports. A proposed connection on a pentagon contradicts
that separation. A connection on a hexagon reflects to its neighbouring
pair. Repeated reflection reaches either a fixed edge or a three-step
facial loop, both impossible. This argument handles every width without
enumerating boundary matchings.

The [cap adapter][cap-port-geometry] derives the separation from injectivity
of the vertex trace. Its complete cubic stars then show that every port
leaves the entire cap, not just that it avoids the other ports.
The [recognition theorem][cap-face-recognition] uses these incidence equations
to construct the exact open-tangle isomorphism and consumes it in the
all-width strict reduction. An isomorphism or an induced-patch check is no
longer supplied as a hypothesis.

The [short-face connectivity law][short-face-connectivity] removes the
separate exterior-connectivity condition. A pentagonal seam joins successive
outside port endpoints by one exterior edge; a hexagonal seam joins them by
two. The hexagon's intermediate vertex cannot return into the cap: its
incoming edge would be another boundary port, whose next rotated edge is
internal, contradicting the final outside endpoint. Thus all port endpoints
lie in one exterior component. Ambient connectedness and classification of
every outgoing dart exclude any further exterior component. This argument
uses neither a colouring nor a cyclic cut-size condition, and applies at
every width.

The [actual cap consumer][cap-exterior] uses this derived connectivity in the
strict reduction and colouring reconstruction. The entire map loses exactly
`6m` vertices, including every vertex of the replacement cycle. The `8m`
traced vertices must still be distinct. Minimality supplies the ambient map
class, and a smaller-map colouring reconstructs a genuine original colouring.
A face pattern alone has not yet been proved sufficient at every width.

This is one concrete meaning of a compositional map: the graph operation
replaces a cap by a cycle, the boundary relation retains compatible shared
choices, and colouring reconstruction goes back from the smaller map to
the original. The short-face law supplies the exterior geometry used by
that reconstruction. These maps compose through their common interface;
independent choices at each port would lose information the repair needs.

The [independent face replay][cap-face-probe] checks 3,214 actual faces in
140 saved maps. It finds twelve matching central faces, all in GP(2,0);
each has forty distinct cap vertices, short seam faces, exposed ports and
a connected exterior. It separately checks the literal face trace at
sector counts two through twenty. These are finite program checks,
separate from the Lean family proof and from a coverage theorem.
The [audit receipt][cap-face-measurements] records the checked dependency
chains. The complete classical theorem and finite tube-stabilization
certificates are excluded. The coverage and original-certificate counts
remain 633 and 630.

The [exterior-arc replay][cap-exterior-probe] checks 956 arcs: 418 pentagonal
and 538 hexagonal. It includes both literal cap/cap and cap/cycle gluings at
sector counts two through twenty, plus the twelve saved GP(2,0) occurrences.
These remain finite program checks; the general connectivity argument and
its strict-reduction consumer are kernel-checked separately in the
[new audit receipt][cap-exterior-measurements]. No additional colouring
certificate or catalogue removal is credited.

[cap-face-trace]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapFaceTraversal.lean
[short-face-ports]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/Compositional/ShortFacePortExclusion.lean
[cap-port-geometry]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapPortGeometry.lean
[cap-face-recognition]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapRecognition.lean
[cap-face-probe]: ../../../../tools/fourcolor/classical/padded-cap-recognition-probe.json
[cap-face-measurements]: ../../../../tools/fourcolor/classical/padded-cap-recognition-measurements.json
[short-face-connectivity]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/Compositional/ShortFaceBoundaryConnectivity.lean
[cap-exterior]: ../../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/PaddedCycleCapExteriorConnectivity.lean
[cap-exterior-probe]: ../../../../tools/fourcolor/classical/padded-cap-exterior-probe.json
[cap-exterior-measurements]: ../../../../tools/fourcolor/classical/padded-cap-exterior-measurements.json
