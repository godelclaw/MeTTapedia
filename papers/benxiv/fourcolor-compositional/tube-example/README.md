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

The remaining theorem is geometric: recognize the piece in the intended
source class, derive wire separation and physical exterior closure, and
prove that this replacement stays in the class on which minimality supplies
a colouring. Planarity and bridge-freedom alone do not suffice. The
[independent replay][coupled-probe] finds planar bridgeless originals whose
disconnected exterior acquires a bridge after replacement. Those originals
have triangular faces, excluded by the intended minimal-counterexample
normal form. The next argument must use that stronger geometry explicitly.

The [audit and measurements][coupled-measurements] cover the actual witness
chain and exclude the former configuration-specific repair certificate.
This advances the geometric implementation of the existing shared proof;
the complete baseline still retains 633 configurations and 630 original
configuration certificates. No additional certificate saving or global
coverage is credited.

[coupled-wiring]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiring.lean
[coupled-rotation]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiringRotation.lean
[coupled-witness]: ../../../../lean/fourcolor-classical/MettapediaFourColor/DiamondCoupledWiringWitness.lean
[joint-tangle]: ../../../../lean/fourcolor-classical/MettapediaFourColor/JointDiamondTangle.lean
[coupled-probe]: ../../../../tools/fourcolor/classical/coupled-wiring-probe.json
[coupled-measurements]: ../../../../tools/fourcolor/classical/coupled-wiring-measurements.json
