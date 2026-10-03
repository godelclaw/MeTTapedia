# Near-linear Four Colour catalogue bridges

## Flat-seven returns and a shared-core test

Two small replay recipes test the proposed continuation through flat
degree-seven centres. Each gives a 162-vertex triangulated sphere of degrees
five through seven containing a facial triangle of three flat sevens.
All cycles of length three through five pass the short-cycle obstruction
test: a three- or four-cycle has an empty side, and a five-cycle has a side
containing at most one vertex. Flat sevens therefore need not form an
acyclic graph under these hypotheses. This does not refute continuation
with additional hypotheses or a separately justified progress measure.

| Recipe | Legal flips | Short cycles checked | Source occurrence | Boundary ports |
|---|---:|---:|---|---:|
| [First return](flat-seven-return-example.json) | 70 | 1,815 | D0092 | 11 |
| [Second return](flat-seven-return-extension-example.json) | 310 | 1,823 | D0063 | 10 |

In the first example, the union of radius-two balls at the three centres
contains no complete-core reading of D0000, D0001, D0004, D0006, D0051,
D0052 or D3009. The second example excludes those same readings and also
D0092 and D0142. All rooted darts and both orientations are tested;
boundary identifications are permitted in the negative search. The simple
diamond, chain and one/two-five wheel profiles are absent in both unions.
These are specified local inventories, not the entire reduction library.
Only the three centres are asserted flat; flatness of their entire
neighbourhoods is not assumed or established.

The positive D0092 and D0063 occurrences retain every source vertex,
ordered boundary edges, full core stars and cyclic order. Their induced
seven-vertex cores lie within radius two, and their full boundaries within
radius three. Their [core correspondence](flat-seven-return-core-map.json)
preserves all eleven internal edges and five internal facial triangles,
with one global reflection. Four prescribed degrees change and the
boundaries have different lengths. This supplies a concrete candidate for
a common family argument; it does **not** establish boundary transport,
colouring repair or a new reduction.

The [verifier](audit_flat_seven_return.py) replays legal flips from the
existing sphere fixture, compares compiled and breadth-first rule matching,
checks all short cycles, and verifies the supplied core map without an
isomorphism search. The [first receipt](flat-seven-return-audit.json) and
[second receipt](flat-seven-return-extension-audit.json) are exact program
checks, not Lean certification. No coverage entry or proof dependency is
removed. Replay from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_flat_seven_return.py
python3 tools/fourcolor/near-linear/audit_flat_seven_return.py --fixture flat-seven-return-extension-example.json
```

D0063, D0092 and D0142 are copied unchanged from the
[near-linear catalogue](https://github.com/near-linear-4ct/reducible-configurations/tree/c2ce7a96e35256201526e2abb51a39d04a588b53/D)
at revision `c2ce7a96e35256201526e2abb51a39d04a588b53`, under its retained
[MIT licence](LICENSE). The recipes pin their hashes and the existing
discharging-rule revision. These examples concern the flat facial
seven-triangle setting of
[Lemma 8.5](https://arxiv.org/html/2603.24880v1#S8.Thmthm5);
they do not contradict the paper's larger catalogue coverage.

## Boundary choice versus coordinated recolouring

The shared five-triangle core does not justify a fixed boundary-collapse
transfer from D0092 to D0063. Three explicit source colourings exclude all
220 choices of source seam, target rotation and reflection. Each failure
has a short forced-colour explanation and an independent exhaustive check
of the seven target interior vertices. The
[Lean obstruction](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTriangleCollapseObstruction.lean)
certifies one fixed alignment: a genuine source colouring would leave a
target triangle with only two available colours.

Adaptive interior choices fare differently. The
[program audit](five-triangle-collapse-audit.json) enumerates all source
and target colourings with one vertex fixed to colour zero, giving 7,818
and 3,732 distinct edge traces. Every source trace has some successful
collapse and alignment. This assertion concerns interior extension only.

An explicit planar exterior exposes the missing coupling. For one source
colouring, there are 40 distinct proper collapsed traces. Six extend through
a decagon triangulated as a fan, and sixteen extend into D0063, but no trace
does both. The source colouring is held fixed in this test. The glued target
and fan themselves have 414 compatible traces outside this restricted set,
so the obstruction concerns the proposed transport choices, not colourability.

A coordinated recolouring resolves this particular obstruction. Keep one
fixed seam and the same fan exterior, and switch the complete two-vertex
component with colours zero and three in the glued source graph. The new
boundary extends into D0063 while agreeing with that exterior at every
retained vertex. The
[Lean witness](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTriangleJointChoice.lean)
checks the initial and final proper colourings, the complete component, the
exact fan adjacency on both interfaces and the common boundary colours.
The [seven-root audit](five-triangle-collapse-measurements.json) uses only
standard axioms and no configuration rank or repair table.

This is one compatible repair in a specified context. It proves no uniform
family reduction, arbitrary-exterior repair law or geometric coverage.
The next contract must coordinate the retained exterior Kempe components
with recolouring and seam selection. Separate existence of an interior
choice and an exterior choice is insufficient. No catalogue entry or
certificate dependency is removed by this test.

Replay `lake build kernelFiveTriangleCollapse` in the classical package,
and from the repository root run
`python3 tools/fourcolor/near-linear/audit_five_triangle_collapse.py`.
The [fixture](five-triangle-collapse-example.json) stores explicit colouring
witnesses and the one-step repair; its repair search is not replayed.

## A fixed seam can remain blocked through every Kempe history

The next context test rules out a stronger unconditional contract. Attach a
decagon fan to D0092, retaining ten ordered ports and bypassing source boundary
vertex 6. In the displayed colouring every pair of distinct colours has one
connected support. Every whole-component Kempe switch therefore only renames
colours globally. This remains true after any finite number of adaptive switches.

Both orientations of this seam leave target vertices 11, 12 and 14 of D0063
with only two available colours, although they form a triangle. The
[Lean theorem](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTriangleKempeTrap.lean)
proves failure for the existing physical Kempe closure and proof-relevant GSLT
histories. The general
[palette invariant](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/KempePaletteRigidity.lean)
uses six connected pair supports; it does not enumerate recolouring histories.
A different source colouring reconstructs in the very same fan exterior, also
checked in Lean. The obstruction is thus to repair of a prescribed choice while
retaining this seam, not to the existence of compatible colourings.

The [exact program audit](five-triangle-kempe-trap-audit.json) independently
checks a spherical rotation with 18 vertices, 48 edges and 32 triangular faces,
preserving the source core's cyclic stars. The embedding check is not a Lean
planarity theorem. The sphere has a degree-three vertex: this example does not
refute a contract with stronger minimal-counterexample hypotheses. Alternative
seams, rollback and different reductions remain available mechanisms to test.

The [eight-root dependency audit](five-triangle-kempe-trap-measurements.json)
uses only standard axioms and no configuration repair table. No coverage entry
or original certificate dependency is removed. Replay
`lake build kernelFiveTriangleKempeTrap` and
`python3 tools/fourcolor/near-linear/audit_five_triangle_kempe_trap.py`.
The [fixture](five-triangle-kempe-trap-example.json) contains six short walks
and explicit colourings, rather than a table of search histories.

## Removing the old interior permits a uniform fan repair

The whole-source obstruction above does not obstruct the exterior repair
contract used by the reduction machinery. That contract permits the old
interior to be removed before recolouring. Retaining its colouring throughout
would impose an additional restriction.

The [ordered-fan theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OrderedFanKempe.lean)
proves that any two proper colourings of a fan of any finite length are joined
by genuine Kempe switches. It works for any palette admitting those two
colourings. Align the hub colour, then align successive path vertices by
swapping two colours on a suffix. The hub and the already aligned predecessor
use neither swapped colour. The existing partial-transposition theorem
decomposes each suffix operation into switches of whole connected components.
The resulting witness is a GSLT history; no table of colouring states is used.

The [concrete consumer](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTrianglePuncturedRepair.lean)
identifies the ten retained vertices of the trapped example with the exact
induced fan, including every edge between them. Every proper exterior state
can reach one explicit boundary colouring which reconstructs both the original
source and the target patch. In particular, the previously trapped state can
be repaired on this exterior. Lean also proves that no history keeping the
whole old source can reach that same boundary endpoint. The source has a
degree-three vertex, so it does not satisfy minimum-degree-five hypotheses.

This proves one law for all fan lengths and supplies an actual patch consumer.
It does not extend the law to arbitrary planar exteriors, prove that the
coverage argument supplies fan exteriors, or remove a catalogue dependency.
The concrete reduction retains ten of eighteen vertices; the all-length
theorem concerns recolouring, not an all-length family of patch reductions.
No bound on extracted execution time is claimed.

The [eight-root audit and replay measurements](five-triangle-punctured-measurements.json)
use only standard axioms, with no classical Four Colour theorem or configuration
repair table. The generic proof built in 2.7 seconds; the concrete consumer
replayed in 4.049 seconds and its audit in 3.461 seconds. These are module
measurements, not savings in the complete classical proof. Replay
`lake build Mettapedia.GraphTheory.FourColor.OrderedFanKempe` in the main package
and `lake build kernelFiveTrianglePuncturedRepair` in the classical package.

## Current pair partitions are insufficient for repeated updates

The [boundary observation theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/KempeBoundaryObservation.lean)
separates two requirements for a compressed exterior state. On every graph,
the current boundary colours and all current bichromatic connectivity
relations determine the boundary colours after one rooted Kempe switch.
They do not determine the new connectivity relations needed for later moves.

A four-cycle with three retained ports proves the distinction:

```text
port 0: colour 0 ----- port 1: colour 1
       |                     |
hidden: colour 1 or 3 -- port 2: colour 2
```

Both choices at the hidden vertex are proper and give the same observed
boundary word and all six pair partitions. In each state, the component of
colours 0 and 2 rooted at port 0 is a singleton. Switch it. Both boundary
words become `(2,1,2)`, but the colour-2 ports are connected through colours
2 and 3 precisely when the hidden vertex has colour 3. Consequently no
function of the old summary computes the full new summary for this operation.
A second switch, using colours 2 and 3 at port 0, yields boundary words
`(3,1,2)` and `(3,1,3)`. Lean also rules out computing the boundary word after
these two commands from the initial summary. The proof consumes the existing
GSLT non-factorization criterion.

This is an obstruction to deterministic updating of this particular summary.
It is not an impossibility of compositional repair. The same module certifies
an invisible interior switch joining the two initial states and a two-step
physical history producing the other outcome. A relational summary may retain
both possibilities, but concatenating its transitions requires compatible
concrete witnesses or a proved preparation/lifting law. Existentially choosing
a different hidden witness at each step does not establish such a law.

The [spherical replay](flat-seven-observation-audit.json) finds the same failure
on the complete 155-vertex punctured exteriors of both existing flat-seven
fixtures, with 11 and 10 ports respectively. It checks four actual proper
colourings, the hidden component and both boundary-rooted component switches
in each exterior. Before the switches, all six boundary partitions agree;
afterwards the words still agree and two pair partitions differ. A further
common boundary command produces different boundary words in each example.
The ambient spheres have degrees 5 through 7, three marked flat centres, and no obstructing
short cycles under the existing test. Flatness of an entire surrounding ball
and minimal-counterexample hypotheses are not asserted. These geometric
applications are exact program evidence; the general four-cycle obstruction
is separately kernel checked.

Replay `lake build Mettapedia.GraphTheory.FourColor.KempeBoundaryObservationAudit`
in the main package and
`python3 tools/fourcolor/near-linear/audit_boundary_observation.py` from the
repository root. The [measurement receipt](boundary-observation-measurements.json)
records the eight-root audit and build costs. The
[fixture](flat-seven-observation-example.json) stores one initial exterior
colouring and two rooted commands per case. The shared boundary command is
executed in both states. No table of possible histories is stored. No coverage
entry or original certificate dependency is removed.

## Exact independent elimination with joint repair choices

The [independent lifting theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/IndependentLift.lean)
provides a positive alternative to deterministic partition updates. Let `S`
be any finite independent set of hidden vertices in a finite graph, with an
arbitrary colour palette. The retained graph and hidden degrees are unrestricted.
Its interface consists of the retained graph and the joint constraints

```text
for every hidden vertex v:
    some colour is absent from all retained neighbours of v.
```

These constraints characterize extension exactly. A joint operation may switch
any union of components of one colour pair, provided its target still satisfies
all the constraints. Every such history lifts to an actual Kempe history
between the specified full endpoints. Conversely, every actual history projects
to such a joint history. A designated retained boundary can stay fixed through
every physical move. The proof prepares hidden colours, decomposes a proper
partial transposition into actual components, then finishes the hidden colours.
It uses the existing fibration and path-composition theorems. No table of
colouring states or histories occurs in the proof.

The [certified consumers](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/IndependentBoundaryRepair.lean)
include the preceding four-cycle example and a five-vertex star. In the star,
the hidden hub sees leaf colours `(1,1,2,3)`. Changing either first leaf alone
to `0` leaves no colour for the hub. Changing both together to `0` is valid:
the hub changes from `0` to `1`, while the last two leaves stay fixed. Lean
proves both individual extension failures and the joint physical repair.
Thus requiring every retained component to move separately is too restrictive.

The [spherical consumers](independent-repair-audit.json) replay this mechanism
on the two complete punctured exteriors. Each eliminates 33 independent
vertices from a 155-vertex exterior, retaining 122 vertices and 33 availability
constraints of widths 5 through 7. Both starting boundary words fail to extend
to their seven-vertex patches. Two joint operations per example reach words
that reconstruct proper colourings of the entire 162-vertex ambient sphere.
All preparation, component switching, finishing, and final ambient edges are
checked. In the D0092 second operation all 18 selected retained components
have invalid targets individually; the joint target is valid. In the D0063
second operation the same holds for all 28 selected components. Each joint
operation in these fixtures lifts to one full-exterior component switch.
The fixtures store only the initial colouring, the hidden set and two commands.
These geometric applications remain independent program evidence; the generic
law and the four-cycle/star consumers are kernel checked.

This is elimination into a graph **with retained constraints**. It is not a
standalone ordinary Four Colour reduction, and it does not prove all starting
colourings of these exteriors repair. Iterating elimination requires preserving
the accumulated constraints; closure in a compact family is not established.
No catalogue entry or original configuration certificate is removed. The
[measurement receipt](independent-repair-measurements.json) distinguishes these
claims and records the audit and costs.

Replay `lake build Mettapedia.GraphTheory.FourColor.IndependentBoundaryRepairAudit`
in the main package and
`python3 tools/fourcolor/near-linear/audit_independent_repair.py` from the
repository root.

## Adjacent interiors: extension and step lifting separate

The [two-vertex fibre theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/TwoVertexFibre.lean)
proves that any two proper colourings of a finite graph agreeing outside two
vertices are connected by Kempe switches avoiding that exterior. The palette
and degrees are unrestricted; the two hidden vertices may be adjacent.
Either one vertex can be recoloured first, or a two-colour interchange repairs
both. This is a uniform proof without a colouring-state table.

Nevertheless, [an exact nine-vertex example](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/AdjacentHiddenObstruction.lean)
shows that connected fibres and extendable targets do not suffice for lifting
moves between different retained colourings. Its core is the triangle `0,1,2`,
with leaves `3,6` at `0`, `4,7` at `1`, and `5,8` at `2`. Hide `0,1` and protect
all six leaves. Both full colourings

```text
vertex:   0 1 2 | 3 4 5 6 7 8
initial:  0 2 1 | 1 0 2 3 3 3
target:   2 1 0 | 1 0 2 3 3 3
```

are proper. In the retained graph, switching colours `0,1` at vertex `2`
produces the target restriction in one component move. Yet every nontrivial
full component at the initial state touches a protected leaf. Consequently
**no history fixing that context reaches any extension of the target**.
Lean proves this by a local transparency invariant and induction on arbitrary
histories. The results refute both single-component and joint-operation
on-image lifting without the independent-set hypothesis.

The same example has a precise repair. Permit only leaf `3` to change
temporarily and switch these actual full components in sequence:

| Colour pair | Component vertices | Colour at leaf 3 afterward |
| --- | --- | --- |
| `0,1` | `2,0,3` | `0` |
| `0,2` | `3` | `2` |
| `1,2` | `1,0,3` | `1` |

This reaches the stated target and restores the entire boundary. The other
five leaves remain fixed throughout. Saturated path witnesses certify all
three physical components; the repair also yields a GSLT history.

Thus repeated elimination needs control of allowed transitions as well as
endpoint extension. Temporarily changing a context vertex must itself be
justified when the patch is placed in a larger graph. The example has
degree-one leaves; it does not establish an obstruction in the stronger
minimal-counterexample geometry, rule out alternative decompositions, or
prove compact compositional Four Colour proofs impossible. No coverage entry
or original certificate dependency is removed.

Replay `lake build Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstructionAudit`.
The [measurement receipt](adjacent-hidden-measurements.json) records eleven
audited roots and costs. No external configuration certificate is used.

## Unbounded cooperation with one uniform repair proof

The [boundary-cooperation family](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryCooperation.lean)
replaces each of the preceding six leaves by `r` copies, keeping the same
triangle. It has `3 + 6r` vertices. The reduced command still hides only two
adjacent corners and changes the third by one component switch. Both full
endpoint colourings exist and agree on every boundary leaf.

Lean proves an exact cost for the surrounding cooperation:

```text
fewer than r boundary vertices may change  →  the core cannot move
all r copies of the first leaf may change  →  a physical repair exists
                                             and restores every boundary colour
```

The lower bound uses one untouched representative from each leaf group.
They recover the frozen nine-vertex obstruction. The new general
[history projection theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/HomProjection.lean)
shows that a physical history pulls back along any graph homomorphism from a
finite observing graph, with the protected context pulled back as well.
A full component may split, so one full step becomes a sequence of smaller
component switches. This proves the lower bound for arbitrary histories,
including temporary changes to unprotected leaves.

The matching repair has three uniform partial-transposition phases: switch
the first colour pair through the core and first leaf group, recolour that
leaf group, then switch the second core pair. The middle phase decomposes
into separate physical components. No colouring-state or history table is
used, and all widths produce actual GSLT histories. This disproves a constant
bound on the number of cooperating boundary vertices for this contract while
providing a short proof for the entire family. It is not a lower bound on
proof length, interface description size, or the number of structural laws.

The leaves have degree one and core degrees grow with `r`. These examples do
not establish an obstruction under the stronger geometric hypotheses of the
coverage argument. Nor do these repair histories establish a strict graph
reduction or geometric supply theorem. The surrounding graph must permit
any temporary boundary changes. Coverage and certificate counts are unchanged.

Replay `lake build Mettapedia.GraphTheory.FourColor.BoundaryCooperationAudit`.
The [measurement receipt](boundary-cooperation-measurements.json) records the
uniform statements, dependency audit, and verification costs.

## Frozen observers in the actual spherical exteriors

The [frozen-observer theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/FrozenBoundaryObserver.lean)
transports the obstruction into an arbitrary finite graph through a graph
homomorphism and a permutation of the four colour labels. The observer's
leaves need not be leaves of the ambient graph. Injectivity and inducedness
are unnecessary: proper colourings and physical histories pull back along
the homomorphism. Protecting the images of its boundary therefore freezes
the observed core throughout every possible history.

The [independent replay](frozen-observer-audit.json) checks two concrete
applications on the complete 155-vertex punctured exteriors of the existing
162-vertex spherical fixtures. The ambient degrees are five through seven.
Each operation hides two adjacent exterior vertices off the original patch
ports, switches one actual retained component, and has a proper extension
over those two vertices.

| Original patch | Retained component size | Original patch ports changed | Ambient degrees at the observer core |
| --- | --- | --- | --- |
| D0092 | 17 | 4 | `5,5,7` |
| D0063 | 5 | 1 | `5,7,6` |

In both cases the nine observer vertices map to eight distinct exterior
vertices; two observer leaves have the same image. All nine observer edges,
the complete initial colour pattern, the protected boundary images, both
proper exterior endpoints, and the changed observed core are checked. Thus
the target cannot be reached while keeping every unchanged retained vertex
fixed. The replay checks the premises of the universal Lean theorem and
requires no search through recolouring histories. The actual geometric
applications remain program evidence; they are not kernel-certified graph
instances.

Extension over the newly hidden pair is a different obligation from restoring
the original seven-vertex patch. Both selected target words still fail the
latter test. These witnesses refute endpoint-only acceptance of a proposed
fixed-context step; they do not refute the existence of successful choices.
The earlier two-step independent-set repairs still colour both complete
spheres. Whole-ball flatness and minimal-counterexample hypotheses are not
asserted, and no coverage entry is removed.

Replay `lake build Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserverAudit`
and `python3 tools/fourcolor/near-linear/audit_frozen_observer.py`.
The [fixture](frozen-observer-example.json) pins the existing source colourings
and stores only the observer map and reduced command. The
[measurement receipt](frozen-observer-measurements.json) separates the five-root
kernel audit from the concrete program checks.

## Exact guarded repair across an interacting hidden pair

[GuardedLift](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/GuardedLift.lean)
repairs the failed endpoint-only contract. For hidden adjacent vertices `u,v`,
let `A_u(C)` and `A_v(C)` be the colours absent from their retained neighbours
in colouring `C`. For a proposed retained partial transposition `σ`, the guard
asks for colours `x,y` before and `x',y'` after such that

```text
x ∈ A_u(C),  y ∈ A_v(C),  x ≠ y
x' ∈ A_u(D), y' ∈ A_v(D), x' ≠ y'
x' = x or σ(x);  y' = y or σ(y).
```

These are local colour conditions, not a hypothesis about an unknown repair
history. The kernel theorem proves that guarded histories are equivalent to
physical Kempe histories for every finite graph, every palette, and every
choice of two hidden vertices. The proof prepares the hidden colours, realizes
a proper partial transposition as actual component switches, and finishes at
the requested extension. The proved two-vertex fibre theorem ensures that
successive witnesses compose.

The general construction applies to larger hidden sets only when the
corresponding fibre-connectivity hypothesis is separately proved. Subsequent
elimination must preserve the generated transition guards; a constrained
interface cannot be silently treated as an ordinary graph.

[GuardedBoundaryRepair](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/GuardedBoundaryRepair.lean)
certifies that the nine-vertex obstruction has neither a guarded step nor a
guarded history with its boundary fixed. Its three-switch repair still passes
through the same interface when the cooperating leaf may temporarily move.

The [concrete replay](transition-guard-audit.json) checks both spherical
exteriors again. It rejects each frozen-observer command and reconstructs
the two successful physical switches that restore the original patch in each
162-vertex sphere. The hidden pair's guard observes six retained neighbours
in D0092 and eight in D0063. Deleting the hidden edge makes both bad commands
pass: independent marginal choices lose exactly the relevant constraint.

The four-colour program checks at most 16 before assignments and four after
choices for each one, with no search through histories. The actual geometry
and reconstruction instances remain program evidence. This result establishes
a faithful interface contract, not a new coverage theorem or a smaller
unavoidable set; no catalogue or certificate saving is credited.

Replay `lake build Mettapedia.GraphTheory.FourColor.GuardedBoundaryRepairAudit`
and `python3 tools/fourcolor/near-linear/audit_transition_guard.py`.
The [measurement receipt](transition-guard-measurements.json) records the
universal theorem and the separate finite applications.

## Existing certified components

The [constructive recognition receipt](seven-pair-recognition-measurements.json)
records a rooted construction of the same shared seven-pair sector.
One actual edge, triangle attachments and a general degree-closing theorem
supply all 31 facial correspondences. The actual consumer takes only the
retained degree test and the surrounding pair hypotheses.

The [independent replay](audit_seven_pair_recognition.py) checks all fourteen
degree-seven rooted edges in each of two triangulated spheres. It recovers
the existing 32-vertex sector and tests retained label identifications on
a nine-vertex bipyramid. These are program checks, separate from the Lean
proof and from the unresolved degree-profile supply theorem. Replay
`lake build kernelSevenPairRecognition`. No catalogue entry, rank certificate
or classical member check is removed by this recognition bridge.

The [seven-pair sector receipt](seven-pair-sector-measurements.json) records
an actual geometric continuation. A shared facial chart with fifteen fixed
degrees forces positive charge if its three marked outer vertices are low.
Consequently, flatness forces a high vertex at one of those same positions.
The minimal-map consumer distinguishes it from both selected centres and
retains its radius-two support, or radius five from the original fan receiver.
Six other chart degrees are unrestricted. The theorem does not assume
that distant chart labels are distinct, and does not assert that the new
vertex differs from every other retained high vertex.

The proof checks 83 outgoing-rule exclusions and eleven incoming-rule maps;
these finite geometric checks remain in its dependency graph. The final
extra unit follows by a shared five/six boundary-degree argument. No
configuration certificate or complete Four Colour theorem is used. The
classification that supplies this profile remains open, and the classical
coverage count is unchanged. Replay `lake build kernelSevenPairSectorData`,
then `lake build kernelSevenPairSector`. The independent input audit is
`python3 tools/fourcolor/near-linear/audit_seven_pair_sector.py`.

The [complete wheel-family receipt](wheel-family-measurements.json) records
kernel certification of every D3009 repair state and input trace. A shared
action checker validates each recolouring once while retaining each
exterior pairing's joint compatibility. The existing boundary-collapse law
then supplies all six ordered two-five variants without new repair tables.
The actual-map consumer proves strict reconstruction and supplies the next
adjacent-seven pair from a shared fan. Broader geometric coverage remains
open; no classical coverage entry is removed by this result.

The [four-triangle geometry](four-triangle-measurements.json) shares one
injectivity and inducedness proof between the distinct D0051 fan and D0052
tripod cores. Both full source files, degree profiles and core facial
intervals are checked; the actual minimal-map consumer is kernel certified.
The [complete source and repair bridge](four-triangle-repair-measurements.json)
now identifies the full ten-port patches with classical configurations 33
and 37, including opposite orientation conventions. One rank-coverage
theorem consumes their existing certificates and supplies full proper-domain
repair. A supplied complete occurrence yields actual strict two-vertex
descent and compatible ambient reconstruction; different boundary labels
may coincide. The [joint boundary completion](facial-boundary-measurements.json)
now derives all source edges and complete positive core stars from four
facial triangles and six degrees. Both complete occurrences and actual
strict reconstruction are connected. A proved reflection of the tripod's
full source aligns its positive geometric completion with its reversed
classical repair. The joint coverage classification remains open. No original
certificate dependency or coverage entry is removed.

The same parameterized seam theorem now serves both earlier three-triangle
chains and both four-triangle layouts. Owners read each exterior port once;
the across-edge triangle law proves agreement at every closing seam. This
retains the joint boundary, while allowing distinct exterior labels to
coincide. Replay `lake build kernelFacialBoundary`, then the migrated
consumers with `lake build kernelChainRecognition` and
`lake build kernelExtendedChain`.
Replay `lake build kernelFourTriangleRepair kernelFourTriangleGeometry`.
Replay the source audit with
`python3 tools/fourcolor/near-linear/audit_four_triangle_sources.py`.

The [shared-fan tripod receipt](rule-fan-tripod-measurements.json) connects
this repair to the actual six-star `[receiver, 5, 5, a, b, 5]`.
For either placement of degrees seven and six at `a,b`, a degree-five
outer tip across `a–b` supplies the tripod. In a minimal counterexample
with a unique high neighbour `q` at the seven, the remaining tip must
have degree six or be exactly `q`. Its identity and radius-three support
are retained. Other free-degree profiles and these two surviving seam
cases still need joint classification. Replay `lake build kernelRuleFanTripod`.
The independent [geometry test](rule-fan-tripod-audit.json) finds both
placements after 83 and 103 legal flips of the existing spherical fixture;
it checks all source core edges, corners and ambient degrees. It does
not assert the full flat-neighbourhood hypothesis. Replay with
`python3 tools/fourcolor/near-linear/audit_rule_fan_tripod.py`.

The [exact high-boundary receipt](punctured-charge-measurements.json)
extends the cyclic rule formula to a high receiver with high neighbours.
Low-edge contributions retain the actual adjacent degree guards; all high
transfers remain signed boundary observations. For the actual retained
flat-seven pair, the first low budget plus its unique high-edge input is
ten. With no other high neighbours at either end, the two low budgets sum
to twenty by cancellation of that same edge. The second centre's additional
high neighbours otherwise remain explicit. The same local rule equivalence
turns a `5–6–6–5` rim segment into the three tripod matches whenever the
intermediate outer tip has degree five, excluding this tip in a minimal map.
Replay `lake build kernelExactCyclicCharge` first, then
`lake build kernelPuncturedCharge`. The concrete Lean instances keep their
exact executable sums symbolic; their numerical values are program evidence.

The [finite boundary audit](punctured-charge-audit.json) compares two source
matchers on 235 low-to-high edges at 47 receivers. In its retained flat
pair, the first low budget is twelve and it exports two units to the second;
the second low budget is nine and it exports one further unit to another
high vertex. Thus the combined low budget is twenty-one, with external
boundary contribution minus one. Only the selected pair is asserted flat;
this fixture does not satisfy the full original flat-ball hypothesis.
Replay `python3 tools/fourcolor/near-linear/audit_punctured_charge.py`.
This establishes exact accounting and a local forbidden pattern, leaving
joint geometric classification and catalogue compression open.

The [joint-rule receipt](joint-tripod-rules-measurements.json) records a
second recognition law: `002_1` and `003_1` on one six-to-seven dart,
together with `002_2` on its rotation-determined adjacent dart, force the
tripod when the adjacent sender has degree six. Their joint contribution
is therefore at most two in a minimal map. The proof constructs the core
from the shared source readings and consumes the complete boundary and
strict reconstruction theorem. Replay `lake build kernelJointTripodRules`.
The [independent replay](joint-tripod-rules-audit.json) exhibits these
matches in the existing sphere. It checks that the shared-fan sender and
both retained seven-centres are flat, while the original receiver has
charge `+3`. Three flat observations do not establish a flat radius-three
ball. Replay `python3 tools/fourcolor/near-linear/audit_joint_tripod_rules.py`.
No new repair table, removed certificate dependency or coverage saving
is claimed. The next classification must retain the forbidden triple
as a joint constraint on actual adjacent readings.

The [seven-pair example](seven-pair-four-triangle-example.json) explains the
choice of these cores. It is a 162-vertex sphere obtained by 1,625 legal
edge flips. Independent matchers agree on all 4,704 rooted rule tests for
the two flat seven-valent centres in both orientations. All 1,819 short
cycles pass the obstruction test. There is no tested diamond, D0004/D0006
chain or one/two-five seven-wheel core in the union of their radius-three
balls. An injective D0052 core occurs within radius two, and D0051 within
radius three. Their complete source images need radii three and four,
respectively. This is a program check of a restricted family inventory,
not a counterexample to universal reducibility or to the stronger
shared-fan/flat-neighbourhood hypotheses. Replay it with
`python3 tools/fourcolor/near-linear/audit_seven_pair_example.py`; see the
[receipt](seven-pair-four-triangle-audit.json).

The [second-fan classification](second-fan-measurements.json) retains the
other side of the same six-star: a flat seven either supplies a new high
neighbour, has the single-five D3009 profile, or has exactly two fives with
one outer five-tip and zero extra charge. The classification is checked
without a repair hypothesis; a separate consumer excludes the single-five
branch using the explicit D3009 repair contract. The
[two-five experiment](two-five-wheel-probe.json) checks all three separations
on the seven-rim wheel. Each closes all 22,144 boundary states in Python;
no new Lean repair or coverage saving follows from that experiment alone.
Replay it with `python3 tools/fourcolor/near-linear/probe_wheel_repair.py --two-fives`.

The [three-triangle chain](../../../lean/fourcolor-classical/MettapediaFourColor/NearLinearChainRepair.lean)
now has a shared repair: `D0006` is exactly classical configuration 7, and
`D0004` inherits its repair through one boundary-triangle subdivision. The
source bridge checks all adjacencies, cyclic stars, degrees and ordered ports.
No separate repair table is introduced for `D0004`.

This target comes from a [whole-neighbourhood example](chain-profile-example.json),
not solely a catalogue shape match. A finite program check finds adjacent
flat centres of degrees eight and seven, with all other neighbours of the
eight-centre of degree at most six. It checks all 461 simple cycles of lengths
three through five and finds no obstructing cycle. Neither of the mixed and
pentagonal diamond cores occurs in the union of the two radius-two balls.
The five-vertex `D0004` interior does occur. Lean verifies its thirteen distinct
source vertices and complete oriented core stars, and consumes its repair in
actual graph reconstruction with explicit exterior-closure and initial-colouring
hypotheses. A subsequent
[actual reduction](../../../lean/fourcolor-classical/MettapediaFourColor/ActualChainReduction.lean)
derives those witnesses from vertex minimality and the actual planar exterior.
Its geometric occurrence contract requires the five complete core stars,
their degrees, distinct core vertices and boundary images outside the core;
boundary images need not be distinct from each other. The example supplies
this contract and a cyclic triangular rotation in Lean. The flatness,
global planarity and short-cycle checks remain program evidence.

Replay source fidelity and the example from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_chain_sources.py
python3 tools/fourcolor/near-linear/audit_chain_profile.py
```

The package gates are `lake build kernelNearLinearChain kernelChainReduction`. The
[receipt](chain-measurements.json) separates local repair, concrete occurrence,
and conditional reconstruction. The
[actual-reduction receipt](chain-reduction-measurements.json) closes the
initial-colouring and exterior bridge through an existing strict two-vertex
reduction. General occurrence recognition and coverage remain open. The
[source pins](chain-sources.json) retain upstream attribution and the MIT licence.
This step removes no entry or certificate dependency from the complete assembly.


The [rerooted reduction](../../../lean/fourcolor-classical/README.md#changing-the-reduction-edge-removes-a-residual-branch)
now excludes the degree-five second sender in the actual minimal-map
domain. A different edge of the same rule reading exposes the existing
mixed diamond and its strict replacement. This removes one local branch;
the [measurements](rule-pair-residual-measurements.json) retain the unchanged
global coverage and certificate counts.

The latest [paired rule budget](../../../lean/fourcolor-classical/README.md#a-paired-budget-retains-both-sender-choices)
retains both sender degrees, proves the two incoming edges distinct, and
bounds their joint net supply by seven or eight units from below. At a flat
degree-eight receiver the remaining net supply is at most thirteen. The
[measurement record](rule-pair-budget-measurements.json) separates its general
proof, minimal-map consumer, finite instances and open coverage obligations.

The configuration files are unmodified inputs from
[near-linear-4ct/reducible-configurations](https://github.com/near-linear-4ct/reducible-configurations),
pinned to `c2ce7a96e35256201526e2abb51a39d04a588b53`.
Their MIT notice is retained in [LICENSE](LICENSE); [sources.json](sources.json)
and [five-sources.json](five-sources.json) record the individual hashes. The associated paper is
[The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring](https://arxiv.org/abs/2603.24880).

The Lean bridge identifies `D0000` and `D0001` with the existing diamond
configurations 1 and 2. It checks all source rows, complete adjacency,
prescribed internal degrees, every cyclic neighbour list and ordered boundary
alignment. A boundary-triangle insertion between the two source presentations
commutes with the existing reference insertion. Their repair laws reuse the
shared profile certificate and the general boundary-split theorem.

The repair conclusion produces an actual graph colouring compatible with any
supplied Kempe-closed exterior trace relation containing the initial proper
trace. The second entry's repaired witness also has a compatible GSLT insertion
history. This history records construction choices; it does not compute the
exterior Kempe recolourings.

From the repository root, source fidelity can be replayed with:

```sh
python3 tools/fourcolor/near-linear/audit_diamond_sources.py
```

From `lean/fourcolor-classical`, the kernel and dependency audit is:

```sh
lake build MettapediaFourColor.NearLinearDiamondAudit
```

The audit covers 23 roots and excludes all original configuration certificates
and complete Four Colour endpoints. The shared finite profile is retained.
See [diamond-source-audit.json](diamond-source-audit.json) and
[diamond-measurements.json](diamond-measurements.json).

These two entries were already covered by the existing mathematics. The bridge
adds no catalogue compression credit and changes neither the 633 coverage
entries nor the 629 original certificate dependencies in the complete assembly.
It does not verify the rest of the new catalogue, its geometric supply theorem,
its simultaneous repairs or its near-linear running time.

## A five-entry repair family

One retained classical certificate now supplies the repair contracts for five
entries from the repeated nine-vertex core. Arrows below transfer repair:

```text
           D0604 = classical configuration 225
              /           |           \
           D0464        D0465        D3202
              \           /
                  D0370
```

The actual graph construction runs in the opposite direction. Each step
inserts a vertex in a boundary triangle, replacing one boundary edge by two
edges while retaining their joint colouring relation. The general theorem
`BoundaryTriangleRepair.repair` restricts a repaired upper colouring to a
proper colouring of the lower graph. It applies to any graph and boundary
tail satisfying its repair premise; the five catalogue instances check the
complete graph isomorphisms, cyclic neighbour orders and ordered boundaries.
The five source inputs and prescribed internal degrees are checked separately.

`NearLinearFiveBase.reference_repair` proves that the existing configuration-225
rank certificate covers the whole proper fourteen-port domain after colour
permutations. This retains that finite certificate and adds one kernel-checked
mask comparison. `NearLinearFiveRepair` then supplies all five repair contracts
using the same split-and-reconstruction law. No independent rank certificate
is needed for the four lower entries. Their rings have lengths 12 and 13;
the upper ring has length 14.

`NearLinearFiveGSLT.coloring_square` proves that both insertion orders from
`D0370` to `D0604` produce the same complete colouring, including both newly
inserted vertices. `compatible_histories` starts with one actual repaired
`D0370` witness and supplies both GSLT histories with that common endpoint.
This is commutation for a fixed starting colouring; it does not equate the
results of independent Kempe repairs or extract exterior Kempe moves.

Replay source fidelity from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_five_sources.py
```

With the audited reference artifacts and configuration-family dependencies
prepared as in the [package guide](../../../lean/fourcolor-classical/README.md),
run from `lean/fourcolor-classical`:

```sh
lake build kernelNearLinearFamily
```

The six-module replay includes `NearLinearFiveAudit`. It excludes all complete
Four Colour endpoints and every original rank certificate except configuration
225. See [five-source-audit.json](five-source-audit.json) and
[five-measurements.json](five-measurements.json) for exact hashes and costs.

This is shared local repair reasoning for a finite five-entry family. It
changes neither the 633 coverage entries nor the 629 original certificate
dependencies of the complete classical assembly. The geometric occurrence,
strict smaller-map construction and reconstruction against an actual exterior
remain to be connected for this family. Recognition, coverage, coordinated
batch repairs and the newer algorithm's running time are separate obligations.

## Recognizing a diamond through an overlap

`OverlappingPentagonalSectors` isolates the cyclic mechanism suggested by
[Figure 11](https://arxiv.org/html/2603.24880v1#S8.F11). In the dual cubic map,
two views anchored at an actual edge read the same pentagonal face from
consecutive boundary darts. Its neighbouring faces have cyclic positions

```text
first centre -> second centre -> B -> D -> A -> first centre
```

One view reads `A` and `D` backwards; the other reads `B` and `D` forwards.
Five-step closure proves that the two readings of `D` are the same dart,
so every observation of it agrees. If `A`, `B` and `D` are pentagonal too,
the shared face and these three neighbours supply the existing diamond
occurrence. The two centre-face lengths and the rest of the graph are
unrestricted. The corresponding positions differ on a six-cycle; the
pentagonal hypothesis has mathematical content.

The theorem `strict_reduction` consumes the existing geometric recognition
and joint diamond repair. In a connected bridgeless spherical cubic map
with minimum face length five, cyclic edge connectivity at least five and
two-sided faces, it replaces twelve vertices by four, preserves the smaller
map's class, and reconstructs a source colouring from a smaller colouring.
`not_in_minimal` derives the ambient conditions from minimality.

This is a local recognition law for an already proved reduction, with no
new rank certificate. It is not a decoding of the complete Figure 11
cartwheels, a classification of degree-eight zero-charge pairs, or a proof
that every such pair has these readings. The all-flat supply theorem still
requires that classification and its residual cases. No classical coverage
entry or complete-assembly certificate dependency is removed here.

With the existing geometric dependencies prepared, run from
`lean/fourcolor-classical`:

```sh
lake build kernelOverlapSupply
```

The dependency audit checks nine roots, requires the geometric reduction
consumer, and excludes complete colouring endpoints and original catalogue
rank certificates. The joint diamond profile certificate is still retained
by that consumer. See [overlap-measurements.json](overlap-measurements.json).

## Coverage assembly and remaining local obligations

The [formal coverage assembly](../../../lean/fourcolor-classical/README.md#conditional-flat-neighbourhood-coverage-assembly)
now separates the radius and case argument from the still-open geometric
classification. `LocalCoverageAssembly.radius_twelve` composes three local
supply laws, transporting one complete supported occurrence through every
change of centre. `eight_of_overlap` further decomposes the degree-eight law
into classification, a specified second centre in an exceptional occurrence,
and a joint closing argument for both occurrences.

The concrete consumer runs on the actual quotient-face dual and excludes
the already certified pentagonal-overlap outcome from a minimal
counterexample. Other outcomes remain explicit residual witnesses. The
charge input has not yet been identified with the full source discharging
calculation. The source exceptional pattern is now decoded as described
below, while its supply from flatness remains open. The proof does not
assume that every pair of flat cartwheels is a diamond.

The [obligation record](coverage-obligations.json) lists the exact open fields
and their source references. The [measurement record](coverage-measurements.json)
records the kernel replay and dependency audit. From the prepared classical
package, replay with `lake build kernelFlatCoverage`. No classical coverage
or certificate dependency is removed by this conditional assembly.

## The exceptional overlap and the D1774 core

The exact `getX` function from the pinned primary
[computer checks](https://github.com/near-linear-4ct/computer-checks/tree/6cb85666ce89cf8bd813132e4c5dd56053e367a5)
encodes Figure 12: seventeen vertices, cyclic neighbour lists with explicit
gaps, and prescribed degrees. The unaltered excerpt and `D1774.conf` are
retained with hashes in [exception-sources.json](exception-sources.json).
The shared [MIT notice](LICENSE) applies to both source repositories.

`ExceptionalPattern.Occurrence` reads that data into an actual simple graph
with a vertex rotation, preserving every listed edge, prescribed degree and
known cyclic step. Gaps impose no step. Vertex collisions are permitted at
this stage and remain an explicit geometric obligation.

The next-centre field is now proved for this source pattern. Source vertex
14 has degree eight and lies within two edges of vertex 0. If a second
exceptional occurrence is centred at that actual vertex, the cyclic word
around its centre forces the neighbour two positions before any degree-seven
neighbour to have degree five. The first occurrence fixes the intervening
dart. Triangular face closure supplies the additional edge, so the two
occurrences force the corner used in Figure 13.

```text
first exact X occurrence
        |
specified second degree-eight centre within distance two
        |
second X occurrence at that same vertex
        |
shared rotation forces the extra degree-five corner
        |
all 13 D1774 core edges and all 8 prescribed degrees
        |
full boundary occurrence and compatible repair [OPEN]
```

`ExceptionalCore.coreHom` transports all core edges; `core_degrees` proves
the prescribed ambient degrees. Their entire support lies within radius
three of the first centre. `JointReading` retains both source occurrences,
their alignment, and the core's exact realization, so their cyclic-order
information remains available for boundary reconstruction. All retained
observations, including the second source occurrence, lie within radius four;
the support used by the scaffold includes them all.
`overlap_supply` instantiates the existing
degree-eight scaffold with these joint readings: its next-centre and joint
core-reading fields are proved, while classification remains a hypothesis.
It does **not** instantiate the scaffold with certified reductions. The
results below supply the actual dual rotation, exclude core collisions and
prove inducedness in the minimal regime. Moving to the full eleven-port
occurrence still requires boundary completion with cyclic order and a
colouring-repair contract. Zero-charge classification and transport of the
published source observations remain open. No coverage or certificate
dependency is removed here.

Replay the independent source comparison and the Lean proof audit with:

```sh
python3 tools/fourcolor/near-linear/audit_exception_sources.py
```

From the prepared classical package:

```sh
lake build kernelExceptionalOverlap
```

See [exception-source-audit.json](exception-source-audit.json) and
[exception-measurements.json](exception-measurements.json). The dependency
audit excludes complete Four Colour endpoints and original catalogue rank
certificates; the source data are decoded and checked in Lean.


## Facial transport and the collision alternative

`ExceptionalCoreOrientation` checks all eighteen directed core corners
against the full pinned cyclic neighbour rows. Fifteen come directly from
the first exceptional occurrence. The remaining three follow from one
closing corner and the generic facial-triangle rotation law. No boundary
neighbours are removed before testing consecutive turns.

`ExceptionalCoreLocalInjectivity.corner_chain_injective` proves a uniform
rule: consecutive facial corners follow powers of the actual vertex
rotation, and a chain no longer than the ambient degree cannot repeat a
neighbour. Its source consumer proves local injectivity at every D1774 core
vertex, using the prescribed degrees forced by the joint occurrence.

`ExceptionalCoreCollision.source_core_alternative` now has two checked
outcomes for two actual exceptional occurrences aligned at the prescribed
second centre:

```text
actual aligned occurrences
        |
all core edges, degrees and facial corners
        |
local injectivity
        |
        +-- injective orientation-preserving core reading
        |
        +-- nonfacial triangle within radius two of the first centre
```

The finite collision partition leaves only four unordered pairs of core
vertices. Each closes an actual three-edge path. Three cases use the same
central edge: its two facial third vertices have degree eight, whereas the
collided endpoint has degree five. The fourth case uses adjacency to exclude
one facial third vertex and a degree mismatch to exclude the other. The
triangle carries an actual `SimpleGraph.Walk.IsCycle` proof of length three.
The retained source context is essential to these exclusions; the internal
core graph alone does not retain all the necessary observations.

The reusable laws concern facial transport, injective corner chains and
exclusion by the two flanking corners. The four-pair source check remains a
finite obligation. This is a concrete collision alternative, not a general
first-collision theorem for arbitrary patch programs.

No planarity assumption is needed for these laws. The next result supplies
the local-faciality corollary's geometric hypothesis in the actual dual of
a graph-backed minimal Tait counterexample, using an established separator
theorem. The injective branch still needs inducedness, eleven-port ring
completion and the repair contract.

Run `lake build kernelExceptionalEmbedding` with the prepared dependencies.
The source consumer's dependency audit requires both the constructed core
reading and the actual collision argument; it excludes complete Four Colour
endpoints and original catalogue rank certificates. See
[embedding-measurements.json](embedding-measurements.json).
Coverage and certificate counts remain 633 and 629, respectively.

## Collision elimination in the actual minimal dual

`ActualDualRotation` gives the quotient-face dual its actual dart rotation.
It reuses the primal darts, exchanges the vertex and face permutations, and
proves that unique shared edges yield a faithful simple-graph backing.
`MinimalExceptionalEmbedding.graph_eq_coverage_dual` identifies its adjacency
with the graph used by the coverage scaffold. Thus the geometry is not
attached to an unrelated triangulation with a similar graph.

The existing `GoertzelV24MinimalDualTriangleClassification` proves that a
dual triangle cuts off one primal vertex in a graph-backed vertex-minimal
Tait counterexample. This follows from cyclic five-edge-connectivity and
the actual three-edge separator, using the earlier small-cut reconstruction
theory. The new bridge proves that every face incident with an edge at that
cubic vertex is one of its three cyclic face readings. Those three readings
form a facial triangle in the actual dual rotation. Consequently every dual
triangle has one of the two facial orientations.

```text
two aligned actual exceptional occurrences
                  |
       exact core and retained turns
                  |
      injective OR nonfacial triangle
           |                |
           |        singleton-cut classification
           |                |
           |        actual triangle is facial
           |                |
           |          contradiction
           |
   injective eight-vertex core homomorphism
```

`MinimalExceptionalEmbedding.source_core_injective` is the checked source
consumer. It constructs the joint reading, uses the explicit collision
argument, and excludes the collision through the same actual rotation.
The theorem does not assume core injectivity or a full D1774 occurrence.
The uniform actual-dual and facial-triangle laws can be reused by other
patches; the present consumer still uses the D1774 four-pair collision check.
A general first-collision theorem for arbitrary construction programs remains
open.

This result assumes a graph-backed vertex-minimal Tait counterexample and
the two actual exceptional occurrences. The inducedness result below
excludes extra ambient core edges. Supply from the paper's final-charge
classification, the full eleven-port ring, colouring repair and strict
reduction remain open. No catalogue or certificate dependency is removed
from the complete assembly.

Run `lake build kernelExceptionalDual`. The twelve-root audit requires the
actual dual bridge, singleton separator and source collision theorem in the
dependency closure. It admits only `propext`, `Classical.choice` and
`Quot.sound`, and excludes complete Four Colour endpoints and original
catalogue rank certificates. See
[minimal-embedding-measurements.json](minimal-embedding-measurements.json).

## Induced core from facial intervals and short paths

The core has thirteen edges and fifteen distinct unordered nonedges.
Eleven nonedges join vertices with a common core neighbour. The remaining
four pairs have distance three. All eight core stars are consecutive
intervals strictly shorter than the prescribed ambient degree; each retains
at least one exterior neighbour.

`FacialPatchInduced.corner_chain_successor` proves the relevant general
rotation law. If `n` retained consecutive neighbours satisfy `n < degree`,
then a facial corner between retained entries can only join successive
indices. The strict inequality excludes a wraparound corner. Combined with
the actual minimal dual's triangle-faciality theorem, this rules out any
extra edge between two neighbours of a core vertex.

The second law, `FacialPatchInduced.reflects_of_short_paths`, is independent
of rotations and of the catalogue. Suppose an injective graph homomorphism
reflects adjacency between neighbours of each source vertex, all source
vertex pairs have a path of length at most three, and every ambient
four-cycle has a diagonal. Then the entire homomorphism reflects adjacency.
An extra edge across a three-edge source path closes a four-cycle; either
diagonal reduces the claim to the same local reflection law twice.

```text
retained proper neighbour intervals
             +
actual triangles are facial
             |
no extra edge across any two-step core path
             +
actual four-cycles have a diagonal
             |
no extra edge across any three-step core path
             +
kernel-checked core diameter at most three
             |
       exact induced core
```

`ExceptionalCoreInduced.four_cycle_chord` transports the existing minimal
dual four-cycle theorem through the exact adjacency bridge.
`ExceptionalCoreInduced.source_core_induced` consumes that geometry and the
same two aligned source occurrences used for injectivity. It establishes
the exact adjacency equivalence, rather than adding absence of extra edges
as a field. This is a special case of the inducedness task in the paper's
Lemmas 3.1 and 9.2; the source diameter-three fact avoids the five-cycle
case needed for diameter-four configurations.

The finite source checks retain the star bounds, consecutive source edges
and short-path witnesses. The new reusable laws are not a colouring-repair
theorem. The eleven-port completion and conditional reconstruction below
now preserve shared boundary choices and allow boundary identifications.
Compatible repair, strict reduction, final-charge classification and
coverage remain open; counts remain 633/629.

Run `lake build kernelExceptionalInduced`. The nine-root audit requires the
actual source construction and the triangle/four-cycle geometry. Only
standard axioms are allowed, and complete Four Colour endpoints and original
catalogue rank certificates are excluded. See
[induced-measurements.json](induced-measurements.json).

## Eleven-port completion and exact reconstruction

The source core's partial cyclic stars now extend to all eleven ring ports.
For an actual directed edge `d`, triangular closure proves

```text
second endpoint of predecessor(d)
                =
second endpoint of successor(reverse(d)).
```

This is `FacialStarCompletion.across_edge`. Combined with the exact degree
and retained core-star interval, it supplies each of the eight seams around
the core. There is one chosen reading for each ring label; the seam law
proves agreement with every other reading of that label. Two ring labels
occur in three core stars, so their agreement uses two applications of the
same law.

`ExceptionalBoundaryCompletion.row_agrees` identifies every full source
star entry with an actual rotation power. A kernel-checked source edge
classification then constructs a homomorphism of the complete nineteen-vertex
source graph, including the ring edges. The source labels and their order
are retained. `ExceptionalBoundaryOccurrence.full_turn` preserves all full
cyclic core-star steps; `star_covers` proves that every actual incident edge
has a source reading.

No assumption makes the boundary globally injective. The theorem
`ring_outside_core` uses induced core adjacency and injectivity of a full
vertex rotation to exclude capture of a core vertex by a ring label. It
allows distinct ring labels to denote the same exterior vertex.

The general theorem `PatchBoundaryGluing.reconstruct` applies to any graph
patch whose interior map is injective, whose boundary avoids the interior,
and whose incident-edge coverage is complete. Given an actual patch
colouring and an exterior assignment, proper off the interior, agreement
on the entire boundary reconstructs a colouring of the ambient graph while
fixing every exterior vertex.

Its actual consumer is `ExceptionalBoundaryReconstruction.reconstruct`.
The companion `extension_iff` gives the exact contract:

```text
proper exterior assignment extends to the ambient dual
                         iff
the source completion has a colouring with those same eleven observations.
```

The equality is about joint assignments, not independent port possibilities.
If ports have equal ambient images, the common exterior assignment enforces
the corresponding equality of colours. The theorem works for every colour
type and reconstructs a witness; it is not merely a numerical count.

The next obligation is to obtain such a compatible colouring, allowing
justified exterior Kempe changes. No repair rank, strict reduction or
zero-charge supply theorem is established by this equivalence. No global
boundary embedding or general collision theorem for all triangle programs
is asserted. Counts remain 633 coverage entries and 629 original catalogue
certificate dependencies.

Run `lake build kernelExceptionalBoundary`. The fourteen-root dependency
audit requires actual source construction, core injectivity, inducedness,
full incident-edge coverage and reconstruction. It allows only standard
axioms and excludes complete Four Colour endpoints and original catalogue
rank certificates. The source and object hashes, replay times and gate
results are in [boundary-measurements.json](boundary-measurements.json).

## Complete exceptional boundary repair

`ExceptionalRepairCertificate.repair` now proves repair for every proper
zero-sum eleven-port trace. The terminal relation consists of actual colourings
of the complete nineteen-vertex D1774 source. Each terminal witness is checked
against all forty-three edges, including the ring, and its entire ordered trace.

The certificate contains 7,381 trace representatives, including 1,383 terminal
ones. Every nonterminal record supplies a whole-chord mask for each possible
unsigned exterior skeleton. `KempeMaskCertificate.check_sound` proves that
these masks preserve the same signed exterior chromogram. The selected answer
has strictly smaller rank. `KempeIndexedCertificate.sound` performs the common
well-founded argument, quantifying over every Kempe-closed exterior predicate.
Records need not be uniquely identified by their traces.

```text
one proper boundary trace and its actual exterior witness
                         |
       choose complete chords in that same exterior
                         |
              strictly smaller repair rank
                         |
           genuine full source colouring
                         |
       align all ports by one colour translation
                         |
                  reconstruct the map
```

The complete check retains 93,665 unsigned-skeleton cases. It is a finite
repair certificate with a reusable checker and reconstruction law; no
case-free family theorem or catalogue removal is credited. The generator is
untrusted. Its output, all terminal colourings, all rank decreases and the
coverage of all proper inputs are checked by kernel reduction. The full
finite replay took 5,964 seconds; this is verification cost, not an algorithmic
colouring bound. A separate regeneration reproduced both generated files
byte for byte.

`GraphTraceAlignment.align` preserves the whole boundary assignment by one
Klein-group translation. `ExceptionalRepairReconstruction.reconstruct` uses
the earlier actual graph geometry and allows coincident ring images. It still
requires Kempe closure of the actual exterior relation and an initial proper
exterior trace. The finite certificate does not supply those geometric inputs.

Replay with `lake build kernelExceptionalRepair`; after the finite artifacts
are prepared, `kernelExceptionalRepairConsumer` checks alignment,
reconstruction and the twelve-root dependency audit separately. The audit
allows only standard axioms and excludes complete Four Colour endpoints and
original catalogue rank certificates. Counts remain 633 coverage entries and
629 original configuration certificate dependencies.

## Constructed source, local query and valid contraction

`ExceptionalConstruction.program` builds the complete D1774 source with nine
Y operations and eight H operations, interspersed with rotations. The
kernel comparison identifies all three permutations on its eighty-six darts.
The face presentation recovers every source edge, every cyclic star and the
ordered eleven-port ring. `ringTrace_iff` transports actual colouring witnesses
and their complete traces between the literal source and this construction.

The established Gonthier/Werner configuration compiler, as formalized by
Chris Emery, supplies embeddability. Its local recognition query is also
checked exactly. It observes degrees `5, 5, 8, 7, 5, 5, 5, 5` along a specified
branching walk. Matching this list at arbitrary vertices would not suffice:
the dart steps and common starting edge are part of the query.

`KempeRepairContract.reducible_of_repair` proves a general bridge: an
all-proper-trace repair law supplies the coclosure field of every valid
contract on the same perimeter. Its proof derives a proper boundary trace
from an actual contract colouring, using the contract's exclusion from the
ring. D1774 has a checked singleton contract on the edge joining source
vertices 13 and 14 (zero-based labels). Its two darts are off the ring and
lie on distinct nodes.

`ExceptionalConstructionRepair.not_fitted` now excludes a matching local
query in a reference minimal counterexample. The proof consumes the source
construction, exact trace transport, finite joint-chord repair and singleton
contract, then reuses the established query-to-preembedding, contraction,
exterior-closure and patch reconstruction theorems. It uses no complete
Four Colour endpoint or original catalogue rank certificate.

The matching query is now derived from the two actual exceptional occurrences,
as described below. A starting singleton contract colouring is also supplied
directly in the graph-backed minimality regime. The local consumer below now
also establishes exterior embedding and closure in that same domain, without
identifying the two minimality definitions. Zero-charge classification and
occurrence supply remain separate.

Replay with `lake build kernelExceptionalConstruction` after preparing the
finite repair artifacts. Its seventeen-root audit checks the representation,
query compiler and reconstruction dependencies. This establishes source
reducibility and reuse; it removes no coverage entry or existing certificate
dependency. See [construction-measurements.json](construction-measurements.json).

## Actual overlap recognition through compositional query moves

`DualGraphQuery` constructs the exact dual hypermap on the graph's actual darts.
Its face permutation is the given vertex rotation. The general `stepR` and
`stepL` theorems turn directed facial corners into the elementary recognition
moves. `arity_eq_degree` identifies each query observation with the full ambient
degree under vertexwise cyclicity.

`ExceptionalQueryReading.walk` composes those moves through the retained joint
core. The two branches use the same directed starting edge and the same corner
witnesses. `fitted` proves that the resulting eight observations satisfy the
exact query compiled from the D1774 construction. `actual_fitted` instantiates
this theorem at the two aligned exceptional occurrences in the graph-backed
minimal facial dual. The source walk starts at numbered dart 84 and visits
source vertices `16,18,11,14,17,15,12,13` (zero-based labels); those readings are
also kernel checked.

This recognition proof needs no new hypothesis asserting a D1774 occurrence,
core injectivity or distinct ring images. It uses the already retained core
corners and degrees. Under reference minimality of this exact dual hypermap,
`not_minimal` consumes the source construction, finite repair and contraction
chain to exclude the overlap. The graph-backed minimality hypothesis has not
been shown to imply that reference hypothesis. The direct contract-colouring
route below supplies its starting witness without such an implication;
the local exterior consumer below now completes that geometric bridge.

Replay with `lake build kernelExceptionalQuery`. Its nine-root audit retains
the actual corner, degree and reconstruction dependencies, permits only the
standard axioms, and rejects complete Four Colour endpoints and original
configuration rank certificates. The D1774 finite repair certificate remains.
This closes the local query-recognition obligation; coverage remains 633 entries
and the complete assembly retains 629 original configuration certificates.
See [exceptional-query-measurements.json](exceptional-query-measurements.json).

## Initial contract colouring in the actual graph-backed domain

The existing adjacent-pair reduction provides a strict smaller planar cap.
`MinimalSingletonContract.one_zero` uses vertex minimality to colour that cap,
then reconstructs a conserved field on the original graph with exactly one
zero edge. `ConservedContract.of_conserved` integrates the full field into an
actual face assignment. Every edge difference is preserved, including its
zero set, so the result is a genuine contract colouring.

`ContractTransport.ccColoring_push` transports that assignment and its entire
contracted edge list together. `ActualDualContract.map_eq_source_relabel`
identifies all three permutations of the physical source hypermap with those
of the actual dual query map. `singleton_colorable` therefore provides an
initial contract colouring for every selected dart of that exact map, using
graph-backed vertex minimality throughout. `not_colorable` proves the reverse
consumer: a proper colouring there would reconstruct an original Tait colouring.

This closes the starting-witness obligation. The local exterior consumer below
now applies the finite D1774 repair using sufficient local hypotheses, including
treatment of boundary identifications. Classification from final charge,
geometric supply and global coverage remain open.

Replay with `lake build kernelMinimalSingletonContract`. The twelve-root audit
checks 24,706 dependency declarations and permits only standard axioms. It
excludes complete Four Colour endpoints, original configuration ranks, the
D1774 finite repair and the reference minimal contract-colouring theorem.
The new modules add no enumeration or colouring certificate. Coverage remains
633 entries and the complete assembly retains 629 original configuration
certificates. See
[minimal-singleton-contract-measurements.json](minimal-singleton-contract-measurements.json).

## Actual exceptional closing law through local embedding

`ExceptionalLocalRepair.aligned_not_in_minimal` now excludes two aligned actual
X occurrences in a graph-backed vertex-minimal Tait counterexample. It consumes
their full source geometry and the checked D1774 repair, supplying both the
embedding and the initial contract colouring rather than assuming either.

The reusable geometric contract is `FaithfulKernelEmbedding.FaithfulKernel`:
core darts are injected and an ambient edge reversal between their images is
already a source edge reversal. Together with a preembedding, plainness and
cubicity, these two local facts imply injectivity on the complete off-perimeter
disk. Distinct boundary faces need not have distinct ambient images.
`InjectiveEmbeddedRepair.colorable` then composes the actual contract colouring,
exterior Kempe closure and patch reconstruction. These two arguments adapt
Gonthier and Werner's embedding proof as ported by Chris Emery, with its MIT
attribution retained. They factor out the reference consumer's stronger global
Birkhoff-ring and pentagonal hypotheses.

`ExceptionalDartReading` certifies this local contract from the induced core
and complete cyclic stars. It checks the finite source dart positions and star
cycles, but adds no colouring-rank table. `ExceptionalPreembedding` transports
the same reading through the exact Y/H numbering. `LocalPreembedding.of_radius2`
constructs its ring-link paths from the source kernel's radius-two property.
Every observation and every reconstruction stage uses this one map.

The final consumer combines this disk injection with
`ActualDualContract.singleton_colorable`, which comes from the existing strict
smaller planar cap and vertex minimality. `ExceptionalLocalRepair.overlap_supply`
fills the second-centre and joint closing fields of `EightOverlapSupply`.
Its zero-charge classification remains an explicit hypothesis. The low-degree
and degree-seven supply laws, residual cases, charge transport and global
coverage are still open.

After preparing the existing source and finite repair dependencies, run
`lake build kernelInjectiveEmbeddedRepair`, then `lake build kernelExceptionalExterior`. The
29-root audit excludes complete Four Colour endpoints, original catalogue rank
certificates, the reference minimal-contract theorem and the global
`embed_full`/`embed_inj` chain. It permits only standard axioms. The D1774 finite
repair is retained in the final local consumer and absent from the generic and
geometric roots. Coverage remains 633 entries / 629 original configuration
certificate dependencies. See
[exceptional-exterior-measurements.json](exceptional-exterior-measurements.json).

## Actual discharge and a first classification prune

The complete 84 oriented rules (43 rules with their required reflections) are
retained unmodified in [discharging-rules](discharging-rules), pinned to
`d85bfe09e9584d675fdf33a1da61067575ec4883` of
[the discharging-rule repository](https://github.com/near-linear-4ct/discharging-rules).
The MIT notice is in [LICENSE](LICENSE), and individual source hashes are in
[discharging-sources.json](discharging-sources.json).

`NearLinearRuleData` checks the headers, all 638 vertex rows, complete
adjacency, explicit cyclic gaps, degree intervals and marked endpoints. Each
vertex observed by a rule has a path of length at most two from either
endpoint, whose intermediate vertex has prescribed degree at most eight.
Every rule has a prescribed degree-five vertex, and every sender has degree
at most eight.

`NearLinearCharge.Occurrence` interprets these observations in actual graph
darts, retaining all known rotation steps. Occurrences may identify distant
vertices. An applicable rule is counted once, using existence of a reading;
the charge does not count alternate witnesses. Starting charge is
`10 * (6 - degree)`, followed by incoming minus outgoing rule amounts.
This is the mathematical rule semantics, not a proof that the C++ search
implements or exhausts it.

The resulting uniform laws establish:

- No degree-five vertex within radius two means no charge crosses any edge
  incident to the centre. Its final charge equals its initial charge.
- A flat centre of degree seven or eight therefore has a degree-five vertex
  within radius two.
- A rule application retains one degree-five witness close to both endpoints.
- Two distinct flat degree-eight centres require exactly forty units of net
  external charge. Their shared transfers cancel, with the same outside
  vertices retained in the boundary sum.

`ExceptionalFlatCharge.overlap_supply` applies the first prune in the actual
graph-backed minimality domain and reuses the completed exceptional-pair
repair. Classification of the remaining neighbourhoods still has to be
proved. There is no claim here of cartwheel completeness, a smaller catalogue,
new reducibility, or a near-linear running time. The ledger remains 633
coverage entries and 629 original configuration certificate dependencies.

From the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_discharging_sources.py
```

With the exceptional exterior artifacts prepared, from
`lean/fourcolor-classical`, run sequentially:

```sh
lake build kernelNearLinearRuleData
lake build kernelNearLinearCharge
```

See [source fidelity](discharging-source-audit.json) and
[kernel measurements](charge-measurements.json). The charge audit excludes
complete Four Colour endpoints and original configuration rank certificates.
The D1774 finite repair occurs only in the consumer of the existing closing
law; it is absent from the rule and charge proofs.

## Exact rooted matching and a concrete joint-view test

`RuleTraversal` interprets a source construction as flips, vertex rotations
and inverse rotations of an actual graph dart. Its transport theorem uses
one occurrence throughout, including when distinct source vertices share an
ambient image. `RuleTraversalData` certifies all 638 vertex traces for the 84
pinned rules: each trace follows known source transitions, reaches its
advertised vertex, and has length at most seven.

`RuleMatcher.candidate_eq` proves that any rooted occurrence has exactly the
candidate vertex images produced by those traces. `check_iff` then proves
that checking the candidate's complete adjacency, degree bounds and known
cyclic steps is equivalent to `NearLinearCharge.Applies`. Checking succeeds
or fails without searching over vertex assignments. `chargeAt_eq` identifies
the resulting computation with the existing occurrence-based final charge;
`checked_pair_budget` consumes two computed flatness certificates and yields
the exact forty-unit external boundary budget.

The generator is untrusted. Lean checks its output against the original
rule data. The matcher audit forbids reduction certificates, original
configuration certificates and complete Four Colour endpoints. From prepared
rule data, replay with:

```sh
python3 tools/fourcolor/near-linear/generate_rule_traces.py
cd lean/fourcolor-classical
lake build kernelRuleTraversal
lake build kernelRuleMatcher
```

The [measurement record](rule-matcher-measurements.json) separates the finite
traversal-data check from the generic proof and audit.

The [saved flat-pair example](flat-pair-probe.json) is independent program
evidence. Starting with an edge-subdivided icosahedron, 417 legal oriented
edge flips produce a 42-vertex triangulation with adjacent degree-eight
vertices 11 and 18. Both have final charge zero and their net external supply
is forty. The two radius-two balls have 26 vertices each, with 33 in their
union. The `D0001` core image `[38, 39, 36, 27]` lies in that union but neither
individual ball; its full source vertex reading is retained in the report.
Other reducible pieces already occur in the individual balls, so this is not
an example proving that joint inspection is necessary.

Two independent implementations agree on all 20,160 rule/root tests on this
graph: compiled traces and breadth-first dart propagation. They identify 391
rooted rule occurrences. The saved report retains the initial faces, every
edge flip, final faces, source rule revision and actual rule images. Replay
from the repository root:

```sh
python3 tools/fourcolor/near-linear/probe_flat_pairs.py \
  --replay tools/fourcolor/near-linear/flat-pair-probe.json \
  --output /tmp/flat-pair-replay.json
cmp tools/fourcolor/near-linear/flat-pair-probe.json /tmp/flat-pair-replay.json
```

The flat-charge computation and the straddling core reading remain program
evidence. The latter checks complete core stars and ring edges while allowing
boundary identifications; a full embedded occurrence and reconstruction for
that particular core are additional obligations. The rotation and a different
rule-pair consumer in the same graph are certified below. Neither
this example nor the generic matcher establishes cartwheel enumeration
completeness, absence of obstructing cycles, or a charge-to-reduction law for
all flat pairs. The coverage ledger remains 633 entries and 629 original
configuration certificate dependencies.


## Two charge rules force a shared geometric reduction

`RulePairDiamond` gives a structural law for `rule003_2` (index 4) and
`rule004_1` (index 5). The second incoming root is determined by two backward
turns at the first root's receiver. The exact rule matcher proves that both
readings then share the receiver and the same neighbouring vertex.

If the first sender has degree five and the shared neighbour has degree six,
the first reading supplies two consecutive turns at that neighbour and the
second supplies three more. Cyclicity forces the sixth turn. Triangular
closure transfers the resulting corner across the edge, exposing a five–six
edge with a degree-five vertex on each flank. The receiver's degree need not
be eight, and the surrounding graph has no fixed size bound.

```text
rule 003_2: two turns --+--> same six-valent star --> closing corner
rule 004_1: three turns+                                |
                                              mixed diamond
                                                    |
                                          13 removed, 5 added
                                                    |
                                       reconstruct actual colouring
```

`ActualRulePairDiamond` transports this result through the actual facial
dual. Its degree-to-face-length theorem retains the source dart. The existing
mixed-diamond reduction supplies strict descent by eight vertices and
colouring reconstruction. Consequently, in a graph-backed vertex-minimal
counterexample, the checked first rule and the two degree guards force the
aligned second rule check to be false. This is a usable forbidden joint
charge profile; no cartwheel-classification premise is assumed.

The same five-turn path also has a degree-five branch. Cyclicity then
identifies the last outer vertex of the second reading with the first outer
vertex of the first reading. `identified_corner` proves this equality in the
actual graph. With the first sender and other outer corner of degree five, triangular closure
exposes the all-pentagonal diamond. The existing twelve-to-four replacement
again decreases the full map by eight and reconstructs its colouring.

The source rules bound both the shared degree and that other corner's degree
between five and six. `pair_alternatives` therefore gives a complete split
for this aligned pair with a degree-five first sender:

```text
five prescribed turns at the shared vertex
                  |
          +-------+--------+
          |                |
       degree 6         degree 5
          |                |
    closing corner    endpoints identified
          |                |
    mixed diamond     other corner's degree
       13 -> 5          /             \
                       5               6
                  pentagonal        retained
                   12 -> 4          residual
```

`ActualRulePairDiamond.surviving_pair_degrees` discharges both reduction
branches in graph-backed vertex minimality: a surviving pair must have shared
degree five and other-corner degree six. This is a necessary local condition;
it does not assert that the residual is irreducible or occurs in a minimal
counterexample.

`RulePairExample` checks a nonempty instance on the saved 42-vertex graph:
root `25 → 18`, second root `28 → 18`, shared vertex 5 and derived mixed edge
`26 → 5`. The cyclic star at vertex 5 is
`26, 25, 18, 28, 19, 1`. Lean checks vertexwise cyclicity, triangular closure,
both full rule checks and the two degree guards; `has_mixed` consumes the
general structural theorem. It does not certify the experiment's flatness,
spherical flip history or absence of other reductions.

`RulePairCollisionExample.has_pentagonal` uses the same certified rotation
at root `41 → 39` and second root `9 → 39`. Both readings identify vertex 30;
the resulting edge `30 → 32` has five-valent flanks 4 and 41. Lean checks the
complete rule matches and guards, then consumes the general collision law.
A separate exhaustive program scan finds eleven degree-five overlaps in this
graph: four satisfy the pentagonal guard and seven retain the five/six profile.
That scan is not a coverage theorem.

The independent source-fidelity replay is:

```sh
python3 tools/fourcolor/near-linear/audit_rule_pair_example.py
```

It compares all 42 Lean cyclic stars with the saved oriented faces. It also
records a limit of the earlier straddling-core candidate: vertex 38 is absent
from every positive rule reading incident with the two flat centres. Thus
those positive readings do not directly supply that particular four-vertex
core. Other geometric or negative-rule information could still do so.

Prepare the finite example once with `lake build kernelRulePairExampleData`,
then run `lake build kernelRulePairDiamond` with the rule/traversal data and
both diamond artifacts prepared. Its dependency audit requires the actual
strict-reduction and reconstruction chain. The shared diamond profile
certificate remains; original catalogue certificates, the D1774 certificate
and the complete Four Colour endpoint are absent.

This removes two explicitly described branches of joint rule profiles from the
remaining classification and specifies the surviving degrees. It removes no
coverage entry or existing assembly certificate. The exact forty-unit budget
still needs a complete account of the surviving profiles. See
[measurements](rule-pair-diamond-measurements.json).

## Continuing a rule beyond the original pair boundary

[chain-boundary-example.json](chain-boundary-example.json) retains a generated
162-vertex triangulation and its 100 legal edge flips. The adjacent centres
have degrees eight and seven; the seven is the eight's only neighbour of
degree above six. Both final charges are zero. Their radius-two balls contain
22 and 20 vertices, with 27 in their union. That union contains neither known
diamond core nor the chain degree word in either orientation.

The charge rule `rule004_2` in the reversed rotation retains three successive
neighbours of a degree-six outer vertex. Their degrees are `5,6,5`. Continuing
once reaches another degree-five vertex, beyond both original radius-two
balls, and recognizes the existing chain. All thirteen source vertices fit
within radius four of the degree-eight centre.

[RuleChainRecognition](../../../lean/fourcolor-classical/MettapediaFourColor/RuleChainRecognition.lean)
proves this implication for arbitrary triangular rotations. Its actual-map
consumer excludes the continuation in graph-backed vertex minimality, using
the same strict reduction, reconstruction and configuration-7 base certificate.
[ChainBoundaryExample](../../../lean/fourcolor-classical/MettapediaFourColor/ChainBoundaryExample.lean)
certifies the concrete cyclic geometry, rule and degree-word readings, full
occurrence, boundary crossing and radius bound. It does not certify the
example's global sphericality, flatness or absence of obstructing cycles.

Replay the separate program evidence with:

```sh
python3 tools/fourcolor/near-linear/audit_chain_boundary.py
```

The audit reconstructs the spherical triangulation from its saved flips,
checks 5,040 rooted rule matches in both orientations by two independent methods, checks both sides
of all 1,826 simple cycles of length three through five, verifies the absence
of the three known core patterns in the original view, and checks the complete
chain and all Lean cyclic stars. Results are in
[chain-boundary-audit.json](chain-boundary-audit.json).

With the preceding chain artifacts prepared, `lake build kernelChainBoundary`
replays the new theorems and their dependency audit. The
[kernel receipt](chain-boundary-measurements.json) records all four modules
and the seventeen-root audit. This supplies a concrete
reason to extend local views during the coverage search. It neither proves
universal family supply nor removes a catalogue entry. The complete assembly
still uses 633 coverage entries and 629 original configuration certificates.

## Completing the second chain profile

The degree-six word `5,6,6,5` now constructs an actual D0006 occurrence,
including all nine ordered boundary ports. The eight-port D0004 word
`5,6,5,5` has been refactored to use the same parameterized
[fan boundary law](../../../lean/fourcolor-classical/MettapediaFourColor/FanBoundaryScheme.lean).
Shared rotation readings determine a single boundary map, so the three
triangles retain their common vertices throughout completion.

[ActualExtendedChainReduction](../../../lean/fourcolor-classical/MettapediaFourColor/ActualExtendedChainReduction.lean)
connects this recognition to strict descent and reconstruction in the actual
minimal-map domain. It reuses the already certified D0006 repair from
classical configuration 7. There is no new rank certificate.
[ExtendedChainExample](../../../lean/fourcolor-classical/MettapediaFourColor/ExtendedChainExample.lean)
constructs the whole source from directed edge `(48,117)` of the retained
162-vertex graph and checks all fourteen images. Those images lie within
radius two of centre 48; flatness and global sphericality of the example
remain separate program evidence.

The [kernel receipt](extended-chain-measurements.json) records the common
geometry, exact source bridge, actual reconstruction and finite example.
This gives a second concrete consumer of the generic completion theorem.
The next coverage obligation is to derive one of the supported reductions
from the surviving joint charge profiles, or retain and characterize a
counterexample to that proposed local supply claim. Coverage remains 633
entries with 629 original certificate dependencies.

## A uniform cyclic charge budget

[CyclicCharge](../../../lean/fourcolor-classical/MettapediaFourColor/CyclicCharge.lean)
proves `T(v) >= 10(6-d) + 4k + 2m` for any receiver of degree `d >= 7`
whose neighbours all have degree five or six. The count `k` is the number
of five-valent neighbours. The count `m` is over receiver wedges with a
five-valent opposite facial tip; tips need not be distinct. The proof
constructs the first five oriented source rules from actual shared
triangles, reindexes the rotation, and retains all remaining signed terms.

[CyclicFanContinuation](../../../lean/fourcolor-classical/MettapediaFourColor/CyclicFanContinuation.lean)
uses both known outer tips of the same-root rules002_2/003_2 fan. At a flat
seven with only low neighbours, at most one neighbour is five. The actual
minimal-map consumer identifies that five with the retained shared vertex:
either an adjacent third high centre exists, distinct from the previous
two and within radius three, or all other neighbours are six. At a flat
eight with only low neighbours, the same argument bounds the fives by four.

The [finite input](cyclic-charge-examples.json) and
[independent audit](cyclic-charge-audit.json) check four receiver profiles
against all incident source rules, using two independent matchers. Two
positive examples consume the general law in Lean. The input also records
two legal flips producing the single-five residual with zero charge. Its
original centre has positive charge nine, so it is not a jointly flat or
minimal-counterexample instance. Its flatness is program evidence only.

Replay with `lake build kernelCyclicCharge` and:

```sh
python3 tools/fourcolor/near-linear/audit_cyclic_charge.py --output tools/fourcolor/near-linear/cyclic-charge-audit.json
```

The [receipt](cyclic-charge-measurements.json) keeps classification and
compression separate. The single-five residual, joint-flatness closure,
initial supply and global coverage remain open; counts stay 633 / 629.

## Joint rule-fan coverage branch

Rules `002_2` and `003_2`, matched on the same directed edge, jointly fix
`[receiver,5,5,a,b,5]` around a degree-six sender when its next neighbour
after the receiver has degree five. The three low-degree alternatives consume the mixed diamond,
D0004 and D0006. On the actual minimal-map domain, one of `a,b` must have
degree at least seven. It is a distinct vertex within radius two of the
receiver. The flat degree-at-most-eight domain thus supplies a second flat
centre of degree seven or eight.

The [Lean theorem](../../../lean/fourcolor-classical/MettapediaFourColor/ActualRuleFanSupply.lean)
uses all three reconstruction consumers; its dependency audit retains only
the shared diamond profile and the existing configuration-7 rank certificate.
The [kernel receipt](rule-fan-supply-measurements.json) distinguishes this
local supply result from initial profile classification and global coverage.
Three finite examples use the exact source rules and exercise each branch.
Replay their independent program check with:

```sh
python3 tools/fourcolor/near-linear/audit_rule_fan_supply.py --output tools/fourcolor/near-linear/rule-fan-supply-audit.json
```

`lake build kernelRuleFanSupply` checks the general laws, actual reductions,
finite consumers and audit with the earlier artifacts prepared. The next
obligation is to exploit the overlapping views at the supplied centre,
retaining shared vertices and detecting repeated centres. No universal
coverage or termination theorem is claimed, and the assembly counts stay
633 coverage entries and 629 original configuration certificates.

## Signed charge supplies an alternative to returning

The earlier joint fan can return to its original receiver when continued
through the same six-valent sender. Flatness supplies more information than
the degree word alone. [RuleFanCharge](../../../lean/fourcolor-classical/MettapediaFourColor/RuleFanCharge.lean)
proves that two consecutive fives on each side of a six-to-high edge force
three incoming contributions of at least `3,4,3`. The same facial triangles
construct the related rule occurrences, preserving their shared vertices.

At a degree-seven receiver with only degree-five/six neighbours, the two
flanking triangles add one unit each. Cyclicity makes these five senders
distinct. The complete 84-rule semantics gives zero reverse transfer and
nonnegative remaining contributions. Thus the final charge is at least
`-10 + 1 + 3 + 4 + 3 + 1 = 2`.

Consequently, if its neighbours all have degree at least five, a flat seven
receiving this fan must have a high-degree neighbour.
[ActualRuleFanCharge.third_center](../../../lean/fourcolor-classical/MettapediaFourColor/ActualRuleFanCharge.lean)
applies this to the previous source-rule profile when the first free vertex
is a flat seven and the second free vertex is five. The actual minimal-map
facial triangle theorem excludes an edge back to the original receiver.
The new high centre is adjacent to the second, distinct from both previous
centres, and within radius three of the first.

The [finite example](rule-fan-charge-example.json) uses two legal edge flips
of the retained 162-vertex triangulation. Lean verifies its cyclic geometry,
the low-neighbour hypothesis and the positive conclusion using the general
theorem. The [independent replay](rule-fan-charge-audit.json) computes exact
charge eight and agrees on all 1,176 incident rule checks. Replay with:

```sh
python3 tools/fourcolor/near-linear/audit_rule_fan_charge.py --output tools/fourcolor/near-linear/rule-fan-charge-audit.json
```

`lake build kernelRuleFanCharge` checks the general law, actual consumer,
finite example and dependency audit. The [receipt](rule-fan-charge-measurements.json)
records the scope and costs. This branch uses no original configuration
rank certificate. It neither excludes longer centre cycles nor closes the
degree-eight or second-free-degree-six branches. Coverage remains 633
entries with 629 original certificate dependencies.


## An extra source rule supplies a reduction

`ExtraChargeReduction.closing` completes the actual five-valent sender star
of rule `004_1` (index 5). With a six-valent shared neighbour and a
five-valent second successor of the sender, the outer triangle gives either
a mixed diamond or the eight-port `D0004` chain. One geometric law handles
both outer degrees. `ActualExtraChargeReduction.not_occurrence` consumes
the existing strict reductions and compatible colouring reconstructions;
no starting colouring or exterior-closure assumption is supplied by its caller.

`ActualExtraChargeReduction.flat_alternatives` strengthens the preceding
single-five classification. In its residual branch, this particular extra
rule is absent at the shared-five-to-first-free edge. Other additional
incoming rules remain possible and must still be classified.

The [input record](extra-charge-examples.json) has two finite consumers of
the general theorem, with both complete source-rule readings kernel checked.
The chain branch constructs its full boundary occurrence. The same record
replays five legal flips from the retained 162-vertex sphere: both centres
then have charge zero, the original shared fan survives, and the extra rule
exposes the existing chain. Thus joint flatness alone permits the degree
profile; the matched source rule explains a repair inside that example.

Run `lake build kernelExtraCharge` in `lean/fourcolor-classical` for the formal
result. Run
`python3 tools/fourcolor/near-linear/audit_extra_charge.py --output tools/fourcolor/near-linear/extra-charge-audit.json`
from the repository root for its independent finite evidence. The latter
compares 2,357 rule readings with an independent propagation checker.
The [measurement record](extra-charge-measurements.json) distinguishes the
Lean results from program-checked flatness and sphericality. The chain
reconstruction retains classical configuration 7 and the shared profile.
Counts remain 633 coverage entries and 629 original certificates; no new
assembly dependency or coverage entry is removed.


## Exact accounting of the residual inflows

`ExactCyclicCharge.exact_charge` strengthens the lower bound to the identity
`finalCharge(v) = 10(6-degree(v)) + 4k + 2m + E`. The domain is a finite simple
graph with triangular dart rotation, a receiver of degree at least seven,
and all its neighbours of degree five or six. Neither planarity nor a
single-cycle condition on each vertex rotation is needed for this identity.
The counts retain actual neighbours and marked wedges; two wedges may share
a five-valent outer tip. The remainder counts all matches of rules 5..12.
The other source types cannot have a sender of degree at most six.

In a single-five neighbourhood, rules 9 and 10 cannot occur: both would
retain distinct adjacent five-neighbours of the receiver. At a flat seven
with at least two marked outer five-tips, exactly two budgets remain:

| Marked tips | Additional rule-edge matches |
| --- | --- |
| 2 | 2 |
| 3 | 0 |

`ExactFanResidual.alternatives` connects this to the actual shared fan,
retaining the previous index-5 exclusion on its specified edge. These are
budgets, not two completed repair arguments. The source types still allowed
in the remainder are 5, 6, 7, 8, 11 and 12.

The [inputs](exact-charge-examples.json) and [independent audit](exact-charge-audit.json)
replay both charge budgets on spherical triangulations with both centres flat.
The two-extra example still has the marked rule excluded by the preceding
reduction. Only the three-tip example also satisfies that exclusion.
It has no extra transfer at all, so eliminating extra
rules alone cannot close the geometric obligation. Both examples have an
injective complete source-graph match of [D3009](D3009.conf), with its core
induced: a seven-valent centre, one five-valent neighbour and six six-valent
neighbours. The input manifest pins its upstream revision, source hash and
MIT licence. The general occurrence is now proved below. Colouring repair and
strict reconstruction remain open.

Run `lake build kernelExactCyclicCharge` in `lean/fourcolor-classical`.
Run `python3 tools/fourcolor/near-linear/audit_exact_charge.py --output tools/fourcolor/near-linear/exact-charge-audit.json`
from the repository root. Two base receivers consume the Lean identity to
give `2 + E` and `8 + E`. The program checks their extra counts as 2 and 1,
giving charges 4 and 9. These numerical matcher counts, the modified graphs
and the D3009 occurrences are program evidence. The
[measurement record](exact-charge-measurements.json) separates these scopes.
The actual-map continuation retains configuration 7 through the preceding
reduction. Coverage remains 633 entries /629 original certificates.

## Completing the residual wheel

`ActualWheelOccurrence.occurrence` constructs D3009 from the single-five
seven-valent profile in the actual minimal facial dual. It assumes only
that profile, not an embedded source occurrence. The construction proves
all source edges, all eight complete core stars and degrees, an induced
core, and injectivity of all 21 vertices. Every image is within radius two
of the retained centre. Extra edges between boundary vertices are not
excluded or needed by this statement.

The geometric argument is compositional. `WheelNeighborhood` first gives
an ordered wheel at arbitrary degree. Source neighbour stars then grow the
thirteen-port boundary; the actual facial seam identifies their shared
observations. An outer port cannot fold into the induced core. If two owned
outer ports coincide, the resulting four-cycle forces adjacent owners.
Facial triangles then force the common vertex to be their designated seam,
contradicting its two different owner positions. Thus the complete boundary
is a genuine simple cycle, with distinct vertices.

`ActualWheelOccurrence.residual_occurrence` consumes the exact-charge
classification without changing its centre, marked five-neighbour or rule
exclusion. Both retained budgets supply this same source shape. The occurrence
construction uses no configuration repair certificate or complete Four Colour
theorem; the residual supply still retains configuration 7 through the prior
reduction. No D3009 repair is assumed from the source catalogue.

Replay with `lake build kernelWheelNeighborhood` in `lean/fourcolor-classical`.
The [receipt](wheel-occurrence-measurements.json) records sixteen audited roots,
only standard axioms, and the full regression gates. The
[source audit](wheel-source-audit.json), reproduced by
`python3 tools/fourcolor/near-linear/audit_wheel_source.py`, verifies the source
hash and equality of its numeric rows with the Lean decoder input.

The next obligation is compatible colouring repair and actual strict
reconstruction. The exact construction and colouring interface are now proved
below. The occurrence theorem removes no coverage entry or certificate
dependency. Counts remain 633 /629.

## Shared cyclic choices for the wheel

`D3009Construction` builds the pinned source with eleven Y and eight H steps.
Its 94 darts retain all three permutations, every source edge and cyclic star,
and the thirteen ports in source order. Actual colouring witnesses and their
ordered traces transport exactly. The reference construction also supplies
the embeddability contract.

`WheelColouring.coloringEquiv` applies to any boundary graph and any
fixed-point-free rim successor. A complete colouring is equivalent to its
boundary colouring, one shared centre colour, and compatible colours around
the rim. `WheelColouringGSLT.extends_iff` identifies this with a closed GSLT
route, uniformly at every width at least two. Splitting the route keeps the
common centre colour and both interface colours. These are exact extension
laws; they do not assert that an arbitrary boundary assignment extends.

`D3009Colouring` proves the exact graph isomorphism and consumes those laws.
In particular, `two_sectors_iff` reconstructs a source colouring from compatible
three-step and four-step sectors. `constructionTrace_iff` equates the Y/H
construction's trace with this cyclic interpretation. The witness equivalence
retains multiplicities as well as support; it supplies no executable Kempe
recolouring algorithm.

`D3009ColouringExample` checks a successful pair and a precise failed closure.
For the proper boundary word `0101010101013`, each rim vertex must use colour
2 or 3. The seven-cycle cannot close with those two colours. Both sectors have
histories, even with the same centre colour and agreement at their shared
middle seam, but the other seam cannot close. Exterior recolouring remains
available; the example refutes only independent sector inhabitation.

The [finite probe](wheel-repair-probe.json) goes further experimentally:

| Centre degree | Ring length | Canonical traces | Direct extensions | Survivors after full pairing closure |
| --- | --- | --- | --- | --- |
| 5 | 9 | 820 | 257 | 0 |
| 6 | 11 | 7,381 | 1,381 | 0 |
| 7 | 13 | 66,430 | 7,496 | 0 |

These are independent program results, not Lean repair certificates. Every
terminal witness is checked on all graph edges. The closure considers all
noncrossing pairings and all unions of whole chords, up to complementary
choices and global colour permutation. In particular the thirteen-port case
allows three-chord answers. At width seven the exact pinned source is used;
its boundary labels are a checked rotation of the uniform wheel incidence.
Reproduce with `python3 tools/fourcolor/near-linear/probe_wheel_repair.py`.

Replay the proofs with `lake build kernelWheelColouring` in
`lean/fourcolor-classical`; see the [receipt](wheel-colouring-measurements.json).
The nineteen-root audit excludes configuration repair certificates and the
complete Four Colour theorem. Neither a uniform D-repair law nor the D3009
repair has yet been kernel certified. The next test is a compact repair
certificate with a measured kernel cost, followed by actual exterior repair
and strict reconstruction. Coverage and original certificate counts stay
633 /629.


## A repaired wheel seed

`generate_wheel_seed_repair.py` extracts the answer closure of the concrete
nonextending boundary `0101010101013`. The complete finite discovery still
has 66,430 canonical states, but this seed uses only nine retained states:
one repair record and eight terminal source colourings. There are 132
unsigned exterior pairings and 31 selected answers exchange three chords.
This does not establish that those three-chord moves are necessary.

`WheelSeedRepairCertificate.seed_repair` checks that finite certificate in Lean.
The theorem meets every Kempe-closed exterior containing the seed. Its
`repaired_sectors` consumer obtains compatible GSLT sector histories;
`repaired_construction` preserves the same trace in the pinned Y/H source.
No other boundary trace is covered merely by the independent rank search.

Generate the flat data with:

```sh
python3 tools/fourcolor/near-linear/generate_wheel_seed_repair.py \
  --output WheelSeedRepairData.lean --report wheel-seed-generation.json
```

`--cache` optionally retains the untrusted discovery ranks between runs.
The kernel checks every consumed fact independently of that cache. Replay
`lake build kernelWheelSeedRepair`; the
[receipt](wheel-seed-repair-measurements.json) records proof scope and costs.
The complete D3009 repair contract remains open. The following geometric
consumer supplies actual exterior closure and strict reconstruction conditional
on that full contract. No catalogue entry is removed by this seed.


## The wheel occurrence as a repair disk

`D3009Preembedding` maps all 94 source darts by their actual ordered endpoints.
The retained complete core stars preserve the face operation and arities;
whole-source vertex injection preserves dart identity. The same reading gives
an injective disk for the exact Y/H construction.

`D3009RepairGeometry` proves that the edge from the degree-seven centre to its
degree-five neighbour is a valid singleton contract. Given a full thirteen-port
repair law, the actual minimal-map consumer obtains a contract colouring from
the established strict two-vertex reduction and reconstructs the ambient
colouring. This would exclude the recognised degree profile and resolve the
wheel branch of `ActualWheelOccurrence.residual_occurrence`.

The full repair law remains an explicit hypothesis. The nine-state seed
certificate alone does not discharge it. Replay `lake build kernelWheelEmbedding`;
the [receipt](wheel-embedding-measurements.json) records ten audited roots and
standard axioms only. No coverage entry or original certificate is removed.


## One collapse transfers repair to every two-five wheel

`TwoFiveWheelData` removes the private outer fan vertex at any of the six
degree-six positions of D3009. Reinsertion is exactly a boundary-triangle
subdivision, with all graph edges, cyclic stars, degrees and ordered ports
checked. Each target has twelve boundary vertices and the same eight core
vertices, with two rim degrees five and all remaining rim degrees six.

`TwoFiveWheelRepair.transfer` applies the existing boundary split and
reconstruction theorem to all six positions. Its sole repair premise is
the full thirteen-port D3009 law; the separately running finite replay
has not yet discharged that premise. None of the three Python closure
experiments is used by the proof, and no target repair certificate is added.
`TwoFiveWheelColouring.repaired_sectors` retains the same Kempe-closed
exterior relation and obtains two GSLT sectors with shared centre and
seam colours. This establishes compatible existence, not a counted or
executable Kempe-recolouring algorithm.

Replay `lake build kernelTwoFiveWheel`; the
[receipt](two-five-wheel-measurements.json) records the fourteen-root audit.
Actual two-five occurrence is supplied by the shared geometric theorem
below; the subsequent disk theorem supplies ambient reconstruction conditional
on the same full source repair.
Coverage and original configuration certificate counts stay 633 /629.


## One geometric completion for both wheel families

`WheelBoundaryCompletion` separates finite source rows and outer-port
ownership from the geometric argument. Triangular closure equates the
readings of a shared seam. Inducedness of the wheel core excludes a port
from returning into the core. A collision between different outer ports
produces a four-cycle; its chord and a facial triangle contradict the
owned positions. This proves injectivity rather than requiring it.

`D3009BoundaryLayout` and `WheelBoundaryLayouts` supply the finite laws for
D3009 and all six twelve-port targets. `ActualWheelOccurrence.occurrence` consumes the
shared theorem for D3009. `TwoFiveWheelOccurrence.supplied` selects the
second-five position from the actual cyclic neighbour orbit and constructs
the corresponding source, preserving all edges, full core stars and both
marked neighbours. Every source vertex lies within radius two of the same
centre. Additional ambient edges between boundary vertices are permitted.

`SecondFanWheelOccurrence.alternatives` combines the charge classifier with
these occurrences without assuming a colouring repair. Its outcomes are a
new high neighbour, the original one-five wheel, or a complete two-five
wheel carrying the exact two-five/one-tip/no-extra-transfer observations.
The target repair is already a consequence of the full D3009 repair by the
preceding collapse theorem. The disk and strict reconstruction are supplied
by the following common construction argument, with that repair premise explicit.

Replay `lake build kernelWheelBoundaryCompletion`; see the
[receipt](wheel-boundary-completion-measurements.json). The general geometric
argument has actual consumers in both families. Coverage and original
certificate counts remain 633 /629.


## One strict reconstruction argument for the six two-five placements

`TwoFiveWheelConstruction` checks exact Y/H programs for every target.
Each source has ninety darts, twenty dual vertices and twelve boundary ports.
The complete edge/node/face permutations agree with the programs; the full
cyclic stars and ordered colouring traces agree with `TwoFiveWheelData`.

`TwoFiveWheelPreembedding` reads every source dart through the previously
proved actual occurrence. Its complete cyclic stars establish the same
preembedding and faithful kernel at every second-five position. The shared
kernel-to-disk theorem then gives injectivity of the repair disk.

`TwoFiveWheelRepairGeometry` checks the centre-to-marked-five contract at
all six positions. Existing graph-backed vertex minimality supplies its
initial colouring by strict two-vertex descent. The family repair transfer
then reconstructs a genuine ambient colouring, compatible with the same
exterior. The full thirteen-port D3009 repair is an explicit premise; no
additional target repair certificate is needed.

The actual consumer `second_high_neighbor` applies this to the shared fan.
Both single-five and two-five wheel outcomes are excluded, leaving a new
high neighbour within radius three of the original receiver. It retains
the same flat second centre throughout. Universal coverage is still open.

Replay `lake build kernelTwoFiveConstruction`, then
`lake build kernelTwoFiveEmbedding`; the
[receipt](two-five-embedding-measurements.json) records the finite source
checks, disk/reconstruction audit and unchanged catalogue counts.

## From the shared fan to joint seven-centre views

`RuleFanSevenCluster.pair_exists` consumes the actual shared six-valent fan,
flatness and the degree-at-most-seven bound within radius three. The existing
diamond and chain reductions force one of the two free positions to be high.
The single full D3009 repair, including its six transferred two-five repairs,
then supplies a high neighbour of that same selected position. Both vertices
are flat sevens, and neither is the original receiver.

`unique_or_third` retains this pair when selecting a second high neighbour
of its first centre. If there is none, every other neighbour has degree at
most six. Otherwise the three distinct sevens form an induced path or an
actual facial triangle, with the two possible orientations retained. The
third centre also differs from the original receiver. The complete
radius-two views fit within radius five of the original receiver.

`occurs_of_joint_laws` supplies the same supported occurrence after one of
three joint closing laws is established. These laws are still explicit
hypotheses. They correspond to the unique-neighbour and path cases of
Lemma 8.6 and the facial seven-triangle case of Lemma 8.5 in the pinned paper;
their computational classifications have not been imported as assumptions.
The radius-five degree bound is available for the full joint views.

Replay `lake build kernelRuleFanSevenCluster`. The
[receipt](rule-fan-seven-cluster-measurements.json) records the eight-root
audit. The existing shared diamond profile and classical configuration 7
remain in the initial fan reduction; the full D3009 repair remains an
explicit premise. No new repair certificate or coverage entry is removed.
