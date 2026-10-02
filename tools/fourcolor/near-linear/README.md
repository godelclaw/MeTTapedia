# Near-linear Four Colour catalogue bridges

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
directly in the graph-backed minimality regime. The remaining exterior
embedding hypotheses must still be established there; the two minimality
definitions are not identified implicitly. Zero-charge classification and
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
exterior embedding and closure still need their own geometric bridge.

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

This closes the starting-witness obligation. Applying the finite D1774 repair
still requires justified exterior embedding and closure, including treatment
of boundary identifications. The reference consumer asks for Birkhoff ring
and pentagonal conditions; these must be supplied from the actual geometry,
or replaced by sufficient local hypotheses in a direct consumer. Classification
from final charge, geometric supply and global coverage remain open.

Replay with `lake build kernelMinimalSingletonContract`. The twelve-root audit
checks 24,706 dependency declarations and permits only standard axioms. It
excludes complete Four Colour endpoints, original configuration ranks, the
D1774 finite repair and the reference minimal contract-colouring theorem.
The new modules add no enumeration or colouring certificate. Coverage remains
633 entries and the complete assembly retains 629 original configuration
certificates. See
[minimal-singleton-contract-measurements.json](minimal-singleton-contract-measurements.json).
