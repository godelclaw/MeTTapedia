# Classical Four Colour sources and compression baseline

The [actual-occurrence receipt](two-diamond-occurrence-measurements.json)
connects the shared-tip reduction to a supplied exact vertex shore of an
actual source graph. It proves a twelve-vertex decrease, preservation of
the required map class and reconstruction back to the source. The generic
reassembly adapter retains every vertex, edge pair and rotation; the same
adapter transports supplied colourings pointwise. The twelve-root audit
permits only configuration 6's retained base in repair and excludes complete
colouring endpoints. An exact occurrence excludes a vertex-minimal
counterexample, but the theorem does not yet derive that occurrence from a
face pattern or supply coverage. Counts remain 633 coverage entries and
629 original configuration certificates.

The [boundary-hub reconstruction receipt](two-diamond-hub-measurements.json)
records the exact removal of the shared-tip disk's exterior-closure hypothesis.
The actual twenty-vertex disk is replaced by its eight-cycle, losing twelve
vertices and preserving the spherical cubic connected bridgeless class.
A supplied smaller colouring lifts to an ordered hub; reference Kempe repair
selects compatible choices; exact readback produces a genuine exterior
colouring. The exterior may be disconnected and may change colour.
The generic closed-observation gluing law is consumed by this reconstruction.
Geometry and transport exclude all configuration certificates; repair retains
configuration 6's base. No further original certificate or coverage entry is
removed. Earlier receipts below record the hypotheses at their checkpoints.

Replay the local kernel audit with
`lake build MettapediaFourColor.TwoDiamondHubAudit` in the integration package.
Because the generalized `SourceTait` helpers also serve the complete assembly,
the checkpoint additionally replays `kernelAdapters` and `kernelComplete`.

The latest [shared-tip double-diamond receipt](two-diamond-measurements.json)
records exact kernel semantics for configurations 3 and 6 and the repair
transfer from 6 to 3. The complete audit now retains 629 original certificates
and all 633 coverage configurations. No new rank table is added.

`python3 tools/fourcolor/classical/two_diamond_shared_tip_probe.py --check`
replays the original construction programs, whole-graph colourings, joint tip
choices and normalized Kempe closure. Dropping shared-tip agreement falsely
accepts 246 and 672 boundary assignments in the two members. This replay is
program evidence; the complete graph/ring correspondence, witness reconstruction,
one proper rejected boundary, and actual certificate replacement have separate
kernel proofs. Historical receipts retain their checkpoint counts.

The [shared-tip disk-to-cycle receipt](two-diamond-cycle-measurements.json)
records a further geometric step: replace the actual twenty-vertex cubic
disk by an eight-cycle with equal ordered boundary returns and Euler mass.
Kernel proofs preserve the spherical cubic connected bridgeless map class
in every fixed exterior and count all twelve removed vertices. The same joint
witness supplies the GSLT construction and physical disk colouring.
Colouring reconstruction still requires exterior Kempe closure; the audit
requires the retained configuration 6 base in repair and excludes every
colour certificate from pure geometry and joint construction.

```sh
python3 tools/fourcolor/classical/two_diamond_cycle_probe.py --check
```

This independent replay checks 48 seam cases, including 24 spherical cases
and 16 spherical cases with disconnected exteriors. For the literal
eight-cycle exterior, all 258 proper colourings repair in at most two physical
component switches: 114 extend directly, 126 need one switch and 18 need two.
This is program evidence for that example, not a kernel theorem about repair
depth or closure of arbitrary exteriors. Actual occurrence recognition and
geometric coverage remain open. This step removes no further certificate
dependency or coverage entry; the complete assembly remains at 629 and 633.

The same replay now checks 128 orientation/seam choices for an exterior made
of two disjoint two-vertex trees. Two choices give simple spherical cubic
bridgeless 24-vertex maps of girth five, with twelve pentagons and two hexagons.
Thus exterior connectivity does not follow from these ambient hypotheses.
For the first example, all 8,388,607 vertex bipartitions are also checked:
there is no cyclic cut below five, and each of the twelve cyclic five-cuts
has a five-vertex shore. These are the cut conditions used by
`CubicDualInternallySixConnected`; the result remains independent program
evidence, with no claimed kernel theorem or decoder bridge.
All 144 proper colourings of this exterior also pass the proposed capping
test: a degree-eight boundary vertex conserves the joint edge field, and
face-potential integration recovers every edge colour and the positively
ordered mirrored-reference ring trace. This is a bounded test of the next
closure adapter, not a proof of that adapter at arbitrary size.

`MettapediaFourColor.SourceTaitInverseAudit` separately checks exact transport
from conserved edge fields to reference face colourings, uniqueness up to a
common shift, and the edge-preserving round trip on the smaller diamond map.
The latter retains its exterior, cycle and joint seam witnesses. All these
roots exclude configuration colour certificates and complete Four Colour
endpoints. Exterior closure, new occurrence recognition and catalogue coverage
remain outside this representation result.
The [transport measurements](source-tait-inverse-measurements.json) record
the nine-root, 20,634-declaration audit, both build gates and the extended
program replay. The older disk-replacement receipt retains its historical
probe hashes and now names their source revision explicitly.

The [proof-plan guide](../../../papers/benxiv/fourcolor-compositional/README.md)
connects these source and measurement records to the compositional argument
and its current research questions.

The classical baseline is the 633 configurations and discharging argument of
Neil Robertson, Daniel Sanders, Paul Seymour and Robin Thomas, *The four-colour
theorem*, Journal of Combinatorial Theory B 70 (1997), 2–44. Georges Gonthier and
Benjamin Werner's Coq/Rocq development is the formal reference.

The source survey found existing Lean ports. This integration reuses Emery's
port, replays its complete reference theorem, and checks a separate
compositional assembly with shared discharging proofs. The complete endpoints
and their measurement scope are described below.

| Source | Pinned revision | Declared licence | Role |
| --- | --- | --- | --- |
| [Rocq fourcolor](https://github.com/rocq-community/fourcolor) | `c1d6b1cd5288bea4b067aac13cdde3c18dffe018` | CeCILL-B | Reference construction programs and complete proof |
| [Chris Emery's Lean port](https://github.com/corun1024/4ct) | `3db71e0a786a1f19be04c5266fe3d06fed216885` | MIT, including the attribution notice in LICENSE | Pinned dependency of the integration package; Lean 4.34.0-rc2 |
| [Robert D. Barish's Lean port](https://github.com/RBarish-UTokyo/FourColorTheorem-Lean4) | `20fa34599f5189dd569d96dd22f306c94ab1c446` | Apache-2.0 with NOTICE and upstream CeCILL-B text | Independent comparison; Lean 4.35.0-rc2 |

Both Lean repositories claim complete proofs with only `propext`,
`Classical.choice` and `Quot.sound`. Emery's pinned reference has been replayed
and independently audited here; Barish's port was a source comparison.
The original pilot, complete reference replay and compositional adapter gates
are recorded separately. The ports' existing uniform certificate techniques
are part of the baseline, not new compression attributable to this development.

Other surveyed projects include
[tangentproofs/fourcolor-lean](https://github.com/tangentproofs/fourcolor-lean)
(`b2bcd36c7e50848f000af423f23151309c075638`, archived with open proofs),
[WaterKing201030/FourColorTheoremLean](https://github.com/WaterKing201030/FourColorTheoremLean)
(`c36f6d8120024ddf91e4ea4033bfa2842bcecbb8`, an unfinished top-level theorem), and
[TonalidadeHidrica/FourColorTheorem](https://github.com/TonalidadeHidrica/FourColorTheorem)
(`1c0cb61da4f953b29097b12ed1737b09890c7080`, preliminary structures).

The [padded-cap receipt](padded-cap-measurements.json) records a uniform strict
reduction for every even `m ≥ 2`: the `8m`-vertex cap is replaced by a
`2m`-cycle, preserving the map class and reconstructing every smaller
colouring with the exterior fixed. The geometric replacement is proved
at odd widths too; their colouring lift still has a nonconstant guard.
GSLT and exact graph-representation consumers are audited. The
[colour replay](padded-cap-probe.json) checks 87,348 nonconstant colourings
and 24 constant even-width colourings. The
[geometry replay](padded-cap-geometry-probe.json) checks widths 2 through 20
and an all-five/six 96→60 reconstruction. GP(2,0)'s guarded 80→50 example
remains available. The later odd-width repair and face-derived recognition
are recorded below; broader geometric coverage remains open.

The subsequent [all-width physical repair](padded-cap-physical-measurements.json)
handles constant boundary words by a joint exterior/cycle switch. Actual
[face-trace recognition](padded-cap-recognition-measurements.json) constructs
the cap shore from its faces, an injective vertex trace and short seam faces.
The [exterior-connectivity receipt](padded-cap-exterior-measurements.json) now
removes the separate connected-exterior hypothesis from that face-derived
strict reduction. One or two actual exterior edges join consecutive ports;
boundary completeness and ambient connectivity exclude other components.
The [independent replay](padded-cap-exterior-probe.json) checks 956 such arcs,
including both five- and six-sided seam faces. The
[pentagonal recognition receipt](pentagonal-padded-cap-measurements.json)
now removes the separate vertex-injection condition at sector count five.
Actual face operations realize the forty-vertex partial diagram, and a
compact joint-route certificate proves distinctness from ambient girth.
Normal form supplies girth. The actual face-pattern consumer then replaces
the cap by a ten-cycle and reconstructs all smaller colourings, with thirty
fewer vertices in the whole map. It supplies neither local injectivity nor
exterior connectivity as hypotheses. The certificate checks geometry;
the shared all-width colouring law is reused. Separation at other widths
and global coverage remain open, and the complete assembly still retains 633
configurations and 629 original certificate dependencies.

```sh
python3 tools/fourcolor/classical/pentagonal_padded_cap_probe.py
```

This independent replay checks the decoded internal reversals and ports,
cyclic translation and every translated collision/phase route. It checks
936 normalized cases and 4,680 translated cases, with at most twelve
simultaneous operations. The flat route data comprises eight blocks and
960 four-byte records, including 24 unused equal-vertex rows. No new
colouring certificate or coverage reduction is credited.

The [combined occurrence replay](residual-coverage-probe.json) inspects the
four Goldberg controls and their explicit dual-and-truncate maps. Seven
contain one of the current diamond, padded-cap or three-row tube patterns.
The 240-vertex residual has none, although all forty alternating dart-phase
orbits are simple. Their widths are eighteen, and their strips have one or
two rows. The replay checks a shifted free-wire replacement giving a
168-vertex connected bridgeless spherical cubic map, a proper colouring of
its 252 edges, and reconstruction of all 360 original edges with every
exterior dart colour retained. It also inspects all 1,332 simple dual
circuits of lengths three through five: the twelve cyclic circuits have
five edges and a five-vertex shore. These finite diagnostics are not kernel
certificates of the universal cut or minimality hypotheses.

The [two-row colouring receipt](two-row-wiring-measurements.json) records
the independent Lean component: at every width `k ≥ 3`, two rings accept
every nonzero word and its one-port shift, and compatible exterior witnesses
glue into an actual closed colouring. The
[new geometry receipt](two-row-free-wire-measurements.json) records the
strict reduction at every width `k ≥ 3`: two internally connected exterior
shores and an opposite boundary first return suffice to remove both rows,
with exactly `4k` fewer vertices and no new exterior vertices. The actual
replacement stays connected, bridgeless, spherical and cubic. Every smaller
colouring reconstructs with all exterior dart colours retained. The
embedded-slab consumer excludes these rows in a minimal counterexample.
The audit checks eleven roots independently of complete Four Colour
endpoints and finite tube stabilization.

The [domain replay](two-row-free-wire-domain.json) verifies these precise
conditions against the stored 240-vertex residual: all 216 row-rotation
steps, two 84-vertex shores and all 36 first returns. It reuses the saved
colourings and occurrence record; it does not repeat the census. The
[short-face recognition receipt](two-row-recognition-measurements.json)
records the next kernel-checked bridge: an actual two-row slab with five-
or six-dart end faces derives the two connected shores and opposite
boundary return. The strict reduction and minimality consumers retain
neither of those as separate hypotheses.

The [short-face replay](two-row-short-faces.json) checks the implication
at all twenty two-row starts in the stored residual: 720 end-face paths,
no earlier boundary hit. Broader geometric supply and global coverage
remain open. No additional catalogue or certificate dependency is removed.

The [constructed-growth receipt](two-row-growth-measurements.json) records
the next consumer: one recognized row with a hexagonal seam constructs its
actual successor and the literal two-row slab, with identity seam matching.
In the all-five/six-face class, at every width `k ≥ 3`, its short end faces
derive both exterior conditions and supply the strict reduction. Exactly
`4k` vertices are removed, with all exterior dart colours retained in
reconstruction. A minimal counterexample therefore meets a pentagonal
seam at every recognized starting row: zero extensions, and recognized
chains have length at most one. The raw alternating-cycle recognizer
locates an actual outgoing cycle dart on that pentagon. The ten-root
audit excludes complete classical endpoints and finite tube stabilization.
The [alignment replay](two-row-growth.json) checks 2,160 collar-star dart
positions and 360 identity seam labels at all twenty saved starts. It is
independent program evidence, not a kernel occurrence certificate.
Initial cycle supply, nonsimple closing lobes and pentagonal-stop reduction
remain open; the complete assembly still retains 633 configurations and
629 original configuration certificates.

```sh
python3 tools/fourcolor/classical/residual_coverage_probe.py
python3 tools/fourcolor/classical/two_row_free_wire_domain.py
python3 tools/fourcolor/classical/two_row_short_faces.py
python3 tools/fourcolor/classical/two_row_growth.py
```

The [enlarged supply replay](family-supply-probe.json) tests the current
diamond, face-derived padded-cap and hexagonal-seam simple-cycle union on
44 explicit rotations. The [new fixtures](family-supply-fixtures.json)
retain eighteen isolated-pentagon rotations generated at orders 60–80,
the generator source hash and command. Each is also dual-and-truncated;
the eight larger saved controls are included. All local roots and all
dart/phase orbits are inspected, without a cycle-length cutoff.

Thirty-nine maps have a qualifying occurrence. Five transformed maps of
orders 222–240 do not: four have no simple complete alternating orbit,
and one has six simple rows all stopping at pentagons. Explicit proper
colourings show that these are colourable residuals. The replay checks
6,396 simple dual circuits of lengths three through five and finds only
the sixty trivial pentagonal cyclic circuits. Shortest extracted lobes
have lengths 31, 33 or 35 and split the twelve pentagons as five and seven.
This is independent finite evidence against unconditional supply by this
union, not a kernel normal-form or minimal-counterexample certificate.
The [receipt](family-supply-measurements.json) records the exact scope.

```sh
python3 tools/fourcolor/classical/family_supply_probe.py
```

The [dual-and-truncate replay](dual-truncate-colouring.json) checks one
vertex-to-edge colouring law on all five residuals above. A proper
three-vertex source colouring gives expanded star colours `a+b, b, a`.
The [uniform Lean theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateColoring.lean)
constructs the actual rotation and target edge colouring; its
[GSLT consumer](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateConstructionGSLT.lean)
supplies compatible witnesses on every complete sweep and through exact
representation adapters. The
[source words](dual-truncate-colouring-fixtures.json) and concrete adapters
are independently replayed. The
[compact input certificates](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateResidualCertificates.lean)
now check all five saved source/target rotations, proper source words and
exact representation adapters in the kernel. One shared decoder verifies
edge fibres and the supplied neighbour order. All target colourings and
GSLT route witnesses come through the uniform law, without a stored target
colouring. The
[input receipt](dual-truncate-input-measurements.json) records this audit,
source identities and kernel costs separately from the
[uniform-law receipt](dual-truncate-colouring-measurements.json). The source
colouring hypothesis remains explicit for the general family, and no
coverage entry is removed.

```sh
python3 tools/fourcolor/classical/dual_truncate_colouring.py
python3 tools/fourcolor/classical/generate_dual_truncate_certificates.py --check
```

The emitter is untrusted. Little-endian data pages preserve the original
cyclic neighbour rows, source colour words, vertex inverses and cyclic
offsets. The Lean declarations validate every mathematical condition used
by the reconstruction. Their decoder and consumer audit uses only the
standard axioms. Input hashes bind the replay to its saved rotations; the
JSON parser and emitter are not proof-trust assumptions.

## Target-only inverse recognition

The [inverse recognition receipt](dual-truncate-inverse-measurements.json)
records the uniform Lean recovery from marked target facial corners. The
actual target frame recovers a source edge involution and face permutation;
source vertices are rotation orbits. Literal reconstruction preserves target
alpha, rho and vertex identity. Unmarked hexagons give source cubicity;
spherical Euler, connectivity and a threefold vertex decrease are derived.
The cube consumer uses the inverse in genuine colouring reconstruction and
every complete GSLT sweep. The 24-root audit excludes old target-colouring
shortcuts, source colour words and complete classical endpoints.

```sh
python3 tools/fourcolor/classical/dual_truncate_inverse_probe.py
```

The [program replay](dual-truncate-inverse-probe.json) recognizes five saved
residual targets without reading their saved sources, then replays every dart
of each reconstructed target. Cube fixture generation is separate from the
target-only recognizer. All six examples replay 3,528 darts. The recovered
source rotations and marked face indices are retained for subsequent source-domain
checks. The dodecahedron diagnostic is rejected: its mandatory nonhexagonal
faces overlap. The replay is independent evidence, not a kernel certificate
for the five larger source cut domains.

This face-cover mechanism follows classical leapfrog recognition;
[Fowler and Pisanski](https://doi.org/10.1039/FT9949002865) give its Clar-type
interpretation. The general source-colouring bridge below derives its domain
from target connectivity and size. Occurrence coverage remains open. No
additional catalogue saving or unconditional Tait-to-Tait reduction is claimed.

## Recovered source cut domain

The [source-domain receipt](dual-truncate-source-domain-measurements.json)
records an actual 18-vertex target whose nonhexagonal faces determine a cover
and recover the triangular prism. Its connected spherical cubic source has a
cyclic three-edge cut. Exact graph-isomorphism transport makes this an
obstruction on the recovered graph, rather than just its original labels.
The existing connected-pair argument nevertheless supplies source choices,
actual target colours and every complete GSLT sweep. The 14-root audit
excludes source colour words, the cyclic-four supplier and classical
Four Colour endpoints.

```sh
python3 tools/fourcolor/classical/dual_truncate_source_domain_probe.py --check
```

The replay constructs a fixture separately, then gives the recognizer only
the actual target rotation. It verifies the recovered cyclic-three cut and
finds twelve suitable coupled pair/root choices. Source vertex-connectivity
three is independently checked. The source colouring itself is supplied by
the Lean structural proof. The target has two triangles, three squares and
six hexagons; this is not a pentagonal/hexagonal normal-form obstruction.
The broad inverse domain does not force cyclic-four source connectivity.
The broader source supplier below discharges the colouring bridge on the
stated larger target domain; occurrence coverage remains open. No additional
catalogue saving is claimed.

## Uniform subcubic source bridge

The [uniform source receipt](subcubic-source-measurements.json) records the
completed subcubic three-vertex-colouring bridge. Its kernel theorem covers
every finite simple graph of degree at most three with no four-clique, using
low-degree insertion and two coupled path-closing laws. The relative law
copies one exterior colour to an internally supported seed and preserves
all exterior values. Actual path selection and insertion orders are proved;
no table of source colour words is consumed.

`DualTruncateBrooksSource` derives the recovered source domain from target
connectivity and size greater than twelve, then reconstructs target Tait
colours and every complete GSLT sweep. `DualTruncateBrooksExample` consumes
this same law on the prism and cube expansions. The 24-root audit checks
12,375 declarations and excludes their earlier source-specific suppliers,
colour-word tables and complete classical endpoints. The four-clique
exception is separately kernel-checked.

```sh
python3 tools/fourcolor/classical/subcubic_source_probe.py
```

This independent constructive replay examines all 33,868 labelled simple
graphs through six vertices: 12,912 are subcubic, 36 contain a four-clique,
and the remaining 12,876 receive proper colourings. Larger prism families
and a disconnected regular example exercise both coupled branches and
separate-region composition. The output contains no source colouring table.
The general kernel theorem is stronger than this finite diagnostic.

Face-cover occurrence, the small exceptional target domain, and a strict
Tait-to-Tait reduction remain separate. No coverage configuration or original
configuration certificate is removed; counts remain 633 and 629.

## Exact open-patch corner elimination

The [patch receipt](dual-truncate-open-patch-measurements.json) records an
exact colouring-witness equivalence for dual-and-truncate patches at every
size. Keep the polygon-corner colours and reconstruct each cross-edge
colour from its two adjacent polygon colours. The shared balance equation
retains agreement at both cross endpoints. No source vertex-colouring
supplier is needed by this general reconstruction.

The selected region is closed under source edge reversal. The
[actual edge observer](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateOpenPatch.lean)
proves exactly which polygon colours an exterior sees. Compatible summaries
reconstruct genuine Tait colourings with every exterior edge fixed,
including cut edges. Both inverse laws and the equality of colouring counts
are proved. The reconstructed colouring supplies every complete faithful
GSLT construction sweep.

The [cube patch](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateOpenPatchExample.lean)
has fourteen selected target vertices and ten exterior vertices. Its summary
carries ten internal polygon-colour variables, restoring seven forced cross
variables among the original seventeen interior edges. A small diagnostic
corner word supplies a genuine exterior-preserving witness with a nonzero
cyclic difference. The general law uses no such word. The
[collapse theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/DualTruncateCornerCoherence.lean)
says precisely when a retained witness can be represented by source vertex
colours: all corners at each source vertex must agree. Genuine cyclic vertex
rotations make the zero-difference criterion equivalent.

```sh
python3 tools/fourcolor/classical/dual_truncate_open_patch_probe.py --check
```

The [independent replay](dual-truncate-open-patch-probe.json) exhausts all
336 source vertex subsets of the cube, triangular prism and four-clique.
It projects and reconstructs 353,283 local witnesses and 38,790 completions
of fixed exteriors. All retained corner states match the actual witnesses.
On the cube's three-cell patch, paired boundary profiles admit 192 actual
witnesses but only 144 source-compatible witnesses; their tested supports
are equal. A particular fixed exterior admits seven witnesses, two with
varying corners. The four-clique expansion separately has six Tait
colourings and no three-vertex source colouring. This latter observation
is a program diagnostic, not a kernel-certified target obstruction.

This compresses colouring variables while retaining exact reconstruction.
It proves neither a smaller embedded graph replacement nor a coverage
theorem, and removes no classical configuration or certificate. The next
structural task is to prove when actual geometry forces or permits repair
of the cyclic differences while preserving the required visible choices.

## Exact separated-forest source choices

The [forest receipt](dual-truncate-forest-measurements.json) records a
uniform geometric answer to that collapse question. In a simple cubic
source with cyclic vertex rotations, select an induced forest such that
each exterior source vertex has at most one selected neighbour. The
supplied exterior is locally Tait and its visible polygon corners agree
with one source value at each exterior source vertex. Selected source
values are not prescribed. Every genuine extension then has coherent
corners and corresponds to exactly one proper source assignment fixing
those exterior values. The inverse map reconstructs the same target
colouring, so support, witnesses and counts are all preserved.

The proof uses a general finite-forest lemma. Nonzero cyclic differences
agree across source edges and sum to zero at each vertex, preventing a
leaf in their support. Separation exposes every exterior source corner,
so the paired observations force differences there to zero. The remaining
support lies in the selected forest and must be empty. No bound on forest
size and no complete source-colouring supplier enter the family proof.

The kernel consumer has ten selected target vertices, fourteen exterior
vertices and eleven internal edge variables: six polygon variables and
five forced cross variables. Only two source variables are retained,
with exactly three compatible assignments. Selected input values are zero;
the actual exterior alone is supplied. The inverse maps and every complete
GSLT construction sweep are audited together with the uniform law.

```sh
python3 tools/fourcolor/classical/dual_truncate_forest_probe.py --check
```

The [independent replay](dual-truncate-forest-probe.json) checks 56 qualifying
patches and all 352 extensions of their supplied exteriors. It includes
every qualifying source subset of the cube and triangular prism, longer
paths in four circular prisms, and five patches in the sixty-vertex
dodecahedral expansion. The largest tested path retains ten source
variables for a forty-two-vertex target patch. Larger fixtures remain
program checks, separate from the kernel-certified two-cell consumer.
The earlier three-cell cube example is excluded: an exterior source vertex
has two selected neighbours, and the broader corner relation is necessary
to retain all its witnesses.

This proves exact compression of the colouring constraints on the stated
family. It does not yet construct a smaller embedded replacement or show
that every target contains such a patch. No configuration or original
certificate is removed from the complete classical assembly.

## Two-cell joint seam obstruction

The follow-up [two-cell receipt](two-cell-replacement-measurements.json)
records the uniform joint-choice condition and a kernel-checked actual
sixty-vertex exterior which violates it. The ten-vertex patch has eight
ordered cut ports; the literal eight-cycle accepts its supplied word.
The original map is spherical, cubic, connected and bridgeless, with only
pentagonal and hexagonal faces. No extension of this fixed exterior exists.

```sh
python3 tools/fourcolor/classical/two_cell_replacement_probe.py --check
```

This [independent replay](two-cell-replacement-probe.json) closes the cycle
replacement into a fifty-eight-vertex map and checks its geometry and
actual colouring. Those closed replacement claims are program checks,
distinct from the kernel's original-map and literal-cycle claims. It also
enumerates one eight-cycle, 132 rooted plane cubic trees and fourteen
noncrossing wire pairings; none has its entire boundary support contained
in the original patch's support. This is a bounded list, not all smaller
pieces. Under paired observations some candidates have empty support, so
their vacuous inclusion is not a successful reduction.

The replay retains 213 abstract bad colour orbits consistent with the
tested parity, relabelling and noncrossing component-union conditions.
No physical exterior realizing that complete model is supplied. Bare
matching closure therefore does not provide a universal repair argument;
actual geometric input, a different operation or exterior recolouring is
still needed. No catalogue or certificate saving is credited.

## Successful physical two-cell repair

The [repair receipt](two-cell-physical-repair-measurements.json) records a
successful actual history for the same sixty-vertex example. Lean certifies
the saturated seventeen-edge red-purple region and its preservation of the
fifty-vertex exterior, changes the joint cut word to `BBRRBBPP`, and derives
the two compatible interior choices. Reconstruction supplies an original-map
Tait colouring and compatible witnesses for every complete GSLT sweep.
The audit checks 28 roots and excludes both the classical endpoint and a
complete source-colouring certificate. Its three uniform laws contain no
finite graph data.

```sh
python3 tools/fourcolor/classical/two_cell_physical_repair_probe.py --check
```

The [independent component replay](two-cell-physical-repair-probe.json)
checks all eight port-touching one-component swaps; four reconstruct through
the patch. It also certifies the selected region's sixteen exterior vertices
and seventeen-edge path. Lean checks saturation and exact reconstruction;
component connectivity and the complete eight-swap census are program
checks. This is an actual successful choice after a fixed-exterior failure,
not a guarantee for every exterior or Kempe class. It introduces no smaller
embedded operation and removes no catalogue entry or certificate dependency.

## Uniform source transport and coupled reconstruction

The [family receipt](two-cell-source-repair-measurements.json) records exact
partial-source-to-physical-edge transport and a shared two-insertion
constructor. The constructor uses actual incidences, a proper partial
exterior and a separated source pin. It supplies the two coupled choices;
a complete source colouring is not an input. The physical mask is derived
uniformly from the source region, and successive steps retain the preceding
field's exterior observations.

Three kernel consumers reconstruct targets with 18, 60 and 60 vertices.
The last uses two successive switches, with the second region checked in
the first step's state. The audit checks 28 roots and excludes complete
colour-word suppliers and classical endpoints; uniform laws contain no
finite graph data. The prism consumer is outside the pentagonal/hexagonal
subclass. The [independent replay](two-cell-source-repair-probe.json) checks
the physical edge effects and actual component connectivity separately.

```sh
python3 tools/fourcolor/classical/two_cell_source_repair_probe.py --check
```

The replay also checks 1,298 canonical blocked partial source exteriors on
five small embedded cubic sources, using up to the first three source edges
with distinct exterior pins. Perimeter order is read from the actual patch.
All 302 alternating-perimeter cases have a separating third-colour source
component. Of 996 adjacent-perimeter cases, 354 fail that separation test
and 78 admit no single source-component repair. One such case has the
recorded two-step repair. These finite counts do not establish universal
availability or exclude other physical target-edge operations. No strict
smaller embedded operation or coverage saving is claimed; the catalogue
and original-certificate counts remain 633 and 629.

## Geometric availability at alternating source pins

The [uniform theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/SourceAlternatingBoundaryRepair.lean)
derives a separating third-colour source component from actual spherical
cubic geometry and four alternating observations in retained facial
first-return order. The deleted shore and the full face dual are connected,
and opposite darts have distinct faces. Properly coloured paths using the
two different third-colour pairs are edge-disjoint; the spherical boundary
separation theorem prevents both crossing connections. The constructed
component is a saturated source region, and its switch is consumed by the
joint insertion constructor, exact physical edge transport and GSLT sweep
semantics. Neither a successful component nor a full source colouring is
supplied as an input.

```sh
python3 tools/fourcolor/classical/source_alternating_boundary_probe.py --check
```

The [receipt](source-alternating-boundary-measurements.json) separates the
kernel implication from the [finite replay](source-alternating-boundary-probe.json).
The replay computes capped retained facial steps and their first return,
compares that order with the actual expanded patch perimeter, and checks
geometry and reconstruction for all 302 alternating partial exteriors on
five small sources. Both repair branches occur: 251 first-pin and 51
second-pin repairs. Geometry of these finite instances remains program
evidence; no kernel fixture adapter is asserted here.

This advances availability on the alternating domain. The 996 adjacent
controls remain outside its hypotheses. A strictly smaller embedded
operation and occurrence coverage are still needed for a catalogue saving.
The catalogue and original-certificate counts remain 633 and 629.

## Adjacent source pairs with a derived order

The [geometric adapter](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/AdjacentSourceBoundaryRepair.lean)
derives the alternating repair's actual port order from local cubic
rotations and connected planar complementary shores. Four distinct
exterior pins exhaust the boundary. The retained first-return order is
the inverse of the deleted one; a shared reflection preserves the two
insertion pairs. The full facial dual and deleted-pair connectedness are
also derived. Whole source and target reconstruction, exact physical
exterior agreement and faithful GSLT witnesses consume this adapter.

```sh
python3 tools/fourcolor/classical/adjacent_source_boundary_probe.py --check
```

The [receipt](adjacent-source-boundary-measurements.json) records thirteen
audited roots using only the standard three axioms, with complete-colouring
suppliers, classical endpoints and finite fixtures excluded. The
[independent replay](adjacent-source-boundary-probe.json) checks both shore
connections and both actual first-return permutations on thirteen pairs
from five sources. These concrete geometric instances remain program
checks; the uniform geometric adapter and its consumers are kernel-checked.
Colouring existence, counts and execution histories are not identified.
Strict reduction and occurrence coverage remain separate. This tranche
removes no catalogue entries or original configuration certificates.

## Actual 03|12 source splice and joint reconstruction

`AdjacentSourceSplice` deletes two adjacent source vertices and pairs their
exposed half-darts across the two omitted vertices. The literal splice
retains parallel edges, preserves spherical cubic geometry and gives a
bridgeless spherical cubic expanded target with exactly six fewer vertices.
A supplied proper smaller source three-colouring restricts to a proper old
exterior. Its new seam inequalities force either direct coupled insertion
or the alternating pattern handled by embedded separation. Whole original
source and target witnesses, exact physical exterior agreement and every
complete faithful GSLT sweep reconstruct from that input.

```sh
python3 tools/fourcolor/classical/adjacent_source_splice_probe.py --check
```

The [receipt](adjacent-source-splice-measurements.json) records seventeen
kernel-audited roots and their exact dependency requirements. Classical
endpoints, whole-colouring suppliers and finite graph fixtures are excluded.
The [independent replay](adjacent-source-splice-probe.json) checks literal
smaller source and target face cycles, parallel seams and exact cardinalities
on thirteen interfaces from five sources. It reconstructs all 2,680 smaller
source witnesses normalized at the first pin: 2,076 direct insertions,
502 first-pin repairs and 102 second-pin repairs. Finite geometric instances
remain program checks. The uniform theorem accepts an explicit smaller
source witness; it does not establish that every smaller target Tait
colouring has such a preimage. Counts, all recolouring histories, recursive
domain closure and global coverage remain separate. No further catalogue
entry or original configuration certificate is removed.

## Arbitrary target witnesses on a spanning-face domain

`DualTruncateSpanningFace` turns every target Tait witness into a genuine
source three-colouring when the connected spherical source has two-sided
faces, cyclic cubic rotations and one face touching every vertex. Its
cross-edge field telescopes on each face. `RotationClosedEdgePotential`
uses the existing spherical cycle-space theorem to recover every literal
edge difference, including parallel edges. The spanning face fixes one
joint phase, so the reconstructed source values are all nonzero.
Re-expansion preserves all cross-edge observations; polygon colours may
change. This calibration theorem alone supplies no physical history.

`AdjacentSourceSpanningFaceReduction` consumes this witness in the actual
six-vertex splice reduction, whole-map reconstruction and faithful GSLT
sweeps. `DualTruncateSpanningFaceExample` separately recognizes the actual
theta multigraph domain and calibrates every target input. The generic law
does not depend on that example. The [receipt](adjacent-source-spanning-face-measurements.json)
records twenty-one audited roots, excludes complete classical endpoints,
Brooks suppliers and source colour words, and checks fixture independence.

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceAudit
```

From the repository root:

```sh
python3 tools/fourcolor/classical/adjacent_source_spanning_face_probe.py --check
```

The independent replay recognizes six spanning-face interfaces among the
ten previous smaller prism outputs and calibrates all 1,488 normalized
target witnesses there. It verifies actual incidence, complete source
properness, cross-edge equality and the induced coherent target witness.
The four interfaces without such a face are outside this mechanism.
The finite splice recognitions remain program evidence; the kernel theta
fixture checks the geometric domain and calibration rather than a splice.
The ladder and prism-rung consumers below now establish one unbounded
geometric family and recursive ladder closure. Broader occurrence coverage
remains open. Catalogue and original-certificate counts remain 633 and 629.

## Physical face-phase normalization and strict reconstruction

`DualTruncateFacePhaseKempe` proves that an actual target Tait witness and
a proper source choice with the same literal cross field differ by a
constant phase on each face. A nonzero phase selects a saturated polygon
region for its colour pair. Three region stages clear all phases, preserving
every cross edge and actual intermediate Tait properness. Each stage can
contain several connected Kempe components; no constant bound on the number
of individual component swaps is asserted.

`DualTruncateFacePhaseGSLT` retains the common source choice, pair labels,
intermediate fields and exact physical update. Cross-field conservation
composes along every authored route. `AdjacentSourceFacePhaseReduction`
uses spanning-face calibration to initialize that history from an arbitrary
smaller target input, extracts the repaired terminal source witness, and
consumes it in actual coupled splice reconstruction and construction sweeps.
Its operational theorem includes the legal history, target map class,
six-vertex decrease and full original Tait witness.

The [receipt](adjacent-source-face-phase-measurements.json) records thirty-two
audited roots and one nontrivial theta repair with all parallel edge identities
retained. The uniform proof has no dependency on that finite fixture, complete
classical endpoints, source colour tables or generic Brooks suppliers.

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseAudit
```

From the repository root:

```sh
python3 tools/fourcolor/classical/adjacent_source_face_phase_probe.py --check
```

Independent replay checks all 1,488 inputs on the six recognized spanning-face
splice outputs, including 1,350 nontrivial repairs. All intermediate fields
are proper; all original cross colours survive; the final field equals the
shared source image. The region masks are independently decomposed into
actual bichromatic components: up to six occur per history in this census.
The earlier finite splice geometries remain program evidence. The all-width
prism-rung consumer below supplies one kernel-certified geometric family;
broader coverage remains open.
No further configuration or certificate dependency is removed.

## A complete recursive ladder family

`CappedLadderRotation` computes the actual faces at every width `m ≥ 1`,
including the distinct parallel end edges, and proves the spherical class,
connectedness, two-sidedness and a spanning face. `CappedLadderEndReduction`
deletes an end vertex pair and sews exactly its exposed rail darts. The
retained-dart equivalence identifies this operation with the preceding ladder;
intact edges and rotations stay fixed. The expanded graph loses six vertices.

Every arbitrary smaller target Tait witness first undergoes the physical
face-phase repair. All initial cross colours survive; polygon colours can
change. Reconstruction uses the actual terminal source witness and preserves
its whole retained-star view. `CappedLadderFamilyGSLT` recursively constructs
all widths from the two-vertex, three-edge base, with compatible witnesses
at every step. The reverse paths terminate by their decreasing width rank.
The reverse witness paths concern these constructed compatible states;
the theorem does not fix an arbitrary larger colouring along every reduction.

The [receipt](capped-ladder-measurements.json) records forty-seven audited
roots and 20,288 dependency declarations. Only the standard axioms occur;
complete colouring endpoints, generic Brooks suppliers and saved source colour
words are absent. The small base is excluded from the structural and
arbitrary-input reconstruction roots.

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.CappedLadderAudit
```

From the repository root:

```sh
python3 tools/fourcolor/classical/capped_ladder_probe.py --check
```

Independent replay checks twelve geometric widths and 468 retained-dart
sewings. Exhaustive normalized inputs at four small widths give 340 target
colourings, including 300 nontrivial physical repairs. These checks are
separate from the all-width kernel proof. Broader occurrence remains open.
This family is not yet a dependency replacement in the completed classical
assembly: 633 coverage configurations and 629 original certificate
dependencies remain.

## Actual prism-rung recognition at every width

`PrismRungCoordinates` constructs the actual simple spherical prism with two
oppositely ordered rims and literal rung edges. `PrismRungGeometry` classifies
its actual faces at every rim width `n ≥ 3`, proving connectedness, the
spherical equation and two-sided edges. `PrismRungSplice` identifies the
canonical rung deletion and four-dart sewing with the capped ladder of width
`n-1`. Its exact dart and vertex equivalences commute with incidence, edge
flips and vertex rotations. Parallel edges remain distinct throughout.

`PrismRungReduction` consumes the transported smaller geometry and connected
original exterior in the existing arbitrary-input phase repair and coupled
reconstruction. Every smaller target Tait input admits three region stages;
exactly six expanded vertices disappear. The cross field stays fixed during
normalization. Coupled insertion may switch a component in the original
exterior before restoring the two removed vertices. Complete faithful
construction sweeps receive the reconstructed colouring witnesses.

The [receipt](prism-rung-measurements.json) records thirty-four audited roots
and 24,016 dependency declarations. Complete classical endpoints, generic
Brooks suppliers, saved source colour words and finite family bases are
absent from these roots.

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.PrismRungAudit
```

From the repository root:

```sh
python3 tools/fourcolor/classical/prism_rung_probe.py --check
```

Independent replay checks 1,650 retained darts at twenty-two rim widths and
336 normalized target inputs at three small widths. There are 297 nontrivial
physical repairs and 88 original-exterior component repairs. The all-width
theorem is separate from this finite census. It supplies an exact transfer
of a shared structural argument to one actual embedded family, with no new
colour table. Broader occurrence, coverage and complete-assembly integration
remain open; no further configuration or certificate dependency is removed.

## Target colouring choices on parallel seams

The [target diagnostic](adjacent-source-target-kempe-probe.json) exhausts
2,920 target edge-colourings modulo global colour permutation on ten
triangular-prism, cube, pentagonal-prism and hexagonal-prism splice outputs.
Actual parallel edge identities are retained. The exact corner round trip
is checked for every witness, and the 284 coherent states equal the
independently enumerated source-colouring image. Every computed Kempe class
contains such an image. Saved paths lift the normalized search to literal
physical component switches, without applying global colour renamings.

```sh
python3 tools/fourcolor/classical/adjacent_source_target_kempe_probe.py --check
```

This also tests a proposed progress measure: count source vertices whose
three corner observations disagree. Six normalized states, on the two
hexagonal-prism side splices, admit no single Kempe move which strictly
decreases that count. Their saved repair paths still reach coherence.
The test therefore rejects that strict one-step measure in this domain,
while supporting investigation of joint choices and multistep repair.
These are finite program checks. No general Kempe-repair theorem, recursive
domain closure, kernel-certified fixture or catalogue reduction is claimed.

## Complete endpoints

`FourColor.CompositionalComplete.colorable_of_planeDrawing` proves
`SimpleGraph.Colorable 4` for every finite simple graph with an actual
noncrossing path drawing in the plane. The drawing supplies distinct vertex
positions and noncrossing injective edge paths; it contains no colouring or
coverage assumption. Empty and disconnected graphs and isolated vertices
are included.

For the original bridgeless spherical cubic source class,
`CompositionalComplete.supported_source_construction` supplies an exact
construction trace and compatible GSLT colouring witnesses. The companion
`supported_source_sweep` covers any complete valid vertex order. Witnesses
retain literal source vertices, edges and cyclic order. These conclusions
assert successful choices along the whole route.

The complete assembly consumes every catalogue certificate and all seven
arity proofs, with 231 independent discharging computations replaced through
semantic transport. Its audit checks each endpoint's dependencies and rejects
the original unconditional theorem and the 236 superseded declarations.
The reference theorem is audited separately. Only `propext`, `Classical.choice`
and `Quot.sound` occur in the audited declarations.

The [dependency receipt replays](dependency-artifact-measurements.json) record
source and compiled-artifact hashes for the adapters and arity-ten presentation.
Those replays reproduce the same proof artifacts; they add no compression credit.

Build instructions are in the
[integration package](../../../lean/fourcolor-classical/README.md).
`complete-assembly-measurements.json` records the source and artifact hashes,
reference replay scope, final gate times and audit results. All 633 configurations
remain. Runtime and artifact-size savings remain unclaimed.

## Data inventory

The [original source guide](https://thomas.math.gatech.edu/FC/ftpinfo.html)
documents the configuration format. Original C programs grant permission for
scholarly-research use; the downloaded configuration and rule files contain no
separate redistribution licence. This directory contains metadata and checks,
not redistributed original source files. The Rocq and Lean snapshots have the
licence notices listed above, which must accompany any reused source.

`inventory.json` records hashes and the reproducible results of
`../classical_source_inventory.py`:

* 633 connected triangulated free completions with an ordered outer ring.
* Ring sizes 6 through 14, with 137 configurations at size 14.
* 249 zero-residual headers and 384 nonzero-residual headers in the original
  data. These are header values, not independently recomputed reducibility.
* 32 published rule labels, expanded to 67 directed machine entries, including
  32 inverse entries.
* Exact agreement of all 633 construction programs, symmetry flags and
  contraction references between the pinned Rocq and Emery sources.
* Agreement of ring sizes between those programs and the original data.

The geometry checks traverse the supplied rotation systems: symmetric simple
adjacency, connectivity, an outer ring, triangular inner faces and Euler
characteristic two. These initial inventory checks do not prove reducibility,
validate discharging, or establish an isomorphism between an original free
completion and its construction program. The separate map comparison below
checks the latter correspondence at the program level.

Given the four pinned source files, reproduce the inventory with:

```sh
python3 tools/fourcolor/classical_source_inventory.py \
  --configurations unavoidable.conf --rules rules \
  --rocq-programs configurations.v --lean-programs Configurations.lean \
  --output inventory.json
```

`configuration_map_isomorphism.py` compares all 633 original free completions
with a finite-array mirror of the pinned Lean decoder. Each saved dart
bijection preserves edge reversal and cyclic order, allowing a global reversal
of orientation. The specified outer ring is preserved up to rotation and
reversal. A second verifier checks cyclic adjacency on the face quotient.
All 384 nonzero-residual contraction edge sets also match under such a
bijection. The 249 zero-residual original records supply no contraction to
compare with the reference's chosen contract.

`configuration-map-isomorphism.json` records the successful comparison of
59,664 darts, the input and decoder hashes, and the saved-witness hash. Negative
controls reject swapped dart images, reversed orientation with an unchanged
mapping, duplicate vertex images, and missing contraction edges. Every saved
witness is read back and checked again. The original data and generated
witness file are supplied separately:

```sh
python3 tools/fourcolor/classical/configuration_map_isomorphism.py \
  --configurations unavoidable.conf \
  --lean-programs lean/externals/fourcolor/FourColor/Configurations.lean \
  --lean-geometry lean/externals/fourcolor/FourColor/CfMap.lean \
  --lean-contract lean/externals/fourcolor/FourColor/CfContract.lean \
  --witnesses configuration-map-witnesses.json \
  --output configuration-map-results.json
```

This is source-fidelity evidence. Equivalence of the finite-array mirror with
the noncomputable Lean decoder is not proved by this program. The comparison
does not establish reducibility, validate discharging or remove a configuration.

## Internal templates and boundary transport

`classify_internal_templates.py` groups the original free completions by the
embedded graph induced by their internal vertices. It retains cyclic order
and permits a single global orientation reversal. The 633 configurations
have 140 internal templates, of which 90 occur more than once. Each saved
witness separately records the boundary contacts, full vertex degrees and
original contraction edges. Those data are not identified by template equality.

The classifier checks its dart bijections after writing and reading them back.
Five corruptions of each witness are rejected. `verify_internal_templates.py`
independently enumerates vertex graph isomorphisms with NetworkX, then checks
the cyclic neighbour orders. Its 633 within-class and 9,730 between-class
comparisons reproduce the partition without reading the saved dart witnesses.

The smallest repeated template is the four-vertex diamond. Its members are
configurations 1, 2 and 4, with ring sizes 6, 7 and 8. A bounded transport test
replaces a boundary colour `c` by adjacent distinct colours `a, b` satisfying
`a XOR b = c`. This is the local Tait relation at a cubic star. For each of
the pairs 1 to 2 and 2 to 4, the test tries every source port and every cyclic
rotation and reflection of the target support.

None of the 196 star images is contained in the target support. Even the closest
images contain 60 and 222 colourings absent from the target, respectively.
A separate backtracking search on the original free completions reconstructs all three boundary
supports, using four vertex colours and their nonzero XOR differences around
the ring. These agree with the stored supports, up to boundary orientation.
The three support sizes are 96, 234 and 486.

The weaker, existential transport condition does succeed: each pair has four
fixed attachment alignments where every source word admits at least one
target-supported branch. `diamond_subdivision_geometry.py` explains this
through actual graph operations. Subdividing the edge of a boundary triangle
and joining the new vertex to its opposite vertex produces configuration 2
from 1, and configuration 4 from 2. Saved isomorphisms preserve cyclic order
and the outer ring; corrupted mappings, orientations and boundary images are
rejected. These catalogue identifications are program checks.

The general colouring result is kernel-checked in
[`BoundaryTriangleSubdivision.lean`](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryTriangleSubdivision.lean).
Every old colouring extends, preserving all retained vertices. When the three
chosen vertices form a triangle, the new vertex has exactly one available
colour. This gives a bijection onto the target colourings which still
distinguish the deleted edge's endpoints, and an exact counting consequence.
Its GSLT step presentation carries no assumed colouring; the route semantics
constructs compatible witnesses from an explicit starting colouring.

The graph theorem assumes no embedding. Using it as a planar boundary
operation additionally needs the specified boundary face. It does not show
that an arbitrary exterior supplies compatible new boundary colours or Kempe
choices. Consequently it does not replace the family's reducibility checks.

`internal-template-probe.json` records the source and program hashes, timings,
controls and scope of the finite probes. `triangle-subdivision-measurements.json`
records the separate Lean gate and axiom audit. The template
count does not count reducibility proofs, and the failed star inclusion does
not refute a uniform diamond-family theorem or other ways of choosing compatible
colourings. This experiment removes no configuration or independent proof check.

The later [boundary-split result](../../../papers/benxiv/fourcolor-compositional/diamond-example/README.md)
uses a different direction. Splitting a Kempe-closed exterior relation remains
Kempe-closed, and repair descends when successful graph colourings reconstruct
after collapse. Configuration 2's retained rank certificate now supplies both
its own repair and configuration 1's through that law. Together with the
separate configuration-4 joint repair, this leaves 631 reference certificate
dependencies in the complete proof. All 633 catalogue entries remain.
`diamond-split-measurements.json` records the source hashes, gates, dependency
audit and costs; a common core repair rule covering all three diamonds remains open.

`audit_diamond_ear_family.py` checks a different operation: attach a fresh
vertex to the ends of a retained boundary edge. It independently checks 4,652
chromogram merges and enumerates complete colourings for the first three ears
on each diamond core. `diamond-ear-probe.json` records these nine graph cases.
The general Lean result covers arbitrary finite repetitions at the first
boundary edge, retaining the joint relation and reconstructing actual GSLT
colouring histories. `diamond-ear-measurements.json` records its twelve-root
audit and kernel costs. This is a contextual family theorem; it introduces no
new core repair, removes no further certificate and proves no coverage claim.

```sh
python3 tools/fourcolor/classical/audit_diamond_ear_family.py \
  --output diamond-ear-probe.json
```

With the original configuration file and the pinned reference's generated
`cpc.py` inputs, reproduce the results with Python 3.9 or newer. The independent
template verifier also requires NetworkX (the recorded run used version 2.4).

```sh
python3 tools/fourcolor/classical/classify_internal_templates.py \
  --configurations unavoidable.conf --output internal-templates.json
python3 tools/fourcolor/classical/verify_internal_templates.py \
  --configurations unavoidable.conf --classification internal-templates.json \
  --output internal-templates-check.json
python3 tools/fourcolor/classical/probe_diamond_star.py \
  --configurations unavoidable.conf --inputs generated-inputs \
  --output diamond-star-results.json
python3 tools/fourcolor/classical/diamond_subdivision_geometry.py \
  --configurations unavoidable.conf --output diamond-subdivision-results.json
```

The Lean audit checks five roots, their named mathematical dependencies and
their axiom sets. From `lean/mettapedia`, reproduce it with:

```sh
lake build Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivisionAudit
```

The omitted target colourings matter for reducibility. The exact finite
Kempe-closure test in `probe_diamond_kempe.py` considers every balanced
chromogram, all six colour permutations and all proper zero-sum traces at
rings 6–8. Restricting the seven-port target to the 132 words generated from
the preceding support leaves 132 contract traces in a disjoint Kempe-closed
set. Continuing only that branch to ring 8 leaves all 108 contract traces
uncovered. Saved closed-set witnesses are checked again after serialization;
nine deliberately corrupted witnesses are rejected. These are abstract closed
predicates, not claimed to be realizable planar exteriors. The Kempe coclosures
of the full original supports cover all contract traces in these three examples.

[`BoundaryTriangleAlternatives.lean`](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryTriangleAlternatives.lean)
provides the complete colouring decomposition. A target colouring either
distinguishes the deleted edge's endpoints, or identifies them. In the latter
case it comes from the contracted graph and a fresh colour avoiding the merged
vertex and the opposite triangle vertex. There are exactly two such fresh
colours. Both branches give an explicit disjoint-sum equivalence, preserving
any further constraint on the target colouring. For a finite graph, the target
colouring count is the old count plus twice the contracted count.

The separate program `diamond_coloring_alternatives.py` checks these branches
on the original embedded diamond instances. It independently enumerates the
old, contracted and target graphs, and compares the actual colouring sets.
With one vertex fixed to colour zero, the results are:

| Subdivision | Old colourings | Contracted colourings | Target colourings | Boundary supports: distinct / equal endpoints |
| --- | ---: | ---: | ---: | ---: |
| 1 to 2 | 144 | 54 | 252 | 132 / 102 |
| 2 to 4 | 252 | 150 | 552 | 246 / 240 |

The support unions recover all 234 and 486 target words. This identifies the
missing alternative without claiming that either branch alone always succeeds.
The general equivalence and contextual theorem are kernel-checked; the
catalogue instantiations remain program checks. Neither replaces a reducibility
check. `diamond-kempe-probe.json` and `triangle-alternatives-measurements.json`
record the two kinds of evidence separately.

```sh
python3 tools/fourcolor/classical/probe_diamond_kempe.py \
  --inputs generated-inputs --output diamond-kempe-results.json \
  --witnesses diamond-kempe-witnesses.json
python3 tools/fourcolor/classical/diamond_coloring_alternatives.py \
  --configurations unavoidable.conf --geometry diamond-subdivision-results.json \
  --inputs generated-inputs --output diamond-alternatives-results.json
```

From `lean/mettapedia`, the audit checks four roots and their dependencies:

```sh
lake build Mettapedia.GraphTheory.FourColor.BoundaryTriangleAlternativesAudit
```

## What the compositional bridge must preserve

Configuration programs already exist in the reference proof. Encoding their
syntax as graph operations is only the beginning. The useful adapters must
preserve actual darts, cyclic order, boundary traces, planarity hypotheses and
colouring witnesses. C-reducibility permits recolouring the exterior; keeping
every exterior colouring fixed would strengthen the required theorem beyond
what the classical proof supplies.

## Kernel pilot

The pinned Emery source passed the following fresh certificate checks on Lean
4.34.0-rc2 with Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
`pilot-measurements.json` records generated-source hashes, exact theorem names,
compiler options, artifact sizes and measurement scope.

| Configuration (one-based) | Ring | Checker | Frontend seconds | Peak RSS (GiB) |
| --- | --- | --- | ---: | ---: |
| 1, Birkhoff diamond | 6 | Bulk | 2.85 | 2.35 |
| 4 | 8 | Bulk with contraction | 3.19 | 2.35 |
| 9 | 10 | Bulk with contraction | 3.36 | 2.37 |
| 20 | 12 | Bulk with contraction | 7.40 | 2.53 |
| 110 | 14 | Bulk with contraction | 22.49 | 4.01 |
| 34 | 10 | Bulk plus residual certificate | 6.22 | 2.39 |

The reference expresses every result as C-reducibility. For configurations
that are already D-reducible it supplies an arbitrary valid contraction; the
bulk/residual checker distinction is therefore different from D/C-reducibility.

These times include elaboration, kernel checking and proof serialization, with
dependencies already built. They exclude native C output. A normal Lake build
of the ring-14 sample took 527.6 seconds including C generation; a replay
without `-c` took 22.5 seconds. C emission is unnecessary for these certificate
theorems. The reference project's build pool likewise omits it.

All six reducibility roots use only `propext`, `Classical.choice` and
`Quot.sound`. An audit of 8,284 imported public `FourColor` declarations found
no other axioms. The conditional real-plane theorem and the bulk and residual
checker soundness theorems also passed. This pilot does not reproduce all 633
configurations, the discharging presentations or the unconditional theorem.
The largest residual checks are outside this initial ladder; extrapolating from
the diamond alone would understate their cost. The subsequent reconstruction
pilot below adds a large residual configuration and a discharging sample.

The generators used were the reference's `tools/cpc.py`, `tools/planes.c`,
`tools/residual.c`, `scripts/gen_bulk_jobs.py`, `scripts/gen_maskc_jobs.py` and
`scripts/gen_hybt_jobs.py`. Their output is untrusted input to the Lean
checkers. The generated modules use the reference's packed natural-number
encoding and `decide +kernel`. Compilation required one compatibility edit:
`Mathlib.Basic.Denumerable` becomes `Mathlib.Logic.Denumerable` in
`FourColor/Finitize.lean`. No proof body changed.

Full replay instructions are provided by the pinned reference's `build.sh`
and `scripts/build_pool.py`; the generated certificate files are deliberately
absent from its Git repository. Retain its licence and attribution notices
when reusing source. The dependency revision and compatibility edit above
must be recorded when comparing these measurements with upstream results.

The checked audit sources are retained in `audit/`. In a prepared reference
checkout, `PilotAudit.lean` belongs at `FourColor/PilotAudit.lean` and
`CompleteAudit.lean` at `FourColor/Pilot/CompleteAudit.lean`. The latter imports
the five separately generated bulk modules at `FourColor/Pilot/CfgNNN.lean`
and the residual module at `FourColor/Bulk/Cfg/Hyb033.lean`. Module indices are
zero-based, as in the measured theorem names. These audit files belong to the
reference checkout's dependency environment, not the main library's import
graph.

## Compositional integration

The adapter sources now live in the
[`lean/fourcolor-classical`](../../../lean/fourcolor-classical/README.md)
integration package, which depends on the pinned reference and the existing
Mettapedia library. Its default target checks the adapters without generating
native C code for certificate proofs. The package's LICENSE retains the
reference's MIT notice and Gonthier/Werner attribution.

| Module | Checked obligation |
| --- | --- |
| `CompatibleTraces` | A supplied contract colouring gives matching traces on a configuration and its actual exterior |
| `PatchWitness` | An explicit glued colour function reads back the two supplied assignments, after a constant colour shift on the disk |
| `EmbeddedReconstruction` | The matching assignments remain data at the middle interface of a GSLT reconstruction route |
| `Config4Reconstruction` | The route consumes configuration 4's actual ring-eight certificate and proved decoded-map geometry |
| `ClassicalAssembly` | The conditional real-plane theorem consumes witness reconstruction for every fitted catalogue entry, with the reference's discharging obligations retained |
| `HypermapDictionary` | The two hypermap presentations agree on permutations, components and planarity on the same finite dart type |
| `HypermapTransport` | Exact relabelling preserves the hypermap and its colourings, allowing finite dart carriers in any universe |
| `SourceTait` | Classical face colours descend to literal Tait edge colours and supply compatible witnesses along exact source construction traces |
| `PairChargeTransport` | Paired semantic bounds survive reflection and exchange of endpoints, with the part and offset transported together |
| `GraphColoringBridge` | Colours on actual graph darts descend to Mathlib vertex colourings, using vertexwise cyclicity and preserving every supplied dart colour |
| `HubcapOrbit` | Equal rotated boundary inputs and equal bounds share a checker certificate |
| `PeriodicHubcap` | Two representative checks close the same ten-position discharging case as the reference's `f10_128` |
| `HalfTurnHubcap` | Five representatives close `f10_242` by the same orbit lemma, using its period-five boundary |
| `ChargeBound` | Checker results become semantic charge bounds, transport through reflection, and compose around a hub |
| `ReflectedHubcap` | Three representatives close the same `f10_242` part, combining rotation and semantic reflection |
| `HubcapCharges` | Arbitrary integer charges obey the weighted-cover inequality; semantic single-edge and paired-edge bounds assemble a successful hubcap |
| `NearestRegions` | Compact sites with connected exclusive cores have connected strict nearest regions in any real normed space |
| `CompactPlaneMap` | A two-site contact is non-corner map adjacency, and map colours transfer to graph colours |
| `PlaneDrawing` | Actual noncrossing injective paths construct all the compact-site hypotheses, including isolated vertices |
| `OrbitAssembly` | The complete arity-ten presentation supplies a coverage input to the reconstruction-based assembly, using the shared periodic certificate |
| `Orbit11Assembly` | The shared arity-eleven presentation composes with the arity-ten proof, leaving five arities and reducibility explicit in both colouring endpoints |
| `Orbit9Assembly` | The shared arity-nine presentation joins the other two, leaving arities five through eight and reducibility explicit in both colouring endpoints |
| `BridgeAudit` | The imported reference and GSLT declarations use only the three permitted axioms |

The operational sequence is:

```text
supplied contract colouring
    -> selected disk and exterior assignments with matching traces
    -> explicit colouring of the ambient map
```

The middle state contains both colour functions, their colouring proofs, and
their boundary compatibility. Gluing preserves the selected exterior exactly;
the disk is shifted by a constant colour to align the boundary. The selected
exterior can differ from the original contract assignment. Selection uses
classical choice and the reference's Kempe-closure existence argument. This
does not extract an executable sequence of Kempe moves.

The reconstruction consumes the reference's embeddability, embedding, planarity,
plainness, bridgelessness, connectivity, cubicity, Birkhoff-ring and pentagonal
hypotheses. It does not assume a minimal counterexample or invoke the final
Four Colour theorem. The configuration consumer supplies its own checked
reducibility and embeddability; the surrounding map and contract colouring
remain inputs. Unavoidability and strict reduction supply are separate.

`ClassicalAssembly.fourColorTheorem_of_checks` connects the reconstruction to
the main argument. Minimality supplies a contract colouring; the explicit
reconstructed assignment contradicts noncolourability. This replaces the
reference's terminal embedding argument inside the quiz-tree soundness proof.
The resulting real-plane theorem still assumes all 633 reducibility results
and the seven discharging presentation results. It does not invoke the
reference's already assembled conditional or unconditional theorem.

The hypermap dictionary is an equivalence on a fixed finite dart type, not a
bijection between arbitrary hypermaps and labelled rotation systems. Its
planarity proof explicitly handles the differing Euler conventions and the
reference's natural-number genus. The path-drawing endpoint below supplies a
separate connection to the standard finite planar-graph statement.

`HypermapTransport` preserves components, face cycles, planarity and actual
colour assignments under an arbitrary dart equivalence. Relabelling through
`Fin` permits the reference's universe-zero assembly to colour any finite
dart carrier. `SourceTait` then proves the source spherical map's reference
hypotheses and converts its face colouring into a Tait colouring on the
original edge carrier. The exact formula at a dart is the Klein-group sum
of the colours on its two face sides, followed by a fixed palette embedding.
The existing dart-colouring adapter handles parallel edges.

The source construction theorem now has a consumer:
`OrbitAssembly.supported_source_construction_of_checks` supplies an exact
geometric construction trace and compatible GSLT colouring witnesses for
every map in the source class. Every complete valid vertex sweep also has
support. These statements choose compatible assignments; they do not assert
that an arbitrary partial colouring extends. Their remaining inputs are the
same reducibility and six presentation obligations as the other assembly
endpoints. `source-tait-measurements.json` records the bridge and its audits.

`GraphColoringBridge.colorable_of_checks` gives `G.Colorable 4` for a finite
simple graph with the existing graph-backed rotation data, vertexwise cyclicity,
and hypermap planarity, conditional on the same catalogue and presentation
checks. The proof colours the dual hypermap and reads back the node colours.
It uses the original graph's literal darts: edge reversal swaps their endpoints,
and the node orbits are exactly the nonempty fibers over vertices. Merely
preserving a vertex label would be too weak; the single-cycle condition is
proved to supply the missing implication.

The readback keeps the supplied colour at every dart and assigns zero to
isolated vertices. Its generic form admits an empty dart set and requires no
connectedness or cubicity hypothesis. A converse pulls vertex colourings back
to dart colourings. This is a bridge between colouring representations; it
does not yet construct a planar rotation from an arbitrary topological graph
embedding.

`PlaneDrawing.colorable` takes the other route: from actual embedded paths to
compact half-edge sites, then to a simple plane map, and finally back to colours
on the original vertices. It assumes the plane-map Four Colour theorem and
constructs every intermediate geometric object. Its arc conditions express
distinct vertices, injective paths with the specified endpoints, reversal,
and the absence of vertex/interior and different-edge/interior crossings.
`OrbitAssembly.colorable_of_planeDrawing` supplies the plane-map theorem from
the conditional compositional assembly. The map may have additional
adjacencies; the proof establishes preservation of all original graph edges.
`plane-drawing-measurements.json` records the bridge's source hashes, checks,
axioms and remaining assembly hypotheses.

To replay the adapters, prepare the pinned reference with the dependency
revisions above and build Mettapedia's imported GSLT and hypermap modules.
The reference artifacts must include the generated ring-eight group
`FourColor.Bulk.Cfg.Grp08_00`, `FourColor.Bulk.Cfg.Hyb218`, and
`FourColor.Present7Chk85`, together with `FourColor.Present10Defs` for the
periodic discharging consumer.
The following directory names are example input and output locations:

```sh
python3 tools/fourcolor/classical/replay_adapters.py \
  --reference reference-4ct --mettapedia lean/mettapedia \
  --reference-artifacts reference-artifacts --output adapter-build
```

The script checks the reference revision and common toolchain, compiles the
twenty adapter and audit modules and the package root without native C emission, and runs
the axiom audit. It records source hashes, exit statuses and wall times. Its
default output is a dedicated directory; the package target instead writes the
proof artifacts to the package's ordinary build directory. It does not generate
or check the whole classical catalogue.

The earlier adapter replay, before the path-drawing bridge, covered 16,409 imported
public declarations and found only `propext`, `Classical.choice` and `Quot.sound`.
`reconstruction-measurements.json` records the exact source hashes and results.
The additional kernel measurements were:

| Check | Frontend seconds | Peak RSS (GiB) |
| --- | ---: | ---: |
| All five ring-eight configurations, reference group | 6.11 | 2.37 |
| Configuration 219, ring 14, all nine certificate modules combined | 1,644.56 | 19.97 maximum across modules |
| Discharging definitions `Present7Defs` | 24.65 | 2.78 |
| Discharging check module `Present7Chk85` | 244.33 | 7.27 |

The configuration theorem is `FourColor.Bulk.Hyb218.reducible`. The discharging
sample checks one module of the arity-seven presentation; it is not the whole
presentation or the unavoidability theorem. The unconditional reference root
has not yet been reproduced by these measurements.

## Compression ledger

The first checked local compression is the periodic case `f10_128`: ten
independent discharging computations become two representative computations,
plus a finite check of their boundary-input equalities. The general orbit
lemma assembles the full hubcap, and `PeriodicHubcap.succeeds` closes the
actual part using discharging soundness. It does not import the reference's
ten check theorems.

The second case, `f10_242`, has period five. `HalfTurnHubcap.succeeds` uses the
same generic theorem to replace its ten checks by five representatives, with
a separate check of the complete rotated inputs. Its measurement record is
`half-turn-hubcap-measurements.json`. This is an intermediate comparison:
`ReflectedHubcap.succeeds` now uses only three representatives. The generic
`ChargeBound.reflect` transports the actual charge inequality through the
reference's mirror map. `ChargeBound.successful_of_bounds` composes the
individual inequalities around the hub. The coverage proof consumes this
semantic certificate directly, without importing `HalfTurnHubcap` or
asserting that the Boolean checker is reflection invariant. The current
measurements are in `reflected-hubcap-measurements.json`.

`HubcapCharges` generalizes the reference's weighted-cover argument to
arbitrary integer charges. Single-edge and paired-edge semantic bounds can
therefore be combined regardless of whether they came directly from the
checker or through transport. The reference's cover data and split trees
remain the same. `semantic_hubcaps.py` applies this theorem to 21 further
arity-ten hubcaps. `PairChargeTransport` additionally transports paired
bounds through reflection and exchange of endpoints. The part and the
relative offset both transform; reflecting only the part would be unsound.
Together the single-edge and paired transports reduce these 188 independent
checks to 121, with a kernel-checked part identity for each of the 67
replacements. The three paired replacements occur in `f10_835`, `f10_951`
and `f10_998`; `paired-charge-measurements.json` records their consumers.

All these replacements are consumed by the complete arity-ten presentation
and the conditional `OrbitAssembly` endpoint. Its 2,580 explicit hubcap checker
obligations become 2,498, with 69 separate finite checks classifying or
identifying boundary inputs. These are counts of independent checker proof obligations, not
all reductions performed by the kernel. All 633 configurations remain.
The complete `CompositionalComplete` endpoints consume this result and the
additional arity-nine and arity-eleven sharing: 231 independent computations
are replaced in total, with 218 finite input identities counted separately.
Fewer separate checks, fewer distinct arguments, and a smaller unavoidable
set are different results. Removing a configuration from the unavoidable set
also requires a new coverage proof.

`periodic-hubcap-measurements.json` compares the original ten-check fragment
with the replacement and records the shared lemma's separate cost. This small
example does not establish a runtime or artifact-size improvement. The new
generic proof has overhead; the measured result is the reduction in independent
discharging computations and its checked local consumer.

`orbit_presentation.py` reconstructs fifteen modules of the arity-ten coverage
proof, checking exact hashes for all input checker sources and definitions.
It changes import names and namespaces, removes the
twenty declarations `c10_128_1` through `c10_128_10` and `c10_242_1` through
`c10_242_10`. It replaces the first combining proof with `PeriodicHubcap.fit`,
removes `f10_242`, and replaces its sole consuming hubcap step with
`ReflectedHubcap.succeeds`. The additional 21 hubcaps retain representative
checks and convert their combining theorems to semantic certificates.
Each consuming step invokes `Hubcap.succeeds` with the original cover.
Unaffected proof bodies are retained. The generated source includes the
reference's licence and attribution. The final audits check the axiom set,
follow proof dependencies through every replacement and the explicit colouring
reconstruction, and reject all 87 superseded check declarations and the original
`exclude10` theorem. `semantic-hubcap-measurements.json` records the weighted-cover
theorem and the earlier single-edge sharing across all 21 consumers;
`paired-charge-measurements.json` records the paired extension, and
`orbit-presentation-measurements.json` records the coverage build.

The audit also follows the finite graph endpoint
`OrbitAssembly.colorable_of_planeDrawing`. Its geometric bridge constructs
compact half-edge sites and connected nearest-site regions from injective
noncrossing paths in the real plane. Thus the colouring conclusion concerns
the original simple graph, with no supplied rotation or colouring hypothesis.
The plane-drawing measurement record documents this bridge separately from
compression; it removes a representation obligation, not a catalogue entry.

After the adapter gate and the arity-ten reference checker modules are built:

```sh
cd lean/fourcolor-classical
lake build kernelOrbitPresentation
```

The generated source and compilation receipts are in `.lake/orbit-audit`.
`orbit-presentation-measurements.json` records the corresponding source hashes,
frontend times and artifact sizes. Compilation uses the ordinary Lean kernel
and emits no native C code. This integration establishes consumption of the
shared certificate; it does not establish a runtime or artifact-size saving.

The arity-eleven target reuses the same semantic reflection theorem in thirteen
hubcaps. Their 140 independent computations become 78, with 62 separately
checked identities of complete boundary inputs. The whole arity-eleven
presentation changes from 571 to 509 independent checks. `Orbit11Assembly`
composes it with the shared arity-ten presentation: together they replace 144
checks, changing 3,151 to 3,007, plus 131 finite identity/classification checks.
The audit follows both the finite graph and exact source-construction endpoints,
requires every selected hubcap, and excludes all replaced check declarations.
The remaining hypotheses are reducibility and arities five through nine.

With `Present11Defs`, the adapters and the shared arity-ten presentation prepared:

```sh
cd lean/fourcolor-classical
lake build kernelOrbit11Presentation
```

`orbit11-presentation-sources.json` pins the nine reference presentation sources
and their part definitions. `orbit11-presentation-measurements.json` records
the checked replacements, generated-source hashes, compiler options, frontend
times and artifacts. The target retains the original covers and split trees.
No configuration is removed, and no runtime or artifact-size saving is credited.

The arity-nine target shares 32 further hubcaps. Their 237 independent checks
become 150: semantic reflection replaces 70 single-charge checks, and reflection
or exchange of endpoints replaces 17 paired-charge checks. Each replacement
checks the complete boundary input and, for a pair, its relative offset.
`Orbit9Assembly` composes all three presentations. Together their 11,363
independent checker obligations become 11,132, with 218 separate finite
identity/classification checks. Reducibility and arities five through eight
remain explicit inputs; all 633 configurations remain.

With the adapters, shared arities ten and eleven, and the reference arity-nine
artifacts prepared:

```sh
cd lean/fourcolor-classical
lake build kernelOrbit9Presentation
```

`shared_presentation.py` rebuilds the dependency cone of the modified checks:
35 presentation modules, followed by the assembly and audit. It imports the
other 57 presentation modules unchanged. The 93 input sources are pinned in
`orbit9-presentation-sources.json`; generated sources and receipts are written
to `.lake/orbit9-audit`. The audit requires both colouring endpoints to consume
every selected hubcap, rejects the original three coverage roots and all 236
superseded checker declarations, and checks the permitted axioms.
`orbit9-presentation-measurements.json` records the successful replay of all
37 modules: 760.098 summed frontend seconds and 4,134 MiB sampled peak
individual Lean RSS. Source and artifact hashes were verified before installing
the checked outputs in the package. No runtime or artifact-size saving is claimed.

`reflection_candidates.py` searches the pinned single-edge queries for pairs
with equal bounds and reflected full input parts. It finds 450 possible
additional identifications beyond exact-input equality. All 70 arity-nine,
66 arity-ten and 62 arity-eleven identifications have checked consumers;
the remaining 252 are candidates.
Only consumed, kernel-checked applications enter the compression ledger.
Dual-edge reflection is outside this search. Replay it with:

```sh
python3 tools/fourcolor/classical/reflection_candidates.py \
  --reference lean/externals/fourcolor --output reflection-results.json
```

`paired_charge_candidates.py` searches paired queries under reflection and
exchange of endpoints. It finds 91 additional matches beyond exact-input
equality, including the three arity-ten replacements consumed above. The
17 arity-nine matches also have checked consumers. The other 71 remain
candidates, including some that cross hubcaps. Equal bounds
and complete part data are required. This inventory is a program search;
each credited application separately checks its identity and semantic proof
in Lean.

```sh
python3 tools/fourcolor/classical/paired_charge_candidates.py \
  --reference lean/externals/fourcolor --output paired-charge-results.json
```

`compression-ledger.json` keeps the baseline and credited changes separate.
The first bounded experiment tested whether two configurations could share a
bulk certificate built from their common colourings. For each pair, the base
was the intersection of their boundary supports, and the demand was the union
of their contraction supports. The second configuration was tested in every
cyclic rotation and reflection, after closing both supports under colour
permutations.

The program checked all 9,964 pair alignments at ring sizes 8, 9 and 10. None
closed under the reference's bulk certificate rule. The smallest remaining
demand was 49 orbits for configurations 19 and 48 (one-based), both at ring 10.
The stronger reference residual search also left contract traces unresolved
for that pair. These results rule out this particular sharing experiment;
they do not prove that the configurations cannot share a different certificate,
or that either configuration is not reducible.

The separate comparison of all 633 stored supports found no same-ring
inclusions in their original boundary order. That comparison did not search
all boundary orientations. The shared-certificate search did search all
orientations, but only at the three ring sizes above.

`common-support-probe.json` records the input manifest hash, controls, trial
counts and scope. The positive control closed the support of configuration 3;
the same demand with an empty base left 101 orbits. A second implementation
reproduced every trial's support sizes and residual count. All of this is
program evidence, not a kernel-checked obstruction theorem. The experiment
earns zero compression credit.

After generating the pinned reference's `cpc.py` inputs and compiling its
`tools/planes.c`, reproduce the pair search with:

```sh
python3 tools/fourcolor/classical/probe_common_support.py \
  --inputs generated-inputs --planes reference-tools/planes \
  --output common-support-results.json
```

The default rings reproduce the measured search. The output includes every
trial and all input hashes; configuration indices in the JSON are zero-based.

## Bounded disk replacement search

The bounded diamond disk-replacement search is reproduced with:

```sh
python3 tools/fourcolor/classical/probe_diamond_disk_replacements.py \
  --output diamond-disk-replacement-results.json
```

`diamond-disk-replacement-probe.json` records 90,651 generated triangulated
disks with the same eight boundary vertices and zero through three interior
vertices. For configuration 4 and the first longer fan, each candidate has an
actual colouring in the target's fixed Kempe-closed obstruction. Every witness
is checked on the candidate graph. The program independently checks disk
incidences, vertex links and closure under flips; twelve negative controls
reject corrupted evidence. Candidate and witness streams have deterministic
digests. The complete flip component of each seed is enumerated, but a theorem
identifying those components with all embedded disks is outside the result.
This is program evidence, earns no compression credit, and leaves boundary
identifications and joint relations between replacement choices untested.

## Reusable semantics audit

`audit/ReusableSemanticsAudit.lean` follows thirteen roots through 11,486
declarations in their combined dependency closure. It checks their axiom sets
and required links to witness composition, literal graph decoding, boundary
colouring transport, counting, and the actual MeTTa premise engine. All roots
use only `propext`, `Classical.choice` and `Quot.sound`.

The counting theorem obtains matrix multiplication from a bijection of
colouring witnesses. The MeTTa consumer preserves possible final bindings
when a repeated freshness condition is removed inside any serial context;
it does not claim preservation of answer order or multiplicity. Graph
representation conversion transports an existing colouring. This is separate
from establishing that every planar graph has a colouring.

After dependency preparation, the audit took 4.726 seconds with a maximum RSS
of 3,551,556 KiB. `reusable-semantics-measurements.json` records the source and
artifact hashes, roots, axiom sets and measurement scope. This audit does not
rebuild every dependency, inspect unrelated imported declarations, or earn
compression credit. Reproduce it from `lean/mettapedia` with:

```sh
lake build \
  Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition \
  Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT \
  Mettapedia.GraphTheory.Representation.ColoringTransport \
  Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation \
  Mettapedia.OSLF.MeTTaIL.PremiseRouteSemantics
lake env lean ../../tools/fourcolor/classical/audit/ReusableSemanticsAudit.lean
```

## Shared diamond joint-profile certificate

`generate_diamond_profile_certificate.py` reconstructs the literal configuration
1, 2 and 4 graphs, independently enumerates their ordinary colourings, and
searches for Kempe descent ranked by joint available-colour sets and boundary
length. It generates short flat string records for a separate Lean check:

```sh
python3 tools/fourcolor/classical/generate_diamond_profile_certificate.py \
  --lean-output lean/fourcolor-classical/MettapediaFourColor/DiamondProfileData.lean \
  --report tools/fourcolor/classical/diamond-profile-candidate.json
```

The program report is candidate evidence. The kernel-checked consumer and its
integration receipts are recorded in `diamond-profile-measurements.json`.
There are 92 ranked profile types, 236 trace representatives and 291 answer
references. All 183 proper six-port traces, all 546 proper seven-port traces,
and all 108 inputs of the eight-port joint contract are covered. The eight-port
certificate covers 684 traces in total; it does not claim to cover every
repairable trace.

The generator first tests a uniform single-chord exchange: after choosing the
fixed colour and anchor, every opposite-parity active partner must give a
lower-ranked profile. The Lean theorem `KempeChordExchange.answer_exists`
proves coverage for arbitrary boundary length. It handles 11, 45 and 15
nonterminal representatives in the three cores. The coupled two-ear rule then
handles 4, 7 and 13 more. `KempeChordMasks.recolor_matches` transports any
compatible active mask through the same exterior, reinserting fixed-colour
ports. The separate finite `six_checked` theorem supplies two disjoint cyclic
ears for every balanced six-active-port skeleton. Either ear or both may be
exchanged, so their joint choice is retained. There are nine local ear-pair
classifications per consumer, 216 in total; finite ranks and target references
also remain. Joint anchor projection handles the last five states in
configuration 4. It retains only the complete masks seen at two or three
selected anchors, including shared chords, then permits one mask or the union
of two. Generic `KempeAnchorProjection.labels_paired` and `paired_or` prove
reconstruction through the same exterior at arbitrary boundary length.
The three concrete patterns have 7, 10 and 10 distinct signatures at eight
active ports; their five uses retain 44 local classifications. The classifier
still generates balanced unsigned skeletons and identifies equal projections.
No byte, runtime or net primitive-check reduction is claimed.

The generator independently checks each chosen structural step against every
matching chromogram. The ninth base-36 word-record digit is 1--8 for a chord
anchor plus one, 9 for coupled ears, A--C for joint anchor patterns, or zero for
a terminal. `structural_counts`, `coupled_counts` and `anchor_counts` check the
consumer counts. `zero_terminal` excludes a residual finite-cover branch.
No additional whole configuration certificate or catalogue entry is removed.

The ranked-answer principle is reused from the reference development. The
local proof no longer depends on the original `coversRec` checker or its
soundness theorem; projected classifications, target references and ranks
remain explicit finite data. Actual terminal graph witnesses use the shared diamond
summary. Ordered-ring transport and the reference contract decoder connect
the result to strict reduction in the complete proof. The complete endpoint
audit excludes the original configuration 1, 2, 3 and 4 certificates; 629 original
certificates and all 633 configurations remain. Short records avoid repeatedly
decoding the whole data stream during kernel evaluation. This encoding change
is separate from mathematical compression, and no byte or runtime saving over
the reference is claimed.

## Hexagonal seam recognition

`hexagonal_seam_probe.py` constructs the dart involution and vertex rotation
of two literal zigzag rows, reads their face cycles, and checks every seam
permutation at widths two through seven. The recorded 5,912 cases agree with
the general Lean theorem: all seam faces are hexagons exactly for cyclic
translations. The script also constructs closed five-port examples with
pentagonal caps, verifies simple cubic incidence, connectedness and absence
of bridges, and checks explicit Tait colourings. The shifted example has
30 vertices and Euler characteristic two; the noncyclic control has Euler
characteristic zero and an 18-sided face. The control is not a planar
counterexample. These are finite program checks, not Lean certificates.

```sh
python3 tools/fourcolor/classical/hexagonal_seam_probe.py \
  --output hexagonal-seam-probe.json
```

`hexagonal-seam-measurements.json` records the separate Lean proof and audit.
The general result constructs aligned coordinates along arbitrary chains of
recognized oriented rows from their actual hexagonal seam faces. Exact
side-colouring support composition then supplies the existing strict
shore-splice argument, without an assumed common port labelling. The
five-port bound at that checkpoint was 446,403 rows; that step established
geometric alignment. The physical strip reduction below now improves the
bound to four. The facial adapter
derives rotation compatibility from face incidences and alternating retained
degrees. The complete proof still retains 633 configurations and 629 original
configuration certificates. See the [tube guide](../../../papers/benxiv/fourcolor-compositional/tube-example/README.md#recognizing-compatible-seams-in-actual-graphs)
for the exact hypotheses and remaining recognition/coverage obligations.


## Recognized strips and four-ring physical reduction

`hexagonal_strip_probe.py` checks selected complete capped strips with three,
five and seven rows. Nonzero seam shifts accumulate into a literal dart
relabelling preserving both edge reversal and vertex rotation. Five- and
seven-row examples shorten to four, and a colouring is reconstructed with
all 20 exterior edge colours fixed. The report contains explicit witnesses.

```sh
python3 tools/fourcolor/classical/hexagonal_strip_probe.py \
  --output hexagonal-strip-probe.json
```

These finite program checks are separate from the Lean theorem.
`HexagonalTubeAssembly`, `SlabExterior`, `RotationSystemExactTransport` and
`HexagonalTubeReduction` now connect actual recognized strips to the physical
four-ring normal form. A graph-backed vertex-minimal counterexample has at
most four rows in such a five-port strip; no connected-shore premise is added.
The row supply and width hypotheses remain to be justified more broadly.
`hexagonal-strip-measurements.json` records that checkpoint's audit and costs.
No additional classical configuration certificate or catalogue entry is
removed, and no counting equality or executable Kempe procedure is asserted.

## Whole-collar successor construction

`nextRow` in `HexagonalCollar.lean` constructs the next complete row from actual face
traversal around a recognized row. Hexagonal seam faces, distinct candidate
vertices and short output-port faces suffice. The converse identifies the
candidate vertices in every oriented successor, giving an exact criterion.
The joint colouring relation and its interior witnesses compose through the
constructed row. `stopsWithin_three` in `HexagonalCollarProgress.lean` consumes the
four-ring physical reduction: in the pentagon/hexagon class, a minimal
counterexample meets a pentagonal seam face or an actual vertex collision
within three successful extensions of a supplied five-port row.

```sh
python3 tools/fourcolor/classical/hexagonal_collar_probe.py \
  --output hexagonal-collar-probe.json
```

The independent probe tests all 574 simple ten-cycles in seven explicit maps,
in both orientations. It finds 48 alternating rows, 28 constructed hexagonal
successors and 20 pentagonal stops. No collision appears in this sample.
Two Goldberg examples, of 80 and 180 vertices, have no alternating ten-cycle;
these zero-coverage results are included explicitly. `hexagonal-collar-measurements.json`
records the separate Lean audit, exact hypotheses and remaining obligations.
That checkpoint left collision geometry open. The following theorem now
discharges it for hexagonal collars; initial-row supply, pentagonal stops,
other widths and other face sizes remain coverage tasks.


## Hexagonal collar noncollision and finite growth

`HexagonalCollarNoncollision.lean` derives candidate-vertex injectivity from
the existing oriented row, cubic cyclic stars and actual hexagonal seam
faces. A mixed collision would propagate by reflection of the cyclic indices
until edge reversal had a fixed point. `hexagonalNextRow` consequently needs
only the face conditions, and its support theorem reconstructs genuine
compatible colouring witnesses.

`pentagonWithin_card` proves that growth from a recognized row reaches a
pentagonal seam in every finite cubic map with faces of size five or six.
`pentagonWithin_three` consumes physical four-ring reduction to sharpen this
to three extensions at width five in a minimal counterexample. Neither theorem
supplies a reduction at the terminal pentagon or an initial suitable row.

```sh
python3 tools/fourcolor/classical/hexagonal_collar_growth_probe.py \
  --output hexagonal-collar-growth-probe.json
```

The probe follows all 48 recognized oriented starts in seven explicit maps,
checking actual complete boundaries and fresh vertices throughout. Every
history reaches a pentagon; the longest has six extensions. The sharper
three-extension theorem assumes minimal-counterexample status. Two Goldberg
examples have no starting alternating ten-cycle. The kernel audit, exact
hypotheses and costs are recorded in
`hexagonal-collar-noncollision-measurements.json`. No additional classical
certificate or configuration is removed by this geometric result.

## Simple alternating cycles and complete rows

`CycleFrameWalk.lean` constructs the actual simple closed walk of a cyclic
frame. `AlternatingCycleRecognition.lean` then derives connected facial sides,
alternating retained degrees, chordlessness and complete ordered interfaces
from a simple cycle with alternating local turns. The ambient graph is
bridgeless spherical cubic; width is at least two and unused-port faces have
size five or six. Exact joint colouring support is preserved. The constructed
row feeds pentagonal termination and, at width five in a minimal
counterexample, the physical four-ring reduction.

```sh
python3 tools/fourcolor/classical/alternating_cycle_probe.py \
  --output alternating-cycle-probe.json
```

The independent probe inspects every dart/phase orbit of twelve explicit
rotations. It checks 468 simple oriented rows, 1,082 successful extensions
and 468 pentagonal endpoints, retaining eight nonsimple orbits as controls.
Goldberg `GP(n,0)` for `n = 1,...,8` has `12n` simple oriented rows of width
`5n` in these tests. The width-five zero-start examples thus have broader
rows. This finite pattern neither proves universal simplicity nor supplies
a wider-row reduction. `alternating-cycle-measurements.json` records the
separate Lean audit. No original certificate dependency or configuration is
removed by this recognition step.

## Simple lobes when a full orbit is not simple

`AlternatingWalkLobes.lean` proves that any nonbacktracking infinite dart walk
in a finite simple graph contains a contiguous simple cycle segment of length
three through the ambient vertex count. Applied to alternating trajectories,
it preserves every internal step and supplies exact connected facial shores
in bridgeless spherical cubic graphs. Its closing transition is unrestricted;
no tube contract or reduction for that transition is asserted.

```sh
python3 tools/fourcolor/classical/alternating_lobe_probe.py \
  --output alternating-lobe-probe.json
```

The probe replays 137 explicit rotations from `alternating-lobe-fixtures.json`,
without requiring the generator. It inspects all dart/phase orbits and 31,728
first-return segments. Every segment is checked for simplicity and closure;
the shortest in each map is additionally checked for alternating internal
turns, exact facial separation and its pentagon counts. Thirty maps have no
simple complete orbit. The first displayed witness has 30 vertices and orbit
lengths 68, 22, 68, 22. All 164,220 edge subsets of sizes one through four
are checked for cyclic cuts, finding none. An explicit Tait colouring is
verified and retained. Its eleven-edge lobe separates five from seven
pentagons.

The fixtures were generated with plantri 5.5; the source hash and command
are recorded. Generation completeness, minimality of the witness and the
turn/curvature relation are not Lean-certified. This is finite evidence
against universal simple-orbit supply, not against colourability. The general
Lean extraction and facial-separation results have a separate dependency
audit in `alternating-lobe-measurements.json`. A reducible contract for the
closing transition remains open; no catalogue or original-certificate savings
are credited to this result.

## Cycle contraction with a retained seam colour

`CycleSeamTransfer.lean` proves an exact contraction/reconstruction law for
literal cycle tangles at every length at least three. Merging distinct
adjacent nonzero ports adds their Klein colours. A smaller colouring lifts
exactly when its retained seam colour differs from the first old port.
The proof reconstructs actual tangle witnesses and preserves any additional
predicate on that seam. A kernel-checked four-cycle example shows why the
guard cannot be dropped.

```sh
python3 tools/fourcolor/classical/cycle_seam_probe.py \
  --output cycle-seam-probe.json
```

The independent replay checks 6,534 marked cases of lengths three through
seven, including exact deletion and reinsertion of the internal edge
colours. It also verifies the actual C30 colouring and its eleven-edge lobe,
then checks the five rotations having distinct first port colours. These
are program checks, not a Lean embedding adapter. The two-sided port
placement, an exterior operation and strict map reduction remain separate
obligations. `cycle-seam-measurements.json` records the theorem audit; no
additional classical certificate or catalogue savings are claimed.

## Physical lobe seams and a joint pentagonal patch

The equal-port seam operation deletes two adjacent lobe vertices and joins
the two cycle ends and the two exterior ends in the inherited rotation.
Its reconstruction guard requires different colours on the two new edges.
`lobe_seam_repair_probe.py` checks actual geometry, two independent colouring
enumerators, two physical Kempe-switch implementations, and reconstruction.

```sh
python3 tools/fourcolor/classical/lobe_seam_repair_probe.py \
  --output lobe-seam-repair-probe.json
python3 tools/fourcolor/classical/pentagonal_lobe_patch_probe.py \
  --output pentagonal-lobe-patch-probe.json
```

Of 137 supplied rotations, 103 have an odd shortest lobe. All 103 tested
smoothings preserve spherical connected bridgeless geometry and remove two
vertices. Among 59,376 smaller colourings, 348 are trapped away from the
reconstruction guard: 83 maps admit repair from every smaller colouring,
and 20 do not at the chosen seam. C30-plantri-1 has 228 smaller colourings,
96 immediate reconstructions and one Kempe class, with maximum repair
distance two. The first failure, C36-plantri-35, has 18 trapped colourings;
six of its sixteen distinct odd first-return lobes instead admit full repair.
These are finite program results, not a uniform seam theorem.

The larger pentagon-plus-eleven-cycle patch has sixteen cubic internal
vertices and six ports. The second replay extracts its dual disk, verifies
the primal/dual colouring bijection, and recognizes the same ordered disk
in all 29 sampled eleven-lobe cases. It checks 252 colourings and 132 supported
words among 183 proper zero-sum words. Chromogram closure removes unsupported
words in two rounds, 51 → 6 → 0. All fourteen ordered six-leaf tree
replacements fail direct support inclusion.

`PentagonalLobePatch.lean` proves the literal disk's boundary repair for
every Kempe-closed exterior predicate, with actual colouring witnesses.
It retains 22 terminal representatives and nine finite cover checks.
`PentagonalLobePatchAudit.lean` audits four roots / 3,347 dependencies against
the standard axioms and excludes catalogue certificates and the complete
theorem. `PentagonalLobeTangle.lean` reconstructs actual cubic-tangle colourings,
preserves the entire ordered boundary and glues compatible exterior witnesses.
The program compares the exact Lean adjacency, witness data, all forty-eight
darts and every cyclic order against the extracted patch. The original witness
and tangle receipts remain in `pentagonal-lobe-patch-measurements.json`.

`PhysicalKempeBoundary.lean` now proves exact transport from physical
noncrossing component closure to the reference chromogram language. It
reconstructs every answer using a union of the same original components and
has a consumer on embedded spherical six-port cyclic bond boundaries.
`PentagonalLobePhysicalRepair.lean` uses this transport, cubic cut parity and
exact support correspondence to glue the patch starting from any proper
exterior colouring. The seven-root audit checks 21,333 dependencies, only the
standard axioms, and no catalogue certificate or complete theorem.

```sh
python3 tools/fourcolor/classical/pentagonal_lobe_tree_probe.py
```

The new replay tests all fourteen ordered four-vertex trees on each of the
29 extracted sixteen-vertex patches. All 406 replacements are simple,
connected, bridgeless spherical cubic maps with twelve fewer total vertices.
All 29 exhaustively computed exterior supports are reference Kempe-closed.
For C30, all fourteen smaller maps are colourable and their boundary words
belong to the same literal exterior support. These are independent finite
checks; the receipt is `pentagonal-lobe-physical-measurements.json`.

`PentagonalLobeTreeGeometry.lean` now proves the specified path-shaped tree's
geometry in every connected exterior. It has the same ordered face return
and Euler mass as the literal patch. The actual sewn map loses twelve vertices
and six faces, preserves exterior cofaciality, and remains connected,
bridgeless, spherical and cubic. A general boundary-essential replacement
lemma handles the tree's internal bridges. The theorem permits multigraphs.

`PentagonalLobeTreeReduction.lean` restricts a smaller-map colouring and
consumes the physical repair to reconstruct a source colouring, with physical
noncrossing explicit and cubicity inherited from the source. Its minimality
consumer has no dependency on the complete Four Colour theorem or original
catalogue certificates. The new gate is:

```sh
lake build MettapediaFourColor.PentagonalLobeTreeReductionAudit
```

`pentagonal-lobe-tree-measurements.json` records the geometric and colouring
roots, dependency audit, source hashes and build costs.

`PentagonalLobeEmbeddedReduction.lean` now derives physical noncrossing from
an exact recognition isomorphism and the spherical embedding. The source
has two-sided faces and connected exterior. Patch connectedness, the opposite
exterior boundary order and dual connectedness are proved; exact reassembly
reconstructs the original graph's colouring. The recognition fields are local
incidence and rotation data, without colouring hypotheses. The new gate is:

```sh
lake build MettapediaFourColor.PentagonalLobeEmbeddedReductionAudit
```

`pentagonal-lobe-embedded-measurements.json` records this scoped geometric
consumer. `PentagonalLobeDistinctAttachments.lean` further derives exterior
connectedness from six distinct exterior attachment vertices and the
minimality-derived cyclic four-edge cut bound. The underlying graph theorem
applies to any nonempty side of a cubic graph with fewer than eight ports,
distinct selected-side attachment vertices and that cyclic cut bound.

```sh
lake build MettapediaFourColor.PentagonalLobeDistinctAttachmentsAudit
python3 tools/fourcolor/classical/matching_boundary_connectivity_probe.py --output tools/fourcolor/classical/matching-boundary-connectivity-probe.json
```

The first command runs in `lean/fourcolor-classical`; the second runs from the
repository root. `pentagonal-lobe-attachments-measurements.json` records the
proof and actual reduction consumer. The program checks all 29 extracted
exteriors and two circular-ladder examples showing why the port bound and
distinctness matter for that theorem's general graph class.

`PentagonalLobeMinimalExterior.lean` now derives connectedness without distinct
attachments in the intended minimal source. The patch contains a cycle; a
side with at most six ports and more than two vertices is connected under the
cyclic-four bound. Euler and minimum face size leave at least four exterior
vertices. The strict-reduction consumer and minimal-counterexample exclusion
retain exact local recognition, but require no separately supplied exterior
condition or root.

```sh
lake build MettapediaFourColor.PentagonalLobeMinimalExteriorAudit
```

Run this in `lean/fourcolor-classical`.
`pentagonal-lobe-minimal-exterior-measurements.json` records the eleven-root
audit, source/artifact hashes and exact scope. The later geometric consumer
below constructs recognition for the specified two-cycle family. Broader
supply and coverage remain open. The unchanged
406-case replacement replay remains independent program evidence. No new
catalogue or original-certificate saving is credited.

## Cycle orientation and pentagon spoke order

```sh
python3 tools/fourcolor/classical/lobe_spoke_order_probe.py --output tools/fourcolor/classical/lobe-spoke-order-probe.json
```

This exhaustive local experiment fixes the literal eleven-lobe's outer
incidence and rotations. It varies all 120 pentagon spoke assignments and
32 inner rotation choices. The open face-count histogram is 2,880 cases
with three faces, 950 with five, and ten with seven. The ten cases meeting
the connected spherical-shore Euler count all coincide with the literal
patch after relabelling by their spokes. The script checks every edge
reversal and rotation permutation. It does not certify general lobe supply
or the geometric recognition implication.

The formal result follows a uniform route, at arbitrary cycle length:
`CubicCycleIncidence.Frame.uniform_geometry` reconstructs incidence from
actual graph vertices and neighbours. Spherical geometry and a connected
complement force uniform local rotations and determine the exact port
return with the same global orientation choice. No local rotation or
isomorphism is a field of the graph input. Its attachment order to the
outer lobe is now established by the separate theorem below.

```sh
lake build Mettapedia.GraphTheory.FourColor.CycleBoundaryRecognitionAudit
```

Run this in `lean/mettapedia`. The nine-root audit checks 20,865 dependency
declarations and excludes the complete Four Colour theorem and catalogue
certificates. `cycle-boundary-recognition-measurements.json` records exact
scope, source/artifact fingerprints and unchanged compression counts.

The next formal step, `ElevenLobeSpokeOrder.Incidence.inner_geometry_affine`,
derives that the spoke matching is a shift or reflected shift, with the same
direction as the actual inner rotations. The graph input supplies two disjoint
cycles and an arbitrary bijective matching of the inner spokes to the five
inward outer positions. The outer turns are stated geometrically; no inner
rotation or cyclic matching is assumed. The outer cycle supplies connectedness
of the inner complement. The exact complementary face return takes three
steps across ordinary gaps and four across the closing gap. Opposite
planar-bond orders force the matching formula.

```sh
lake build Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrderAudit
```

Run this in `lean/mettapedia`. The eight-root audit checks 21,053 dependency
declarations with only standard axioms and no catalogue or complete-theorem
dependency. `eleven-lobe-spoke-order-measurements.json` records its source and
artifact hashes. This proves the order implication geometrically; it does not
turn the program enumeration into a kernel-certified finite classifier.
The full literal patch isomorphism is now constructed by the geometric
consumer below. Supply/coverage remain open. The old probe inputs are unchanged.

## Complete recognition of the two-cycle lobe family

```sh
lake build MettapediaFourColor.PentagonalLobeRecognitionAudit
```

Run this in `lean/fourcolor-classical`. `PentagonalLobeRecognition` constructs
the literal sixteen-vertex patch from two disjoint cycles, their five-spoke
matching and the stated outer turns in an actual spherical cubic source.
The same orientation witness controls adjacency, rotation and the finite
coordinate codec. Six exposed darts and all internal edges are preserved;
cubicity rules out hidden inner attachments. The actual consumer replaces
the patch by a four-vertex tree, preserving the source class and reconstructing
colourings. Minimum face size five and cyclic edge-connectivity at least
four supply exterior connectedness; minimality supplies both bounds.

The twelve-root audit checks 26,523 dependency declarations and requires the
full geometry-to-reconstruction chain, excluding original catalogue
certificates and the complete theorem. `pentagonal-lobe-recognition-measurements.json`
records the source/artifact pairs, timings and scope. No fresh colouring-case
enumeration is introduced: the new compact tables check a 16-vertex/48-dart
representation codec. Existing lobe witness and answer-cover checks remain.
This closes recognition for one shape in arbitrary qualifying exteriors.
General stopping-lobe supply, broader local families and coverage remain
open. No further original certificate or catalogue entry is removed.

## Facial origin of the pentagonal lobe

From the repository root:

```sh
python3 tools/fourcolor/classical/pentagonal_corona_probe.py
```

The replay examines all 1,644 pentagons in the 137 saved rotations. Exactly
76 have four pentagonal neighbours and one hexagonal neighbour. All 76
face-traced patches have sixteen distinct vertices and an induced outer
eleven-cycle. These occur in the same 29 maps as the previously selected
lobes; all earlier instances are recovered. The report
`pentagonal-corona-probe.json` records source/input hashes and every
occurrence. It is independent program evidence, not a general noncollision
or coverage proof.

From `lean/fourcolor-classical`:

```sh
lake build MettapediaFourColor.PentagonalCoronaFaceReductionAudit
```

The Lean theorem constructs both cycles and all outer turns from actual face
lengths. A generic separation theorem transports equalities by simultaneous
dart rotation and edge reversal. The finite diagram passes every one of the
720 ordered collision/phase checks at depth six; the actual face-derived
darts satisfy the realization laws before global vertex injectivity is known.
Triangle-freeness therefore implies distinctness of the sixteen traced
vertices. The ambient hypotheses, or minimality, supply triangle-freeness.
Outer inducedness also follows: a chord would consume two of
six possible outward darts and create a forbidden cyclic cut of at most four
edges. The general boundary theorem uses cubic forest counting and allows a
disconnected exterior. The joint repair then gives the strict twelve-vertex
ambient reduction with genuine colouring reconstruction. Neither local
geometric premise is now assumed. The twelve-root audit
checks 26,708 dependencies using the standard three axioms and excludes
complete Four Colour endpoints, catalogue certificates and diamond reducibility.
`pentagonal-corona-noncollision-measurements.json` records the scope,
source/artifact pairs and module costs. The 720 geometric separation cases
and the partial flip-involution check are separate from colouring checks.
The earlier `pentagonal-corona-measurements.json` and
`pentagonal-corona-chord-measurements.json` retain their historical scopes.
No additional colouring enumeration or complete-proof certificate saving is claimed.

A separate local count can be replayed from the repository root:

```sh
python3 tools/fourcolor/classical/pentagonal_corona_chord_probe.py
```

The six outward positions have fifteen unordered pairs. One pair is already
a perimeter edge; the other fourteen possible chords each leave four outward
darts. `pentagonal-corona-chord-probe.json` retains this bounded test. It does
not construct an exterior or prove minimality; those are separate Lean arguments.

The separation search is independently replayable:

```sh
python3 tools/fourcolor/classical/pentagonal_corona_separation_probe.py
```

The report `pentagonal-corona-separation-probe.json` records the diagram,
all-case statistics and a digest of deterministic replayed witnesses. Short
terminal paths of lengths at most one, two and three separate respectively
652, 712 and 720 ordered cases. All cases at the final threshold use at most
six shared operations. The Lean `by decide` check independently verifies
the bounded predicate; a proved soundness theorem gives it meaning in every
actual triangle-free realization. The finite check took 25 seconds and the
audit 7 seconds, including elaboration and kernel checking. The source class,
whole-map size and colouring reconstruction are proved separately and consumed
by the face-pattern endpoint. Broader local cores and global coverage remain open.

## Smaller diamond core for the facial family

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.PentagonalDiamondFaceReductionAudit
```

The theorem starts with a central pentagon and three consecutive pentagonal
neighbours. It derives twelve distinct vertices, six genuine ports and the
complete tangle isomorphism. The shared diamond profile reconstructs genuine
colouring witnesses. Replacing the core by the four-vertex tree preserves the
ambient map class and decreases the whole vertex count by eight.

`pentagonal-diamond-measurements.json` records the 18-root, 27,171-declaration
audit. It excludes the earlier corona's separate 22 terminal-colouring and
nine answer-cover checks, all original configuration certificates and the
complete Four Colour endpoints. No extra catalogue entry or certificate is
removed from the complete assembly. Incidence/coordinate checks and the
396 collision cases are geometric checks, counted separately from colouring.

Replay the independent bounded experiments from the repository root:

```sh
python3 tools/fourcolor/classical/pentagonal_diamond_probe.py
```

The script reconstructs the literal core, checks its ordered dual graph and
Lean codecs, replays all separation cases and recognizes 458 rooted patterns
across 75 of the existing 137 maps. It also checks full boundary repair for
six-, seven- and eight-port coronas. The eight-port test leaves an abstract
600-word closed obstruction, while five of 132 tree contracts avoid it.
The report retains every obstruction word and its chromogram witness.
This finite evidence is separate from the kernel theorem and does not assert
that an actual exterior realizes that obstruction or that all source maps
contain the smaller core.

## Mixed diamond: exact recognition at seven ports

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.MixedDiamondFaceRecognitionAudit
```

A central pentagon with consecutive neighbour lengths five, six, five gives
the thirteen-vertex dual of configuration 2. The other two neighbour lengths
are unrestricted. The actual occurrence and ordered colouring observation
are proved; `DiamondProfileReducibility.repair002` supplies the shared repair.
The original recognition checkpoint left physical Kempe closure explicit.
The uniform boundary theorem below now discharges that geometric premise.
At that recognition checkpoint, an initial exterior colouring and a valid
strict replacement remained separate obligations. The strict replacement
below now supplies both.

`mixed-diamond-measurements.json` records 21 audit roots and 27,512 dependency
declarations. The audit excludes the complete Four Colour endpoints, original
catalogue certificates and older independent colouring checks. The existing
six-port diamond and corona audits also pass after the generic dart-transport
extension. Global totals remain 633 configurations and 629 original certificate
dependencies; this recognition introduces no colour certificate.

```sh
python3 tools/fourcolor/classical/mixed_diamond_probe.py
```

Run the independent replay from the repository root. It reconstructs the
literal diagram, all nine codec tables and its ordered dual correspondence,
then replays 468 collision/phase cases. Four cases need four-cycle exclusion;
the others already separate under triangle-freeness. In the same 137 fixtures,
the face scan finds 1,059 rooted occurrences, 792 central faces and 130 maps
with the pattern. All scanned occurrences have seven actual ports. The scan
does not certify each fixture's internal-six normal form or universal coverage.


## Uniform matching codec and actual exterior closure

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.MixedDiamondExteriorClosureAudit
```

The matching-to-chromogram theorem is now uniform in boundary width. Its
stack induction preserves the original paired endpoint choices and
reconstructs every accepted answer by whole-component switches. It replaces
the previous six-port enumeration. Uniform cyclic arithmetic also replaces
the five-port arc classification; the planar separator supplies physical
noncrossing in either boundary orientation.

The actual seven-port mixed diamond consumes these results. Normal form
supplies a connected exterior with no distinct-attachment assumption. Its
proved boundary order discharges reference Kempe closure, so one genuine
exterior colouring suffices for full reconstruction. The strict replacement
supplying that initial colouring is proved in the following section.

`uniform-kempe-measurements.json` records twenty audited roots, exact artifact
hashes and separately measured classification and catalogue changes. The
complete proof still retains 633 configurations and 629 original certificates.
The audit excludes complete Four Colour endpoints, original certificates and
the removed finite matching/arc translations from the new theorem chains.

```sh
python3 tools/fourcolor/classical/uniform_matching_probe.py
```

The independent replay checks all noncrossing involutions through width eight
and all their chromograms' complete answer sets. It additionally checks 6,188
ordered cyclic quadruples through width sixteen and the mixed diamond's
literal connectedness, seven first-return arcs and Euler mass. These are
bounded program checks; arbitrary-width correctness comes from the Lean
induction. Neither the replay nor exterior closure implies global coverage.


## Mixed-diamond strict replacement

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.MixedDiamondFaceReductionAudit
```

The actual thirteen-vertex mixed diamond now has a five-vertex tree
replacement. One general map-preservation theorem supplies the topology
for both this seven-port reduction and the earlier six-port reductions.
Restricting a colouring of the smaller map supplies an exterior witness;
physical Kempe closure and the existing shared repair reconstruct the
original colouring. The whole-map vertex decrease is eight. Minimality
therefore excludes the actual face pattern under its derived normal form.

`mixed-diamond-reduction-measurements.json` records fourteen audited roots,
28,102 dependency declarations, artifact hashes, module timings and the
regression gates. No complete Four Colour endpoint or original catalogue
certificate occurs in these theorem chains. The 633 retained configurations
and 629 original certificate dependencies are unchanged.

```sh
python3 tools/fourcolor/classical/mixed_diamond_reduction_probe.py
```

The replay reads both literal interiors from Lean, checks their cubic
rotations, ordered first returns and Euler mass, then checks all fourteen
dihedral sewings to a fixed five-vertex exterior with repeated attachment
vertices. Seven seams are spherical and seven are nonplanar orientation
controls. Every sewing preserves Euler characteristic, connectedness and
bridge-freedom and removes eight vertices. Named edges are deleted
separately during bridge checks. This is bounded geometric evidence;
arbitrary-context reconstruction and strict reduction come from Lean.

## Coupled eight-port wiring

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.DiamondCoupledWiringAudit
```

The two-vertex wiring, including its two free boundary wires, realizes the
joint contract required by configuration 4. The actual graph construction
has exact witness restriction and reconstruction in every exterior with
distinct endpoints for each free wire. Against a Kempe-closed exterior,
the existing shared repair reconstructs the original fourteen-vertex piece.
The vertex-count difference is twelve. This construction theorem alone does
not assert ambient class preservation. The occurrence and strict-reduction
theorems below derive it under the source normal form.

`coupled-wiring-measurements.json` records the fifteen audit roots and their
dependencies. No new colouring certificate, complete-theorem dependency,
or additional catalogue compression is claimed.

```sh
python3 tools/fourcolor/classical/coupled_wiring_probe.py
```

The replay extracts the reference four-edge contract and checks the exact
108-word boundary support of both its six-vertex network and the two-vertex
wiring. Forgetting the common central edge admits 216 spurious words.
Thirty-two geometric samples test both orientations and connected or
disconnected exteriors. Eight connected planar samples preserve the sphere
and bridge-freedom. Four planar disconnected-exterior samples introduce a
bridge; all four original maps have triangular faces. These are bounded
controls for the next geometric theorem, not a refutation of the intended
normal-form domain or a coverage theorem.

## Actual joint-diamond occurrences

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.JointDiamondOccurrenceAudit
```

An exact fourteen-vertex occurrence supplies an actual internal hexagon.
Euler counting, the eight-port cut argument and spherical boundary order
derive exterior connectivity and physical Kempe closure. Triangle exclusion
separates the free wire endpoints. The actual smaller wiring and its whole-map
colouring reconstruction therefore no longer assume these exterior conditions.
The count decreases by twelve. The occurrence is still an input; recognition
from face lengths remains open. The strict reduction below now proves
smaller-map class preservation.

`joint-diamond-occurrence-measurements.json` records twenty audit roots,
23,910 dependency declarations, artifact hashes and the regression gates.
Standard axioms only; no new colouring certificate or catalogue saving.

```sh
python3 tools/fourcolor/classical/joint_diamond_occurrence_probe.py
```

The replay propagates the literal dart generators from every root in the
137 saved fullerene rotations. It checks all rotations, internal reversals,
fourteen distinct vertices and eight genuine outgoing ports. Across 15,864
roots it finds 1,424 occurrences on 712 vertex subsets in 126 maps. Every
exterior is connected. Every wired graph is connected, bridgeless, loop-free
and spherical, with twelve fewer vertices. Internal-six connectivity of
the fixture collection is not certified by this census. The report retains
per-map counts, representative witnesses and an ordered census digest.

## Strict coupled-wiring reduction

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.JointDiamondReductionAudit
```

In `JointDiamondOccurrenceReduction`, `strict_reduction_of_occurrence` proves
the entire reduction from a supplied exact occurrence under normal form. The
actual replacement remains connected, bridgeless, spherical and cubic. It has
twelve fewer vertices, including both new vertices. Smaller-map minimality
supplies a colouring, and the shared joint repair reconstructs the original.

`JointDiamondCutLifting` extends hypothetical exterior cuts through the old
core. The coupled four-port case needs two extensions, with four and ten old
vertices respectively. Internal-six connectivity applied to both cuts rules
out the new bridge. `OpenTanglePortFaceCount` and `DiamondCoupledWiringFaces`
account for both free wires through exact ordered returns. The decreases are
twelve vertices, eighteen edges and six faces, preserving Euler characteristic.

`joint-diamond-reduction-measurements.json` records 28 audited roots and
28,002 dependency declarations, standard axioms only. The complete Four Colour
endpoints, original configuration certificates and superseded independent
diamond repairs are excluded from the new theorem dependencies.
The complete baseline still retains 633 configurations and 629 original
configuration certificates. Recognition from a face pattern and broader
coverage remain separate obligations.

```sh
python3 tools/fourcolor/classical/joint_diamond_class_probe.py
```

This independent replay reads the literal source and wiring incidence tables.
It checks all 1,024 binary seam assignments, their eight zero-cut assignments,
the four old-core extensions and the complete face corrections. The receipt
keeps these finite geometric checks separate from the Lean theorem for
arbitrary qualifying exteriors. No new colouring certificate is introduced.

## Structural source choices for dual-and-truncate maps

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.DualTruncateStructuralAudit
```

`CoupledThreeColouring` proves a finite Brooks argument: in a graph of maximum
degree at most three, two nonadjacent neighbours of a closing vertex may share
a colour when their deletion leaves a connected graph. Connectivity supplies
a reverse-distance order, including a later neighbour at every earlier
insertion. The closing insertion retains the joint initial choice. A connected
noncomplete graph whose every two-vertex deletion is connected supplies the
pair from an actual shortest path.

`DualTruncateStructuralColoring` translates these source choices to nonzero
Klein colours and consumes them in the literal reconstruction and every
complete GSLT sweep. `DualTruncateCoupledExample` proves actual paths in the
cube's retained graph and reconstructs its 24-vertex target. The audit checks
19 roots, excludes source colour-word certificates and complete Four Colour
endpoints, and uses only the standard axioms.

```sh
python3 tools/fourcolor/classical/coupled_source_colouring_probe.py --check
```

The replay reads no source colour words. It derives fresh shared choices,
checks every target dart through the independent literal adapter, and checks
all 14,564 two-vertex deletions across the five residual sources. Every deletion
is connected. These five structural-domain checks remain program evidence;
the general theorem and cube consumer are kernel checked. The receipt
`coupled-source-colouring-measurements.json` records this scope, fingerprints
and kernel cost. The source-domain bridge for recognized inverse targets
and occurrence coverage remain open; the forward spherical geometry is
established below. No additional catalogue entry or original configuration
certificate is removed.

## Source connectivity from cyclic cuts

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSourceAudit
```

`CubicPairDeletionConnectivity` derives connected deletion of every pair of
distinct vertices from simple cubic degree and cyclic edge-connectivity at
least four. The proof counts the actual outgoing darts of two different
retained components inside the six darts starting at the deleted pair. One
component has at most three crossings; the reused forest-boundary theorem
forces a cyclic cut on that boundary, contradicting the hypothesis.

`DualTruncateCyclicSource` consumes the cut result in actual source colours,
literal target Tait reconstruction and every complete GSLT sweep. A
connected noncomplete source supplies its initial pair; a specified suitable
nonadjacent neighbour pair retains equal colours. No per-deletion
connectivity certificate or source colour word is a theorem input.

`DualTruncateCyclicSourceExample` proves the cube's cut condition with an
exact interpretation of its finite boundary observation. All 256 vertex
sides are covered by that check; the uniform theorem then derives all 28
pair deletions and reconstructs the 24-vertex target. The audit checks 18
roots and excludes source colour-word certificates and complete classical
endpoints.

```sh
python3 tools/fourcolor/classical/cyclic_source_connectivity_probe.py --check
```

The independent replay reads the cube's flat neighbour table, verifies all
cuts and pair deletions, and derives fresh coupled source choices. A
ten-vertex cubic separator diagnostic violates the cut domain and has a
disconnected pair deletion. The measurement receipt records this program
evidence separately from the kernel theorem, source domain and consumers.
Recognized inverse sources and global coverage remain open. Forward spherical
geometry is established below. Catalogue and original-certificate counts
remain 633 and 629.

## Dual-and-truncate face geometry

```sh
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.DualTruncateGeometryAudit
```

`DualTruncateFaceGeometry` classifies the actual target faces by a complete
joint tag: a source vertex or a source quotient face. Cyclic source vertex
rotations make this classification exact. A cubic source vertex produces a
hexagon, and a source face keeps its length. The face bijection proves Euler
preservation and separates the facial sides of every target edge. Source
pentagonal and hexagonal facial boundaries persist when the source boundary
simplicity hypothesis is supplied.

`DualTruncateMapGeometry` lifts actual source walks and derives target
bridge-freeness from distinct facial sides. It establishes every field of the
existing connected, bridgeless spherical cubic map class from a connected
cubic spherical source with cyclic vertex rotations. Source bridge-freeness
is not required. The colouring consumers combine these results with the
cyclic-cut source supplier and every complete faithful GSLT sweep.

`DualTruncateGeometryExample` derives the cube source geometry and its
24-vertex, 36-edge target with six square faces and eight hexagons. The audit
checks 19 roots and excludes complete classical endpoints and source
colour-word certificates.

From the repository root:

```sh
python3 tools/fourcolor/classical/dual_truncate_geometry_probe.py --check
```

The replay checks actual face identities and lengths, Euler, connectivity,
bridge-freeness and the exact saved target adapters for five residual pairs,
in addition to the kernel cube. It reads no source colour words. A diagnostic
with split source vertex rotations refutes the face-count formula when the
cyclicity condition is dropped. `dual-truncate-geometry-measurements.json`
records fingerprints, kernel costs and the distinction between the uniform
theorem, the kernel cube and the larger program checks. The five larger
source geometry and cut domains are not yet kernel-certified.

The forward geometric theorem is proved. Inverse recognition and occurrence
coverage remain open. This changes source vertex colouring to target edge
colouring; it does not establish an unconditional Tait-to-Tait reduction.
Catalogue and original-certificate counts remain 633 and 629.

## Joint repair of the two port-six boundary forms

```sh
cd lean/fourcolor-classical
lake build kernelStripSixJointRepair
```

`StripSixJointRepair` repairs both boundary forms in
`StripSixConnection.input`. Sixteen local stages use the same
`KempeRetainedMatching.two_anchor_coclosure` theorem. Each of the 82 selected
continuations either enters an earlier stage or reconstructs the complete
D0099 core through the existing symbolic ear relations. Paired choices keep
one actual exterior matching. No table of complete colouring witnesses is
introduced, and later theorem applications require no strategy synthesis.

`StripSixJointRepair.classified_repair`, in `StripSixJointReconstruction`,
consumes an actual zero/one component containing port six and excluding
port eight, together with the existing boundary-list hypotheses. It needs no further zero/two separation
guard. `disk_compatible` derives the exterior closure from a planar rotation
with one ordered facial boundary and triangular remaining faces, using the
Gonthier/Emery Kempe theorem. `disk_whole_repair` also consumes complete
source-core stars and exact exterior coverage, reconstructs an ambient
colouring, and proves that the exterior has strictly fewer vertices.

The initial colouring must lie in the stated two-form domain. This is not
an unconditional reduction for every smaller colouring, nor a theorem that
every planar graph supplies this patch. No physical switch-count bound,
near-linear runtime, catalogue deletion or complete-assembly dependency
saving is claimed. The audit excludes complete Four Colour endpoints,
original bulk certificates and the large wheel/exceptional repair tables.
Measurements are recorded in `strip-six-joint-repair-measurements.json`.

## Cyclic core coverage with shared boundary vertices

```sh
cd lean/fourcolor-classical
lake build kernelCyclicCore
```

`CyclicCoreStars.covers` proves a common geometric law: a nonempty source
neighbourhood closed under the actual cyclic vertex rotation covers every
ambient neighbour. It needs no injectivity or degree equality. The existing
D0092 star theorem and `StripCyclicReading.Reading.core_stars` for D0099
both consume it. The source-specific checks only verify that the decoded
rows have the required predecessors.

`StripSixJointRepair.whole_repair_of_core_injective` weakens the former
global injectivity hypothesis: core vertices remain distinct and boundary
vertices stay outside the core, but boundary vertices may coincide.
Agreement with the same actual exterior colouring retains the resulting
equal-colour constraints. The original globally injective theorem is a
specialization. `StripCyclicReading.Reading.whole_repair` derives the core
star premise from the cyclic reading and reconstructs the whole colouring,
with a strictly smaller exterior.

Exterior Kempe closure, exact exterior coverage and the initial two-form
boundary domain remain hypotheses of this earlier consumer. The common
deletion law below now supplies the first two from actual geometry.
Universal occurrence supply is still open. This is a shared
geometric argument and a strengthened repair consumer; no catalogue entry,
original configuration certificate or complete-assembly check is removed.
Replay measurements are in `cyclic-core-measurements.json`.

## Common core deletion with identified boundary vertices

```sh
cd lean/fourcolor-classical
lake build kernelPatchDisk
```

`PatchDisk.Source` describes a finite source through its core rotations,
short boundary fans, adjacent triangle tips and exact core-incident dart
count. D0092 and D0099 satisfy this same contract. A reading preserves
these turns in the ambient graph, keeps core vertices distinct, prevents
boundary vertices from entering the core, and is injective on each core
neighbourhood. Exact prescribed core degrees supply the last condition
from cyclic star coverage. Boundary vertices need not all be distinct.

`PatchDisk.Reading.outside_planar` derives the actual exterior geometry
from a connected spherical triangulation and such a reading. Deleting the
core retains a connected graph with the ordered facial boundary and
triangular remaining faces. The proof identifies every removed dart and
vertex, then transfers Euler balance. It is uniform in core size, boundary
length and ambient size under the stated source contract.

`PatchDiskRepair.d0099_repair` consumes this geometry in the existing
two-form joint repair. It requires no separate exterior-planarity or
Kempe-closure premise: an initial exterior colouring in the specified
domain reconstructs a whole colouring agreeing with the repaired exterior,
and the exterior is strictly smaller. The existing D0092 planar-exterior
theorem now applies the same deletion law.

`PatchDiskFoldedExample` checks an actual 19-vertex spherical triangulation
where source ports zero and two coincide. The eight core vertices remain
distinct. Deletion leaves eleven vertices and an eleven-dart facial
boundary whose vertex list has a repeated entry. This is a geometric
example, not a claim about minimal counterexamples or supply of a repair
colouring.

The sixteen-root audit checks the common geometry, both source adapters,
actual reconstruction and the folded example. It excludes complete Four
Colour endpoints, original bulk certificates and the large repair tables.
The new finite checks concern small source rows and this example; no table
of colouring witnesses is added. Costs and source hashes are recorded in
`patch-disk-measurements.json`.

Initial boundary-class supply, repair of arbitrary smaller colourings and
universal occurrence coverage remain open. No catalogue entry, original
configuration certificate or complete-assembly check is removed.

## Limits of single-contraction boundary supply

```sh
cd lean/fourcolor-classical
lake build kernelStripContractionSupply
```

The D0099 reconstruction above still needs a suitable starting boundary.
`StripContractionSupply.no_domain_supplier` tests one proposed way to obtain
it: choose an internal edge, contract it, and use a colouring of the smaller
graph. The theorem excludes every one of the thirteen internal edges as
a guarantee that **all** smaller colourings enter the selected repair
domain. That domain is exactly direct source extension or one of the
sixteen `StripSixJointRepair` and eleven `StripChainRepair` stages, allowing
edge-colour permutations with the ordered ports fixed.

Three boundary words suffice for the obstruction. For each contraction,
the proof constructs a proper colouring of the actual eighteen-vertex
`SimpleGraph.map` quotient of the nineteen-vertex source. The quotient
identifies precisely the chosen edge endpoints. Its boundary does not
extend to the source while fixed and does not match any selected stage.
Only ninety-one interior-colour digits are stored. The twelve-root audit
checks the source, quotient, extension semantics and domain exclusion;
it excludes the complete theorem, bulk certificates, large repair tables
and the repair-stage proofs themselves.

An independent replay also enumerates the source boundary modulo vertex
colour renaming, keeping port order. There are 7,381 proper classes:
1,587 extend directly and 5,794 do not. The `StripSingletonRepair.before`
list domain contains seven proper classes, of which five do not extend.
Of all nonextending classes, 5,767 lie outside the selected twenty-seven
stages. These census counts are program checks, separate from the Lean
obstruction. Replay them with:

```sh
python3 tools/fourcolor/near-linear/audit_strip_contraction_supply.py
```

The result does not exclude further Kempe recolouring, another replacement,
or a successful choice of smaller colouring. It does not assert that these
witnesses occur in every admissible ambient geometry. In particular, it
does not refute compositional reducibility or compact coverage. It rules
out a specific unconditional input-supply shortcut. Measurements and
source hashes are in `strip-contraction-supply-measurements.json`; no
compression or catalogue reduction is credited.

## Compatible repairs can defeat greedy flexibility scores

```sh
cd lean/fourcolor-classical
lake build kernelStripFlexibility
```

`StripFlexibilityBarrier` tests a proposed structural progress measure for
the D0099 core: the cardinalities of the six exact elimination relations.
Both inputs of `StripCriticalChain` start with sizes `(3,2,2,2,1,0)` and
already have compatible repair theorems in `StripChainRepair`.

For each input and each of the three nonzero Kempe difference colours,
the new theorem supplies an admissible noncrossing matching. Every subset
of its whole chords preserves the original matching chromogram and weakly
decreases every relation size. The terminal relation stays empty, so none
of these one-round outcomes extends to the source. Only six matchings are
stored; there is no new table of core-colouring witnesses or repair stages.

`no_greedy_score` is uniform over every monotone function from the six
cardinalities to any preordered score space. Such a score cannot guarantee
strict improvement against every admissible matching. This includes
positive weighted sums and monotone lexicographic scores.
`repair_despite_barrier` pairs this obstruction with the existing repair
of both inputs. The audit also checks the existing actual-exterior
consumer, which reconstructs compatible source and exterior colourings.

These are boundary-contract obstructions in the universal matching model.
No simultaneous realization of the three adversarial matchings by one
physical exterior is asserted. Neutral steps, temporary decreases,
nonmonotone scores and more informative summaries remain possible.
The result does not refute compositional repair.

An independent program also tests the complete finite boundary domain:

```sh
python3 tools/fourcolor/near-linear/audit_strip_flexibility.py --full-domain
```

Of 7,381 boundary classes modulo colour renaming, 1,587 extend directly.
Iterating the exact rule “choose a palette, then for every noncrossing
matching choose a batch reaching an earlier layer” repairs the remaining
classes in seven layers, with sizes 1,068, 1,067, 1,192, 1,350, 893, 176 and
48. The program inspects 238,457 matching layouts. Each of six tested
simple scores stalls on some inputs; the full iteration leaves none.
This is finite program evidence, not a Lean certificate for all boundary
classes, a physical-switch bound or geometric coverage in arbitrary maps.

The useful distinction is between a terminating staged repair and a repair
that must increase local flexibility at every stage. The former remains
available for the two certified inputs; the latter fails under the stated
model. Measurements and source hashes are in
`strip-flexibility-measurements.json`. No coverage entry, original
certificate dependency or complete-assembly check is removed.

## A uniform first phase for all D0099 boundary colourings

`StripEndPhase.repair` restores the left core triangle for every proper
boundary assignment. When this triangle cannot be coloured, its two outer
vertices have the same forced colour. The exchange at boundary edge four,
with difference `b(4) + b(6)`, removes that conflict for every possible
partner. A partner before the anchor repeats one attachment colour; the
next partner changes the forced colour; every later partner repeats another
attachment colour. These three cases give one argument over arbitrary
boundary assignments. No complete boundary-word or core-colouring table
is stored.

The proof recovers the matching supplied by the exterior, retains its
chromogram, and reconstructs a genuine colouring of the induced source
containing all eleven ports and core vertices 0, 1 and 3. The source and
exterior witnesses agree at every port. `StripEndPhase.from_reading`
derives exterior closure from an actual source reading in a spherical
triangulation; it requires no selected initial boundary word and allows
boundary identifications. `disk_consumer` applies the same law to the
previously certified physical disk. Five core vertices remain to restore.

```sh
cd lean/fourcolor-classical
lake build kernelStripEndPhase
```

The independent first-phase replay checks all 1,093 initially obstructed
classes among the 7,381 proper boundary classes, including every distinct
anchor partner. The optional continuation experiment asks whether the
remaining repair can keep the left triangle colourable at each stage:

```sh
python3 tools/fourcolor/near-linear/audit_strip_end_phase.py --phase-game
```

All 6,288 left-feasible classes succeed in that finite matching game:
1,587 extend directly, and seven further layers contain 938, 868, 1,003,
1,118, 645, 116 and 13 classes. This is program evidence for a staged
continuation, not a Lean second-phase proof or a bound on physical Kempe
switches. A compact structural explanation of the remaining phases is open.
In particular, colourability of the two end triangles separately does not
assert a compatible colouring of the entire core.

The ten-root audit excludes complete Four Colour endpoints and large
repair certificates. Source and replay measurements are in
`strip-end-phase-measurements.json`. This is partial restoration, not a new
complete source reduction; coverage remains 633 entries with 629 original
configuration certificate dependencies. No compression credit is assigned.


## Composing the triangle phase with an adjacent diamond repair

`StripDiamondPhase.repair` restores core vertices 0, 1, 2 and 3 for every
proper D0099 boundary. It first consumes the end-triangle theorem, then
adds the fourth vertex through a joint repair. The second phase retains
the same exterior predicate and may change the triangle's colours.
`compatible` reconstructs one source colouring agreeing with a genuine
exterior colouring at every ordered port. `from_reading` obtains exterior
closure from the spherical triangulation, including identified ports.

Failure to extend the first triangle has three equality patterns on the
six consecutive ports 3 through 8. Up to colour renaming, these are
`010231`, `010230` and `012020`. If ports 8 and 3 agree, exchange at edge
4 with difference `b(4) + b(6)`; otherwise use edge 3 with difference
`b(3) + b(6)`. Each choice works for every distinct matching partner.
The classification and local release laws use bounded kernel computation
on six boundary observations; they store no complete boundary words, matchings or core
colouring witnesses.

```sh
cd lean/fourcolor-classical
lake build kernelStripDiamondPhase
lake build kernelStripDiamondContinuation
```

The independent replay checks the local predicate against the actual
source adjacency over all 7,381 boundary classes. The 548 inputs with a
colourable triangle but an uncolourable diamond fall into the three
patterns; all 5,480 partner updates pass. Replay it with:

```sh
python3 tools/fourcolor/near-linear/audit_strip_diamond_phase.py
```

This is a two-stage partial repair. Four core vertices remain; a full
repair with a structural progress argument and geometric coverage is open.
The twelve-root audit excludes complete Four Colour endpoints and the
large repair tables. `strip-diamond-phase-measurements.json` records source
hashes, replay costs and the unchanged compression counts. No catalogue
entry or original certificate dependency is removed by this result.

## Triangle support, exact gluing and a repaired obstruction

`StripTriangleConsistency.compose_iff` composes the two D0099 halves on
their common vertices 2 and 4. For every boundary, a shared pair in both
interface relations is equivalent to a complete core colouring.
`source_iff` reconstructs the actual decoded source when its boundary is proper.

The boundary trace `12212233312` distinguishes this joint interface from
iterated triangle support. Every retained colour has a compatible assignment
on every incident triangle, and all eight vertex domains remain nonempty.
Nevertheless the left half permits only the interface pair `(2,1)` while
the right half permits `(3,1)` or `(3,2)`. Lean proves nonextension and the
failure of local triangle support as a sufficient gluing condition.

`StripTriangleConsistencyRepair.compatible_changed` supplies the positive
control: this same boundary has a complete repair in any compatible
Kempe-closed exterior. A half-block matching law selects one of four
successful exchanges: `(6,7)`, `(7,8)`, `(8,10)` or `(7,4)`. The reconstructed
source and exterior colourings agree at every ordered port. The boundary
trace must change.

```sh
cd lean/fourcolor-classical
lake build kernelStripTriangleConsistency
```

The independent program `audit_strip_triangle_consistency.py` compares
triangle filtering with direct source colouring on all 7,381 canonical
proper boundaries. It finds 1,587 direct extensions, 5,793 local rejections
and this one surviving obstruction. That census is program evidence;
Lean proves the specific obstruction, the uniform composition theorem and
its compatible repair. The fifteen-root audit excludes the complete Four
Colour theorem and the large repair tables. Measurements are recorded in
`strip-triangle-consistency-measurements.json`.

This adds a precise limitation and a repaired example. Universal D0099
repair and geometric supply remain open. The coverage and configuration
certificate counts remain 633 and 629; no compression credit is assigned.

## Protecting one repaired end while repairing the other

`StripProtectedEnds.safe_exists` proves that every proper colourable left
end triangle has a nonzero palette preserving its colourability under any
suffix exchange of its five boundary observations. This does not guarantee
that the palette also satisfies the other end's repair conditions.

`StripProtectedEnds.repair` supplies a shared repair for an alternating
right-end family when that intersection condition holds. Its boundary
observations at positions `(9,10,0,1,2,3)` have the form `(x,y,x,y,x,z)`.
The palette satisfies `f != 0`, `f != x+y`, and either `z=y` or `f=x+z`,
with `x != y` and `x != z`. A component exchange anchored at edge 9 restores
the right end for every partner supplied by the exterior matching. The
safe-palette hypothesis retains left-end colourability.

The two end witnesses reconstruct the actual source with only core
vertices 2 and 4 omitted. `compatible` aligns every ordered boundary port
with a colouring of the same exterior; previously chosen interior colours
may change. `from_reading` supplies exterior closure from an actual D0099
reading in a connected spherical triangulation. The repair conditions on
the boundary remain explicit. Two concrete boundary forms consume the
same theorem.

```sh
cd lean/fourcolor-classical
lake build kernelStripProtectedEnds
```

The thirteen-root dependency audit excludes complete Four Colour endpoints
and the large repair tables. `strip-protected-ends-measurements.json` records
17,465 bytes of new Lean source and 25.269 seconds of frontend checking with
prebuilt dependencies. Small finite palette checks remain; no boundary
strategy table or interior colouring table is stored.

The independent `audit_strip_protected_ends.py` census finds 176 canonical
boundary classes satisfying the family and protection conditions. Its
optional `--phase-game` test finds that all 6,288 left-colourable classes
can reach the 4,503 both-end-colourable classes while retaining the left
end, and all 4,503 can reach full extension while retaining both ends.
Those finite matching games are discovery evidence, not Lean termination
theorems. Their invariants hold at batch endpoints; they do not provide a
bound on physical component switches.

The new theorem is a conditional six-vertex restoration. General protected
preparation, restoration of the two bridge vertices, strict reduction and
geometric supply remain open. No coverage configuration or original
certificate dependency is removed; the counts remain 633 and 629.
