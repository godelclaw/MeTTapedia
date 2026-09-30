# Classical Four Colour sources and compression baseline

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
audit excludes the original configuration 1, 2 and 4 certificates; 630 original
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
degrees. The complete proof still retains 633 configurations and 630 original
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
lake build MettapediaFourColor.PentagonalCoronaChordExclusionAudit
```

The Lean theorem constructs both cycles and all outer turns from actual face
lengths. Distinctness of the sixteen traced vertices remains explicit.
Outer inducedness now follows from minimality: a chord would consume two of
six possible outward darts and create a forbidden cyclic cut of at most four
edges. The general boundary theorem uses cubic forest counting and allows a
disconnected exterior. The joint repair then gives the strict twelve-vertex
ambient reduction with genuine colouring reconstruction. The ten-root audit
checks 26,634 dependencies using the standard three axioms and excludes
complete Four Colour endpoints, catalogue certificates and diamond reducibility.
`pentagonal-corona-chord-measurements.json` records the scope, source/artifact
pairs and module costs. The earlier `pentagonal-corona-measurements.json`
remains the historical receipt for the version assuming outer inducedness.
No additional colouring enumeration or complete-proof certificate saving is claimed.

A separate local count can be replayed from the repository root:

```sh
python3 tools/fourcolor/classical/pentagonal_corona_chord_probe.py
```

The six outward positions have fifteen unordered pairs. One pair is already
a perimeter edge; the other fourteen possible chords each leave four outward
darts. `pentagonal-corona-chord-probe.json` retains this bounded test. It does
not construct an exterior or prove minimality; those are separate Lean arguments.
