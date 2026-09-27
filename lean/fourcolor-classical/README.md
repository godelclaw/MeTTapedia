# Classical Four Colour and compositional reconstruction

This package combines [Chris Emery's Lean port](https://github.com/corun1024/4ct)
with MeTTapedia's GSLT colouring-witness semantics. It reuses the classical
mathematics of Robertson, Sanders, Seymour and Thomas, following Gonthier and
Werner's formalization. The dependency is pinned to
`3db71e0a786a1f19be04c5266fe3d06fed216885`; `LICENSE` retains its MIT notice and
upstream attribution.

The current root exposes the checked reconstruction and conditional assembly.
The additional `OrbitAssembly` endpoint supplies the arity-ten presentation
using rotation and reflection to share certificates. Reducibility and the
other six arities remain explicit inputs to that endpoint. The full baseline
replay must pass before an unconditional integration root is accepted.
`Orbit11Assembly` also supplies the arity-eleven presentation by semantic
reflection, leaving reducibility and the five lower arities explicit.

The source dependency is `../externals/fourcolor`, prepared by the repository's
`lean/bootstrap_local_repos.sh`. It uses Lean 4.34.0-rc2 and the same pinned
Mathlib as Mettapedia. The compatibility preparation changes the obsolete
`Mathlib.Basic.Denumerable` import to `Mathlib.Logic.Denumerable`; it changes no
proof body.

```sh
python3 lean/fourcolor-classical/scripts/prepare_reference.py
```

The preparation verifies the source revision and the complete original file
before making the import edit. It refuses unrelated local changes.

## Kernel build

First prepare the reference's generated certificates and proof artifacts, as
described in [the source and measurement record](../../tools/fourcolor/classical/README.md).
The reference uses `scripts/build_pool.py` to avoid unnecessary native C output
for its large proof certificates. Its artifacts do not have Lake's ordinary
incremental-build traces, so a normal `lake build` would repeat that work.

With the reference and the imported Mettapedia libraries already built:

```sh
cd lean/fourcolor-classical
lake build kernelAdapters
lake env lean MettapediaFourColor.lean
```

The target checks the pinned revision, compiles the adapter sources into this
package's ordinary Lean artifact directory, and audits the imported public
declarations against `propext`, `Classical.choice` and `Quot.sound`. It records
source hashes and exit statuses in `.lake/adapter-audit/adapter-results.json`.
If reference artifacts live elsewhere, set `FOURCOLOR_REFERENCE_ARTIFACTS` to
that artifact directory.

To check the coverage proof that consumes shared certificates, also prepare
the reference checker modules `Present10Chk1` through `Present10Chk24`.
The nine modules reconstructed by the target need their source but do not
need their original proof artifacts. Then run:

```sh
lake build kernelOrbitPresentation
```

This target reconstructs fifteen presentation modules from exact, hashed
reference sources, in the namespace `FourColor.Orbit10`. It replaces the twenty
checks for `f10_128` and `f10_242` with the five representatives supplied by
`PeriodicHubcap` and `ReflectedHubcap`. It also removes 67 checks from 21 other
hubcaps, using semantic reflection and exchange of paired endpoints to
assemble each hubcap from retained representatives. The cover data and
split trees are preserved. Unaffected proof bodies are retained. Import names
and namespaces change so the original
and modified developments remain distinct. The generated sources,
including the reference licence and credits, are available in
`.lake/orbit-audit/src`; compilation receipts are in `orbit-results.json` in
the same audit directory.

`OrbitAssembly.fourColorTheorem_of_checks` consumes the resulting `exclude10`.
The audits verify that its dependency graph includes every semantic replacement
and the explicit colouring reconstruction, and that all 87 superseded check
declarations and the original arity-ten theorem are absent.

The next target composes this presentation with shared arity-eleven certificates:

```sh
lake build kernelOrbit11Presentation
```

It requires the reference's `Present11Defs` artifact and the shared arity-ten
package. It reconstructs all nine arity-eleven presentation modules, followed
by `Orbit11Assembly` and `Orbit11Audit`. Its generated sources and receipts are
in `.lake/orbit11-audit`. Both the graph-colouring and exact source-construction
endpoints consume all thirteen new semantic hubcaps. The audit excludes all
62 replaced arity-eleven checks, the 87 superseded arity-ten declarations and
both original arity coverage theorems.

## What is preserved

The hypermap dictionary preserves actual dart permutations, components and
planarity. Reconstruction retains compatible disk and exterior colourings as
GSLT witnesses and glues them into an explicit ambient colouring. The graph
bridge preserves every supplied dart colour while descending to a colouring
of the original simple graph; isolated vertices receive zero.

`HypermapTransport` relabels darts through an equivalence, preserving all
three permutations, components, planarity and face colourings. Relabelling
through a finite ordinal makes the catalogue theorem available for finite
dart carriers in any Lean universe.

`SourceTait` connects that theorem to the original spherical cubic map class.
The source Euler equation and connected cyclic rotations imply reference
planarity; the existing bridge theorem supplies two-sided faces. Adjacent
face colours determine nonzero edge differences, which descend through the
existing dart-colouring adapter to the original literal edges, including
parallel edges. The exact colour formula is proved at every dart.

`OrbitAssembly.supported_source_construction_of_checks` supplies a closed
GSLT construction trace, an exact geometric model of the source, and
compatible colouring witnesses. It consumes the shared arity-ten proof,
with reducibility and the other six presentations still explicit. The
dependency audit follows this source-construction endpoint independently
of the plane-drawing endpoint and requires every semantic hubcap in both.

The reference's Kempe-closure argument selects compatible assignments using
classical choice. The adapter does not extract an executable Kempe-move path.

`PlaneDrawing` gives a second graph endpoint using actual noncrossing paths in
the real plane. Its data are distinct vertex positions, an injective continuous
path for each oriented edge, reversal of paths when edges are reversed, no
vertices in edge interiors, and disjoint interiors for different unoriented
edges. It has no rotation, Euler characteristic, or colourability field.

The proof cuts every edge at its midpoint. The closed half-edges incident to
each vertex form a compact site; deleting their outer midpoints gives its
connected, dense exclusive core. The regions strictly nearest to these sites
are open, connected and pairwise disjoint. An edge midpoint is a non-corner
contact of exactly its endpoint regions, so their map colours give different
vertex colours. Empty graphs, disconnected graphs and isolated vertices need
no extra assumptions. The region map can have extra adjacencies; the transfer
uses preservation of every original graph edge, rather than an isomorphism
of adjacency relations.

`NearestRegions.isConnected_region` proves the metric part in any real normed
space, without convexity of the sites. `CompactPlaneMap` proves the precise
contact-to-adjacency and colouring transfer. `PlaneDrawing.colorable` constructs
all their geometric inputs from the drawing and concludes Mathlib's
`SimpleGraph.Colorable 4`, assuming the plane-map Four Colour theorem.
`OrbitAssembly.colorable_of_planeDrawing` supplies that plane-map theorem from
the GSLT reconstruction and shared arity-ten proof. Its remaining hypotheses
are reducibility and the other six arity presentations. The dependency audit
checks that the graph endpoint consumes the geometry and the shared certificate.

## Compression baseline

The reference contains 633 configurations, rings up to size 14, and 32 published
discharging-rule labels. Its own packed-data and uniform checker techniques
belong to the baseline.

`HubcapOrbit.oneEntries_fit_periodic` assembles a hubcap from one certificate
per distinct rotated boundary input. Its consumer `PeriodicHubcap.succeeds`
closes the reference's part `p10_127r` with two representative checker
computations instead of the ten used for `f10_128`. A finite kernel check also
verifies the equalities of the rotated parts; the general lemma transports
the two certificates to all ten positions. The original ten check theorems
are not imported by this consumer. `HalfTurnHubcap.succeeds` applies the same
lemma to `p10_241r`: its period-five boundary reduces the ten checks for
`f10_242` to five representatives, again with a separate finite check of the
rotated-part equalities.

`ReflectedHubcap` further reduces those five representatives to three.
`ChargeBound` converts a checker result into a bound on the actual edge
charge. The reference's mirror-map and charge-invariance theorems transport
this bound through reflection; a general summation lemma combines bounds
around the hub to rule out a positive charge. This proof does not assume
that the Boolean checker commutes with reflection. The intermediate
`HalfTurnHubcap` remains available as a comparison, but the coverage proof
now consumes the stronger semantic certificate.

`HubcapCharges` separates the weighted-cover argument from its graph input.
Its arithmetic theorem applies to arbitrary integer charges constrained by
single-edge or paired-edge bounds. `PairChargeBound.of_check` supplies semantic
paired-edge bounds, and `Hubcap.successful` combines these with transported
single-edge bounds. `PairChargeTransport` proves that paired bounds also
transport through reflection and exchange of endpoints, with the part and
offset changed together. The combined symmetries remove 67 computations
across 21 hubcaps, reducing their 188 checks to 121. Every replacement is
verified as a dependency of both the graph-colouring and source-construction
endpoints.

The reduction of 82 independent discharging checks is consumed by the
complete arity-ten coverage proof and the conditional `OrbitAssembly` endpoint.
Its 2,580 explicit checker obligations become 2,498, with 69 separate finite
checks of boundary-input identities or classifications.

`Orbit11Assembly` composes that result with thirteen arity-eleven hubcaps whose
140 computations become 78. The entire arity-eleven presentation goes from
571 to 509 independent checks, with 62 separate full-input reflection identities.
Across both arities, 3,151 checks become 3,007: 144 independent computations
are replaced, and 131 identity or classification checks are counted separately.
Both colouring endpoints consume all replacements.

All 633 configurations remain. An unconditional assembly with all seven
arities and all reducibility certificates is still pending. Exact counts and
measurement scope are recorded in the
[compression ledger](../../tools/fourcolor/classical/compression-ledger.json).
The small pilot shows no measured runtime or artifact-size improvement after
including the generic lemma; those savings are recorded as zero.

A compression result must identify the uniform lemma, the configurations or
checks it replaces, and the kernel-checked consumer. Removing configurations
from the unavoidable set additionally requires a new coverage proof. Certificate
sharing and a smaller unavoidable set are recorded separately.
