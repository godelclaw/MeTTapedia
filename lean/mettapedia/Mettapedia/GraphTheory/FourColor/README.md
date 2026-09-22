# FourColor

This is the canonical modern Lean home for the godelclaw Four Color work.

## Goertzel/Fable checkpoint — 22 September 2026

The active proof branch is `goertzel/proofs`. The Four-Color Theorem is **not
proved by this route**. The following distinctions matter when resuming work:

| Part | Checked result | Still needed |
| --- | --- | --- |
| Physical tree fold | Face-return data, face count and colour support agree with the actual shores of a supplied edge-leaf tree. | A globally supplied decomposition of the required bounded width. |
| D1: decomposition supply | Conditional bond laminarity; obstructions to several proposed ways of extracting bounded interfaces and long nested chains. | A construction of the required bounded-interface supply, or another source-faithful reductive construction. |
| D4: route-native finite base | Exact local composition and fold laws are available. | A concrete finite closure with coverage, adequacy and an audit excluding rejecting roots. |

The final D1 checkpoint is `fd1040139`, which corrects an earlier overclaim:
site witnesses share a residual-defect minimizer, but each has its own second
matching `tau`. Their carriers are **not** thereby disjoint or laminar;
consecutive row steps cannot share `tau`. The laminarity theorem is conditional
on hypotheses which have not been supplied for all sites.

Also, arbitrarily large laminar families can be antichains. The singleton-family
counterexamples rule out a universal long-chain guarantee from family size,
even when shores may be complemented. They do not say that no laminar family
has a long chain. `CommonEdgeLaminarShoreSupply` reformulates an open supply
obligation; its equivalence to the chain version does not discharge either one.

Read the exact statements in
[PhysicalProfileFold.lean](PhysicalProfileFold.lean),
[GoertzelV24MeshBondCarrierSeparation.lean](GoertzelV24MeshBondCarrierSeparation.lean),
[GoertzelV24BondDepthObligation.lean](GoertzelV24BondDepthObligation.lean), and
[GoertzelV24DecomposableFiniteBase.lean](GoertzelV24DecomposableFiniteBase.lean).
The living explanatory documents are `papers/benxiv/goertzel_4cp.tex` and
`papers/benxiv/foundations/compositional-proof-spine.tex`, relative to the
repository root. They are status documents, not substitutes for the primary
Goertzel/Fable manuscripts.

### Fresh checkout

Use a separate checkout or worktree for each active lane. For a new destination:

```sh
git clone --branch goertzel/proofs https://github.com/godelclaw/MeTTapedia.git MeTTapedia-4cp
cd MeTTapedia-4cp
bash lean/bootstrap_local_repos.sh
cd lean/mettapedia
lean --version
lake exe cache get
lake build FourColorLane
lake build Mettapedia.GraphTheory.FourColor.ResearchCheckpoint
cd ../..
python3 papers/benxiv/tools/gen_citation_ledger.py --check
```

Use the checked-in `lean-toolchain` (Lean 4.31.0 at this checkpoint) and pinned
dependencies; do not upgrade them as part of a move. Where both Lake files
exist, `lakefile.lean` is selected, not `lakefile.toml`. The bootstrap preserves
an existing dependency checkout and reports a pin mismatch instead of resetting
it. A source-host build is not evidence of a successful fresh-machine build;
run the gates on the destination too.

`ResearchCheckpoint` separately checks preserved supplemental results. Its
minimal-counterexample selection and abstract reflection modules refer to a
**historical, refuted closed-web target**, explicitly marked in
`GoertzelV24SourceHeadlineAssembly`. They are not the active headline and do not
revive that route. `GoertzelV24IrreducibleBaseBurden` bounds only explicit census
cardinality, not proof length or human-checkability. `GoertzelV24TubeCountGrowth`
distinguishes exact path counts from Boolean support in its specified tube.

Git carries the proof sources. Transfer primary manuscripts and any needed
private research reports separately, with appropriate permissions. Session
archives are optional historical context, not build dependencies; do not commit
them, authentication stores, or unrelated unfinished edits to the proof branch.

### Other proof lanes

`ns/lane` and `4cp/knuth-gate-lab` are separate lanes; do not merge them merely
to move machines. Historical local Millennium branch tips are preserved under
`archive/goertzel-20260922/` on the remote, without rewriting their divergent
existing branch names. These archive refs preserve history, not newly verified
proof releases. In particular, an archived branch is not permission to restore
superseded or forbidden proof architectures into this lane.

## Background module guide

The older guide below describes reusable infrastructure, not the current
headline's complete dependency chain.

Read first:

- `ROADMAP.md` - detailed live status and route surface.
- `Goal.lean` - target shell claim and named oracle surfaces.
- `BoundaryChainPeel.lean` - modern algebraic home for the old
  `LeafPeelData`/`LeafPeelSumData` span-induction layer. The preferred
  aggregate interface now explicitly subsumes the old single-face peel
  interface by singleton peel sets. The face-boundary span is exposed as
  zero/addition closed, and both peel interfaces now identify the zero-boundary
  set exactly with that span once their hypotheses are supplied.
- `Orthogonality.lean` - finite-support chain-dot algebra, named
  face-boundary generator sets, and generic span-to-double-orthogonal
  propagation. The peel-data double-orthogonal theorems now use this generic
  generator-set API instead of repeating set comprehensions, and both
  single-face and aggregate peel interfaces expose their generator sets under
  structure-specific names. It also provides annihilator-facing bridges from
  generator-set membership to orthogonality of the generated span and the
  single/aggregate peel zero-boundary sets.
- `Theorem49CertificateFaceBoundarySpan.lean` - algebraic bridge from a
  `BoundaryRootedFacePeelCertificate` order to the finite face-boundary span
  generated by its listed faces. It gives later adapters a clean generator set
  and proves finite sums over listed faces lie in that span. It also propagates
  orthogonality from listed face-boundary generators to the whole
  certificate-generated span and records the corresponding finite-support
  double-orthogonal containment. Its generator-set equivalence lemmas identify
  the listed-face vocabulary with the generic image-face-boundary vocabulary,
  and its annihilator-facing wrappers turn certificate generator annihilation
  into span orthogonality without restating the listed-face generators,
  without claiming the certificate supplies the old aggregate peel interface.
- `SupportFaces.lean` - modern home for the old dynamic-forest support-face
  selector and induced support-dual adjacency vocabulary. It also exposes the
  support-dual graph as a generic `Mettapedia.GraphTheory.FiniteRelation`, so
  support-dual degrees and weak leaf/min-degree facts reuse the shared
  relation layer.
- `RotationSystem.lean` - dart/face-orbit infrastructure plus
  witness-carrying internal-face helpers, the local `InteriorFacePlanarity`
  package, and the stronger `PlanarGeometry` rotation-system layer ported from
  the old standalone package. It deliberately does not derive planarity from
  bare rotation-system data.
- `SimpleGraphRotationSystem.lean` - the first explicit bridge from
  `SimpleGraph.Dart` to the modern bare `RotationSystem` carrier. It proves the
  edge-flip/two-darts-per-edge obligations from Mathlib's dart API, but it does
  not assert vertex-rotation planarity or construct `PlanarGeometry`. It also
  records the exact stronger source object needed next: a global face-successor
  permutation whose conversion proves `RotationSystem.phi` is that successor.
  Concrete examples can build that permutation from explicit successor and
  predecessor functions via `FaceSuccessorFunctionData`.
- `PlanarBoundaryRotationSystem.lean` - bridge from the existing face-local
  `PlanarBoundaryDartSuccessorCycleEmbeddingData` layer to the global
  face-successor data needed by `SimpleGraphRotationSystem`. It records the
  exact compatibility/coverage obligation: one global dart permutation must
  agree with every local listed face successor. It also provides the
  function/predecessor version for finite examples where inverse laws are easier
  to prove than constructing an `Equiv.Perm` directly, direct forgetful bridges
  back to the face-local successor-cycle source, and explicit coverage /
  disjoint-coverage certificates for using local face cycles without hiding the
  coverage hypothesis.
- `Examples/TriangleGlobalFaceSuccessor.lean` - first active concrete example
  of the `SimpleGraph.Dart` global face-successor route: the two oriented
  cycles of the triangle supply explicit successor/predecessor functions that
  lower through the planar-boundary global-face-successor package and then to
  a bare `RotationSystem`. It exposes function-level, permutation-level, and
  face-local successor-cycle existence wrappers for the triangle, and proves
  that the two local face cycles cover the triangle darts disjointly.
- `IncidenceCounting.lean` - endpoint, face-incidence cover, at-most-two
  internal-face incidence, face-orbit toggle parity, and face-degree
  double-counting infrastructure ported from the old rotation/no-digons
  support layers. It includes the explicit-hypothesis bridge from face-orbit
  toggles to vertex-incidence parity and consumes the canonical
  `RotationSystem.InteriorFacePlanarity` package. The old endpoint-set
  injectivity theorem is represented under the honest `PlanarGeometry`
  no-parallel-edges package, not under bare rotation-system data. It also
  represents the old "interior edge has two internal faces" route as exact
  modern incidence lemmas: a non-boundary edge has the two alpha-opposite
  face-orbit edge sets as its incident faces, and under `InteriorFacePlanarity`
  / `PlanarGeometry` this yields membership in the generic
  `InteriorEdgeFacePair` interface. It also ports the old internal-face
  orbit/cardinality bridge as
  `PlanarGeometry.card_faceOrbit_eq_card_faceEdges_of_internal`.
- `RotationDiskData.lean` - disk-style rotation data, interior-dual adjacency,
  spanning-forest witness vocabulary, and no-digons as an explicit hypothesis.
  It includes the named at-most-one-shared-interior-edge elimination theorem
  for explicit no-digons hypotheses.
- `EdgeKempe.lean` - predicate-level edge Kempe components and guardrails
  ported from the old Kempe API without the unfinished parity theorem shells.
- `Shells.lean` - bundled shell hypotheses.
- `Frontier.lean` - strongest current positive and negative wrapper results.
- `Integration/GRAPH_ROTATION_LEAFPEEL_RECONCILIATION.md` - classification of
  old graph, rotation-system, disk/forest, and leaf-peel material.
- `Legacy/` - regression and obstruction records for routes that failed or
  were narrowed.

## Relationship to `lean/fourcolor/`

`lean/fourcolor/` is not merely a duplicate. It is an older standalone Lean
package built around an old proof attempt, but it also contains reusable
background theory that should be integrated here with care.

Potentially useful old background:

- `FourColor/Triangulation.lean`: `Color`, support sets, `chainDot`,
  `swap`, `delta`, `switch`, face-boundary chains, zero-boundary surfaces, and
  the old leaf-peel algebraic span-induction interfaces.
- `FourColor/Algebra/KempeSwap.lean`: swap preservation lemmas.
- `FourColor/Algebra/KempeCycles.lean`: Kempe-cycle predicates and parity
  lemmas.
- `FourColor/GraphTheory/SpanningForest.lean` and
  `FourColor/GraphTheory/WalkExtras.lean`: finite graph/walk infrastructure.
- `FourColor/Geometry/RotationSystem.lean` and related geometry files:
  planar rotation and face-orbit infrastructure.
- `FourColor/Curriculum/`: graph-theory background lessons and examples.

Old proof-attempt files with substantial gaps should not be ported as if they
were background theory. They should be archived or kept as failure records
unless a human/agent proves the missing mathematics.

## Integration Plan

1. Classify old `lean/fourcolor` files into:
   - reusable background;
   - failed proof attempt;
   - tests/scratch/hammer experiments;
   - upstream-shared package scaffolding.
2. Port reusable background into this namespace or a shared
   `Mettapedia.GraphTheory` namespace, one cluster at a time.
3. After each cluster, run the relevant Lean build and record the log.
4. Replace local duplicate definitions only after proving import compatibility.
5. Retire or gitignore the old standalone package only after useful theory has
   a new, build-checked home.

Do not describe the Four Color theorem as proved from this tree. The current
modern route is an active formal audit/proof attempt with remaining obligations.
