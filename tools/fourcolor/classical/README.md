# Classical Four Colour sources and compression baseline

The classical baseline is the 633 configurations and discharging argument of
Neil Robertson, Daniel Sanders, Paul Seymour and Robin Thomas, *The four-colour
theorem*, Journal of Combinatorial Theory B 70 (1997), 2–44. Georges Gonthier and
Benjamin Werner's Coq/Rocq development is the formal reference.

The source survey also found existing Lean ports. A new development should
audit and reuse them before duplicating their mathematics.

| Source | Pinned revision | Declared licence | Role |
| --- | --- | --- | --- |
| [Rocq fourcolor](https://github.com/rocq-community/fourcolor) | `c1d6b1cd5288bea4b067aac13cdde3c18dffe018` | CeCILL-B | Reference construction programs and complete proof |
| [Chris Emery's Lean port](https://github.com/corun1024/4ct) | `3db71e0a786a1f19be04c5266fe3d06fed216885` | MIT, including the attribution notice in LICENSE | Primary compatibility and certificate pilot; Lean 4.34.0-rc2 |
| [Robert D. Barish's Lean port](https://github.com/RBarish-UTokyo/FourColorTheorem-Lean4) | `20fa34599f5189dd569d96dd22f306c94ab1c446` | Apache-2.0 with NOTICE and upstream CeCILL-B text | Independent comparison; Lean 4.35.0-rc2 |

Both Lean repositories claim complete proofs with only `propext`,
`Classical.choice` and `Quot.sound`. A source claim is distinct from a reproduced
build. The local pilot first checks statement fidelity, checker soundness and
representative certificates; full reproduction and the GSLT adapters are
separate obligations. The ports' existing uniform certificate techniques are
part of the baseline, not new compression attributable to this development.

Other surveyed projects include
[tangentproofs/fourcolor-lean](https://github.com/tangentproofs/fourcolor-lean)
(`b2bcd36c7e50848f000af423f23151309c075638`, archived with open proofs),
[WaterKing201030/FourColorTheoremLean](https://github.com/WaterKing201030/FourColorTheoremLean)
(`c36f6d8120024ddf91e4ea4033bfa2842bcecbb8`, an unfinished top-level theorem), and
[TonalidadeHidrica/FourColorTheorem](https://github.com/TonalidadeHidrica/FourColorTheorem)
(`1c0cb61da4f953b29097b12ed1737b09890c7080`, preliminary structures).

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
characteristic two. They are program checks. They do not prove reducibility,
validate discharging, or establish an isomorphism between an original free
completion and its construction program.

Given the four pinned source files, reproduce the inventory with:

```sh
python3 tools/fourcolor/classical_source_inventory.py \
  --configurations unavoidable.conf --rules rules \
  --rocq-programs configurations.v --lean-programs Configurations.lean \
  --output inventory.json
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

## Reconstruction pilot

The adapter sources in `adapters/` connect the classical semantic argument to
the existing GSLT library. They belong to the prepared reference environment;
they are not yet dependencies of the main Mettapedia library. The accompanying
LICENSE retains the reference's MIT notice and Gonthier/Werner attribution.

| Module | Checked obligation |
| --- | --- |
| `CompatibleTraces` | A supplied contract colouring gives matching traces on a configuration and its actual exterior |
| `PatchWitness` | An explicit glued colour function reads back the two supplied assignments, after a constant colour shift on the disk |
| `EmbeddedReconstruction` | The matching assignments remain data at the middle interface of a GSLT reconstruction route |
| `Config4Reconstruction` | The route consumes configuration 4's actual ring-eight certificate and proved decoded-map geometry |
| `ClassicalAssembly` | The conditional real-plane theorem consumes witness reconstruction for every fitted catalogue entry, with the reference's discharging obligations retained |
| `HypermapDictionary` | The two hypermap presentations agree on permutations, components and planarity on the same finite dart type |
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
reference's natural-number genus. The standard finite planar-graph statement
still needs its representation bridge.

To replay the adapters, prepare the pinned reference with the dependency
revisions above and build Mettapedia's imported GSLT and hypermap modules.
The reference artifacts must include `FourColor.Pilot.Cfg003` from the initial
pilot, `FourColor.Bulk.Cfg.Hyb218`, and `FourColor.Present7Chk85`.
The following directory names are example input and output locations:

```sh
python3 tools/fourcolor/classical/replay_adapters.py \
  --reference reference-4ct --mettapedia lean/mettapedia \
  --reference-artifacts reference-artifacts --output adapter-build
```

The script checks the reference revision and common toolchain, makes a
dependency overlay in its dedicated output directory, compiles the seven adapter
modules without native C emission, and finishes with the axiom audit. It records
source hashes, exit statuses and wall times. It changes neither input checkout
and does not generate or check the whole classical catalogue.

The complete adapter replay passed; its final audit covered 15,360 imported
public declarations and found only `propext`, `Classical.choice` and `Quot.sound`.
`reconstruction-measurements.json` records the exact source hashes and results.
The additional kernel measurements were:

| Check | Frontend seconds | Peak RSS (GiB) |
| --- | ---: | ---: |
| Configuration 219, ring 14, all nine certificate modules combined | 1,644.56 | 19.97 maximum across modules |
| Discharging definitions `Present7Defs` | 24.65 | 2.78 |
| Discharging check module `Present7Chk85` | 244.33 | 7.27 |

The configuration theorem is `FourColor.Bulk.Hyb218.reducible`. The discharging
sample checks one module of the arity-seven presentation; it is not the whole
presentation or the unavoidability theorem. The unconditional reference root
has not yet been reproduced by these measurements.

## Compression ledger

The ledger starts with zero new catalogue eliminations and zero checks replaced
by this development's uniform lemmas. Fewer separate checks, fewer distinct
arguments, and a smaller unavoidable set are different results. Removing a
configuration from the unavoidable set also requires a new coverage proof.
