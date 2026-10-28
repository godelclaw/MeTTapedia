# Mettapedia (Lean 4)

A formalized-mathematics encyclopedia in Lean 4 — probability, logic, computability,
category theory, universal AI, process calculi, and more.

The flagship package uses **Lean 4.33.1**, selected by its `lean-toolchain`.
Mathlib's revision is pinned in `mettapedia/lake-manifest.json`. Other packages
declare their own toolchains.

## Build

From the repository root:

```bash
bash lean/bootstrap_local_repos.sh   # prepare the editable external dependency checkouts
cd lean/mettapedia
lake exe cache get                   # download Mathlib's prebuilt oleans
scripts/check_library_sanity.sh      # build aggregates and check freshness, sources and coverage
```

The migration bundle in `upgrades/4.33.1/` records compatible external source
profiles. Mathlib's cache does not guarantee a prebuilt cache for every external
dependency.

## Layout

`lean/` is a monorepo of independent Lake packages:

| path | contents |
|------|----------|
| `mettapedia/` | the main library; source under `mettapedia/Mettapedia/`, imported as `import Mettapedia.…` (Lake convention: `<package>/<LibName>/`) |
| `externals/` | pinned forks of dependencies (Foundation, exchangeability, Metatheory, CertifyingDatalog, OrderedSemigroups, provenance, mm-lean4) — cloned by the bootstrap |
| `standalone/` | ks-foundations-of-inference, mm-lean4 dev copy |
| `batteries/` | mettail-core, gf-core |
| `algorithms/` | executable GF / MeTTa tools |
| `ramsey36/`, `foet/`, `fourcolor/` | self-contained side projects |

## Notes

- `mettapedia/lakefile.lean` is the flagship configuration, using editable local
  dependencies from `externals/` and `standalone/`.
- Build from `lean/mettapedia`. Avoid a bare `lake update` (it can bump transitive pins past the
  toolchain); use `lake update <pkg>` if you must.
