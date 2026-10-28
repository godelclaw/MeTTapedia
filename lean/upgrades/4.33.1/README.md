# Lean 4.33.1 dependency sources

`externals.json` records source fingerprints and migration patches. Some
published revisions also need a compatibility overlay: its base revision,
patch, digest and changed-source fingerprints are recorded in the same entry.
The effective source profile is the published profile with those changes applied.

`../../bootstrap_local_repos.sh` preserves existing checkouts. For a fresh
checkout it selects the exact published revision, then runs `--prepare` to
apply any recorded overlay and verify the resulting sources. Remote branch
names are not needed to locate a pin. The bootstrap also installs PolyFun and
CSLib, which the library configuration requires.

From this directory:

```sh
python3 replay.py externals/Foundation --verify
python3 replay.py externals/Foundation --prepare
python3 replay.py externals/Foundation --apply
python3 test_replay.py
```

`--verify` is read-only and checks the effective fingerprints. `--prepare`
requires a clean checkout at the overlay's published base and preserves
existing work by refusing a dirty checkout. `--apply` replays the original
migration from its older recorded base and then applies the overlay. With no
mode flag, both patches are tested sequentially in a private index and object
store; the working tree, ordinary index and repository object store are unchanged.

The overlays cover Foundation's 15 source repairs, exchangeability's 44 source
repairs, one Metamath source repair, and LeaTTa's shared atom-carrier import.
The latter keeps the integration on the carrier defined by `mettail-core`
instead of a second copy. The Metamath and Knuth–Skilling pins
also include their published source reorganizations. A source profile identifies
the build inputs; successful proof builds and axiom audits remain separate checks.
