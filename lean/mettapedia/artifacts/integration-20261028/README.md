# Curated mathematical integration

This integration starts from zariuq's main checkpoint
`798623342cec443cca29f2c37751de99628af9d6` and groups the retained developments
into subject commits. The existing upstream history is unchanged.

The detailed original fork history is retained on `main-history` at
`0fcdc5c4367e8faf1a66f7d3c439f9f737a0140b`. The recovered LP development is
archived on `history/lp-grounding-20261028`; the PLeaTTa development and its two
additional ownership studies are on the `history/pleatta-*` branches. These
archive refs are separate from the curated main ancestry. `goertzel/proofs`
is a separate development.

`preservation.json` records every changed upstream file, its original and
curated Git blobs, and the preservation decision. Every upstream Lean source
remains present, including research sources. The CeTTa source and PDF retain
the exact upstream blobs. Established cognitive-architecture import paths and
namespaces remain in place. Old Henkin import paths export the same canonical
subject-library carriers rather than defining a second copy. All 29 Henkin
modules retain their normalized source after that namespace relocation.

From the repository root, verify the recorded upstream delta with:

```sh
python3 lean/mettapedia/scripts/check_upstream_preservation.py
```

The ledger accounts for file identities. Its semantic review entries and the
actual theorem hypotheses describe why an interface was retained or changed;
file presence alone does not establish preservation of a theorem.

The recovered mathematical libraries have explicit boundaries:

* `Mettapedia.Logic.LP.Runtime` retains graph terms, finite readback, exact
  restoration, scoped SLD, demand-driven execution and conservation results.
* `Mettapedia.Logic.Prolog` adds typed Prolog control, source services and owned
  libraries. Least-model soundness keeps its function-free premises; finite
  readback and rational-tree execution are distinguished. The SWI provenance
  manifest and third-party notices stay with the development.
* `Mettapedia.Languages.MeTTa.PLeaTTa` maintains the versioned source profile,
  its embedding into the shared atom carrier, the independent reader and
  ordered-search relations, machine refinement, compiler fragments, and
  indexed ownership theory. Global compiler/search obligations remain explicit
  in its README and historical evidence ledgers.

The earlier predicate-based dignity experiment remains available under
`Mettapedia.Ethics.Dignity.PredicateModel`; the upstream dignity module keeps
its explicit substantive-theory boundary.

The validation record distinguishes newly checked source from reused compiled
artifacts whose source and import identities were verified. The recovered
language and interface checks use warnings as errors. The historical coloring
curriculum retains cosmetic warnings. Its graph API migration is complete:
`FourColorCore` again includes the full original `FourColor` root, together
with `FourColor.IntegrationCore`. The full-root source check covers 72 modules;
the additional audit covers 1,318 coloring declarations and finds no admitted
proof dependencies. The original three migration failures are recorded as
resolved in `legacy-coloring-migration.json`. Older teaching sheets retain
their explicit WIP status outside the maintained roots. These checks do not
claim an unrestricted whole-library build. Existing incomplete legacy research is
identified separately and is not counted as completed mathematics.
`legacy-session-claims.json` records 19 unsupported session-calculus claims;
all 204 original declarations independent of admitted proofs retain their
elaborated type hashes, and the cleaned module proves two counterexamples to
its unconstrained typing rules.

The three previously timed-out PeTTa dependencies now pass. The broader
documentation-index import closure remains unqualified: the bounded replay
left additional timeouts and modules without current source/import receipts.
`validation.json` lists that remaining scope explicitly; the four generated
documentation audits have current passing receipts.

The coherent-tower refinement has a separate
[`validation record`](../coalgebra-tower-refinement-20261028/validation.json).
It checks the 211 original public contracts, original operator semantics and
downstream consumers while sharing the generic and stream tower carrier.

The [integration correction record](../integration-corrections-20261028/qualification.json)
accounts for the independently reviewed 133-module gap: 132 source receipts
and one comment-only historical index. Changed compatibility facades and
aggregates invalidated by rebuilt imports are replayed separately. The LF
PeTTa companion is regenerated from its authored source, restoring opaque
theorems, theorem-chain admission and batch judgments. All 48 kernel parity
rows pass with explicit CeTTa HE/extended and matching PeTTa interpreter/library
versions. Runs with no executed assertions are rejected by the gate.

The maintained Lake targets are `LogicProgrammingTheory`, `PLeaTTaTheory`,
`AttentionEconomyTheory` and `FourColorCore`. They share the package's existing
build directory. The 231 upstream research Lean files remain separate from
the maintained library targets and retain their baseline bytes.

Future deliveries should prepare reviewed bulk commits against current upstream,
preserve detailed development histories on archive refs, and resynchronize the
fork from the resulting upstream main after integration. Update the preservation
ledger for any changed semantic contract, reuse the existing build cache and run
the relevant theory targets.
