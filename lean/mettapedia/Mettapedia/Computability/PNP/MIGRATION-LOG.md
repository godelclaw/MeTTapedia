# PNP Migration Log

- 2026-07-04: Added the v13 public-input interface battery, CD-ENF public-read
  decomposition obligation, structural no-opaque-run check, and checked
  enforced-vs-assumed ledger for the abstract gauge-buffered locked interface.
- 2026-07-04: Added a v14 construction-side toy public-read model that
  instantiates `PublicReadCDENFInterface`, proves neutral-only public reads are
  target-blind, runs `V13InterfaceConsistencyBattery`, and records a
  construction-proved Test 8 ledger row.
