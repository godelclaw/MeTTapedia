# Yang-Mills

This directory contains the Lean side of the godelclaw Yang-Mills mass-gap and
renormalization-route audit. It is not a proof of the Clay Yang-Mills and mass
gap problem.

Ben's v14 proof idea begins with finite Wilson lattice gauge theory, runs an
extended-extraction RG bootstrap intended to contract irrelevant activities,
uses a stopping-scale Kotecký–Preiss polymer expansion for exponential
clustering, transports clustering back to fine scales, and invokes
Osterwalder–Schrader reconstruction to construct the continuum Hilbert space,
Hamiltonian, and mass gap. The Lean lane keeps those layers distinct.

Useful entry points:

- `Mettapedia.QuantumTheory.YangMills` - imports the active Yang-Mills live
  surfaces.
- `Mettapedia.QuantumTheory.YangMills.Regression` - imports the focused
  regression companions.
- `ProofState.lean` - checked proof-state ledger for route nodes, constructive
  gate status, and the open endpoint.
- `Roadmap.lean` - checked roadmap entries for the finite-lattice landmarks,
  scaling diagnostics, extraction audit, conditional OS scaffold, and open
  continuum endpoint.
- `CompletionSteelman.lean` - source-audited completion-input ledger carrying
  the actual Wilson recursion constant and bridge as explicit fields.
- `ConstructiveGateObstruction.lean` - compact packet showing that the current
  RG/extraction route cannot be promoted to a continuum mass-gap theorem until
  the constructive-QFT interfaces clear.
- `ContinuumOSReconstruction.lean` - conditional endpoint: lattice gap and
  clustering plus reflection positivity and OS reconstruction imply a continuum
  spectral mass gap.
- `MassGap.lean` - spectral-gap vocabulary and finite-mass/gap-set surfaces.
- `RGBootstrap.lean`, `RGBootstrapSlack.lean`, and `RGCrux.lean` - RG
  contraction, slack, and route-obstruction arithmetic.
- `ExtractionMajorant.lean`, `ExtractionProjection.lean`, and the
  `Extraction*` modules - extraction/projection algebra and route diagnostics.
- `WilsonBlockMajorant.lean` - concrete finite Wilson observables and norm-one
  gauge-invariant coefficient-majorant extraction.
- `ExtendedExtractionTransfer.lean` - range-only projection counterexample and
  explicit basis/dual-jet matrix transfer theorem.
- `WilsonPolymerRecombination.lean` and
  `WilsonExtractionRecombinationConstant.lean` - norm-one regrouping, the
  rooted meaning of `14`, ledger arithmetic, and analytic-factor obstructions.

Related papers:

- `papers/benxiv/goertzel_ym.tex`
- `papers/benxiv/goertzel_ym.pdf`
- `papers/ym_grassroots.tex`
- `papers/ym_grassroots.pdf`

Cross-problem proof-state scan:

- `lean/mettapedia/Mettapedia/Problems/PROOF_STATE.md`

## Current Status

The latest steelman branch has no code-level `sorry`. File counts are omitted
because the branch is still moving; isolated modules, regression aggregates,
and the full Yang-Mills aggregate have been built with headline axioms confined
to Lean's standard quotient/classical base.

Checked positive pieces:

- finite strong-coupling mass-gap canaries for `Z2`, `Z3`, and nonabelian `Q8`;
- transfer-gap-to-clustering algebra in toy/finite settings;
- a concrete finite Wilson-polynomial extraction with gauge-invariant
  coefficient-majorant constant one;
- the exact scalar contraction and two-source bootstrap arithmetic for any
  supplied recursion constant;
- a conditional continuum OS scaffold:
  `BenYMContinuumOSConditional.continuumMassGap`;
- guardrail canaries for continuum measure, Euclidean covariance, reflection
  positivity, OS reconstruction, and Hamiltonian transfer interfaces.

Checked negative or blocking pieces:

- v14's advertised Wilson recursion constant is not derived as written: F.5
  and Appendix O use inconsistent ledgers, and the fluctuation/cumulant factors
  lack quantitative actual-map proofs;
- projection range alone does not transfer the norm-one realization to v14's
  `P_ext`; explicit dimension-16 invariant-basis and dual-jet matrices with
  conditioning estimates are required;
- union-support recombination is norm one, while `14` is local rooted branching
  rather than a universal total-contact bound;
- lower-even same-constant extraction repairs are arithmetically refuted;
- the finite RG/extraction ledger alone does not clear the constructive-QFT
  promotion gate;
- the continuum mass-gap endpoint remains an open goal:
  `currentYangMillsMassGapEndpoint_blockedByConstructiveGate`.

## Reading Order

1. `ProofState.lean` for the current verdict.
2. `Roadmap.lean` for the checked route map.
3. `Z2StrongCouplingGap.lean`, `Z3StrongCouplingGap.lean`, and
   `Q8StrongCouplingGap.lean` for finite canaries.
4. `WilsonBlockMajorant.lean`, `ExtendedExtractionTransfer.lean`,
   `WilsonPolymerRecombination.lean`, and
   `WilsonExtractionRecombinationConstant.lean` for the current extraction and
   recombination verdict.
5. `RGBootstrapSlack.lean` for the conditional scalar arithmetic.
6. `ContinuumOSReconstruction.lean` and `ConstructiveGateObstruction.lean` for
   the conditional continuum endpoint and the live constructive gate.

This directory should be described as a mass-gap/RG route audit with checked
finite landmarks and a checked conditional continuum scaffold, not as a
completed construction of Yang-Mills theory and mass gap.
