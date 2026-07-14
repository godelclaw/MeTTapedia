# Yang-Mills Lean Lane

This directory records the current formal audit surface for the Yang-Mills route.
It is not a claimed Millennium solution.

Manuscript route (v14): start from finite Wilson lattice gauge theory; run an
extended-extraction RG bootstrap intended to contract irrelevant activities;
obtain stopping-scale clustering from a Kotecký–Preiss polymer expansion;
transport clustering back to fine scales; and use Osterwalder–Schrader
reconstruction to construct the continuum Hilbert space, Hamiltonian, and mass
gap. The formalization keeps those layers separate so that finite arithmetic or
a toy spectral gap cannot silently stand for the continuum construction.

Current status:

- `CompletionSteelman.lean` steelmans the five completion inputs from the
  Ben-facing report.
- The v14 extraction/recombination constant is not derived as written.
  `WilsonBlockMajorant.lean` proves norm-one canonical truncation on concrete
  gauge-invariant finite Wilson observables; `ExtendedExtractionTransfer.lean`
  gives both the basis/dual-jet transfer theorem and a range-only projection
  counterexample; `WilsonPolymerRecombination.lean` proves norm-one regrouping
  by union and refutes the literal total-contact reading of the factor `14`.
- `Dimension16WilsonExtractionCertificate.lean` records the decisive outcome
  of attempting the manuscript-facing coordinate construction. F.4 uses an
  on-shell relation policy while O.9 explicitly selects an off-shell census;
  v14 gives no dimension-16 lattice representatives, quotient basis, dual
  jets, biorthogonality matrix, or conditioning certificate. Appendix I's
  explicit jets belong to the distinct dimension-4 observable sector. Thus
  the source as written cannot instantiate the positive transfer theorem.
- Under Appendix O's other proposed factors, substituting the proved
  extraction factor `1` gives the conditional ledger `C = 5544/5`; depth `15`
  is the least unrestricted two-source depth and `16` the least even depth.
  This is not an actual Wilson RG constant until the remaining analytic factor
  bounds are proved in the same norm.
- The support recurrence is reduced to a manuscript branch choice:
  coarsen-then-thicken is uniformly bounded, while thicken-only is unbounded.
- The two-marked centered correlation identity is a named API; a canary proves
  one-marked pushforward does not imply it.
- KP convergence and Wilson reflection positivity are represented as
  classical-import APIs that plug into the OS scaffold. Their route-specific
  instantiation—actual stopping-scale activities, uniform smallness and source
  summability, decaying remainders, and compatibility for the same Wilson
  family and RG kernels—remains open mathematics.
- The first load-bearing remaining theorem is
  `FirstLoadBearingYangMillsCompletionInput`, the actual Wilson Yang-Mills RG
  map recursion producing the lattice gap/clustering bridge consumed by OS
  reconstruction.

Main status files:

- `ProofState.lean` records route nodes and current endpoint blockers.
- `Roadmap.lean` records the checked roadmap entries.
- `CompletionSteelmanRegression.lean` protects the five-input classification.
- `ContinuumOSReconstruction.lean` contains the conditional OS/Kirk endpoint.

The continuum mass-gap endpoint remains open until the actual Wilson RG
recursion, support branch, two-marked identity, KP convergence, Wilson
reflection positivity, and OS/subsequential-limit machinery are all instantiated
for the same route.

The extraction-side route now needs a source clarification or an explicitly
labeled repair selecting one relation quotient and exact block convention.
Only after that choice is fixed can actual lattice Wilson representatives, a
finite quotient basis, dual jets, and their column-sum conditioning certificate
be constructed. The recombination-side target remains the weighted connected-
cumulant/tree/KP estimate for the actual Wilson activities in that same norm.
