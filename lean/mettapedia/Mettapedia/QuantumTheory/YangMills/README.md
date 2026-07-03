# Yang-Mills Lean Lane

This directory records the current formal audit surface for the Yang-Mills route.
It is not a claimed Millennium solution.

Current status:

- `CompletionSteelman.lean` steelmans the five completion inputs from the
  Ben-facing report.
- The favorable recombination branch is verified:
  `C = 11088/5`, `b = 2`, `dmax = 16`, gain `693/2560 <= 1/3`; all
  `dmax <= 15` fail for that branch.
- The support recurrence is reduced to a manuscript branch choice:
  coarsen-then-thicken is uniformly bounded, while thicken-only is unbounded.
- The two-marked centered correlation identity is a named API; a canary proves
  one-marked pushforward does not imply it.
- KP convergence and Wilson reflection positivity are represented as
  classical-import APIs that plug into the OS scaffold.
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
