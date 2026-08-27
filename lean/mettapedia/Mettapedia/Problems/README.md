# Problem Work Index

This index is for godelclaw-unique problem work in MeTTapedia. It is a
navigation layer only: it does not claim any headline theorem is proved.

The corresponding source-grounded companion index is
`papers/benxiv/README.md`. It summarizes the ideas in Ben Goertzel's original
v23/v13/v7/v14 manuscripts and keeps them distinct from the formal verdicts.
The companion index currently lives on the YM steelman branch pending merge.

Proof-state scan:

- `lean/mettapedia/Mettapedia/Problems/PROOF_STATE.md`

Current organization rule: keep the prover split at repository top level
(`lean/`, `megalodon/`, `mizar/`, `isabelle/`, `cakeml/`). Inside Lean, avoid
reorganizing files shared with `zariuq/main`; organize only godelclaw-unique
problem work and add non-breaking indexes before moving imports.

## Four Color Theorem

Canonical modern Lean work:

- `lean/mettapedia/Mettapedia/GraphTheory/FourColor/`
- Entry point: `lean/mettapedia/Mettapedia/GraphTheory/FourColor/README.md`
- Detailed live roadmap:
  `lean/mettapedia/Mettapedia/GraphTheory/FourColor/ROADMAP.md`
- Import aggregator:
  `lean/mettapedia/Mettapedia/GraphTheory/FourColor.lean`

Older Lean work:

- `lean/fourcolor/`
- Status: not a duplicate. It is an older attempt around a failed proof route,
  but it contains useful background theory that should be integrated carefully:
  color algebra, `chainDot`, Kempe swaps/cycles, rotation systems, spanning
  forest/walk theory, and curriculum graph theory.
- Do not delete this package until the reusable background theory has been
  extracted or explicitly marked obsolete.

Cross-prover work:

- `mizar/4cp/`
- `isabelle/4CP/`
- `megalodon/4CT/`

Proof-state caveat:

- The modern Lean tree is the canonical route, but it still has admit-like
  obligations and should not be described as a completed proof.
- The old standalone Lean package has many proof gaps in the Kempe proof
  attempt. Its background theory still needs semantic triage.

## P versus NP

Lean route-audit work:

- `lean/mettapedia/Mettapedia/Computability/PNP/`
- Entry point: `lean/mettapedia/Mettapedia/Computability/PNP/README.md`
- Import aggregator: currently included through the Computability/PNP modules,
  with `CruxSynthesis.lean` acting as a broad ledger surface.

Megalodon crux work:

- `megalodon/PNP_crux/`
- `megalodon/PNP_grassroots/`

Paper trail:

- `lean/mettapedia/papers/pnp_crux.tex`
- `lean/mettapedia/papers/pnp_grassroots.tex`

Proof-state caveat:

- Ben's current v13 route seeks an upper--lower clash in fixed-clock
  description length on a gauge-buffered locked SAT ensemble. Its midpoint is
  CD evidence normalization plus an Atomic Evidence Budget and boundary
  mixing, rather than v12's claim that short computations become local.
- The adaptive hidden-gauge product law, positive-rank action, and substantial
  scaffold mechanics are checked. The complete faithful M4 target is also
  machine-checked uninhabited: D.8, D.31, D.48, Definition 7.4/Hypothesis 7.5,
  and full public observability are jointly inconsistent on a nonempty target.
  The manuscript route needs revision; this is not a proof of `P != NP`.
- The Megalodon PNP trees contain the more direct crux attempts, but they still
  contain many admit/axiom markers.

## Navier-Stokes

Lean work:

- `lean/mettapedia/Mettapedia/FluidDynamics/NavierStokes/`
- Entry point:
  `lean/mettapedia/Mettapedia/FluidDynamics/NavierStokes/README.md`

Paper trail:

- `papers/benxiv/goertzel_ns.tex`
- `papers/benxiv/goertzel_ns.pdf`
- `lean/mettapedia/papers/ns_crux.tex`
- `lean/mettapedia/papers/ns_grassroots.tex`

Current reading:

- Ben's v7 proof idea is a lift--linearize--push-down construction: heat flow on
  `SDiff(T^3)`, a Cole--Hopf transform, evaluation of the frame gradient at the
  identity, and a Beale--Kato--Majda closure from identity energy.
- The original SG--Cole--Hopf H1 hypothesis is refuted in the normalized
  Fourier-mode shear model.
- The repaired stochastic-Lagrangian route has a checked conditional BKM
  skeleton, dyadic absorption algebra, frozen-strain obstruction, and
  plane-wave pancake null-structure canary.
- The continuum/global regularity endpoint remains open. The active named pin
  is the pointwise scale-local pancake strain budget, recorded in the repaired
  Navier-Stokes Lean lane as `ScaleLocalPancakeStrainBudget`.

## Yang-Mills

Lean work:

- `lean/mettapedia/Mettapedia/QuantumTheory/YangMills/`
- Entry point:
  `lean/mettapedia/Mettapedia/QuantumTheory/YangMills/README.md`

Paper trail:

- `papers/benxiv/goertzel_ym.tex`
- `papers/benxiv/goertzel_ym.pdf`
- `papers/ym_grassroots.tex`
- `papers/ym_grassroots.pdf`

Status:

- Ben's v14 route starts from Wilson lattice gauge theory, runs an
  extended-extraction RG bootstrap, obtains stopping-scale clustering by a KP
  polymer expansion, transports it back to fine scales, and invokes OS
  reconstruction for the continuum Hamiltonian and gap.
- The Lean subtree is a mass-gap/RG extraction route audit with checked finite
  landmarks and a checked conditional continuum OS scaffold. It is not a
  completed construction of Yang-Mills theory and mass gap.
- The v14 recursion constant is not derived as written. The natural finite
  Wilson-polynomial extraction is gauge invariant and norm one, but transfer
  from v14's range-only projection is refuted without explicit basis and
  dual-jet data. Union-support recombination is norm one; `14` is a rooted
  local branching count, not a total-contact bound. The F.5 and Appendix-O
  ledgers disagree, and the remaining fluctuation/cumulant/KP factors require
  proofs on the actual Wilson map.
- Current central files include `ProofState.lean`, `Roadmap.lean`,
  `CompletionSteelman.lean`, `WilsonBlockMajorant.lean`,
  `ExtendedExtractionTransfer.lean`, `WilsonPolymerRecombination.lean`, and
  `ContinuumOSReconstruction.lean` on the YM steelman branch.
- The continuum endpoint remains blocked by the constructive-QFT gate:
  continuum measure, Euclidean covariance, reflection positivity, OS
  reconstruction, and Hamiltonian mass-gap transfer must be represented for the
  same route before a mass-gap theorem can be claimed.

## Ramsey R(3,6)

Lean work:

- `lean/ramsey36/`

Megalodon work:

- `megalodon/ramsey36/`

Status:

- This is problem-oriented work, but less central to the current godelclaw
  cleanup than Four Color, PNP, and Navier-Stokes.

## Organization To Do

1. Finish the Four Color integration:
   - keep `GraphTheory/FourColor` canonical;
   - port reusable old `lean/fourcolor` background theory only after checking
     it is sorry-free or honestly marking proof gaps;
   - retire the old proof attempt only after useful theory has a new home.
2. Keep PNP, Navier-Stokes, and Yang-Mills in their current topical locations
   for now; add module-level READMEs and status tables before moving any Lean
   files.
3. Keep paper links pointed at the checked repository locations under
   `papers/`; do not pre-move papers while an upstream toolchain/layout update
   may still be in flight.
4. Keep external Megalodon corpora out of public version control; use
   `megalodon/theory/EXTERNAL-CORPORA.md` for source notes.
