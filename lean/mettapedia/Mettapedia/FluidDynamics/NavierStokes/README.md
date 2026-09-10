# NavierStokes

This directory contains the Lean side of the godelclaw Navier-Stokes /
Fefferman-target route audit. It is not a proof of the Millennium
Navier-Stokes problem.

Useful entry points:

- `NavierStokesEquationTarget.lean` - concrete target surface for the
  Navier-Stokes equation on time `R` and space `R^3`.
- `FeffermanGrassrootsInterface.lean` - bridge from current approximation
  packages toward the Fefferman-style target.
- `NavierStokesWitnessConstruction.lean` - honest witness-construction surface;
  includes the zero-data witness and classifies what extra balance is needed
  for boxed steady seed routes.
- `NavierStokesBKMContinuationTarget.lean` and
  `NavierStokesUniformVorticityContinuationTarget.lean` - continuation target
  surfaces.
- `NavierStokesFiniteMode*.lean` - finite-mode classifications and obstruction
  checks.
- `WindowedColeHopfHeat*.lean` and `Fefferman*.lean` - Cole-Hopf/Fefferman
  package interfaces and obstruction/frontier surfaces.

Related papers:

- `papers/benxiv/goertzel_ns.tex`
- `papers/benxiv/goertzel_ns.pdf`
- `lean/mettapedia/papers/ns_crux.tex`
- `lean/mettapedia/papers/ns_grassroots.tex`

Cross-problem proof-state scan:

- `lean/mettapedia/Mettapedia/Problems/PROOF_STATE.md`

Area-local proof-state and live build target:

- `lean/mettapedia/Mettapedia/FluidDynamics/NavierStokes/PROOF_STATE.md`
- `lake -f lakefile.toml build Mettapedia.FluidDynamics.NavierStokes.Live`

## Cluster Map

Source-count scan from 2026-06-21:

- Cole-Hopf/Fefferman window package: 86 files. This is the largest cluster and
  includes `WindowedColeHopfHeat*`, `ColeHopf*`, and `Fefferman*` route
  surfaces.
- Finite-mode classifications and obstructions: 40 files.
- Schwartz, shear, pressure, and transported obstruction family: 28 files.
- Witness construction and shared-witness route: 16 files.
- Target/core analytic infrastructure: 9 files, including the equation target,
  vector-calculus support, Schwartz data, and energy inequality surfaces.
- BKM/continuation targets and bridges: 8 files.
- Topology countermodels: 2 files.
- Other support/frontier/regression files: the remaining files.

This map is an organizational index only. It is not evidence of global
regularity, blowup, or any other Millennium-problem conclusion.

## Current Status

### September 2026 material-flow development

Ben Goertzel's [September 9 commentary](https://bengoertzel.substack.com/p/navier-stokes-blows-up-the-internet)
identifies unforced A/B as his target and distinguishes the core idea from
its unverified details. This documents author intent, not a completed proof.

The stochastic-Lagrangian lane now constructs a local infinite Fourier
velocity and a common-interval material flow for arbitrary admissible smooth
periodic data, with no small-data restriction. Along that flow it derives
the actual velocity-gradient and strain equations, retaining the pressure
Hessian, spin, and viscous terms.

`StochasticLagrangian/LocalMaterialVorticity.lean` derives the actual curl
equation `Dₜω = Sω + νΔω`, including its real Euclidean formulation.
`LocalVorticityDiffusion.lean` proves continuity of the viscous source from
the common third Fourier-moment envelope and applies the reusable
`Mettapedia.Analysis.ODE.QuadraticFormBound` estimate. The strain growth bound
remains an explicit hypothesis of that estimate. The accompanying
`LocalMaterialVorticityAudit.lean` checks the theorem dependencies.

`LocalMaterialStrain.lean` constructs the real symmetric strain path and
proves its `C¹` regularity from the common third-moment envelope.
`LocalSpectralDefect.lean` applies the collision-safe integrated spectral
defect identity to this actual strain and vorticity, without assuming their
ODEs or regularity as extra input. `LocalSpectralDefectSources.lean` exposes
the nonnegative spin contribution and the signed pressure/viscosity terms.

`LocalSpectralResidual.lean` derives the almost-everywhere equation

```text
z = λω - Sω,       R = -W² - Hess(p) + νΔS,       f = νΔω
z' = -λz + source
source = <e,Re>ω - Rω + (λI-S)f,       λ = λ_max(S) ≥ 0
```

Here `e` is a selected top unit eigenvector. No regularity of that selection
is assumed. `LocalSpectralResidualBudget.lean` proves absolute continuity of
`z`, integrability of the actual source, and
`‖z(b)‖ ≤ ‖z(a)‖ + ∫ a..b, ‖source(t)‖` on compact local intervals. It uses
the almost-everywhere extension of the OpenAI-derived dissipative ODE
comparison. There is no exponential factor or spectral-gap assumption.
`LocalSpectralDefectAudit.lean` checks the dependencies of these results.

`InfiniteFilteredEquation.lean` derives the static-filter equation of this
same infinite solution, including the absolutely convergent subgrid fiber
with multiplier `χ(q) - χ(k)χ(q-k)`. It identifies the resolved finite algebra
without assuming autonomous Galerkin evolution. The pressure-corrected
subgrid force is `gχ = Leray(-2πi subgridConvection)`.

`LocalFilteredStrain.lean` derives the resolved strain equation along the
**full** velocity's material path. Writing `v = χu`, it retains the
coefficient reconstructions of

```text
D_u S_v = -S_v² - W_v² - Hess(p_v) + νΔS_v
          + sym ∇gχ + (u-v)·∇S_v.
```

Here `p_v` is resolved pressure; the difference from the filtered full
pressure is included in the Leray-projected `gχ`. Nonlinear output sets
include every resolved pair output. Both the matrix equation and its real
self-adjoint operator form are proved from the local solution's equation.
The static filter has no time derivative; a moving filter would add one.

`InfiniteConvectionEnergy.lean` proves, for `E = ∑ k, |u_k|²`, the all-input
bounds `|convection_q| ≤ |q|E`, `|p_q| ≤ E`, and
`|gχ_q| ≤ 2π|q|E` at a retained sharp-filter output. Square summability is
proved for the actual local solution. Reconstructing finitely many output
modes gives the spatially uniform bound `2π(∑ q, |q|)E`, with the output
cutoff cost explicit. This is not an estimate uniform over all output scales;
the original local estimate uses `E ≤ B`. The following energy development
replaces this local Sobolev payment by the initial kinetic energy.

`InfiniteKineticCancellation.lean` proves the skew-Hermitian transport
cancellation for the actual infinite convection. An absolute first Fourier
moment justifies the exchange of the two energy slots. Pressure projection
does no kinetic work; viscosity gives the signed curl-energy loss.

`LocalKineticEnergy.lean` derives, on the constructed local interval,

```text
E(t) + 2ν ∫₀ᵗ Ω = E(0),
E(t)² + 4ν ∫₀ᵗ EΩ = E(0)²,
E = ∑ q, |u_q|²,       Ω = ∑ q, |curl(u)_q|².
```

The common second-moment envelope justifies differentiation and continuity
of the infinite sums. It disappears from these identities. The fundamental
theorem of calculus uses the equation only in the open interval and
continuity at the endpoints. The physical-data existence theorem constructs
the needed envelope for admissible periodic data with eight continuous
coordinate derivatives; no energy inequality is added as an assumption.

`LocalLowFrequencyBudget.lean` applies this payment to the full pressure,
whose convolution still contains every input mode. With
`C_M = (2π)² ∑ q ∈ M, |q|²`, it proves the spatially uniform retained-Hessian
bound `C_M E(0)` and the time-integrated pressure cost
`∫ 2 (∑ q ∈ M, |Hess(p)_q|) Ω ≤ C_M E(0)² / (2ν)`.
The retained subgrid-force bound also now uses `E(0)` instead of `B`.

The same module evaluates the existing incoming low-source cost on the
actual full vorticity and proves `∫ lowSourceCost ≤ 9 |S| E(0)² / ν²` for a
fixed nonzero source set `S`, independently of the finite receiver set.
Integrability and the required kinetic/enstrophy bounds are derived, not
assumed. This alone does not control an expanding source set.
`LocalEnergyBudgetAudit.lean` checks dependencies
of the cancellation, actual energy identities and their sector applications.

`LocalFilteredVorticity.lean` now derives the curl equation of the actual
filtered infinite solution. At each retained sharp-filter output it is the
finite vorticity RHS plus `curl(gχ)`, not an autonomous Galerkin equation.
The exact misalignment energy derivative retains the signed subgrid work
`2 ∑ q ∈ O, Re <ω_mis,q, curl(gχ)_q>`.
`LocalRetainedEnergyBudget.lean` consumes the initial-data low-source budget
in that equation. Continuity and time integrability of the actual subgrid
curl and remainder are proved, including at the interval endpoints.

`LocalHighHighEnergyBudget.lean` goes further: exchange symmetry absorbs
interactions with a low frequency in either input slot. For `θ > 0`, it proves

```text
E_mis,O(t) + (2-θ)ν(2π)² ∫₀ᵗ D_mis,O
  ≤ E_mis,O(0) + ∫₀ᵗ R_HH + |lowSources| E(0)² / (θν²),
R_HH = resolved high-high work + signed subgrid-curl work.
```

Here `O ⊆ M`, the retained set `M` excludes zero, and `D_mis,O` is the
frequency-squared misalignment energy. There is no output-frequency lower
bound. Choosing `θ < 2` leaves positive dissipation. For a fixed integer
low cutoff `L`, `|lowSources| ≤ (2L+1)³`, so the paid term is uniform over
expanding retained sets. Its constant uses the energy-squared identity;
neither the local Sobolev bound nor the moment envelope appears in it.
The high-high-plus-subgrid remainder remains unestimated.

`LocalRetainedLocalizedEnergy.lean` constructs compressed advection using
the **full velocity** at each difference frequency `q-l`; it proves
skew-adjointness without requiring a symmetric retained patch. The actual
retained curl equation under moving spatial/directional operator localizers
keeps their material rates, resolved stretching, subgrid curl, and the
correction from resolved to full advection. Its viscous contribution is the
signed anticommutator `ν <w, AΔw + ΔAw>`. For an exact self-adjoint operator
partition `∑ Aᵢ = I`, the sum of those contributions equals
`2ν <w, Δw> ≤ 0`, without a cell-count loss or individual commutation with
the Laplacian. This identity does not construct that partition, estimate its
individual sectors, or turn approximate Fourier coverage into exact coverage.
`LocalRetainedEnergyAudit.lean` checks these dependencies.

`LocalFilteredSpectralDefect.lean` pairs the **filtered strain with full
vorticity** along the actual material path. Its gap-weighted defect has a
signed balance across eigenvalue collisions. The discarded strain still
acts through `(S-Sχ)ω`; pressure, subgrid feedback and unresolved transport
remain in the filtered strain remainder. `LocalFilteredViscousDefect.lean`
retains `νΔSχ` and `νΔω` jointly in the regularized energy rate. The full
material rate is integrable on compact interior intervals, without separate
measurability assumptions on chosen-eigenvector terms.

The receiver cutoff is removed in the diffusion payment:

- `InfiniteFourierParseval.lean` proves scalar and vector Parseval for the
  actual infinite continuous reconstruction and its ordinary spatial curl.
- `LocalLowDiffusionBudget.lean` integrates the low-strain gradient cost
  against that full curl, using the actual energy-squared identity.
- `InfiniteFourierDiffusion.lean` proves uniform second-difference
  convergence in the continuous-field Banach norm, including real linear
  images, from two summable coordinate derivatives.
- `LocalJointDiffusionBudget.lean` applies that limit to the filtered
  strain and full vorticity Laplacians. If an integrable full-rate envelope
  satisfies `F ≤ ν linearRate(Sχ,δ,ω,ΔSχ,Δω) + R`, then

  ```text
  ∫₀ᵗ ∫ F ≤ 4 Kχ E(0)² / δ + ∫₀ᵗ ∫ R,
  Kχ = 243 (2π)⁴ ∑ q ∈ modes, |χ(q)|² |q|⁴.
  ```

Here `δ > 0`, `ν > 0`, and `E` is the full squared velocity norm, without
a factor one half. A common third Fourier moment justifies the spatial
limit; its magnitude does not enter the payment. The strain cutoff and
`1/δ` remain explicit. The full-rate/nonviscous integrability hypotheses
in this weak spatial envelope theorem remain explicit too; the separate
material-path identity does not automatically discharge them in space-time.
No all-scale estimate, bound for the high-strain mismatch, or terminal-time
continuation follows yet. `LocalJointDiffusionAudit.lean` checks dependencies.

The Eulerian full-field extension now separates transport, forcing
regularity and signed estimates:

- `InfiniteFourierTransport.lean` identifies ordinary full-velocity
  coordinate derivatives and proves zero mean incompressible transport
  of periodic locally Lipschitz scalars. There is no advector cutoff.
- `LocalAlignmentTransport.lean` applies this to
  `Eδ = <ω, ((λmax(Sχ)+δ)I-Sχ)ω>`, with full ordinary vorticity. Local
  Lipschitz regularity includes eigenvalue crossings; no spectral gap is
  assumed.
- `LocalAlignmentForcing.lean` constructs Eulerian versions of the
  actual path rate and remainder, with their equality checked. The
  remainder contains the all-input subgrid force and discarded-velocity
  transport. Its spatial continuity is proved, not assumed.
- `LocalAlignmentContinuity.lean` proves joint continuity of that
  all-input remainder, strain mismatch, residual and energy on the local
  time window. Dominated convergence is applied to the entire subgrid
  fiber. The corresponding scalar spatial means are time-integrable.
- `LocalSignedAlignmentBudget.lean` retains the signed mismatch pairing
  and the full residual damping. For `z = (λmax(Sχ)I-Sχ)ω`,
  `f₀ = (Sfull-Sχ)ω`, and the actual nonviscous remainder `R₀`, set

  ```text
  Nδ = 2||R₀|| ||ω||² + 2<z,f₀> + 2δ<ω,Sfull ω>.
  ```

  If an integrable scalar `F` satisfies
  `F + u·∇Eδ ≤ actual material rate` almost everywhere in space-time,
  the checked full-velocity transport cancellation and joint diffusion
  payment give

  ```text
  ∫₀ᵗ∫F + ∫₀ᵗ∫||z||² ≤ 4 Kχ E(0)²/δ + ∫₀ᵗ∫Nδ.
  ```

  Integrability of `Nδ` and the residual is derived from the actual
  local solution; only `F` and its chain-rule comparison remain supplied.
  The time hypotheses are almost-everywhere statements, not everywhere
  differentiability claims. `LocalKineticEnergy` supplies the corresponding
  almost-everywhere energy-enstrophy majorant lemma.

This does **not** yet identify `F` with the actual Eulerian time derivative
of `Eδ`. Nor does local integrability bound `∫Nδ` uniformly at a potential
singularity. The sign of `<z,f₀>` is retained, not asserted favorable;
`Kχ` and `1/δ` still prevent an unproved all-scale limit.
`LocalAlignmentAudit.lean` checks the new theorem dependencies.

The actual local mean balance is developed separately:

- `LocalVorticityTime.lean` differentiates full curl in the uniform norm
  of continuous fields and proves a spatially uniform time Lipschitz
  bound from the third absolute Fourier moment.
- `LocalSpaceTimeExtension.lean` clamps time to a compact interior
  interval. It extends field data, not the PDE solution, and proves
  space-time local Lipschitz regularity of full vorticity, filtered
  strain and the alignment energy, including spectral collisions.
- `LocalMeanAlignmentBalance.lean` proves spatial integrability almost
  everywhere, differentiates the spatial mean, and proves
  `∫ₐᵇ∫ DᶠᵘEδ = mean Eδ(b) - mean Eδ(a)` for the original local
  solution. Here `Dᶠᵘ` is the derivative along the straight line with the
  instantaneous **full** velocity. Its mean time integrability is a
  conclusion, not an assumption.
- `LocalMeanAlignmentEstimate.lean` combines that identity with signed
  damping. Subject to the explicit almost-everywhere comparison
  `DᶠᵘEδ ≤ materialRate`, it proves

  ```text
  mean Eδ(b) + ∫ₐᵇ∫||z||²
    ≤ mean Eδ(a) + 4 Kχ E(0)²/δ + ∫ₐᵇ∫Nδ.
  ```

  `LocalEnergySubinterval.lean` supplies the initial-energy payment on
  subintervals; it does not require the dominated cost to be nonnegative.
- `LocalInteriorTrajectory.lean` constructs actual flow curves through
  any prescribed point and time. `LocalVorticityTangency.lean` transfers
  the vorticity equation to curves with the same instantaneous velocity.
  `LocalAlignmentDifferential.lean` identifies the actual energy
  derivative with `materialRate` along such curves wherever the largest
  eigenvalue is differentiable along the curve. It does not assume the
  curve is a trajectory at other times.

The reusable tangent-curve theorem is in `Mettapedia.Analysis.TangentCurveDerivative`:
a locally Lipschitz outer map preserves agreement of derivatives along
tangent curves, even without differentiability of the outer map itself.
Finite local Lipschitz constructions are in `Mettapedia.Analysis.LocallyLipschitz`.
`LocalMeanAlignmentAudit.lean` checks the dependencies of this stage.
The remaining local splice is the almost-everywhere frozen-rate comparison;
the all-scale signed nonlinear estimate and continuation remain unproved.

`FilteredHighHighExample.lean` supplies real, transverse, zero-mean finite
Fourier data whose retained velocity vanishes while its retained subgrid
force does not. The input squared frequencies are five and two; the output
squared frequency is one. This rules out discarding unresolved quadratic
feedback, not unforced global regularity. `LocalFilteredStrainAudit.lean`
checks the dependencies of the filtering identities, witness and estimates.

### Forced-construction pressure test

The [OpenAI forced blowup construction](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
claims bounded-energy singular solutions with smooth compactly supported
forcing (Theorem 1.1 and Corollary 10.6). If correct, this excludes a complete
regularity argument that would also cover those solutions. Its oscillatory
pulses have nonzero mean quadratic stresses despite zero angular mean;
mean-zero oscillation alone cannot justify discarding their feedback.

This does not refute the local identities above or automatically refute the
unforced misalignment-budget conjecture. An external body force adds
`sym ∇F` to the strain rate and `curl F` to the vorticity rate, with pressure
still determined by the actual equation. Setting `F = 0` removes these direct
inputs, not `R` or `νΔω`. Any proposed uniform closure must control the
surviving terms and identify its genuinely unforced mechanism. Integrability
on each compact local interval is not a bound uniform up to a singular time.

None of this closes the scale-critical dynamical misalignment budget,
the remaining field-transfer estimates, or unconditional BKM continuation.
The older route-audit summary below describes earlier layers, not the full
extent of the current local PDE construction.

### Earlier route-audit layers

The directory is best read as a route audit and obstruction library. It has
concrete theorem surfaces and some fully checked toy or boundary cases, but it
does not solve global regularity or blowup.

Current high-signal status:

- `BenH1Break.lean` refutes the original SG--Cole--Hopf H1 adjoint hypothesis
  in the normalized Fourier-mode shear model.
- The July stochastic-Lagrangian repair lane checks the conditional
  pushdown-to-BKM skeleton, dyadic absorption algebra, frozen-strain
  obstruction, and plane-wave pancake null structure.
- The live analytic pin is `ScaleLocalPancakeStrainBudget`: a pointwise,
  scale-local pancake strain budget for the self-consistent Navier-Stokes
  Biot-Savart strain. Until that is proved, the repaired route remains
  conditional.

Before moving files, keep the flat layout stable until the 4.31 stream is
settled, then prefer small import aggregators by cluster:

1. target surfaces;
2. finite-mode work;
3. Cole-Hopf/Fefferman interfaces;
4. witness-construction and obstruction regressions.

Each actual file move should be followed by import rewrites and a Lean build.
