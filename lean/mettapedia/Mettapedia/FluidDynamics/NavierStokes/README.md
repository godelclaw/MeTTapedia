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

This module does not identify `F` with the actual Eulerian time derivative
of `Eδ`; the actual mean-energy estimate below no longer needs that supplied
comparison. Local integrability does not bound `∫Nδ` uniformly at a potential
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

The local comparison and initial-data construction are now proved:

- `PeriodicMaterialDifferentiability.lean` transfers almost-everywhere
  differentiability of a locally Lipschitz real space-time lift to frozen
  material paths on the torus. The advecting velocity need only be spatially
  continuous at each time; no eigenvector field is chosen.
- `LocalAESpectralDifferentiability.lean` applies this to the largest
  eigenvalue of the actual filtered strain. `LocalFrozenAlignmentRate.lean`
  identifies the frozen scalar derivative with the algebraic rate.
- `LocalAlignmentEnergyBudget.lean` proves their equality almost everywhere
  in time and space, spatial integrability of the algebraic rate almost
  everywhere in time, its mean time integrability, and the mean fundamental
  theorem of calculus. Its signed energy estimate has no additional
  derivative-comparison or spectral-differentiability hypothesis.
- `LocalInitialAlignmentBudget.lean` extends the estimate to both ends of
  the local existence interval by continuity. For every real, zero-mean,
  Fourier-divergence-free periodic field with continuous coordinate jets
  through order nine and every positive viscosity, it constructs **one**
  local solution on which **every** admissible finite strain filter obeys

  ```text
  mean Eδ(t) + ∫₀ᵗ∫||z||²
    ≤ mean Eδ(0) + 4 Kχ E(0)²/δ + ∫₀ᵗ∫Nδ,    0 ≤ t ≤ T.
  ```

  The quantified filters have finite symmetric support excluding the zero
  mode, conjugate symmetry, and a finite output set containing the support
  and its pairwise sums. Neither the local solution nor its existence
  interval is chosen separately for each filter. The reusable endpoint
  estimate is in `Mettapedia.Analysis.IntegralEndpointEstimate`.
- `RegularizedSpectralEnergySplitting.lean` and
  `LocalAlignmentRegularization.lean` prove the exact identities
  `mean Eδ = mean E₀ + δ∫||ω||²` and
  `materialRateδ = materialRate₀ + δ Dᵤ||ω||²`, with the latter derivative
  constructed along paths tangent to the full velocity. Its stretching
  contribution is precisely the `2δ<ω,Sfull ω>` retained in `Nδ`.
  Added enstrophy is therefore not free global control.

`LocalInitialAlignmentAudit.lean` checks this stage's theorem dependencies.
The all-scale signed nonlinear estimate, a global continuation bound, and
the unconditional arbitrary-data theorem remain unproved. The constants
`Kχ` and `1/δ` and the unresolved source are explicit in the local theorem.

The nonlinear anisotropy envelope is refined in
`SpectralAnisotropyEnvelope.lean`. Put `g = λmax(Sχ)-λsecond(Sχ)` and

```text
Bε = min (2||R₀|| ||ω||²)
         (4||R₀|| ||ω|| sqrt(Eε/(g+ε))).
Nδ,ε_depleted = Bε + 2<z,f₀> + 2δ<ω,Sfull ω>.
```

The source retains a quantitative alignment gain without choosing a
measurable eigenline. `StrainEigenvalueContinuity.lean` proves continuity
of all three ordered eigenvalues and the adjacent gaps, using the Weyl
bounds for the extremes and the trace identity for the middle eigenvalue.
Regularized transverse coercivity gives
`(g+ε)||ω-<e,ω>e||² ≤ Eε` for a unit top eigenvector `e`. This combines with
the existing anisotropy-depletion bound to give `|anisotropy| ≤ Bε`.

The refined bound is continuous for `ε > 0` and never exceeds the coarse
bound. Its improvement is quantitative: if
`Eε ≤ c²(g+ε)||ω||²` with `c ≥ 0`, then `Bε ≤ 4c||R₀||||ω||²`.
For aligned vorticity and `g ≥ 63ε`, it is at most one quarter of the
coarse bound. At `g = 0` it equals the coarse bound exactly. Neither
alignment nor spectral separation is assumed for the full local theorem.

`LocalDepletedAlignmentSource.lean` constructs this source from the actual
full vorticity, proves joint time-space continuity and the pointwise
material estimate, and keeps joint diffusion intact.
`LocalDepletedAlignmentBudget.lean` proves the initial-data inequality
above with `Nδ,ε_depleted` replacing `Nδ`, including one constructed local
solution for every admissible filter. `LocalDepletedAlignmentAudit.lean`
checks its dependencies. The source parameter `ε` and energy regularizer
`δ` are independently quantified, so varying the source approximation
does not change the viscous payment `Kχ/δ`. The sharper source does not supply a uniform
bound on its accumulated cost, eliminate `Kχ/δ`, or close continuation.

`SpectralAnisotropyLimit.lean` removes the auxiliary source parameter:

```text
B* = min (2||R₀||||ω||²) (4||R₀||||ω|| sqrt(E₀/g))  if g > 0;
B* = 2||R₀||||ω||²                                  if g = 0.
Nδ,* = B* + 2<z,f₀> + 2δ<ω,Sfull ω>.
```

The scalar limit is measurable and bounded by the coarse envelope. On a
simple top eigenline it vanishes at exact alignment. Continuity through
collisions is not asserted. `LocalLimitingAlignmentSource.lean` constructs
the actual limiting source and proves spatial dominated convergence under
an absolute majorant independent of `ε`. `LocalAlignmentSourceLimit.lean`
proves interval integrability and the time-integral limit.
`LocalLimitingAlignmentBudget.lean` then proves the initial-data estimate
with `Nδ,*`, keeping `δ > 0` and its viscous payment fixed. One local solution
and interval again work for all admissible filters and regularizers.
This is a local estimate, not uniform control toward a singular time.

`LocalCoherentAlignmentRate.lean` identifies additional cancellation that
the collision fallback loses. Unregularized alignment energy is nonnegative;
at a zero its frozen scalar derivative is zero. The proved almost-everywhere
identification with the actual material rate therefore gives, at `z = 0`,

```text
materialRateδ = δ Dᵤ||ω||²,
anisotropy(R₀,e,ω) + ν anisotropy(ΔSχ,e,ω) = 0.
```

These statements hold almost everywhere in time and space for the actual
local solution, including multiple top eigenvalues. Neither anisotropy
is asserted to vanish separately, and a zero first derivative does not
prove preservation of coherence. `LocalLimitingAlignmentAudit.lean` checks
the dependencies of the limit and coherent-rate development.

The whole-eigenspace cancellation is quantified in
`SpectralClusterAnisotropy.lean`. For a differentiable symmetric strain path
`S' = -S² + R`, differentiability of the largest eigenvalue implies

```text
<v,Rv> = (λmax' + λmax²)||v||²,   Sv = λmax v.
```

Thus the remainder's quadratic compression is scalar on the entire top
eigenspace. At a double top eigenvalue, the anisotropy is bounded using
distance from the expanding plane and the bottom gap. At a triple
eigenvalue it vanishes for every vector. No continuous or measurable
choice of eigenvectors is assumed.

`SpectralClusterEnvelope.lean` combines these branches in a measurable
scalar envelope. With `r = g` if `g > 0`, and `r = λsecond-λmin` otherwise,

```text
Rν = R₀ + νΔSχ,
Cν = min (2||Rν||||ω||²) (4||Rν||||ω|| sqrt(E₀/r)).
```

The envelope is zero at zero defect, including multiple top eigenvalues.
Its anisotropy bound at collisions requires the actual strain equation
and spectral differentiability; it is not valid for arbitrary remainders.
`LocalClusterAnisotropy.lean` proves that the actual frozen strain derivative
satisfies this equation, and derives the cluster bound almost everywhere
in time and space, simultaneously for every vector. For full vorticity,
the scalar envelope is spatially measurable and integrable.

`LocalClusterMaterialRate.lean` proves the exact joint splitting and the
almost-everywhere estimate

```text
materialRateδ + ||z||²
  ≤ Cν + 2<z,f₀+νΔω> + δ Dᵤ||ω||².
```

Its source is spatially integrable under the third-moment regularity of
the constructed local solution. This preserves joint cancellation but is
not a replacement for the diffusion-paid estimate: `νΔSχ` remains inside
`Rν`, and `νΔω` remains in the signed pairing. Small positive top gaps still
use the line branch; no uniform near-collision modulus or all-scale
source payment is proved. The spectral identities alone do not distinguish
unforced regularity from a forced blowup construction. The new theorem
dependencies are checked by `LocalClusterAnisotropyAudit.lean`.

`StrainEigenvalueRates.lean` differentiates all three ordered eigenvalues
without differentiating a chosen eigenbasis: variational extrema give the
extreme rates, and the trace gives the middle rate.
`LocalSpectralFunctionDifferentiability.lean` extends the actual periodic
almost-everywhere material differentiability theorem to every Lipschitz
scalar strain functional. In particular it supplies both extreme-eigenvalue
differentiability hypotheses for the actual local solution.

`TopPlaneGapTransport.lean` retains the signed source inside the expanding
plane. With ordered eigenvectors `e₀,e₁,e₂`, coordinates `aᵢ = <eᵢ,w>`,
top gap `gₜ`, bottom gap `gᵦ > 0`, and `Rᵢⱼ = <eᵢ,Reⱼ>`, it proves

```text
gₜ' = -(λ₀+λ₁)gₜ + R₀₀-R₁₁,
Q = a₁²(gₜ' + (λ₀+λ₁)gₜ) - a₀a₁(R₀₁+R₁₀),
|anisotropy(R,e₀,w) - Q| ≤ 4||R||||w|| sqrt(E₀/gᵦ).
```

Here `Q` is exactly the anisotropy evaluated on the expanding-plane
projection of `w`. This holds also for small positive top gaps: the
gap-rate and in-plane mixing are retained, not bounded away by the bottom
gap. `LocalTopPlaneRate.lean` constructs the actual frozen top-gap rate
and derives the corresponding almost-everywhere material inequality,
using `R = Rν` and the full vorticity. Only its transverse term is replaced
by the absolute bound. These statements do not prove measurability or
time-integrated affordability of the individual chosen-frame terms, nor
a scale-uniform source budget. `LocalTopPlaneRateAudit.lean` checks their
dependencies.

`BottomSpectralProjectorPolynomial.lean` proves the basis-independent formula

```text
Pbottom = ((λ₀-λ₂)(λ₁-λ₂))⁻¹ (S-λ₀I)(S-λ₁I),   λ₁ > λ₂.
```

The numerator identity holds even without a positive gap. With a positive
bottom gap, differentiating this polynomial quotient constructs bottom-line
and expanding-plane projector derivatives from the operator and scalar
eigenvalue derivatives. `LocalTopPlaneRate.lean` supplies these hypotheses
almost everywhere for the actual frozen material path. No moving
eigenvector choice or positive top gap is required. The following
development bounds the rate; its time-integrated cost remains unpaid.

`RankOneProjectorTangent.lean` represents a self-adjoint projector tangent
`D` as the sum of two rank-one operators determined by `De₂`. In
`BottomProjectorMotion.lean`, the differentiated bottom spectral equation
is tested against `De₂`. Its strain-square term vanishes because `De₂`
is perpendicular to `e₂`. Bottom-gap coercivity then proves

```text
P = Pbottom, Q = I-P, gᵦ = λ₁-λ₂ > 0,
K = Q R P,
||P'e₂|| ≤ ||K||/gᵦ,
||P'|| = ||Q'|| ≤ 2||K||/gᵦ,
|<w,Q'w>| ≤ 4||K||/gᵦ ||Pw||||Qw||.
```

The coupling norm is at most `||R||`, but retains the off-diagonal block
instead of charging the whole remainder. Adding a component which
preserves the bottom eigenline does not change K. If R itself preserves
that line, the plane derivative is zero at the evaluation time; this is
not a claim of coherence preservation over an interval.

`LocalProjectorMotion.lean` derives these bounds almost everywhere for
the actual frozen material projector, with `R = Rν` and no extra assumed
projector derivative or positive top gap. For every `ρ > 0`, it also proves

```text
|<w,DᵤQ w>| ≤ ρ||Pw||² + 4||K||²/(ρ gᵦ²) ||Qw||².
```

Taking `ρ = gᵦ` leaves the explicit source cost
`4||K||²/gᵦ³ ||Qw||²`. This is an absorption inequality, not a proof of
its time integral or a complete residence bound. The pressure, all-input
subgrid, discarded-velocity transport, and viscous terms remain in Rν.
The following development supplies the actual vorticity-energy balance
and fixed-positive-gap spatial integrability. Time integration and
scale-uniform unforced payment remain open.
`LocalProjectorMotionAudit.lean` checks all 35 new theorem dependencies.

`FilteredStrainTrace.lean` derives trace-free filtered strain from the
actual Fourier incompressibility condition, then proves
`λmin ≤ -(2/3)gᵦ`. `BottomProjectedEnergy.lean` uses the unnormalized
bottom-projected energy, which remains defined at vorticity zeros:

```text
Eᵦ = ||Pbottom ω||² = <ω,Pbottom ω>,
fν = (Sfull-Sχ)ω + νΔω,
DᵤEᵦ = 2λmin Eᵦ + 2<Pbottom ω,fν> + <ω,(DᵤPbottom)ω>.
```

`LocalFrozenVorticity.lean` differentiates full vorticity along the same
actual frozen material path as the projector. `LocalBottomEnergy.lean`
combines the exact identity, incompressibility, and the checked transfer
absorption to prove almost everywhere, on the positive-bottom-gap branch,

```text
DᵤEᵦ + (gᵦ/3)Eᵦ ≤ 2<Pbottom ω,fν> + 4||Kν||²/gᵦ³ ||Pplane ω||²,
Kν = Pplane Rν Pbottom.
```

The viscosity pairing remains signed. Its exact split into mismatch and
`2ν<Pbottom ω,Δω>` is proved; the viscous strain contribution also remains
inside Kν. Neither contribution has been dropped or globally paid.

`LocalPhysicalBottomEnergy.lean` constructs one positive local interval
and one solution from real, zero-mean, divergence-free periodic initial
data with continuous coordinate jets through order nine. The derivative
identity and damping estimate hold for every admissible finite filter on
that solution; the common third-moment majorant is constructed from the
data, not added as an independent hypothesis.

`LocalBottomEnergyRegularity.lean` proves continuity of the energy and
signed source wherever `gᵦ > 0`, and spatial integrability on each closed
region `gᵦ ≥ η > 0`. These are not threshold-uniform or time-integrated
estimates. The following development constructs the spatial projector
derivatives and signed parabolic product rule. Moving-region boundary
terms, viscous source cancellation, and the unforced all-scale budget
remain open. `LocalBottomEnergyAudit.lean` checks all 27 new
theorem dependencies.

`StrainSpectralInvariants.lean` expresses the three-dimensional spectral
cubic in traces of operator powers. `BottomProjectorSmoothness.lean`
uses `Analysis/SimpleImplicitRoot.lean` and a rational invariant formula
to prove smoothness of the bottom projector from smooth strain and a
positive bottom gap. No differentiability or separation of the two top
eigenvalues is assumed. `LocalSpatialBottomProjector.lean` constructs
the actual spatial projector derivatives; `LocalSpatialVorticityJets.lean`
supplies the two full-vorticity derivatives from a summable third velocity
moment, without a receiver truncation.

`LocalBottomEnergyDiffusion.lean` proves the actual energy Laplacian
product rule. Writing `P = Pbottom`, `Pⱼ = ∂ⱼP`, `ωⱼ = ∂ⱼω`, and
`W = DᵤP - νΔP`, the signed parabolic source is

```text
Rpar = 2<Pω,(Sfull-Sχ)ω> + <ω,Wω> - 4ν Σⱼ<ωⱼ,Pⱼω>.
(Dᵤ-νΔ)Eᵦ + 2ν Σⱼ||Pωⱼ||² = 2λmin Eᵦ + Rpar.
(Dᵤ-νΔ)Eᵦ + 2ν Σⱼ||Pωⱼ||² + (4gᵦ/3)Eᵦ ≤ Rpar.
```

`LocalPhysicalBottomDiffusion.lean` proves this balance almost everywhere
on the positive-gap branch of one local solution constructed from the
same real, zero-mean, divergence-free order-nine initial data, for every
admissible finite filter. No source-size assumption is added.

The independent `Analysis/OperatorQuadraticForm.lean` proves the two
quadratic-form derivatives. `Analysis/IdempotentDerivatives.lean` exposes
an important correction, also instantiated for the actual spatial projector:

```text
WP + PW = W + 2ν Σⱼ Pⱼ².
```

Thus W is not generally an ordinary projector tangent. The preceding
first-order transfer estimate cannot be applied to W unchanged. These
identities preserve the signed dissipative square. The next layer below
cancels the principal strain diffusion inside W; control of the remaining
cross terms, integration over moving gap regions, and a time/scale-uniform
unforced source budget remain open. `LocalBottomDiffusionAudit.lean`
checks all 49 theorems in that diffusion-identity development.

### Parabolic projector cancellation and transverse control

`Analysis/SpectralRelationDerivatives.lean` differentiates `SP = μP`
twice and proves the material-minus-diffusion subtraction in a general
noncommutative normed algebra. `LocalSpatialSpectralRelation.lean` supplies
the actual Fourier strain derivatives, bottom eigenvalue derivatives,
and projector derivatives. Write

```text
S = Sχ, μ = λmin(S), g = λmiddle(S)-μ > 0, P = Pbottom, Q = I-P,
R₀ = the actual nonviscous strain remainder,
M = Σⱼ [(∂ⱼS)(∂ⱼP) - (∂ⱼμ)(∂ⱼP)],
H = Σⱼ ||∂ⱼS||op², K = Σⱼ (∂ⱼP)², W = DᵤP - νΔP.

(-S²+R₀)P + SW = (Dᵤμ-νΔμ)P + μW + 2νM.
PWP =  2ν PKP,   QWQ = -2ν QKQ.
||QWP|| ≤ ||QR₀P||/g + 4νH/g²                 (ν ≥ 0).
```

The first identity cancels the explicit `νΔS` term, not the gradient
correction. `BottomParabolicProjectorMotion.lean` obtains off-diagonal
coercivity directly from the spectral equation, without assuming that W
is tangent or self-adjoint. `LocalSpatialSpectralBounds.lean` proves
`|∂ⱼμ| ≤ ||∂ⱼS||`, `||(∂ⱼP)e_min|| ≤ ||∂ⱼS||/g`, and
`||QMP|| ≤ 2H/g`. No top-eigenvalue differentiability is required.

`LocalParabolicProjectorEquation.lean` proves the displayed equations for
the actual local solution almost everywhere on the positive-gap branch.
`LocalParabolicProjectorBound.lean` constructs one physical-data solution
supporting both the signed bottom-energy balance and the new transverse
bound for every admissible finite filter. The exceptional null sets may
depend on the filter and interior interval. The bound is for `QWP`, not
the entire operator W; the nonzero diagonal blocks are kept separately.

`Analysis/KernelCrossTerm.lean` and `LocalBottomGradientObstruction.lean`
rule out one tempting pointwise shortcut. If `(∂ⱼP)(Pω) ≠ 0`, there are
no constants A and B such that, for every vector v,

```text
-4<v,(∂ⱼP)ω> ≤ A ||Pv||² + B.
```

The cross term can grow in `ker P`, where the projected square vanishes.
This is not a counterexample using actual NS solution jets: it rules out
the unrestricted algebraic absorption rule. Coupled-sector dissipation,
additional dynamical constraints, or an integrated cancellation may still
control the actual vorticity-gradient term. The scale-critical estimate
near gap closure and across filters has not been proved.
`LocalParabolicProjectorAudit.lean` audits all 38 new theorems in this layer.

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
