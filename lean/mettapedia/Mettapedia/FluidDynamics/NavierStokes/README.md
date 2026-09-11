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

### Two-input pressure localization and the exact spatial weight

`PressureTwoInputLocalization.lean` now proves the actual finite identity

```text
c * (d * B(w,v)) - B(d*w,c*v)
  = c * C(d;w,v) + C(c;v,d*w).
```

The second commutator shifts the **original** second input. The localized
first input is only a receiver, so no zero-mean or divergence-free condition
is imposed on it. `FiniteCutoffAlgebra.lean` proves the support associativity,
pair symmetry, and collected-coefficient norm bound used in this identity.

`PressureTwoInputEnergy.lean` bounds the error energy, for original inputs
with zero mean, by

```text
288 [ C1² Wminus1² V1² G(d) + D1² W1² Vminus1² G(c) ].
```

Here `C1,D1` are the cutoffs' Fourier l1 norms, `W1,V1` are the original
input Fourier l1 norms, `Wminus1,Vminus1` contain one inverse original
frequency, and `G` is the cutoff's first-derivative Fourier energy.
The resulting localized-pressure estimate retains both actual
`localizationDefect` channels, including cutoff-created divergence.

`PressureTwoInputPhysical.lean` identifies the sign against the actual
finite pressure Hessian. For two copies of `curl u` and one cutoff `c`,
the commutator energy is at most

```text
576 C1² (sum |u_k|)² (sum |curl(u)_k|)² integral |grad c|².
```

`PressureTwoInputReconstruction.lean` proves the exact spatial product
identity and its Parseval energy identity. **Using the same cutoff twice
produces the fourth-power energy weight `|c|⁴`, not `|c|²`.** Thus this
two-input estimate does not yet supply the earlier Gaussian quadratic
weight estimate. The weight factorization, cutoff Fourier-l1 cost,
scale-uniform field norms, and time-integrated inverse-gap budget remain
open analytic work. No unconditional regularity theorem is claimed.
`PressureTwoInputAudit.lean` checks constant-cutoff scaling, frequency
shifts to zero, independently shifted inputs, and created divergence.

### Complete one-input pressure localization and Gaussian derivative budget

`NormalizedPressureTrace.lean` writes the actual complex trace as a
polynomial in normalized input directions. Its trace variation costs 4;
combining this with the output-symbol cancellation costs 12:

```text
|k| |T_e(k,p;w,v) - T_e(l,p;w,v)| <= 12 |k-l| |w| |v|.
```

`PressurePairInputStability.lean` includes shifted input zero and zero or
nearly cancelling outputs, without cone or buffer assumptions. The
corresponding right-input bound follows by pair symmetry.

`PressureBilinearLocalization.lean` proves the exact finite identity

```text
c * B_e(w,v) - B_e(c*w,v) = C_e(c;w,v),
C_e(q) = sum_(p+k+a=q) c_a [T_e(p,k;w_p,v_k) - T_e(a+p,k;w_p,v_k)].
```

Here `*` is scalar-vector Fourier convolution and `B_e` is the actual
complex pressure-pair convolution. Equal output frequencies are grouped
before squaring. With `w(0)=0`, the energy bound is

```text
sum_q |C_e(q)|² <= 144 (sum_p |w_p|/|p|)² (sum_k |v_k|)² G(c),
G(c) = sum_a |a|² |c_a|².
```

For actual `w = fourierCurl u`, `PhysicalPressureLocalization.lean`
charges the inverse source frequency to the velocity. The result is
`144 (sum |u_p|)² (sum |v_k|)²` times the **physical first-derivative
energy of the scalar patch**. The physical pressure sign and the
zero-frequency curl condition are proved from the existing definitions.

`GaussianPressureCommutatorBudget.lean` constructs the same actual
Gaussian patch family before selecting Fourier tolerance or source and
output sets. Its summed commutator energy is bounded by that explicit
Fourier l1 factor times the existing integral of `gradientDensity`.
No additional patch-count factor is inserted. Approximation error,
inverse-gap costs, and the gradient density's existing temperature
dependence remain visible.

This closes the **one-input** localization comparison. The two-input
finite comparison above is also checked, but assembly with the adaptive
quadratic pressure weight is still required. The Fourier l1 costs and inverse-gap density do not yet
have the scale/time-uniform control needed for the dynamical
misalignment budget or BKM continuation. No unconditional regularity
claim follows from these spatial bounds. `PressureLocalizationAudit.lean`
and `Analysis/NormalizationConvolutionTests.lean` check the new boundary
cases, coincident-source interference, and theorem axiom closures.

### Complex pressure identification and localization costs

`ComplexPressurePair.lean` and `ComplexPressureMisalignment.lean` extend
the real pressure-pair depletion estimate below to arbitrary complex
vorticity coefficients, with the **same constant 2** and the same explicit
normalized divergence defects. The transverse error is the existing
complex orthogonal projection off a real unit direction. No reality or
phase-alignment assumption is imposed. `ComplexPressureConvolution.lean`
proves the two-channel finite energy bound with constant 8.

`PhysicalPressurePair.lean` identifies these symbols with the actual
finite pressure Hessian and the convergent infinite pressure coefficients:

```text
omega = fourierCurl u,
traceAmplitude(chi,u,q) = -chi(q) sum_k tracePair(k,q-k;omega_k,omega_(q-k)),
tiltCoefficient(chi,u,e,q) = -chi(q) sum_k tiltPair(e,k,q-k;omega_k,omega_(q-k)).
```

The infinite identities assume divergence-free velocity and summable
second absolute Fourier moment; convergence is proved. Mean velocity
and zero input/output frequencies are included. The physical derivative
and inverse-curl phases are checked explicitly, not suppressed in the
identification. A finite physical pressure-tilt energy estimate follows
with both vorticity-misalignment channels retained.

`FourierLocalizationDivergence.lean` uses the existing coefficient of a
genuine scalar-cutoff product. For divergence-free input,

```text
q dot (c*w)_q = sum_(p+k=q) c_p (p dot w_k),
sum_q |q dot (c*w)_q|² <= (sum_k |w_k|)² G(c),
G(c) = sum_p |p|² |c_p|².
```

On an output band of radius at least `R`, the squared normalized
divergence budget gains `R^(-2)`; output zero contributes zero. `G(c)` is
the same first-derivative energy controlled by the Gaussian Fourier
patch construction. Fixed transverse projection commutes exactly with
this localization. The remaining field l1 norm is not scale-uniform.

`PressurePairOutputStability.lean` proves, for arbitrary complex inputs,
that `|tracePair| |k| |p| <= |k+p|² |w| |v|`. This compensates the
output-direction symbol's apparent singularity:

```text
|k| |tracePair(k,p;w,v) [tiltSymbol_e(k+p)-tiltSymbol_e(r)]|
  <= 8 |k+p-r| |w| |v|.
```

This is the **output-symbol part** of the bilinear localization
commutator; the one-input variation and comparison are completed in
the modules listed above. Two-input weighted localization and the
adaptive scale/time budgets remain unresolved. These results do not close
the dynamical misalignment estimate, or unconditional regularity.
`ComplexPressureAudit.lean` checks phases, zero modes, an actual cutoff
that creates divergence despite perfect line alignment, a sharp
derivative-energy example, and the axiom closures of all 44 new theorems.

### Real pressure-pair depletion, including localization divergence

`CoherentPressurePair.lean` retains the cross-product numerator of the
real Biot--Savart pressure pair, including nearly cancelling inputs. For
a unit direction `e`, `PressurePairMisalignment.lean` proves

```text
T = [(p · (k × w))(k · (p × v)) / (|k|² |p|²)] tiltSymbol_e(k+p),
z_w = w - (e·w)e,        D(k,w) = |k·w| / |k|,
|T| ≤ 2(|z_w| |v| + |w| |z_v|) + D(k,w)|v| + |w|D(p,v).
```

The divergence terms vanish for divergence-free vorticity pairs. They
are retained in the general statement because spatial multiplication
by a patch does not preserve divergence-freeness. There is no cone
assumption and no lower bound for `|k+p|`; zero input/output frequencies
are included. When both inputs are exactly aligned and divergence-free,
the pair vanishes.

The coherent numerator is `-(e·(k×p))²`. Near cancellation its cross
product supplies a compensating small factor, so a bad output angle does
not by itself defeat the estimate. The regression family
`k=(n,0,1), p=(-n,1,0), e=(0,0,1)` has a fixed 45-degree output angle while
its coherent pair equals `(0,-n²/[2(n²+1)²],0)`.

`PressurePairConvolution.lean` collects coincident outputs before taking
energy and retains both source/receiver error channels. With
`E(k,w)=|z_w|+D(k,w)/2`, the finite real convolution satisfies

```text
Σ_q |Σ_{k+p=q} T(k,p;w_k,v_p)|²
  ≤ 8 (Σ_k E(k,w_k))² Σ_p |v_p|²
    + 8 (Σ_k |w_k|)² Σ_p E(p,v_p)².
```

No explicit mode-count or frequency-ratio factor is inserted. The source
norm is still **l1**, which can grow with scale. These are real bilinear
pair estimates in a fixed frame; the complex and physical coefficient
extensions are recorded above. Full bilinear localization and scale/time
summation remain required. No dynamical
misalignment budget or unconditional regularity theorem follows yet.
`PressurePairMisalignmentAudit.lean` checks cancellation, the bad-output
angle family, and the necessity of the divergence condition.

### Quantitative Gaussian pressure patches

`LocalGaussianGradientBudget.lean` constructs one finite family of real
patch amplitudes from the actual squared-gap weighted projector `M = rP`.
For every positive localization radius `ρ`, the same patches satisfy

```text
Σᵢ βᵢ² = r²,             Σᵢ βᵢ² dline(e,eᵢ)² ≤ ρ²,
Σⱼᵢ |∂ⱼβᵢ|² ≤ 3[1 + r²ρ²/(2τ²)] Σⱼ ||∂ⱼM||²   almost everywhere,
τ = ρ² / [4(1 + log N)],  N = number of cover centers ≥ 1.
```

The integral bound substitutes the actual vorticity and filtered-strain
gradient estimate for `M`. The construction uses normalized Gaussian
amplitudes in Hilbert matrix coordinates, not a differentiable choice of
eigenvector. Exact normalization cancels the common score rate. An entropy
bound controls the mean squared distance by the nearest squared distance
plus `τ log N`. Local Lipschitz regularity proves genuine almost-everywhere
differentiability, separately from the zero default of the total derivative.

These are spatial amplitudes. `LocalGaussianFourierBudget.lean` now
constructs finite Fourier approximants from their actual coefficients;
`LocalGaussianPressureBudget.lean` charges the pressure replacement error
and inserts this density into the smoothed commutator estimate below. There is no
multiplicative patch-count loss, but the displayed logarithmic count,
inverse-radius, amplitude, and inverse-gap-threshold costs remain. No
uniform dynamical budget or unconditional regularity theorem is claimed.
`GaussianPressurePartitionAudit.lean` audits the NS dependency closure;
`Analysis/GaussianPartitionTests.lean` checks the generic cancellations,
sharp variance constant, norm corner, and Hilbert/operator norm comparison.

### Energy-controlled finite Fourier approximation

`PeriodicFourierWeakDerivative.lean` extends periodic integration by parts
to a real locally Lipschitz field and a smooth complex character. It proves
the actual coefficient identity, including sign and normalization,

```text
Fourier(∂ⱼβ)(k) = (2πi) kⱼ Fourier(β)(k).
```

`PeriodicFourierGradientEnergy.lean` uses Bessel's inequality to bound
every finite restriction of those coefficients by the physical gradient
energy. `PeriodicFourierProjection.lean` supplies the finite coefficient
objects and identifies their evaluation with the L² projections.
`LocalGaussianFourierBudget.lean` then constructs, for the actual Gaussian
patches `βᵢ` and every `δ > 0`, polynomials `pᵢ` with coefficients `cᵢ`:

```text
Σᵢ ||pᵢ - βᵢ||₂² < δ,
|2πi|² Σᵢ G(cᵢ) ≤ ∫ gradientDensity(γ,ρ,τ).
```

No mode-count or patch-count factor is introduced by this approximation.
The density retains the costs displayed above. This is **L² approximation,
not uniform approximation**: exact coverage and weighted line localization
still refer to `βᵢ`. The pressure application combines those spatial
identities with a charged L² replacement error; it does not reuse the old
pointwise coverage assumption for `pᵢ`. The strengthened
`exists_local_gaussian_fourier_family` fixes the cover and its derivative
budget before quantifying over `δ`. Angular tails, uniform pressure norms,
and the dynamical source budget remain open.
`GaussianFourierBudgetAudit.lean` checks the dependency closure, constant
and negative-frequency derivatives, and finite-coefficient energies.

### Gaussian pressure budget with charged approximation errors

`WeightedPressureL2Replacement.lean` integrates exact spatial line
localization and then charges the total L² change in quadratic weights.
`SmoothedPressureL2Budget.lean` also pays for resolvent smoothing and the
elliptic commutator. `LocalGaussianPressureBudget.lean` applies the estimate
to the actual strain/vorticity patches, not an assumed cutoff family:

```text
∫ a₂ Tilt_e(H)²
  ≤ 16η² ∫ a₂ trace(H)² + 8 Σᵢ angularTail(dᵢ)
    + Cε,η / |2πi|² · ∫ gradientDensity(γ,ρ,τ)
    + Rη δ + 32ρ² HessianEnergy,
Cε,η = 1536 B₁² + 72 B₀²/ε + 2ε B_H² + 8εη² B_T²,
Rη = 8 B_H² + 32η² B_T²,        dᵢ = resolvent_ε(cᵢ).
```

The cover depends on `γ,ρ` and the actual field, but not on `δ`, the
pressure truncation, smoothing parameter, or angular threshold. For each
`δ > 0`, one finite coefficient family works for every positive `ε`, every
symmetric finite pressure truncation, and every nonnegative `η`. There is
no additional mode-count or patch-count multiplier. The displayed density
still contains the logarithmic cover-size and inverse-gap/radius costs.

`PressureSmoothingBalance.lean` completes the square in `Cε,η`. Writing
`Q = B_H² + 4η²B_T²`, its exact lower envelope is
`1536 B₁² + 24 B₀ sqrt(Q)`, attained at `ε = 6 B₀ / sqrt(Q)` when both
`B₀` and `Q` are positive. This optimizes only the displayed derivative
coefficient, **not** the angular tail or the full pressure bound. In
particular, taking `ε` to zero cannot remove a nonzero commutator cost.

No fluid-dissipation absorption or scale/time-uniform bound follows yet.
The actual angular tails and pressure norms must still be controlled in
the dynamical source estimate. `GaussianPressureBudgetAudit.lean` checks
zero and nonzero replacement errors, composed errors, sharp physical
smoothing error, and the dependency closure.

### Constructive pressure-patch smoothing

`StochasticLagrangian/FourierResolventSmoothing.lean` constructs the finite
coefficients `d(k) = c(k) / (1 + ε |k|²)` and proves, for `ε > 0`,

```text
G(d) ≤ G(c),       H(d) ≤ G(c)/(4ε),       ||p_c - p_d||₂² ≤ ε G(c)/4.
```

Here `G(c) = Σ|k|²|c(k)|²` and `H(c) = Σ|k|⁴|c(k)|²` use integer torus
frequencies. The physical derivative factors are retained separately in
`FourierCoordinateDerivatives.lean`. Smoothing preserves the exact support,
fixes constant modes, and solves its elliptic coefficient equation. The
sharp constants are attained by the audited single-mode examples.

`PressurePatchSmoothing.lean` charges the approximation error against the
actual pressure Hessian and trace supremum norms. The earlier
`SmoothedPressureBudget.lean` constructs a uniform-approximation patch
family, distinct from the derivative-controlled Gaussian family above,
for every smoothing
parameter, pressure truncation, and angular threshold. Its bound retains the
weighted pressure trace and angular tails, with cutoff cost

```text
[1536 B₁² + 72 B₀²/ε + ε B_H² + 4εη² B_T²] Σ_i G(c_i).
```

`B₀` and `B₁` are the normalized pressure-potential supremum and coordinate
gradient bound; `B_H` and `B_T` are the physical Hessian and trace suprema.
No mode-count or patch-count factor is inserted. This removes a separate
second-derivative cutoff cost but does **not** bound the original patch
gradient energy by the fluid dissipation, control the angular tails, or
establish uniform pressure bounds. Those dynamical estimates remain open.
`PressureSmoothingAudit.lean` checks the new NS theorem dependencies.

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

`SpectralSourceCommutator.lean` separates the two transverse source blocks
from the quadratic misalignment term. It proves
`g||P⊥R₀e|| ≤ ||SχR₀−R₀Sχ||` and the corresponding adjoint estimate;
the source need not be symmetric. `SpectralCommutatorEnvelope.lean` uses
the capped scalar weight to improve the source further:

```text
J = ||SχR₀−R₀Sχ||,       Wε = min(|ω|²,Eε/(g+ε)),
Cε = min(Bε, 2||R₀||Wε + 2(J+ε||R₀||)/(g+ε) |ω|sqrt(Wε)),
Nδ,ε_depleted = Cε + 2<z,f₀> + 2δ<ω,Sfull ω>,       ε>0.
```

The continuous refinement never exceeds `Bε`. Its definition includes a
positive part for nonpositive auxiliary parameters; this is inactive
when `ε>0`. At a top collision it still equals the coarse envelope.

`LocalDepletedAlignmentSource.lean` constructs this sharper source from the actual
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
```

`SpectralCommutatorLimit.lean` removes smoothing from the sharper envelope:

```text
C* = min(B*, 2||R₀||W₀ + 2(J/g)|ω|sqrt(W₀))  if g>0;
C* = 2||R₀||||ω||²                          if g=0,
W₀ = min(|ω|²,E₀/g)                         if g>0;
W₀ = |ω|²                                  if g=0,
Nδ,* = C* + 2<z,f₀> + 2δ<ω,Sfull ω>.
```

The scalar limits are measurable and bounded by the coarse envelope. On a
simple top eigenline they vanish at exact alignment. For a commuting
source and `g>0`, the new envelope is at most `2||R₀||W₀`: the
linear-in-misalignment channel disappears. Continuity through collisions
is not asserted. `LocalLimitingAlignmentSource.lean` constructs
the actual limiting source and proves spatial dominated convergence under
an absolute majorant independent of `ε`. `LocalAlignmentSourceLimit.lean`
proves interval integrability and the time-integral limit.
`LocalLimitingAlignmentBudget.lean` then proves the initial-data estimate
with `Nδ,*`, keeping `δ > 0` and its viscous payment fixed. One local solution
and interval again work for all admissible filters and regularizers.
This is a local estimate, not uniform control toward a singular time.

`LocalSourceCommutator.lean` identifies the actual combined commutator:

```text
[Sχ,R₀] = −([Sχ,Wχ]Wχ + Wχ[Sχ,Wχ])
          −[Sχ,Hess(p_v)] + [Sχ,sym ∇gχ] + [Sχ,(u−v)·∇Sχ].
```

Here `v=χu`, `p_v` is the resolved pressure (not the filtered full pressure),
all operators use the explicit finite output reconstructions, and
`gχ` is the all-input, Leray-projected subgrid force. The combined
commutator is formed before taking its norm; cancellation between
channels is not discarded. Its joint space-time continuity is proved
for the actual local solution. The improvement propagates through the
existing spacetime, smoothing-limit, and excess-diffusion theorems.
No all-scale estimate of this commutator is supplied.

`InfiniteFilteredPressure.lean` and `LocalPressureCommutator.lean` now
cancel the resolved pressure against the pressure correction inside the
projected subgrid force, at every output frequency and in the actual
local solution:

```text
−Hess(p_v) + sym ∇gχ = −χ Hess(p_u) + sym ∇Fraw,
Fraw = −2πi · subgridConvection(χ,u).
```

The infinite fiber is retained, including both-high inputs; finite
support is used only to identify the resolved pressure. The filter acts
on the output of the full pressure, not on its two input velocities.
The raw force is generated filtering feedback in the unforced equation,
not an externally prescribed force.
`FourierPressureCommutator.lean` identifies its real Hessian operator as
`H = Σ_q a_q (q ⊗ q)`, with the full real spatial phase in `a_q`. Thus
`[S,H] = Σ_q a_q ((Sq−b_q q)⊗q − q⊗(Sq−b_q q))` for any scalar shifts
`b_q`. The signed sum precedes the separate norm upper bound.

`FourierPressureTilt.lean` extracts the more selective direct action:

```text
P⊥ H e = Σ_q a_q <q,e> P⊥q.
```

Modes perpendicular to `e` cannot tilt that line. If every active mode is
perpendicular, `H e=0` and
`|anisotropy(H,e,ω)| ≤ ||H|| ||P⊥ω||²`. This hypothesis is not inferred
from pointwise alignment of vorticity. The complete commutator can remain
nonzero because it also measures rotation inside the transverse plane.

`LocalJointSourceTilt.lean` proves symmetry of the actual nonviscous
source and identifies its complete direct tilt `K = P⊥ R₀ e`, preserving
the pressure sum jointly with spin, raw feedback and transport. It proves
the actual pointwise bound

```text
|anisotropy(R₀,e,ω)| ≤ 2||R₀|| ||m||² + 2||ω|| ||m|| ||K||,
m = P⊥ω.
```

No separate adjoint channel is needed for this symmetric source.
`LocalPressureTiltAudit.lean` checks these identities.

`SpectralTiltExcess.lean` absorbs the source using the direct tilt rather
than the full commutator. With `g` the top gap, `W₀` the limiting transverse
weight, and `Yold` the previous source excess, it defines

```text
Ytilt = min(Yold, max(2||R₀||−g²/8,0) W₀ + 8|K|²|ω|²/g²)   if g>0,
        Yold                                                if g=0.
```

It proves `|anisotropy(R₀,e,ω)|≤Q/4+Ytilt`, where `Q` is the squared
spectral residual, and `0≤Ytilt≤Yold≤2||R₀||||ω||²`. At a top collision
the coarse fallback remains; at separated exact alignment the cost is
zero. Preserving the top line suffices for complete absorption below the
threshold `16||R₀||≤g²`, even when the transverse-plane commutator is
nonzero. The intrinsic tilt norm is `||(1−P)R₀P||`; positive-gap projector
continuity and measurable restriction prove measurability of the capped
cost without selecting measurable signed eigenvectors.

`LocalTiltSource.lean` applies this bound directly to the physical material
rate, then reapplies weak spatial diffusion and its smoothing limit. It
does not decrease the right side of an older inequality without proof.
`LocalTiltAlignmentEnergy.lean` supplies an actual local solution from
arbitrary admissible periodic data satisfying, simultaneously for all
admissible finite strain filters and positive energy regularizers,

```text
mean Φδ(t) + ¼∫∫Q ≤ mean Φδ(0) + ∫∫[Xdiff + Ytilt
                         + 2<z,(Sfull−Sχ)ω> + 2δ<ω,Sfullω>].
```

The estimate includes both endpoints of the local solution window.
`Analysis/IntegralEndpointEstimate.lean` requires only integrable source
terms for that extension, not continuity through collisions.
`LocalTiltSourceAudit.lean` checks the physical factory and regressions.
Uniform angular, feedback, collision-sector and diffusion budgets remain
open. The weighted spatial pressure localization below retains the
vorticity/gap weight appearing in this source cost; it does not yet bound
its accumulation in time or across scales.

`FourierPressureTiltEnergy.lean` removes the output-count loss in the
spatial pressure estimate. For a fixed unit direction `f`, write
`a(q)=χ(q)(2πi)²p̂(q)`, with pressure determined by the full velocity.
Finite Parseval gives

```text
∫ |P⊥_f Hχ f|² ≤ Σq |a(q)|²(q·f)²(|q|²−(q·f)²).
```

The angular sum is at most a quarter of the Hessian coefficient energy
`EH=Σq |a(q)|²|q|⁴`. If active pressure modes satisfy
`(q·f)²≤η²|q|²`, it is at most `η² EH`. This is an explicit condition
on the pressure output modes, not a consequence of pointwise alignment.

`FourierPressureHessianEnergy.lean` proves `∫||Hχ||op²≤EH` by applying
Parseval on an orthonormal basis and the generic operator bound from
`Analysis/OrthonormalOperatorBound.lean`. Neither estimate has a mode-count
or basis-cardinality factor.
`SpectralTiltFreezing.lean` compares transverse actions in nearby unit
directions. Its squared bound uses the sign-invariant distance
`dline(e,f)²=min(|e−f|²,|e+f|²)`; eigenvector sign flips cost nothing.
`FourierPressureTiltFreezing.lean` then proves, for any measurable unit
direction field with `dline(e(x),f)≤ρ` and the pressure cone condition,

```text
∫ |P⊥_e(x) Hχ(x) e(x)|² ≤ (2η²+32ρ²) EH.
```

The direction error is paid by Hessian coefficient energy, not an `ℓ¹`
coefficient envelope. These are spatial estimates for the actual pressure
operator. They do not prove that pressure modes obey the cone condition
or control the weighted time-integrated source cost.
`FourierPressureEnergyAudit.lean` checks the
new declarations, zero-filter behavior and antipodal-line invariance.

`RealFourierLocalizationEnergy.lean` realizes a squared Fourier cutoff
weight exactly in coefficient energy. It symmetrizes the real field before
multiplying by the possibly complex cutoff, collects repeated frequencies,
and retains the entire Minkowski-sum output support. Negation closure of
the original field's finite output set is explicit. No spatial compact
support or hard frequency truncation is substituted for the Fourier tail.

`FourierLinePartition.lean` chooses the square-root approximation accuracy
after the finite cell count is known. For arbitrary positive `δ`, the same
family of Fourier weights satisfies `1/2≤Σwᵢ≤3/2` and total squared line
error `Σwᵢ dline(e,fᵢ)²≤(3/2)ρ²+2δ²`; the second term pays the off-cell
tails. `FourierPressurePatchEnergy.lean` then proves

```text
∫ |P⊥_e(x) Hχ(x) e(x)|² ≤ 4Σᵢ Eᵢ + (96ρ²+128δ²) EH,
Eᵢ = ∫ wᵢ(x) |P⊥_fᵢ Hχ(x) fᵢ|²
   = exact collected localized Fourier coefficient energy.
```

There is no multiplicative cell-count factor. The cells and cutoff
bandwidths may depend on the line field and tolerances; no uniform
bandwidth over time or dyadic scale is claimed. The frozen patch energies
remain localized, rather than being replaced by a sum of unweighted
whole-domain bounds.

`LineProjectorTilt.lean` identifies the tilt norm with `||(1−P)HχP||`,
where `P=e⊗e`. Its square is continuous when the projector and pressure
operator are continuous, without any measurable choice of a signed unit
vector. `AdaptiveLinePartition.lean` constructs the required continuous
partition from that projector. The resulting pressure-patch existence
theorem constructs both cells and cutoffs, independent of the subsequent
pressure coefficients. This construction does not extend a top eigenline
through an eigenvalue collision. Pressure-angle control of `ΣEᵢ`, collision
sector treatment and the vorticity/gap-weighted time budget remain open.
`FourierPressurePatchAudit.lean` checks the new dependencies and regressions,
including a purely imaginary cutoff and arbitrary eigenvector sign choices.

`WeightedLineFreezing.lean` instead freezes `sqrt(a) P`. For unit lines,

```text
a dline(e,f)² ≤ 2 ||sqrt(a) Pe − sqrt(b) Pf||².
```

Thus the cells can follow a continuous weighted projector even when the
unweighted line has no continuous extension at zero weight.
`WeightedProjectorTilt.lean` proves continuity of `a |P⊥ R e|²` under
exactly that hypothesis: at zero weight it is squeezed by `a ||R||²`;
at positive weight the projector is recovered by division.
`QuadraticFourierWeightApproximation.lean` approximates general
nonnegative continuous weights, with no unit-interval restriction and
a prescribed total absolute approximation error for finite families.

`WeightedFourierPressurePatch.lean` constructs Fourier polynomials
approximating the square roots of `a` times the partition weights. It
proves, with the same exact localized coefficient energies `Eᵢ`,

```text
|Σᵢ |pᵢ(x)|² − a(x)| ≤ δ,
∫ a(x) |P⊥_e(x) Hχ(x) e(x)|² ≤ 2Σᵢ Eᵢ + (32ρ²+2δ) EH.
```

The weight remains inside the patches. No cell-count factor or global
supremum of `a` multiplies the pressure energy. Patch bandwidth is still
allowed to depend on the weighted field and tolerances.

`SpectralGapTiltWeight.lean` constructs the actual continuous weight
`a=κγ(g)|ω|²/max(g,γ)²`, where `γ>0`, `κγ=0` for `g≤γ`, and `κγ=1`
for `g≥2γ`. The weighted top projector is continuous through collisions.
The source split keeps the full joint tilt and the complementary cost:

```text
Ytilt ≤ κγ max(2||R₀||−g²/8,0) W₀
        + min(2||R₀||||ω||², 8a|K|²)
        + (1−κγ) 2||R₀||||ω||².
```

At `g=0` the last term is the original coarse cost, not zero.
`LocalWeightedPressurePatch.lean` constructs the patches for the actual
filtered strain and full vorticity of any Fourier velocity with summable
first moment, and proves the actual joint-source split. It assumes
neither a global positive gap nor a continuous signed eigenvector.
`WeightedPressurePatchAudit.lean` checks these results and regressions.

`PressureTiltSymbol.lean` factors the pressure action through its real,
even, order-zero symbol `mₑ(k)=(k·e)P⊥ₑk/|k|²`, defined as zero at `k=0`.
It proves `|mₑ(k)−mₑ(l)|≤4|k−l|/|k|` for `k≠0`, including `l=0`.
`FourierPressureTraceSymbol.lean` factors the physical tilt coefficients
and proves that real symmetrization commutes with this symbol. The real
pressure field is formed before multiplication by a complex cutoff.

`FourierPressureLocalization.lean` retains the exact cutoff commutator.
For `Bᵢ=cᵢ*b` with `b` the real-symmetrized Laplacian-pressure coefficients,

```text
Cᵢ(q) = Σ_{p+k=q} cᵢ(p)b(k)[mₑᵢ(k)−mₑᵢ(q)],
Eᵢ ≤ 2η² Σq |Bᵢ(q)|² + 2 Tᵢ(η) + 2 Σq |Cᵢ(q)|²,
Tᵢ(η) = Σ_{q: |mₑᵢ(q)|>η} |Bᵢ(q)|².
```

This is an unconditional split, not a cone assumption. The threshold is
on the actual tilt symbol: both parallel and perpendicular modes have
zero symbol. If all input frequencies have magnitude at least `κ>0`,
the commutator energy is at most
`16 κ⁻² (Σp |cᵢ(p)||p|)² EH`. A separate conditional cone estimate
widens the input gain `η` to `η+4r/κ` for cutoff radius `r`.

`PressureTracePatchEnergy.lean` identifies the scalar patch energy with
`∫ |pᵢ|² |tr Hχ|²`. `WeightedPressureAngularBudget.lean` constructs a
single patch family, valid for every finite negation-closed pressure
truncation and every `η≥0`, with

```text
∫ a |P⊥ₑ Hχ e|² ≤ 4η² ∫ a |tr Hχ|²
                   + 4Σᵢ Tᵢ(η) + 4Σᵢ ||Cᵢ||₂²
                   + (32ρ²+2δ+4η²δ) EH.
```

`LocalPressureAngularBudget.lean` constructs that family from the actual
filtered strain and full vorticity, with the same collision-safe weight
`a`. Neither pressure-cone membership nor tail/commutator smallness is
assumed. `PressureAngularBudgetAudit.lean` checks the dependency closure
and zero, parallel, perpendicular, oblique, and threshold regressions.
Uniform time/scale control of the weighted trace term, angular tails,
cutoff Fourier moments, collision cost, feedback and diffusion is still
open. These spatial constructions do not establish global regularity.

### Quantitatively regular spectral pressure weights

`GapCutoffRegularity.lean` proves that the square root of the linear gap
ramp is not Lipschitz: at `g = γ + γr²` its value is exactly `r` for
`0 ≤ r ≤ 1`. The previous continuous patch construction is valid, but
does not by itself provide the spatial derivative control needed for a
quantitative cutoff estimate.

`GapTruncatedProjector.lean` and `SquaredGapTiltWeight.lean` construct

```text
κ = max(0, min(1, (g−γ)/γ)),  γ > 0,
a₂ = κ² |ω|² / max(g,γ)²,
M = sqrt(a₂) P = κ |ω| P / max(g,γ).
```

The new energy weight is `κ` times the previous weight. For arbitrary
symmetric strains `A,B` and vectors `w,v`, the checked two-state estimate is

```text
||M(A,w)−M(B,v)|| ≤ ||w−v||/γ + 20 |v| ||A−B||/γ².
```

The associated squared line-distance bound retains the local weight,
without requiring a continuous eigenvector choice. The complementary
source cost is now `(1−κ²) 2||R|| |ω|²`, exactly the old collision cost
plus `κ(1−κ) 2||R|| |ω|²`. Regularizing the cutoff does not discard this
additional transition cost.

`LocalSquaredGapPressure.lean` instantiates the regularized weight using
the actual filtered strain and full vorticity. It proves local spatial
and interior space-time Lipschitz regularity, the same angular pressure
budget with weight `a₂`, and the joint-source bound with the adjusted
collision cost. The space-time statement uses a clamped extension of
the coefficients, not a claim of global PDE existence.

`LocalSquaredGapGradient.lean` proves almost-everywhere coordinate
differentiability for periodic Haar measure, measurability and
integrability of the derivative energy, and the physical bound

```text
∫ Σj ||∂j M||² ≤ (2/γ²) ∫ Σj ||∂j ω||²
                  + (800/γ⁴) ∫ |ω|² Σj ||∂j Sχ||².
```

The coordinate and integral estimates use a summable third Fourier
moment of the actual velocity. They do not establish a scale-uniform
cutoff Fourier-moment bound or a time-integrated source budget.
`SquaredGapPressureAudit.lean` checks the dependency closure and the
collision, transition, separated-gap, zero-vorticity, and square-root
regressions. The original linear-weight theorems remain unchanged.

### Elliptic localization with physical product costs

The first-gradient estimate above does not bound the first Fourier
coefficient moment used by the earlier commutator estimate.
`PressureTiltEllipticIdentity.lean` instead expands the pressure
multiplier's exact elliptic product identity. Writing `q=p+k`,
`mₑ(k)=P⊥ₑ k(k·e)/|k|²`, and `b(k)=|k|² φ(k)`, it gives

```text
|k|² [mₑ(k)−mₑ(q)]
  = (2p·k+|p|²)mₑ(q)
    − P⊥ₑ [p(k·e)+k(p·e)+p(p·e)].
```

This includes `k=0` and `q=0`; no inverse output-frequency assumption
is introduced. `FourierPressureEllipticCommutator.lean` supplies `φ`
from the actual pressure coefficients, real-symmetrized before
localization. It retains the original unit-torus derivative phase
already present in `pressureAmplitude`: `φ` is the potential for the
integer-frequency multiplier `|k|²`, not an unscaled pressure value.

`FourierEllipticProductCoefficients.lean` identifies the resulting
scalar and matrix coefficients with mixed first-coordinate products
and second-coordinate cutoff products. `FourierProductEnergy.lean`
uses Parseval and a physical supremum norm, with no coefficient-count
factor. Let `G(c)=ΣⱼΣₚ |pⱼ c(p)|²` and
`H(c)=ΣᵢⱼΣₚ |pᵢpⱼ c(p)|²`. For

```text
B₀ = ||Σₖ φ(k)eₖ||∞,
B₁ = Σⱼ ||Σₖ kⱼ φ(k)eₖ||∞,
```

`LocalPressureEllipticBudget.lean` proves for every unit frozen line

```text
Ecomm(c) ≤ 192 B₁² G(c) + 36 B₀² H(c).
```

The constants count only the three coordinates, not Fourier modes or
patches. They are convenient, nonsharp bounds. The same module
constructs the actual squared-gap patches and substitutes the estimate
in their angular pressure budget: `4Σ Ecomm` becomes
`768 B₁² ΣG(cᵢ) + 144 B₀² ΣH(cᵢ)`. The weighted trace, angular tail,
coverage error, and separate collision cost remain present.

`FourierCoordinateDerivatives.lean` proves that these coordinate
energies are genuine finite-polynomial derivative energies: first
derivatives contribute `|2πi|²` and mixed second derivatives contribute
`|2πi|⁴` in Parseval. The second-derivative cost is not supplied by the
previous first-gradient theorem. The Gaussian construction above now gives
quantitative spatial patch derivative control, and the Fourier projection
construction transfers that control to finite approximants. The charged
pressure replacement is proved in `LocalGaussianPressureBudget.lean`.
Bounds for `B₀,B₁` along the actual solution remain open, as does
uniformity in the pressure truncation, gap cutoff, and time.
`PressureEllipticBudgetAudit.lean` checks the identities, derivative
normalization, complex cutoff, and nonzero-to-zero output regressions.

`PressureTiltDatum.lean`, `PressureTiltOrigin.lean`, and
`PressureTiltAlignment.lean` supply a physical obstruction to a
pointwise-alignment-only pressure closure. On the unit torus, the finite
Fourier coefficients describe the real mean-zero divergence-free datum

```text
u = (2 sin(2πz) + ε(sin(4πy) − 2 sin(2πy)),
     2 sin(2πx), 2 sin(2πy)).
```

At the origin its actual strain and full spatial curl are independent of
`ε`: `S = 2π [[0,1,1],[1,0,1],[1,1,0]]` and `ω = 4π(1,1,1)`.
The top eigenvalue is `4π`, the top gap is `6π`, and both spectral residual
and defect vanish. Nevertheless the Hessian of the pressure determined
by this same velocity is `(48π²ε/5) diag(1,−1,0)`. With `e` the unit top
eigenvector, the checked identity is

```text
||P⊥ Hess(p) e||² = (1536/25) π⁴ ε².
```

For every scalar majorant `F` with `F(0)=0`, the universal pointwise bound
`||P⊥ Hess(p) e|| ≤ F(D)` therefore fails on this family. This is not a
blowup construction or a refutation of a nonlocal/time-integrated budget.
The static obstruction alone does not assert a nonzero total material
source; the actual evolution is treated separately below.
The checked anisotropy estimate remains valid: its mixed term contains
`||m||` as well as the tilt, so it still vanishes at exact alignment.

`FourierPressurePairSum.lean` evaluates the pressure from its ordered input
pairs; `FourierFiniteSupport.lean` identifies full-series reconstruction,
ordinary coordinate derivatives, strain and curl with finite formulas.
The pressure computation also uses the infinite-pressure operator and
its ordinary spatial Hessian. No independently assigned pressure matrix,
truncated vorticity receiver, or external forcing is used. All Fourier
moments of the datum are summable. `PressureTiltDatumAudit.lean` audits
the dependencies and checks both zero and nonzero perturbations.

`PressureTiltTangent.lean` and `PressureTiltResidualRate.lean` compute the
ordinary gradient of the actual infinite Navier–Stokes right-hand side,
including convection, its determined pressure and viscosity. For the
spectral residual `z = (λ I − S)ω`, its initial rate is

```text
z'(0+) = (64π³ε/5) (3 − 5πν, −3 − 5πν, 10πν),
z'(0+)₁ − z'(0+)₂ = 384π³ε/5,
||z'(0+)||² = (24576/25) π⁶ε² (25π²ν² + 3).
```

`PressureTiltEvolution.exists_local_defect_growth` attaches the computation
to an actual local infinite Fourier solution: for every `ν > 0` and `ε ≠ 0`,
the alignment defect at the fixed spatial origin is zero initially and
strictly positive for all sufficiently small positive times. The initial
velocity at the origin is zero. The checked conclusion concerns the fixed
point; its material-trajectory strengthening is stated below. No second
time derivative is assumed.
Neither viscosity nor the other terms in the full right-hand side erase
the computed first-order residual response.

The construction uses `FourierFiniteJets.lean` to supply continuous
coordinate jets of every order, and `PressureTiltLocalSolution.lean` to
instantiate the physical local-solution constructor. `EndpointDerivative.lean`
specializes mathlib's derivative-extension theorem, while
`LocalInitialGradient.lean` and `LocalInitialSpectral.lean` prove the initial
right derivatives from the interior equation and the common third-moment
envelope. `SpectralEigenvalueWithin.lean` gives the one-sided top-eigenvalue
derivative without a differentiable choice of eigenvector.
`PressureTiltEvolutionAudit.lean` checks all new dependencies and the
zero/nonzero-perturbation cases.

This excludes automatic persistence of pointwise perfect alignment, not
global regularity or a spatially nonlocal, time-integrated estimate.
Misalignment can be generated even while the solution remains regular.
Uniform control of its accumulated cost is still the central open step.

`MaterialInitialGradient.lean` extends the physical material gradient
equation to the initial endpoint using closed-interval continuity of
the actual gradient, pressure Hessian and viscous term. At a stagnation
point its initial rate equals the full Eulerian Navier–Stokes rate.
`PressureTiltMaterialEvolution.lean` then constructs the particle starting
at the origin on the same local existence interval, with its ordinary
trajectory equation on the closed interval. On this particle the initial
spectral residual rate is again the nonzero vector computed above, and
the alignment defect becomes strictly positive immediately afterwards.

The sharper theorem
`PressureTiltQuadraticGrowth.exists_material_quadratic_growth` proves

```text
D(t, X(t)) / t² → (4096/25) π⁵ ε² (25π²ν² + 3)  as t → 0+.
```

The coefficient is strictly positive for every `ε ≠ 0`, `ν > 0`.
`SpectralDefectAsymptotics.lean` supplies the reusable mechanism: when the
two transverse strain eigenvalues coincide initially, the lower gap and
spectral width bounds squeeze the quadratic defect coefficient to the
squared residual rate divided by the initial gap. Continuity and a first
right derivative suffice; no second derivative is assumed or claimed.
`PressureTiltMaterialAudit.lean` checks the dependency chain and the
constructed-solution-and-trajectory statement.

Following the fluid therefore does not restore automatic persistence of
perfect alignment. This remains a regular local solution, not a blowup
construction. A closing budget must accommodate this generated defect.

`SpectralSourceCommutatorTests.lean` checks a commuting source on the
simple-top branch and constructs a commuting rank-one source with
anisotropy one at zero strain. This rules out deleting the positive-gap
condition from that branch, not a dynamically constrained NS estimate.
`LocalSourceCommutatorAudit.lean` audits the new and strengthened results.

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

### Signed bottom-sector balance and explicit damping loss

`Analysis/OrthogonalProjectionParabolic.lean` gives the replacement for
projected-gradient-only absorption. `LocalBottomParabolicSectors.lean`
proves symmetry of the actual second spatial projector derivatives and W,
then instantiates the signed identity. With the preceding notation, write

```text
a = Pω, b = Qω, cⱼ = P∂ⱼω, dⱼ = Q∂ⱼω, Pⱼ = ∂ⱼP,
A = Σⱼ ||Pⱼa||², C = Σⱼ ||cⱼ + Pⱼb||², T = Σⱼ <dⱼ,Pⱼa>.

<ω,Wω> - 2ν Σⱼ ||cⱼ||² - 4ν Σⱼ <∂ⱼω,Pⱼω>
  = 2<a,Wb> + 2νA - 4νT - 2νC.

(Dᵤ-νΔ)E + 2νC = 2μE + 2<a,(Sfull-Sχ)ω> + 2<a,Wb> + 2νA - 4νT,
E = ||Pω||²,    A ≤ (H/g²)E.
```

The last bound uses the rank-one estimate
`||Pⱼ(Pw)|| ≤ (||∂ⱼS||/g)||Pw||`, avoiding an unnecessary factor from
the full operator norm of Pⱼ. The complementary-gradient term T stays
signed; completing the square does not make it disappear.

`LocalBottomSectorBudget.lean` combines this identity with the actual
parabolic coupling estimate, trace-free strain, and Young's inequality:

```text
Koff = ||QR₀P||/g + 4νH/g²,
(Dᵤ-νΔ)E + 2νC + (g - 2νH/g²)E
  ≤ 2<a,(Sfull-Sχ)ω> + (3 Koff²/g)||b||² - 4νT.
```

In particular, `4νH ≤ g³` implies `g - 2νH/g² ≥ g/2`. This is a
conditional local geometric criterion, not a property proved for all
solutions. The right-hand side is defined from actual fields, not an
assumed source envelope.

The physical-data theorem constructs one local solution from real,
divergence-free, zero-mean periodic data with continuous coordinate jets
through order nine. For every admissible finite filter, on each interior
interval and almost everywhere on its positive-bottom-gap branch, it
proves both the exact balance and the damping inequality with the actual
ordinary material derivative of E. The null sets may depend on the filter
and interval. It does not supply a time/scale-uniform bound for the signed
source, control the complement of the geometric criterion, or close BKM
continuation. `LocalBottomSectorAudit.lean` audits all 30 new theorems in
this layer; `Analysis/Tests.lean` includes a nonzero-tangent regression.

### Weighted coupled-sector dissipation

`LocalEnstrophyDiffusion.lean` supplies the actual local full-vorticity
energy derivative, Laplacian, and full-gradient dissipation. Together with
the bottom energy, `LocalWeightedSectorEnergy.lean` constructs, for a
constant weight `0 < θ ≤ 1`,

```text
Φθ = E + θ||b||² = θ||ω||² + (1-θ)E,
θ||ω||² ≤ Φθ ≤ ||ω||².
```

Both its material derivative and its Laplacian are proved for the actual
fields. Put `q = 1-θ`. The generic weighted square completion gives the
nonnegative quantity

```text
Dθ = Σⱼ ||cⱼ + q Pⱼb||²
     + θ Σⱼ ||dⱼ + (q/θ)Pⱼa||²
     + θq Σⱼ ||Pⱼb||².
```

`LocalWeightedSectorBalance.lean` proves the exact signed balance

```text
(Dᵤ-νΔ)Φθ + 2νDθ
  = 2μE + 2θ<b,Sχb> + 2<a+θb,(Sfull-Sχ)ω>
    + q·2<a,Wb> + 2ν(q/θ)A.
```

The complementary-gradient cross term is now paid by two-sector
dissipation, at the explicit cost `2ν(q/θ)A`. It is no longer a separate
source. Using the earlier rank-one and parabolic coupling bounds,
`LocalWeightedSectorBudget.lean` proves

```text
(Dᵤ-νΔ)Φθ + 2νDθ + (g - 2ν(q/θ)H/g²)E
  ≤ 2<a+θb,(Sfull-Sχ)ω> + (2θλmax + 3q²Koff²/g)||b||².
```

The condition `4νqH ≤ θg³` leaves at least `g/2` bottom damping. The
expanding-plane stretching term is not controlled by this condition and
remains on the right. At `θ=1`, the energy and dissipation reduce exactly
to full enstrophy density and its usual gradient square; these endpoint
identities are also checked. Taking `θ` toward zero increases the frame
cost and weakens control of total vorticity.

The physical-data theorem constructs one local solution from the same
order-nine periodic data class as above. For each admissible finite filter
and interior interval, its almost-everywhere positive-gap conclusions
hold for all constant weights in `(0,1]` on a common full-measure set.
The exceptional sets may still depend on the filter and interval. This
does not justify replacing the constant by a space/time-dependent weight
without differentiating that weight, or supply the remaining time- and
scale-uniform source budget. `LocalWeightedSectorAudit.lean` audits all
32 new theorems in this layer.

### Actual spectral-defect diffusion and top curvature

`TopEigenvalueSmoothness.lean` constructs smooth top eigenvalues on the
positive-top-gap branch, including through collisions of the lower two
eigenvalues. A variational local-minimum argument proves that the second
derivative of the top eigenvalue dominates the frozen top-direction
Rayleigh second derivative. `LocalSpatialTopEigenvalue.lean` applies this
to the actual filtered spatial strain and proves

```text
Γ = Δλmax − <e, (ΔSχ)e> ≥ 0,       e = top strain eigenvector.
```

No differentiable eigenvector choice is used. Write `ω` for full vorticity,
`S = Sχ`, `λ = λmax(S)`, `Aδ = (λ+δ)I−S`, `z = (λI−S)ω`, and
`F = (Sfull−S)ω`. For every constant real `δ`, the actual energy is
`Φδ = <ω,Aδω> = D + δ|ω|²`, where `D` is the existing top spectral defect.
`LocalSpectralDefectDiffusion.lean` proves its coordinate second-derivative
and Laplacian product rules. `LocalSpectralDefectBalance.lean` combines
these with the actual frozen material derivative:

```text
(Dᵤ−νΔ)Φδ + |z|² + νΓ|ω|² + 2ν Σⱼ<∂ⱼω,Aδ∂ⱼω>
  = Rδ − 4ν Σⱼ<∂ⱼω,(∂ⱼAδ)ω>,

Rδ = <e,R₀e>|ω|² − <ω,R₀ω> + 2<z,F> + 2δ<ω,Sfullω>.
```

Here `R₀` is the actual nonviscous filtered strain remainder. The explicit
`νΔSχ` and `νΔω` responses have canceled against energy diffusion; the
nonviscous pressure, spin, and subgrid terms have not been discarded.
For `ν ≥ 0` and `δ > 0`, the previously proved regularized gradient
inequality pays the mixed term and gives

```text
(Dᵤ−νΔ)Φδ + |z|² + νΓ|ω|² + νδ Σⱼ|∂ⱼω|²
  ≤ Rδ + (16ν/δ) H|ω|²,            H = Σⱼ||∂ⱼSχ||op².
```

`LocalSpectralDefectControl.lean` constructs one local solution from real,
divergence-free, zero-mean periodic data with continuous coordinate jets
through order nine. The identities and paid estimate hold for every
admissible finite filter, every interior interval, and every point with a
positive top gap. No exceptional set or independent spectral derivative
hypothesis is required on that branch. The construction supplies all
constant regularizations on the same solution; `δ = 0` recovers the
unregularized defect and its exact signed identity, not the paid inequality.

This does not extend the spatial identity through top-eigenvalue collisions,
justify variable regularization without product-rule terms, or bound
`Rδ + (16ν/δ)H|ω|²` uniformly in time and frequency. In particular, the
regularization adds stretching and its gradient price grows as `δ` tends
to zero. `LocalSpectralDefectDiffusionAudit.lean` audits the 24 new theorems.
The energy and material rate reuse `LocalAlignmentTransport.alignmentEnergy`
and `LocalAlignmentForcing.materialRate`. The earlier collision-safe weak
integral estimate in `LocalJointDiffusionBudget.lean` remains available;
the new pointwise identity additionally exposes the favorable curvature
and exact signed nonviscous anisotropy on the simple-top branch.
This layer is a new derivation using mathlib and the existing spectral
energy calculus, not a further port from either external construction.

### Curvature-paid alignment depletion of diffusion

`Analysis/PositiveOperatorKernelCurvature.lean` tests a positive operator
curve on an affine vector curve through a kernel vector. Applied to the
actual spectral gap operator, it gives, for every scalar `c` and vector `v`,

```text
κⱼ c² + 4c<v,(∂ⱼA₀)e> + 2<v,A₀v> ≥ 0,
κⱼ = ∂ⱼ²λmax − <e,(∂ⱼ²Sχ)e>,       Σⱼκⱼ = Γ.
```

`LocalSpectralDiffusionDepletion.lean` uses this inequality with
`c = <e,ω>` and `v = ∂ⱼω`. The aligned curvature pays the aligned mixed
gradient. Writing `m = ω−<e,ω>e`, the remaining estimate is

```text
(Dᵤ−νΔ)Φδ + |z|² + νΓ|m|² + νδ Σⱼ|∂ⱼω|²
  ≤ Rδ + (16ν/δ)H|m|²,                  δ > 0.
```

Thus the gradient price is proportional to squared misalignment, not
full enstrophy. The remaining curvature is also weighted by `|m|²`:
the aligned part was spent in the cancellation and cannot be retained
again as extra damping. The nonlinear source `Rδ` is unchanged.
Both `|m|² ≤ D/g` on `g = topGap(Sχ) > 0` and
`|m|² ≤ Φδ/(g+δ)` are checked. The coherent residual satisfies
`g²|m|² ≤ gD ≤ |z|²`.

`LocalSpectralDiffusionBudget.lean` constructs this depleted estimate on
the same physical local solution, for all admissible filters, positive
top-gap points, and positive constant regularizations. It also proves:
if `32νH ≤ δg²`, half of `|z|²` pays the depleted gradient cost. Neither
this condition nor a global bound for `Rδ` has been proved uniformly.

`SpectralDiffusionIncrementDepletion.lean` provides a separate,
collision-safe finite-increment version. For old/new strains `S,T`,
`c = <eS,w>`, `m = w−c eS`, `B = Aδ(T)−Aδ(S)`, and the nonnegative
supporting remainder `σ = <eS,A₀(T)eS>`, the exact remainder is

```text
Eδ(T,w+v) − Eδ(S,w) − incrementRate
  = <v+c eS,A₀(T)(v+c eS)> + σ|m|² + 2<v,Bm> + δ|v|².
```

Consequently the paid increment cost is `(8/δ)||T−S||op²|m|²`, with
`(δ/2)|v|² + σ|m|²` retained on the left. The aligned case has zero
strain-increment cost. No gap or differentiable eigenvector is required.
A scalar majorant uses `Eε(S,w)/(topGap(S)+ε)` with an independent positive
smoothing parameter `ε`; it is not identified with `δ`.

`LocalSpectralDiffusionDepletionAudit.lean` audits the 20 theorems in this
pointwise layer; the generic attained-curvature regression and aligned
finite-increment specialization test its zero-cost limits.

### Collision-safe weak and spacetime depletion

`SpectralDiffusionWeight.lean` caps the scalar transverse majorant:

```text
Wε(S,ω) = min(|ω|², (D+ε|ω|²)/(g+ε)),       ε > 0.
|ω−<e,ω>e|² ≤ Wε ≤ |ω|².
```

The weight is continuous through top collisions. At `g=0` it equals the
coarse weight; on an aligned eigenline it equals `ε|ω|²/(g+ε)`.
`DepletedLaplacianDiffusion.lean` passes the improved finite-increment
inequality through Haar averaging and simultaneous uniform spatial
second differences. Approximation errors still use full vorticity, but
vanish before the final estimate. No selected eigenvector is integrated.

`LocalDepletedDiffusionBudget.lean` discharges those consistency hypotheses
for the actual finite-filter strain and full, untruncated vorticity.
`LocalizedDiffusionIncrement.lean` and `LocalizedLaplacianDiffusion.lean`
retain the actual first-derivative norms under the weak-limit integral.
The diffusion cost is `(16ν/δ)·H·Wε`, where
`H(x)=Σⱼ||∂ⱼSχ(x)||op²`. Writing `Lχ = strainGradientAmplitude`, the
global bound `H≤3Lχ²` is used for dominated convergence only.
The regularized energy uses `δ`, while the diffusion
weight and nonlinear anisotropy envelope use independent parameters
`ε` and `η`. `LocalDepletedDiffusionEnergy.lean` integrates this estimate
on the constructed local solution, including both time endpoints.

`SpectralDiffusionWeightLimit.lean` and `LocalDiffusionWeightLimit.lean`
remove the diffusion-weight smoothing by dominated convergence in space
and time. They prove measurability and integrability of the limit without
assuming continuity across collisions:

```text
W₀(S,ω) = min(|ω|²,D/g)  if g>0;  |ω|² if g=0.
```

`LocalLimitingDiffusionEnergy.lean` also reuses the previously proved
nonlinear-source limit to remove `η`. One physical local solution then
satisfies, for every admissible finite filter and every fixed `δ>0`,

```text
mean Φδ(t) + ∫₀ᵗ∫ |z|²
  ≤ mean Φδ(0) + ∫₀ᵗ∫ (16ν/δ)·H·W₀ + ∫₀ᵗ∫ Rδ,lim.
```

The diffusion cost vanishes on separated aligned eigenlines and never
exceeds the earlier full-vorticity cost. The limiting nonlinear source
retains pressure/spin/subgrid anisotropy, signed strain mismatch, and
the `2δ<ω,Sfullω>` regularization stretching. Neither auxiliary limit
removes `δ`. This weak estimate discards the extra gradient and curvature
damping; it does not silently retain what was spent or dropped.

`SpectralDiffusionExcess.lean` proves `g²W₀≤|z|²` without a positive-gap
assumption. Define

```text
a = (16ν/δ)H,          X = max(a−g²/2,0)W₀.
aW₀ ≤ |z|²/2 + X,    0 ≤ X ≤ aW₀.
```

`LocalExcessDiffusionEnergy.lean` proves spatial and temporal integrability
of this actual excess, including collisions, and constructs one physical
local solution satisfying, for every admissible filter and fixed `δ>0`,

```text
mean Φδ(t) + (1/2)∫₀ᵗ∫ |z|²
  ≤ mean Φδ(0) + ∫₀ᵗ∫ X + ∫₀ᵗ∫ Rδ,lim.
```

The excess is zero wherever `32νH≤δg²`. At a top collision it is
`a|ω|²`; no collision cost is erased by the split. This spends half the
coherent spectral residual, not previously spent curvature or gradient
damping. Uniform scale/time control of the excess and nonlinear source,
collision-sector payment, and global continuation remain open.
`LocalDepletedDiffusionAudit.lean` and `LocalDiffusionDensityAudit.lean`
audit the weak-limit and actual-data results. The previous coarse APIs
remain available; the existing depleted cost definitions are strengthened
to use the local density.

`SpectralSourceExcess.lean` then spends a further quarter of the full residual
on the complete nonviscous source. With `R` that source, `J=||[Sχ,R]||`,
and `C*` the preceding commutator envelope, the source excess is

```text
Y = min(C*, max(2||R||−g²/8,0)W₀ + 8(J/g²)²|ω|²)   if g>0;
Y = C* = 2||R|| |ω|²                                if g=0.
C* ≤ |z|²/4 + Y,                  0 ≤ Y ≤ C*.
```

The minimum prevents an artificial inverse-gap singularity and preserves
zero excess at exact separated alignment. If `[Sχ,R]=0` and
`16||R||≤g²` with `g>0`, the source excess vanishes. Commutation at a
collision is not sufficient: the checked collision regression retains
nonzero anisotropy and excess.

`LocalSourceExcess.lean` proves spatial and time integrability of this
actual source, including the collision fallback. The source commutator
is formed before taking a norm, retaining the previously proved joint
pressure/subgrid cancellation. `LocalExcessAlignmentEnergy.lean` constructs
one physical solution from arbitrary admissible data for which all
admissible finite filters and fixed positive `δ` satisfy

```text
mean Φδ(t) + (1/4)∫₀ᵗ∫ |z|²
  ≤ mean Φδ(0) + ∫₀ᵗ∫ X
    + ∫₀ᵗ∫ (Y + 2<z,(Sfull−Sχ)ω> + 2δ<ω,Sfullω>).
```

This is an explicit absorption inequality, not a uniform bound on its
right side. The commutator cost, collision sectors, strain mismatch,
energy-regularizer limit and global continuation still require estimates.
`LocalSourceExcessAudit.lean` checks the new declarations and regressions.

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
