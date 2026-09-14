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

### Completion outline: proof obligations, not percentages

The end target is an unconditional arbitrary-data unforced regularity theorem
following the repaired stochastic-Lagrangian/pancake route. The periodic
and Euclidean claims must each match their own admissibility and solution
conditions; a periodic construction does not by itself establish the
Euclidean theorem. Local integrability is not uniform control up to a
possible singular time.

The following is a living dependency outline. **Checked** means the stated
obligation is proved for its actual objects, **partial** means some necessary
components are proved, and **open** means the full obligation is not proved.
The steps are not equally difficult and are not units of elapsed time or
fractions of a completed proof.

| Step | Obligation and completion test | Status and present evidence |
| --- | --- | --- |
| S1. Actual equation and objects | Construct the solution, stochastic/material objects, and frequency decomposition from arbitrary admissible data; derive every evolution identity used later from the actual unforced equation. Track the periodic and Euclidean realizations separately. | **Partial.** The local periodic solution, common-interval material flow, vorticity and strain equations are constructed; see `StochasticLagrangian/LocalMaterialVorticity.lean`, `LocalMaterialStrain.lean`, and `LocalSpectralResidual.lean`. This is not a complete arbitrary-data stochastic/Euclidean realization. |
| S2. Spatial field transfer | Transfer the coherent/misaligned geometry to the actual localized operator fields, retaining uniform kernel constants and the inverse-scale gain through integration and limits. | **Partial.** High-input pressure and the low-input complement are identified; moving-line and divergence decompositions retain their source costs. Common periodic envelopes and actual localized weak derivatives in L² are constructed. `PressureCoherentWeakFieldTransfer.lean` identifies both input-coordinate channels, retaining the uniform ratio²/input-scale² energy gain. `GaussianRootWeakChannelBudget.lean` transfers both patch-square sums to the integrable two-point derivative density without individual input suprema or a patch-count factor. `GaussianRootTwoPointDerivative.lean` bounds that density by actual gap/projector derivatives and Gaussian two-point moments, on a common null set that survives translation. `PressureCoherentRelativeMoment.lean` retains the ratio in every prescribed relative kernel moment and integrates squared field separation with an explicit Lipschitz cost. `GaussianRootTwoPointIntegral.lean` proves integrability of the full Gaussian derivative cost and transfers both actual channel-energy sums to it using one constructed envelope. `GaussianRootIncrementBudget.lean` replaces projector separation by actual vorticity/strain increments inside both integrated channel costs, using constructed adaptive centers. `GaussianRootWeightedIncrement.lean` controls the bare vorticity increment by actual sixth-power-weighted palinstrophy with the relative second-moment gain, and splits the full cost while retaining its two-endpoint projector coefficient. Quantitative control of the derivative-weighted costs, remaining interactions, and time affordability are still required. |
| S3. All scales and sectors | Sum over input scales and pay for the other frequency interactions, angular tails, collision sectors, and adaptive cutoff terms without uncontrolled scale, patch-count, or regularization losses. | **Partial.** `PressureHighInputAction.lean` sums all high-input scales in bilinear operator norm. `GaussianRootHighInputBudget.lean` retains the quarter-geometric tail gain after localization and spatial integration, with explicit vorticity-supremum and patch-gradient costs. `PressureHighInputComplement.lean` identifies the remaining input sector as an exact finite sum. Finite support does not establish a uniform or dynamically affordable bound. The other sectors, scale-critical time control, and regularization limits are open. |
| S4. Dynamical misalignment budget | Prove the signed time-integrated nonlinear estimate from the actual unforced evolution, with bounds that remain finite up to any candidate finite singular time. Construct `MisalignmentStrainBudget`, rather than pass it in as a hypothesis. | **Open; decisive mathematical core.** `LocalExcessAlignmentEnergy.lean` supplies an actual-data absorption inequality with explicit source costs. `LocalVorticityEighthEnergy.lean` derives the exact initial-data eighth-moment identity with both positive dissipation terms and signed stretching, using the same weighted palinstrophy as the increment estimate. `VorticityWeightedStretching.lean` identifies that actual full source as the limit of signed two-point cross-product/radial-difference integrals. `VorticityHighAmplitudeSource.lean` pays the bounded-amplitude part at each finite cutoff with actual weighted dissipation, retaining a signed high-amplitude remainder. `VorticityRegularizedIncrement.lean` supplies a cutoff-uniform increment payment for a constructed smooth-annular Riesz regularization. `VorticityRegularizedSource.lean` now identifies its limit with actual stretching; `VorticityRegularizedPayment.lean` pays its low-amplitude source with a single positive threshold independent of cutoff and field. The signed time-integrated high-amplitude bound remains open. `MisalignmentRefinedPin.lean` proves a conditional reduction, not the required dynamical budget. |
| S5. Vorticity control and continuation | Construct the spatial essential-supremum vorticity integrand, prove its finite-time integral is controlled by the preceding estimates, and apply the continuation theorem to the actual solution. | **Open.** Continuation target surfaces and conditional reductions exist. The current `||omega||_sup² sqrt(G)` spatial cost is not yet a controlled BKM integrand. |
| S6. Unconditional theorem and audit | Assemble the arbitrary-data theorem for each claimed domain; check every hypothesis, forcing/pressure convention, limit, and imported result against the target. Compile and audit the final theorem with no assumed analytic budgets or extra axioms. | **Open.** Local lemma builds and foundational-axiom audits are necessary evidence, not completion of this obligation. |

```text
S1 actual NS objects + S2 spatial transfer
                    |
                    v
             S3 all scales/sectors
                    |
                    v
             S4 dynamical budget       <- decisive open estimate
                    |
                    v
             S5 BKM + continuation
                    |
                    v
             S6 unconditional A/B audit
```

The current S4 attack has checked actual two-point top-gap damping and signed
radial-source evolution. The smooth amplitude variant now has an actual
spatial-mean derivative and signed time-weighted identity, with strain,
relative kernel transport and complete viscous curvature retained together.
Its low complement has the same uniform dissipation payment as the original
split. A checked prescribed-strain example shows why angular decay alone
does not pay the source. The missing result is an initial-data-controlled,
cutoff-uniform upper bound on the joint signed time expression, remaining
finite up to a candidate singular time. The current identities are local
on compact interior intervals; no lifespan-uniform bound is inferred.

The separated part of the retained source now has a cutoff-uniform upper
estimate. For every fixed `r > 0`, `VorticitySeparatedSource.lean` proves
the exact near/far split and

```text
|R_far,N(t)| <= b_r(t) E8(t),
b_r(t) = C_r/2 * (1 + ||omega(t)||_2^2),
integral_0^t b_r <= C_r*t/2 + C_r*||u0||_2^2/(4*nu).
```

The displayed enstrophy is the Fourier kinetic energy of the actual curl;
Parseval supplies the physical-space comparison. The coefficient payment
is proved in `LocalSeparatedSourceBudget.lean` from the actual unforced
energy identity, including time zero. The constant is independent of the
kernel cutoff, amplitude threshold, local Fourier envelope and solution.
It depends on the fixed separation radius. `Analysis/AnnularRieszDecay.lean`,
`UnitTorusSeparatedLattice.lean` and `PeriodicRieszSeparated.lean` construct
the bound from annular Schwartz decay and a summable lattice majorant.
This is a paid **linear growth coefficient**, not an absolute source
budget: `E8` is still unknown. The nearby retained interaction remains
signed and dynamically uncontrolled. Letting `r` shrink requires control
of the resulting radius-dependent cost.

The near increment payment now has an explicit radius gain.
`Analysis/PeriodicRieszNearMoment.lean` proves a cutoff-uniform first
moment bound `C1` and therefore

```text
integral_{|h| < r} |h|^2 ||H_N(h)|| <= r*C1,
nearIncrement(r,N,u) <= 48*r*C1*weightedPalinstrophy(u).
```

`VorticityNearIncrement.lean` absorbs the near complement of any fixed
positive amplitude threshold `L` whenever
`r <= nu/(192*L*(C1+1))`. `LocalNearSourceBudget.lean` combines this
with the separated-source payment: for every fixed `L > 0`, a positive
radius depending only on `nu`, `L` and the fixed kernels gives

```text
source_N <= (nu/2)*G8 + nearSource(r,L,N,u) + b(t)*E8,
integral_0^t b <= C*t/2 + C*initialKineticEnergy/(4*nu).
```

Here the radius is chosen using half the viscosity and the sum of `L`
and the earlier viscosity-dependent threshold, so the two absorption
steps together consume only `nu/2`. The signed near source uses the
existing smooth amplitude weight; it is not a sharp support restriction
to amplitudes above `L`. Constants may grow when `L` increases and the
radius decreases. Neither a time-varying choice based on an unknown
supremum nor a bound uniform as `L` tends to infinity is asserted.
The remaining task is a dynamical estimate on this signed near source.

`TwoShearStretchingJet.lean` and `TwoShearStretchingMean.lean` now test a
zero-source sign law against a self-consistent unforced initial jet. The
smooth, divergence-free, `2*pi`-periodic datum
`u0(x,y,z) = (sin y, 0, sin x)` has initial NS acceleration
`(-nu*sin y, 0, -sin y*cos x - nu*sin x)` with zero pressure. The affine
jet satisfies the full momentum equation at time zero, with its actual
Frechet gradient, curl and Laplacian. The normalized Lebesgue mean `R`
of the physical eighth-moment stretching density satisfies

```text
R(0) = 0,
R'(0) = 125/128 > 0
```

for every viscosity. Thus `R' <= b*R` fails for this initial jet for every
coefficient `b`, even after spatial averaging. The affine path is **not**
asserted to solve NS at positive times, and this is not a counterexample
to a quantitative integrated budget, to the retained near-source estimate,
or to global regularity. The check requires the proposed dynamic argument
to account for additive positive production rather than infer a sign law
from vanishing initial stretching. `TwoShearStretchingAudit.lean` records
the momentum and mean-rate checks and their foundational dependencies.

The actual source also has an unconditional angular payment split.
`VorticityAngularPayment.lean` defines an inverse-distance radial increment
`I_N` and an angular integral `A_N`, using the actual vorticity and the
constructed even kernel `H_N`. With `F3(w) = |w|^3*w` and
`M = max(|w(x)|, |w(x-h)|)`, these are

```text
I_N = integral_h (||H_N(h)||/|h|) integral_x |F3(w(x))-F3(w(x-h))|^2,
A_N = integral_h integral_x |h|*||H_N(h)||*M^6*|w(x) cross w(x-h)|^2.

I_N <= 48*C1*G8,
|source_N| <= (nu/2)*G8 + (24*(C1+1)/nu)*A_N.
```

The coincident-point case is handled separately, and integrability is
proved. Neither a vorticity supremum nor a bound on unweighted kernel
mass enters the constants. `Analysis/SchwartzDyadicDecay.lean` constructs
a rational telescoping majorant for dyadic Schwartz sums;
`AnnularRieszSingularity.lean` and `PeriodicRieszSingularity.lean` use it
to prove the dimension-sharp bound `|h|^3*||H_N(h)|| <= C`, uniformly
in the top cutoff.

`VorticityCoherenceBudget.lean` calibrates this payment against the
**explicit extra hypothesis**

```text
|w(x) cross w(y)| <= K*|x-y|*|w(x)|*|w(y)|.
```

Under this projective Lipschitz condition, `A_N <= 2*K^2*C*E8*Z`.
The resulting actual stretching estimate is
`|stretching| <= (nu/2)*G8 + b*E8`, with `b = C'*K^2*Z/nu`.
`LocalCoherenceBudget.lean` derives, for the actual local unforced
solution with a common `K`,

```text
integral_0^t b <= C'*K^2*initialKineticEnergy/(2*nu^2),
E8(t)/8 + (nu/2)*integral_0^t G8 <= E8(0)/8 + integral_0^t b*E8.
```

These are conditional estimates, not propagation of coherence. A common
global projective Lipschitz bound is not supplied by the energy identity
or by the fact that the initial velocity is smooth. It is a sufficient
calibration condition, not a necessary new hypothesis for the overall
arbitrary-data route. Direct dynamical control of the angular integral,
or a suitable localized high-vorticity estimate, remains required.
`AngularCoherenceAudit.lean` separately checks the unconditional and
conditional statements and their foundational dependencies. S4 remains open.

`Analysis/WeightedCrossProductEvolution.lean` and
`LocalWeightedAngularEvolution.lean` make a smooth version of the angular
cost available for a dynamical attack. The polynomial endpoint energy is

```text
P(a,b) = (|a|^6 + |b|^6)*|a cross b|^2,
A_N <= symmetricAngularIntegral_N <= 2*A_N.
```

The source payment also holds with this symmetric integral. Its endpoint
rate is derived along the actual local material paths, including zeros,
and separates amplitude growth, common strain, strain variation, and the
two viscous endpoint terms. This endpoint identity by itself does not
supply an integrated estimate. The spatial and temporal identities below
retain the transport and viscosity channels, without bounding their sum.

`TraceFreeWeightedAngularRate.lean` retains the spectral gap and the
weighted top defects in this rate. In the common-strain case, put
`D = |a|^4*topDefect(S,a) + |b|^4*topDefect(S,b)`. The strain contribution
satisfies

```text
strainRate + 6*D*|a cross b|^2 <= (10*lambda_max - 2*topGap)*P.
```

For trace-free ordered three-dimensional strain, the displayed growth
coefficient is at least `7*lambda_max`. This is a statement about the
upper-bound coefficient, not a lower bound on every pair's actual rate.
Thus the gap term cannot simply be relabeled as net damping of the
weighted cost. Favorable weighted defects remain on the left.

The explicit test `S = diag(1,0,-1)`, `a = (1,0,0)`, `b = (1,1,0)` has
`P = 9`, `P' = 48`, and squared-angle derivative `-1/2`. Both derivatives
are checked for curves with initial velocities `S*a` and `S*b`.
`WeightedCrossProductTests.lean` therefore refutes the implication from
normalized-angle damping to weighted-angular damping under common strain.
The test is **not** a self-consistent spatial NS solution, a blowup example,
or a refutation of a quantitative integrated budget.
`WeightedAngularEvolutionAudit.lean` checks the source comparison, actual
endpoint dynamics, and the limited scope of the obstruction. S4 is still open.

`Analysis/WeightedCrossProductCurvature.lean` derives the complete second
variation. For the sixth-power amplitude weight, set
`W = |a|^6 + |b|^6`, `c = a cross b`, and `c' = v cross b + a cross w`.
The acceleration-free curvature is

```text
C(a,b;v,w) = W''*|c|^2 + 4*W'*<c,c'> + 2*W*|c'|^2 + 4*W*<c,v cross w>.
```

Here `W'` and `W''` are explicitly constructed polynomial first and second
variations, not unknown rates. `WeightedCrossProductCurvatureTests.lean`
checks `C = -638` at `a = (3,1,0)`, `b = (1,0,0)`, `v = (1,-1,0)`,
`w = 0`, including the derivative of the first-variation formula along
the affine endpoint curve. Thus pointwise convexity is false. This test
does not determine the sign of the integrated curvature of an NS solution.

`LocalWeightedAngularDiffusion.lean` proves, for the actual full Fourier
vorticity, that common spatial translation cancels the total second
derivative. With `K_N(h) = |h|*||H_N(h)||`, its integrated viscosity
contribution is exactly `-nu*Q_N`, where

```text
Q_N = integral_h integral_x K_N(h) * sum_j C(w(x),w(x-h);partial_j w(x),partial_j w(x-h)).
```

All spatial integrability obligations are proved. The kernel stays fixed
under common translation, so no kernel derivative is dropped from this
viscosity calculation.

`LocalWeightedAngularMeanRegularity.lean`,
`LocalWeightedAngularMeanBalance.lean`, and
`LocalWeightedAngularMeanChannels.lean` then prove the actual mean balance.
The finite Fourier kernel representative has exactly the same angular
integral. Its norm and torus distance are treated as locally Lipschitz;
material differentiability is established almost everywhere, including
the correct treatment of their nonsmooth sets. Relative transport remains
the derivative of this kernel weight along the actual velocity difference.
For `A_N = symmetricAngularIntegral_N` and its constructed joint rate,

```text
J_N = integral_(x,y) [materialKernelRate_N*P + K_N*nonviscousPairRate] - nu*Q_N,
integral_a^b A_N(t) dt = (b-a)*A_N(a) + integral_a^b (b-t)*J_N(t) dt.
```

This is an exact signed identity on compact interior intervals of the
actual local solution with its common third-moment Fourier envelope.
Neither a cutoff-uniform bound on `J_N`, a budget up to a candidate
singular time, nor global directional coherence has been proved.
`WeightedAngularMeanAudit.lean` checks these distinctions and the
foundational dependencies. The decisive S4 budget remains open.

### Signed separation and radial kernel geometry

`LocalVorticitySeparation.lean` retains the separation direction in the
scalar triple product. Write `a = omega(x)`, `b = omega(y)`,
`h = x-y` for a difference of real lifts, and `A_x = grad u(x)`.
The actual local unforced equation gives

```text
D = (a cross b) dot h,
r_v = u(x)-u(y)-A_x h,
r_g = (A_y-A_x)b,
D' = (a cross r_g) dot h + (a cross b) dot r_v
     + nu * (Delta a cross b + a cross Delta b) dot h.
```

This is an exact material derivative, including zeros. The common full
velocity gradient cancels because its trace vanishes; it need not be
symmetric. Both remainders are constructed from the same velocity field.
The nonviscous part satisfies

```text
|D'_nonviscous| <= |a| |b| (||A_y-A_x|| |h| + |r_v|).
```

The estimate supplies no uniform bound for either remainder. A real lift
is not a globally smooth shortest displacement on the torus. The tests
also retain an example where `D'=0` but the old weighted cross-product
energy has derivative `48`, so this cancellation is not weighted damping.

`Analysis/ScalarTripleProductEvolution.lean` proves the radial algebra:
for `H = c I + d (h tensor h)` and `F_n(a)=|a|^n a`,

```text
pairedStretch_n(H,a,b) = d * D * (h dot (F_n(a)-F_n(b))).
```

The earlier annular construction uses a chosen smooth bump, whose API
provides evenness but not rotational invariance. It is not treated as a
radial kernel. `Analysis/RadialRieszRegularization.lean` instead constructs
an explicitly radial cutoff by applying a scalar bump to the squared
Euclidean norm. Its compact weights lie in `[0,1]` and tend to one at
every frequency of norm at least one. Its inverse-Fourier scalar potential
is invariant under every linear isometry.
`Analysis/RadialRieszHessian.lean` constructs the Riesz kernel entries and
proves `partial_i partial_j potential_N = -(2*pi)^2 kernel_N(i,j)`.
`Analysis/RadialRieszMoments.lean` reconstructs this family as a finite
sum of dilates of its lowest annulus. Its first and second absolute
spatial moments are bounded by `2` and `4/3` times the respective base
moments, independently of `N` (and with a geometric formula for every
positive integer moment).

`Analysis/RadialHessian.lean` now derives the tensor decomposition from
rotational invariance. For a unit vector `e`, the constructed profile is
`g(r) = realPotential(sqrt(r) * e)`. Away from the origin, its Hessian is
`2 g' I + 4 g'' (h tensor h)`, evaluated at `r = |h|^2`.
`Analysis/RadialRieszTensor.lean` transfers this identity to the actual
Fourier-defined kernel, with the Fourier normalization retained. Its
signed stretching pair therefore contains the scalar triple product.
A checked example gives zero stretching for this constructed kernel
while the two endpoint vorticities have nonzero cross product.

`Analysis/PeriodicRadialRiesz.lean` periodizes this new family. It proves
the regularized Riesz Fourier coefficients, their limit, almost-everywhere
evenness, and cutoff-independent positive spatial moments. The first and
second operator moments are at most `2` and `4/3` times the sums of the
corresponding base entry moments. The periodic operator is not claimed
to be radial in a single torus displacement.

`VorticityRadialQuadratic.lean` identifies its convolution with the full
vorticity through the actual curl Fourier series. `VorticityRadialSource.lean`
proves convergence of the weighted spatial source to actual stretching,
including the eighth-moment alignment functional. This is fixed-snapshot
convergence under a summable first Fourier moment, reality and transversality;
the Fourier majorant is not an a priori bound at a possible singular time.

`VorticityRadialPairing.lean` proves the exact signed image representation:

```text
h_z = z + representative(x-y),  F_n(a) = |a|^n a,
imageDensity_z = d_N(h_z) * ((omega_x cross omega_y) dot h_z)
                 * (h_z dot (F_n(omega_x)-F_n(omega_y))),
source_n,N = (1/2) integral_x integral_y sum_z imageDensity_z.
```

Here `d_N` is the radial coefficient constructed from the profile, not an
assumed scalar kernel. The image series converges absolutely for distinct
endpoints; on the diagonal every contribution vanishes. Exchange uses
almost-everywhere symmetry only under spatial integration. The source at
`n=6` tends to the actual eighth-moment stretching term.

This family has its own proved source identification; no equality with the
previous annular kernel is assumed. Spatial representatives are not smooth
material lifts, and spatial convergence does not permit differentiating the
image sum or interchanging its cutoff limit with time. Amplitude weights,
kernel transport, viscosity and the signed time-integrated budget still
require joint control. `VorticityRadialSourceAudit.lean` checks the new
dependencies; S4, BKM continuation and unconditional A/B remain open.

### Complete signed material image rate

`Analysis/SignedRadialStretchEvolution.lean` differentiates all factors of
the radial source, with `p = 2*(n+1)` (`n=2` for the eighth-moment source):

```text
B = h dot (|a|^p a - |b|^p b),  D = (a cross b) dot h,
Q = k D B,
Q' = k' D B + k D B'_common + k (D'_residual B + D B'_residual).
```

Only the common trace-free contribution to `D'` cancels. The common
amplitude derivative retains both the deformation of `h` and the radial
strain excess at the two endpoints. Common rotations contribute zero to
this amplitude derivative; general trace-free strains need not. A checked
finite-dimensional example has `D'=0`, `B=8`, `B'=24` and
`Q'=8*k'+24*k`. With a fixed scalar coefficient `k=1`, the full signed
density grows at rate `24`. This is not a spatial NS counterexample or an
evaluation of the constructed kernel; it excludes an algebraic inference
from triple-product conservation to full-source damping.

A second test includes the moving homogeneous radial coefficient
`k(h)=-(|h|^2/2)^(-5/2)`. At its initial separation, `k=-1`, `k'=-5/2`,
`D=1`, `D'=0`, `B=-8`, and `B'=-24`. Thus `Q=8` and `Q'=44`:
kernel transport contributes `20` and amplitude growth contributes `24`.
The negative inverse-fifth-power shape alone does not repair pointwise
damping. This remains a finite-dimensional test, not a self-consistent
spatial NS solution or an identification of the cutoff-dependent kernel.

`Analysis/RadialRieszCoefficientEvolution.lean` differentiates the actual
constructed coefficient away from zero separation. If
`k(h)=-(2*pi)^(-2)*4*g''(|h|^2)`, its material derivative is
`-(2*pi)^(-2)*8*g'''(|h|^2)*(h dot h')`. The same rate is proved for
the signed pairing of the Fourier-defined Euclidean tensor.

`LocalRadialImageEvolution.lean` instantiates the full rate with the actual
local unforced solution. It separates kernel transport, common-deformation
amplitude growth, unequal-gradient/velocity remainders and both viscous
endpoints. For a constant image shift `z`,

```text
h_z = z + X-Y,
r_v,z = u(X)-u(Y)-A_X h_z = r_v,0 - A_X z.
```

The image shift is not advected affinely. Freezing an image at a reference
time produces a genuine lattice shift, proved using the kernel of the
torus projection. At that time its density is exactly the previously
constructed periodic image density. No derivative of the discontinuous
canonical representative is used.

`LocalRadialImageIntegral.lean` proves absolute continuity and the signed
time identity for a fixed cutoff and image, on a compact interior interval
with nonzero image separation and the stated local Fourier envelope:

```text
integral (kernel transport + common deformation + remainder + nu*viscosity)
  = Q(end) - Q(start).
```

The identity supplies neither a sign nor a uniform bound on this integral.
These individual-image lemmas do not by themselves justify differentiation
through the infinite image sum, the cutoff limit or the spatial integral.
The fixed-cutoff image-sum transfer is established in the following section.
In particular, local absolute continuity does not bound the signed source
up to a candidate singular time. `RadialImageEvolutionAudit.lean` checks
the dependencies; the decisive S4 estimate and unconditional A/B are open.

### Whole periodic pairing and its signed image-rate series

`Analysis/UnitTorusSchwartzPeriodization.lean` constructs a summable
majorant for translates of an arbitrary Schwartz function on each bounded
set of real lifts. Near lattice points are finite and controlled by the
zeroth seminorm; the tail uses a seminorm of order `d+1` and the convergent
lattice inverse-power series. This works at lattice points as well as
away from them. Applied to the Schwartz derivative, the majorant justifies
termwise differentiation and proves that the lifted sum is continuously
differentiable. The constants depend on the input Schwartz seminorms;
no uniformity over a cutoff-dependent kernel family is inferred.

Changing real lifts only reindexes the lattice sum. Both the value and
derivative depend on the projected torus point, not on a representative.
`Analysis/PeriodicRadialRieszEvolution.lean` assembles the actual tensor as
an operator-valued Schwartz function, identifies its sum with the periodic
tensor at every real lift, and sums its derivative series. The signed
radial rate is identified with the derivative of this actual tensor pairing,
not with a separately assumed radial kernel.

`LocalRadialPeriodicEvolution.lean` gives the full actual-solution identity
at fixed cutoff:

```text
d/dt pairedStretch_N(omega(X), omega(Y))
  = sum_z materialImageRate_N(z, X, Y).
```

The complete signed image-rate series converges absolutely at each
snapshot. All four channels from the preceding section remain inside
each term. Coincident torus endpoints are handled exactly: the vorticities
agree, so every first variation is zero. This does not discard a diagonal
or assume that material paths avoid it. The summed rate is also identified
with `fieldRate`, a well-defined field on the product torus.

`LocalRadialPeriodicIntegral.lean` identifies the spatial integral of this
pairing with the actual regularized source and proves the pathwise identity
on every compact interior interval with the stated local Fourier envelope:

```text
integral_time (sum_z complete_signed_image_rate_z)
  = periodic_pairing(end) - periodic_pairing(start).
```

This is an integral of the image sum, not a claim that time integrals may
be interchanged termwise. It is not a uniform upper bound on the source.
The spatial average and the local cutoff passage are supplied below;
the initial-data-controlled, cutoff-uniform S4 budget remains open.
No equality with the earlier annular kernel family is assumed.
`RadialPeriodicEvolutionAudit.lean` checks the dependencies; BKM continuation
and unconditional arbitrary-data A/B remain open.

### Spatially averaged radial source and local cutoff passage

`LocalRadialMeanRegularity.lean` constructs the signed density and explicit
material rate on the product torus. Continuity of the radial periodization
descends through the product quotient, not through a discontinuous choice
of representatives. Tangent paths identify the actual derivative everywhere
on the compact interior interval, including coincident endpoints. The rate
is exactly half the sum of the complete signed image rates; this image sum
stays inside the spatial integral.

`LocalRadialMeanBalance.lean` applies the generic incompressible transport
theorem to this density. Only the product velocity and its proved divergence
identity are reused from the older annular development. The kernels are not
identified. With `S_N` the actual radial source and `R_N` the spatial mean of
the explicit signed rate, it proves

```text
S_N is absolutely continuous,
d/dt S_N(t) = R_N(t) almost everywhere,
integral_a^b S_N(t) dt
  = (b-a) S_N(a) + integral_a^b (b-t) R_N(t) dt.
```

`RadialSourceLocalBound.lean` uses the contractive radial Fourier weights
to bound `abs(S_N)` by a local Fourier-envelope constant times the actual
eighth moment, uniformly in `N`. `LocalRadialSourceIntegral.lean` uses this
majorant only to justify dominated convergence on a supplied smooth interval:

```text
integral_a^b S_N → integral_a^b actual_L8_stretching,
integral_a^b (b-t) R_N(t) dt
  → integral_a^b actual_L8_stretching - (b-a) actual_L8_stretching(a).
```

These are limits of complete signed integrals, not limits of individual
image rates or a pointwise derivative/cutoff interchange. A concrete sufficient
upper-budget obligation is exposed with its endpoint term intact:

```text
(b-a) S_N(a) + integral_a^b (b-t) R_N(t) dt
  <= (nu/2) integral_a^b weighted_palinstrophy + remainder, for every N.
```

If supplied, this implies the actual L8 energy-plus-half-dissipation bound
on that interval. The budget is an explicit hypothesis, not a constructed
estimate. In particular, the local Fourier majorant is not an initial-data
bound up to a candidate singular time. S4 and unconditional A/B remain open.
`RadialMeanBalanceAudit.lean` checks the declarations, coincident density,
and the necessity of retaining the initial-source term.

### Pancake-plane defects and their actual material evolution

`Analysis/RadialPancakeCoherence.lean` bounds the coherent radial image rate
using both normal components of the endpoint vorticities and the failure of
the image separation to be a strain eigenvector. With `p = 2*(n+1)`,
`F_p(a) = |a|^p a`, `D` the scalar triple product, `r = S h - sigma h`,
and `M_p = |a|^p |<h,a>| + |b|^p |<h,b>|`, the bound is

```text
abs(coherent_rate)
  <= abs(D) * ((abs(k') + abs(k)*(2*abs(sigma) + p*norm(S))) * M_p
               + 2*abs(k)*norm(r)*norm(F_p(a)-F_p(b))).
```

`LocalRadialCoherentBound.lean` constructs every quantity from the actual
fields and image separation. Common rotation cancels in the symmetric
normal action. Exact coplanarity together with an eigen-normal makes this
coherent channel vanish; coplanarity alone does not. The full rate still
contains its signed unequal-gradient, image-velocity, and viscous terms.
No summability or time-integrated bound for the displayed cost is claimed.

`LocalRadialNormalEvolution.lean` follows the actual material lifts. For
`z = <h,omega>` it proves

```text
z' = 2*sigma*z + f,
(z^2)' <= -2*kappa*z^2 + f^2/(2*kappa), if sigma <= -kappa < 0.
```

Here `f` consists explicitly of the strain-normal defect, image-velocity
remainder, unequal endpoint gradient, and viscous Laplacian. It is an
internal remainder, not an external body force. Choosing a more negative
`sigma` changes this remainder; compression is not obtained for free.
The endpoint choice at the reference point removes exactly the unequal
gradient term and no other term. These derivative identities also include
zero vorticity and zero separation without division by their norms.

The same file differentiates the actual signed weighted heights
`|omega|^p z`, whose absolute values sum to `M_p`. Their additional amplitude
rate is retained. Even with a common affine field and an exact eigen-normal,
the weighted height evolves at rate `(2*sigma + p*alpha)` times itself,
where `alpha` is the vorticity Rayleigh quotient of that field.

`Analysis/RadialPancakeCoherenceTests.lean` checks the limitation explicitly:
the symmetric trace-free matrix `diag(1,1,-2)`, normal `(0,0,1)`, and vector
`(4,0,1)` give unweighted height `1` with derivative `-4`, but weighted
height `4913` with derivative `4624` at `p=6`. Thus normal damping does not
imply weighted damping. These are derivatives of explicit finite-dimensional
curves, not a self-consistent spatial NS solution or an NS counterexample.
The decisive obligation remains a joint signed, cutoff-uniform dynamical
budget that also controls amplitude growth and the retained remainders.
`RadialPancakeCoherenceAudit.lean` checks the new declarations and examples.

### Joint radial rate and plane-sensitive viscous curvature

`LocalPairedKernelDiffusion.lean` generalizes the common-translation identity
to any continuous periodic operator kernel. It proves that the spatial
integral of the endpoint Laplacian channel is the negative integral of the
complete signed curvature. Only continuity of the kernel is required: the
common translation fixes the separation, so no kernel derivative occurs.
The older annular identity now uses this generic result as well.

`LocalRadialMeanChannels.lean` applies it to the constructed radial kernel.
The mean material rate is exactly the spatially integrated deformation and
relative transport minus `nu` times the signed curvature. Writing that joint
rate as `J_N`, the actual source satisfies locally

```text
d/dt S_N(t) = J_N(t) almost everywhere,
integral_a^b S_N = (b-a) S_N(a) + integral_a^b (b-t) J_N(t),
integral_a^b (b-t) J_N(t)
  -> integral_a^b actual_L8_stretching - (b-a) actual_L8_stretching(a).
```

The last limit is at the eighth-moment exponent and passes only the complete
signed integral to the cutoff limit. It does not assert separate limits or
upper bounds for the deformation, transport, or curvature terms.

`Analysis/RadialPancakeCurvature.lean` exposes the geometry of that curvature
for each nonzero Euclidean image displacement. The scalar identity component
of the actual tensor cancels. The remaining rank-one component has an exact
formula in the normal pairings of endpoint values and their gradients.
It vanishes when both values and both gradients are tangent to the plane
normal to the image displacement. Tangency of the values alone is not enough.

At equal endpoint values `a`, with `<h,a>=0` and gradient increment `d=v-w`,
the eighth-moment curvature of one image reduces exactly to

```text
2*k*|a|^6 * tripleProduct(d,a,h) * <h,d>.
```

The corresponding bound retains both the transverse cross product and the
normal gradient increment. Equal normal derivative components make it zero;
no Lipschitz bound or smallness of those components has been assumed. The
actual periodic curvature is a convergent sum of these image contributions,
away from coincident endpoints. Each image keeps its own displacement; the
sum stays inside the spatial integral. The joint mean balance itself includes
coincident endpoints and does not use this off-diagonal restriction.

These identities remove kernel differentiation but do not pay the signed
curvature or the full time-integrated stretching budget. In particular,
curvature is not a nonnegative dissipation, and no cutoff-uniform estimate
of the surviving weighted gradient increments has been proved.
`RadialMeanChannelsAudit.lean` checks the generalization, geometry, series,
time balance, and the distinction between value and gradient tangency.

### Solenoidal cancellation before estimating curvature

`Analysis/PeriodicRadialRieszSolenoidal.lean` proves that the complete radial
tensor is even, has zero mean, and annihilates transverse Fourier fields.
The real-part formulation does not require an extra reality assumption.
`LocalRadialSolenoidal.lean` constructs these cancellations for the full
vorticity and each full curl-gradient field. No angular restriction of the
kernel is made: such a restriction need not preserve the multiplier identity.

For continuous periodic `K`, `g`, and `q`, with `K` even, mean-zero, and
annihilating `g`, the reusable theorem in `Analysis/SolenoidalCrossIncrement.lean`
proves the exact identity

```text
integral_x integral_y <cross(g(x)-g(y), q(x)), K(x-y)(g(x)-g(y))>
  = integral_x integral_y <cross(g(x), q(y)-q(x)), K(x-y)(g(x)-g(y))>.
```

Thus a constant background cancels; a variable background leaves an explicit
increment. `Analysis/SignedCrossKernelFreezing.lean` splits the frozen-value
curvature into this isotropic derivative contribution and a separate
amplitude contribution. It also gives the full unequal-endpoint remainder,
whose formula vanishes at equal endpoint values without equating gradients.

`LocalRadialCurvatureChannels.lean` applies the identity with
`g = fullCurlGradient u j` and `q = |omega|^(2*(n+2)) omega`, then proves that
the actual signed curvature source is exactly the sum of the background,
amplitude, and endpoint-mismatch channels, with the spatial half factors
retained. The reduced source is substituted into the actual joint rate.
At the eighth-moment exponent, `n=1` and the background weight is `|omega|^6`.

`Analysis/RadialAmplitudeCurvature.lean` identifies the remaining amplitude
channel in each actual radial image. With `d=v-w`, exponent `p=2*(n+2)`,
and radial coefficient `k`, it is

```text
2*p*k*|a|^(p-2) * <a,d> * tripleProduct(d,a,h) * <h,a>.
```

It vanishes for a tangent endpoint value `<h,a>=0`, without requiring tangent
gradients. The periodic theorem sums these signed terms with their individual
image normals; it does not impose simultaneous tangency to all images.

This does not cancel the full frozen curvature. `RadialSolenoidalAudit.lean`
checks a positive longitudinal rank-one symbol annihilating a transverse
increment while its amplitude contribution is `-48*c`, hence has either
sign. These are algebraic symbol tests, not self-consistent fluid solutions.
No channel has yet been bounded uniformly up to a possible singular time
using only initial data and viscosity. The fixed-time cancellation is also
forcing-insensitive; unforced dynamical control remains a separate obligation.

### Normal vorticity and signed projected dissipation

`Analysis/NormalVorticityEnergy.lean` normalizes the separation rather than
the vorticity: `eta(a,h) = <h,a>/|h|`. Its square does not contain a high
vorticity weight. The derivative requires `h != 0`, but zero vorticity is
allowed. The three coordinate-normal energies sum to `|a|^2`; controlling
all normal components would already control the full vector.

`LocalNormalVorticity.lean` constructs the actual strain quotient
`sigma = <h,S h>/|h|^2` and its orthogonal defect `r = S h - sigma*h`.
Along the actual material lifts it proves

```text
eta' = sigma*eta + F,
F = F_nonviscous + nu*eta(Delta omega,h).
```

The internal forcing retains the strain-normal defect, relative velocity,
unequal-endpoint velocity gradient, and the derivative of `|h|`.
`LocalNormalVorticityIntegral.lean` proves absolute continuity and forcing
integrability on compact interior intervals with nonzero separation. If
the actual `sigma <= 0` there, then `|eta(b)| <= |eta(a)| + integral |F|`.
This reuses the OpenAI-derived dissipative comparison through the existing
absolutely-continuous interface. Neither compression in every image nor
initial-data control of the forcing integral is assumed to follow.

For `p=2*(n+2)` and an image tensor `c*I+k*h tensor h`,
`Analysis/RadialAmplitudeBound.lean` and the actual-image corollary prove

```text
|amplitudeCurvature| <= 2*p*|k|*|h|^2*|omega|^p*|v-w|^2*|eta|.
```

At `n=1`, the vorticity weight is sixth order. This identifies its degree;
it does not bound the two-point gradient cost by the one-point weighted
palinstrophy, or justify an absolute image sum.

`LocalNormalVorticityDiffusion.lean` preserves the viscous sign. For every
fixed separation, periodic integration by parts gives

```text
integral eta(omega,h)*eta(Delta omega,h)
  = -integral sum_j eta(partial_j omega,h)^2.
```

The actual normal-square material derivative is identified along the
material paths. Its common-translation spatial integral equals the
nonviscous material-rate integral minus twice viscosity times this
projected gradient energy. Common translation fixes the separation;
relative-separation transport remains in the nonviscous rate. No claim
that a fixed-separation material-rate integral is itself the time
derivative of a spatial mean is made.

`NormalVorticityAudit.lean` checks these results and an algebraic tilt
example: zero initial normal component and zero normal strain quotient
can still have positive normal derivative. Geometric forcing cannot be
dropped. The signed all-image, all-scale time budget remains open.

The dependencies guide the work, not a rigid chronological schedule:
counterexamples to a proposed S3 or S4 estimate can require revising S2.
Imported fluid-equation results must retain their domain, forcing, and
regularity hypotheses. A genuine route obstruction is a result to record
and use to repair the attack, not a completed regularity proof.

### Endpoint correlation correction and its remaining curvature debt

`Analysis/UnitTorusKernelCorrelation.lean` proves that a separation-only
quadratic average against a fixed vector retains just the operator mean.
The actual periodic radial Riesz tensor has mean zero, so this average
vanishes. A receiver weight instead gives the exact increment identity

```text
integral_y w(y) <a,K(x-y)a>
  = integral_y (w(y)-w(x)) <a,K(x-y)a>.
```

`Analysis/PeriodicRadialCorrelationEnergy.lean` constructs the candidate

```text
C_N(omega) = integral_x integral_y
  |omega(x)|^2 |omega(y)|^4 <omega(x),K_N(x-y)omega(x)>.
```

Each real scalar entry of `K_N` has Fourier multiplier of absolute value at
most one. `Analysis/UnitTorusConvolutionEnergy.lean` proves convolution's
Fourier identity and its L2 contraction from Parseval, without replacing
the signed kernel by its absolute value. Applied to the two quartic
endpoint factors, this proves `|C_N| <= d^2 * integral |omega|^8`, uniformly
in `N`. `LocalOcticCorrelation.lean` applies the construction to full
Fourier vorticity and identifies its energy with the existing eighth
moment. In dimension three, `|epsilon| <= 1/18` implies

```text
E8/2 <= E8 + epsilon*C_N <= 3*E8/2.
```

This is equivalence of energies, not a Lyapunov inequality. The actual
two-endpoint material derivative retains both stretching rates, both
viscous terms, and the kernel derivative driven by relative velocity.

`Analysis/OcticKernelCorrelation.lean` splits the exact common-translation
second variation into the pure endpoint curvatures and the mixed product
of their first variations. `Analysis/PeriodicRadialCorrelationDiffusion.lean`
proves both quartic first variations are bounded by `4*|omega|^3*|v|`.
After signed convolution and summing spatial coordinates, the actual mixed
contribution obeys

```text
|mixedGradientContribution N u| <= 288 * weightedPalinstrophy u.
```

Its identity with the integrated mixed curvature is checked. The pure
curvature is not included in that bound. `OcticCorrelationAudit.lean`
checks a positive rank-one operator whose source curvature is `-42`,
ruling out a positivity-implies-convexity shortcut. This is an algebraic
test, not a self-consistent fluid counterexample.

`LocalOcticDiffusion.lean` now integrates the complete common-translation
second variation. If `P_N` and `M_N` denote the pure and mixed spatial
curvatures, respectively, the endpoint viscosity is exactly `-(P_N+M_N)`.
`LocalOcticMeanBalance.lean` integrates the actual product-torus transport
and proves the full local time identity

```text
C_N(b) - C_N(a) = integral_a^b [A_N - nu*(P_N+M_N)].
```

Here `A_N` is the nonviscous material rate: both endpoint stretching terms
and the kernel derivative driven by relative velocity. It is not just
the rate at a fixed separation.

`LocalOcticCorrectedEnergy.lean` combines this identity with the actual
eighth-moment balance. `LocalOcticEndpointBalance.lean` extends the estimate
to the initial endpoint and constructs its local solution from real,
transverse, zero-mean periodic data with nine continuous coordinate jets.
For `|epsilon| <= 1/576`, it proves

```text
H_N = E8/8 + epsilon*C_N
R_N = stretching + epsilon*(A_N - nu*P_N)

H_N(t) + (nu/2)*integral_0^t G8 <= H_N(0) + integral_0^t R_N,
E8(t)/16 + (nu/2)*integral_0^t G8 <= 3*E8(0)/16 + integral_0^t R_N.
```

Only the mixed curvature has been absorbed. The signed residual `R_N`
is explicitly constructed and locally integrable; its initial-data-only,
cutoff-uniform time budget for arbitrary data is **not proved**. The common
Fourier envelope used for local continuity is not a bound at a maximal
existence time.

`Analysis/OcticCorrelationAmplitudeObstruction.lean` rules out a generic
pointwise pure-curvature payment: for the scalar operator `H=-id`, both
endpoint amplitudes can be at most one, the local weighted-gradient cost
can equal one, and the mixed curvature can vanish while the negative pure
curvature is arbitrarily large. This does not refute an integrated estimate
for the actual periodic kernel and a self-consistent fluid field.
`OcticDiffusionAudit.lean` audits the signed balance and endpoint results.
The arbitrary-data global regularity theorem remains open.

### Exact parallel heat-flow tests of the correction

`ParallelHeatFlow.lean` constructs the full infinite Fourier NS evolution of
`u=(0,0,theta(x,y))`. Every nonlinear convolution interaction vanishes before
summation because the velocity is vertical and the frequencies are horizontal.
Finite, real, zero-mean scalar coefficients supply a solution on every finite
forward interval, with every absolute Fourier moment bounded by its initial
value. Neither the solution nor its common regularity envelope is assumed.
`ParallelHeatCorrelation.lean` applies the actual signed octic balance to this
family, retaining its residual. This explicit globally regular family is an
adversarial test, not a replacement for the arbitrary-data target.

`ParallelHeatWitness.lean` instantiates eleven horizontal sine modes with rapid
frequency 65536. The standalone exact-rational diagnostic
`papers/benxiv/ns_octic_parallel_shear_sanity.py` checks their complementary
trigonometric expansion and evaluates the limiting Riesz-multiplier pairing.
At viscosity one, with `H=E8/8+C/576`, it finds

```text
E8'(0) < 0,           12*G8(0) < H'(0) < 13*G8(0).
```

The sign comparisons are rational, not floating-point tests. The script
independently checks the pure and mixed curvature formulas against
`D+P+M=0`, and the eighth-moment derivative against
`E8'=-8*G8-48*radialDissipation`. These computations are **not Lean proofs**.
They warn against automatic monotonicity of this correction at this coefficient;
they do not rule out all smaller coefficients or a signed time-integrated budget.

`Analysis/UnitTorusPolynomialPairing.lean` proves the exact spatial-pairing
formula for polynomial test factors. `Analysis/PeriodicRadialPolynomialPairing.lean`
then proves convergence for the actual regularized kernels to the finite
limiting multiplier sum, including persistence of strict inequalities for
sufficiently large cutoffs. `FourierPolynomialRealAlgebra.lean` reuses the
existing monoid-algebra evaluation map for collected products and real parts.
`ParallelHeatPolynomial.lean` constructs polynomial coefficients for the actual
spatial curl, its squared norm, and both quartic factors, and proves the spatial
evaluation identities. `ParallelHeatPolynomialPairing.lean` identifies the actual
eighth moment and regularized correlation with finite coefficient sums and proves
the correlation's cutoff limit. The numerical witness's positive slope has
**not yet been certified in Lean**; evaluating and differentiating those sums
is still required for a machine-checked counterexample to monotonicity.
`ParallelHeatAudit.lean` audits the original solution and kernel-pairing declarations.

### Signed residual payment on the parallel-flow family

`ParallelHeatGeometry.lean` reconstructs the actual velocity gradient and curl,
proves that strain annihilates vorticity pointwise, and shows that the complete
nonviscous correlation mean vanishes, including relative kernel transport.
Consequently the residual is exactly `R_N = -epsilon*nu*P_N` on this family.

`LocalOcticSignedBudget.lean` proves, for the actual local solution and its
common third Fourier-moment envelope,

```text
integral_0^t R_N - integral_0^t stretching
  = epsilon*(C_N(t)-C_N(0)) + nu*epsilon*integral_0^t M_N,

|integral_0^t R_N - integral_0^t stretching|
  <= |epsilon|*[9*(E8(t)+E8(0)) + 288*nu*integral_0^t G8].
```

This retains time cancellation. When stretching vanishes, the exact uncorrected
eighth-moment identity pays the right side by `45*|epsilon|*E8(0)`.
`ParallelHeatSignedBudget.lean` supplies that vanishing and the actual solution
from finite horizontal, real, zero-mean initial coefficients, giving

```text
|integral_0^t R_N| <= 45*|epsilon|*E8(0)
```

for every `t >= 0`, every cutoff `N`, every real `epsilon`, and `nu >= 0`.
There is no assumed dynamical budget in this family theorem. The absolute value
is outside the time integral: this does not bound `integral_0^t |R_N|`.
In particular, the instantaneous-growth diagnostic does not refute a signed
integrated budget. For arbitrary flows, stretching and the required uniform
eighth-moment/dissipation payment remain open. `ParallelHeatBudgetAudit.lean`
audits the new geometry, coefficient identities, and budget results.

### Full-field curl/strain cancellation and its weighted defect

`Analysis/WeightedCurlCancellation.lean` proves a periodic flux identity
behind the unweighted strain-vorticity cancellation in
[Evan Miller, Theorem 3.1](https://arxiv.org/html/2407.02691v2#S3).
`LocalWeightedCurlCancellation.lean` supplies the actual full vorticity,
curl, gradients, divergence identities and strain from one infinite Fourier
velocity. Four summable absolute velocity moments justify the spatial
derivatives; there is no finite-support or imposed-strain assumption.
For divergence-free velocity, double curl is identified with the negative
ordinary velocity Laplacian, and the checked identity is

```text
integral <omega, S(-Delta u) omega> = 0.
```

The weight used by the eighth-moment route does not pass through that
cancellation unchanged. The same flux proof gives the exact formula

```text
D = integral |omega|^4 *
      (sum_j omega_j <omega, partial_j omega>) * <omega, curl omega>,

integral |omega|^6 <omega, S(-Delta u) omega> = -6*D.
```

The sum over `j` is half the derivative of squared amplitude along vortex lines.
Its vanishing is a sufficient condition for zero defect, not a property
asserted for arbitrary data. All expressions remain defined at zero vorticity.

The existing full eighth-moment stretching source `S8` is connected without
any new assumption: for every real parameter `kappa`, define

```text
J_kappa = integral |omega|^6 <omega, (S(-Delta u)-kappa*S(u)) omega>.
kappa*S8 = -6*D - J_kappa.
```

Both terms retain their signs. No spectral concentration, helicity bound,
or initial-data-only payment of `D` and `J_kappa` is proved. Choosing a large
`kappa` alone does not help: the definition of `J_kappa` retains the original
stretching. These identities expose a self-consistency cancellation for
the coupled strain/vorticity analysis; they do not close the dynamical
misalignment budget. `WeightedCurlCancellationAudit.lean` checks the
declarations, and algebraic jet tests distinguish the weighted flux rate
from the unweighted one without asserting a periodic counterexample.

### Radial absorption with an explicit helicity remainder

`Analysis/WeightedCurlHelicity.lean` proves that the first-jet helicity
`<a, curl D>` is unchanged when any derivative `D_j` is replaced by
`D_j + b_j*a`. Thus pure amplitude derivatives do not contribute to that
factor. A quantitative Young estimate, including zero vorticity, gives

```text
R8 = integral |omega|^4 * sum_j <omega, partial_j omega>^2,
H10 = integral |omega|^6 * <omega, curl omega>^2,
|D| <= eta*R8 + H10/(4*eta)              (eta > 0).
```

`LocalHelicityAbsorption.lean` applies this estimate to the actual Fourier
fields and the existing eighth-moment balance. For positive viscosity and
constant `kappa > 0`, choosing `eta = nu*kappa/2` proves

```text
E8(t)/8 + nu*integral_0^t G8 + 3*nu*integral_0^t R8
  + (integral_0^t J_kappa)/kappa
  <= E8(0)/8 + 3/(nu*kappa^2)*integral_0^t H10.
```

Half the radial dissipation has paid the longitudinal factor; the full
weighted palinstrophy and the other half remain on the left. The spectral
term remains signed. All local integrability and endpoint continuity are
derived from a common fourth Fourier moment, not supplied as budget
hypotheses. That envelope justifies the calculation and is not a bound
uniform toward a possible singular time.

The remaining dynamical obligation is a useful bound on the combination
`3/(nu*kappa^2)*integral H10 - integral J_kappa/kappa`. Neither term is
proved affordable for arbitrary data. In particular, `H10` has an extra
amplitude weight and must not be identified with `G8` or the kinetic-energy
dissipation. `WeightedCurlHelicityTests.lean` checks the sharp Young constant
on an explicit divergence-free first jet, and `HelicityAbsorptionAudit.lean`
audits the algebra and actual initial-endpoint inequality.

### Longitudinally depleted helicity cost

`Analysis/LongitudinalHelicityBudget.lean` retains the direction of the
amplitude gradient before applying Young's inequality. Write
`g_j = <omega, partial_j omega>`, so `g` is half the gradient of
`|omega|^2`, and define

```text
K10 = integral |omega|^4 * (omega dot g)^2 / |g|^2
        * <omega, curl omega>^2.
```

The quotient is zero at `g = 0`. Its measurability is proved; continuity
at those zeros is not asserted. Pointwise Cauchy--Schwarz proves
`0 <= K10 <= H10`. The sharper absorption is proved directly from the
exact product identity between the longitudinal defect, radial density,
and directional helicity density, not inferred by reducing an old upper
bound. `LocalLongitudinalHelicityBudget.lean` derives spatial and time
integrability from the actual local fields and the `H10` majorant, then proves

```text
E8(t)/8 + nu*integral_0^t G8 + 3*nu*integral_0^t R8
  + (integral_0^t J_kappa)/kappa
  <= E8(0)/8 + 3/(nu*kappa^2)*integral_0^t K10.
```

If vorticity is perpendicular to its amplitude gradient, this helicity
cost vanishes even with nonzero curl helicity. More specifically, if
`g = c*n` for a unit normal `n`, its density is bounded by
`|omega|^4 * <omega,n>^2 * <omega,curl omega>^2`. This identifies a normal
misalignment factor, but the normal-gradient hypothesis is explicit:
membership in a strain eigenplane does not supply it here. Its dynamical
propagation, the weighted payment, and the signed spectral defect remain
open for arbitrary data.

`LongitudinalHelicityBudgetTests.lean` proves strict improvement on a
divergence-free first jet with both nonzero amplitude gradient and nonzero
helicity, and preserves the sharp aligned case. These are algebraic tests,
not global periodic solutions. `LongitudinalHelicityAudit.lean` audits this
geometry and the actual initial-endpoint estimate.

### Constant and adaptive helicity centers

`Analysis/SolenoidalRadialFlux.lean` proves the actual periodic flux identity

```text
integral |omega|^(2*n) * omega dot grad(|omega|^2/2) = 0.
```

Consequently a spatially constant center `rho` can be subtracted before
estimating the signed longitudinal-helicity integral. Define

```text
D = integral |omega|^4 * (omega dot g) * <omega,curl omega>,
K_rho = integral |omega|^4 * (omega dot g)^2 / |g|^2
          * <omega,curl omega - rho*omega>^2.
```

`Analysis/CurlHelicityCentering.lean` proves the pointwise absorption using
an algebraic skew correction that preserves the amplitude derivatives.
`LocalCenteredHelicityBudget.lean` supplies the spatial cancellation and
the actual local-solution inequality

```text
E8(t)/8 + nu*integral_0^t G8 + 3*nu*integral_0^t R8
  + (integral_0^t J_kappa)/kappa
  <= E8(0)/8 + 3/(nu*kappa^2)*integral_0^t K_rho.
```

Here `rho` and positive `kappa` are constant in space and time. The
centering identity is integrated, not pointwise. A poorly chosen center
can increase the nonnegative cost; the tests include this case.

`CurlEigenfieldDefect.lean` relates both costs to the same actual field
`b = curl u - rho*u` at `kappa = rho^2`:

```text
curl b = curl omega - rho*omega,
S(-Delta u) - rho^2*S(u) = S(curl b) + rho*S(b).
```

These are identities for the full ordinary spatial operators, with
incompressibility where required, not hypotheses of spectral coherence.

For a spatially varying center, `LocalVariableHelicityCenter.lean` proves
the extra signed term rather than reusing the constant-center cancellation:

```text
D_rho = integral |omega|^4 * (omega dot g)
          * (<omega,curl omega> - rho(x)*|omega|^2),
Q_rho = integral |omega|^8 * omega dot grad rho,
D = D_rho - Q_rho/8,
kappa*S8 = -6*D_rho + (3/4)*Q_rho - J_kappa.
```

The center `rho_delta = <omega,curl omega>/(delta + |omega|^2)` is
constructed from the actual velocity for every `delta > 0`. Its
continuity and locally Lipschitz spatial lift are proved. Its pointwise
directional cost is exactly the old cost multiplied by
`(delta/(delta + |omega|^2))^2`, hence cannot increase. Its remaining
ordinary spatial derivative is expanded explicitly and still contains
`grad(curl omega)`. No initial-data budget for `Q_rho`, `K_rho`, or their
signed combination with `J_kappa` has been proved. The local Fourier
moments justify the calculus; they do not control a possible singular time.

`CenteredHelicityAudit.lean` audits these declarations and the constant
center's initial-endpoint energy bound. This is not an unconditional
regularity theorem or a proof that general solutions approach curl
eigenfields.

`LocalHelicityCenterEvolution.lean` derives the material derivative of
`rho_delta` along the actual local NS trajectories. The derivative of
`curl omega` is reconstructed from the twice-curled full velocity equation;
its viscous term is exactly `nu * Delta(curl omega)`. The higher-moment
estimates in `VelocityRHSMoments.lean` justify these differentiations, not
a global bound on their output.

`Analysis/RegularizedProjection.lean` proves that `rho_delta` minimizes
`|b - rho*a|^2 + delta*rho^2`, with `a = omega`, `b = curl omega`. The
center's own derivative cancels from the derivative of this minimum.
The actual-solution energy derivative is proved, but its remaining source
has no sign bound. The tests show that the minimized energy is not jointly
convex in `(a,b)`, so diffusion cannot be declared dissipative merely from
this minimization.

`LocalRegularizedHelicityBudget.lean` pays the regularized centered cost:

```text
|<a,b-rho_delta*a>|^2 <= (delta/4)*|b|^2,
centeredDirectionalDensity <= centeredHelicityDensity
  <= (delta/2)*|omega|^6*|grad omega|^2.
```

With fixed `kappa > 0`, `nu > 0`, and `delta = nu^2*kappa^2/3`, the
actual local unforced solution satisfies

```text
E8(t)/8 + (nu/2)*integral_0^t G8 + 3*nu*integral_0^t R8
  + (1/kappa)*integral_0^t (J_kappa - (3/4)*Q_rho_delta)
  <= E8(0)/8.
```

The final integral is signed and has not been bounded below by initial
data. It cannot be dropped. This removes the separate centered-helicity
square from the unpaid costs, not the dynamical regularity obstruction.
`RegularizedHelicityAudit.lean` audits the new estimates, derivatives,
tests, and initial-endpoint inequality.

`CurlVorticitySource.lean` and `LocalHelicitySourceEvolution.lean` now
expand the actual material source. With `A = grad u`, `b = curl omega`,
and `H = omega dot b`, they prove

```text
D_t b = -A*b + F_curl + nu*Delta b,
F_curl = 2*sum_j ((partial_j u dot grad) partial_j u) + grad(Delta p),
D_t H = omega dot F_curl + nu*(Delta omega dot b + omega dot Delta b).
```

The common-gradient pairing cancels because omega is the axial vector
of this same velocity gradient. The pressure term is retained until the
ordinary Poisson and advection-divergence identities are applied.
`SpatialTransportLaplacian.lean`, `SpatialCurlCurl.lean`, and
`SpatialAdvectionDivergence.lean` supply these differential identities
for the reconstructed fields, including `div((u dot grad)u) = trace(A^2)`.

`HelicityAngularSource.lean` combines these terms into the exact angular
source, without a third pressure derivative or division by vorticity:

```text
F_curl = -2*sum_m (grad u_m cross partial_m omega),
omega dot F_curl = 2*sum_m grad u_m dot (omega cross partial_m omega).
```

Here `grad u_m` is a row of the velocity gradient, not a column.
Adding any multiple of omega to each vorticity derivative leaves this
pairing unchanged. Purely parallel derivatives therefore contribute zero,
including at vorticity zeros. The actual material derivative of the
regularized center uses this source while retaining the changing denominator.

For every `eta > 0`, `HelicityAngularBudget.lean` proves the spatial bound

```text
integral |omega|^4 * |omega dot F_curl|
  <= eta*(G8 - R8) + (1/eta)*integral |omega|^4 * |grad u|_F^2.
```

The angular dissipation is exactly `G8 - R8`; the mixed gradient cost on
the right is retained, not assumed bounded by initial data. This estimate
does not control the full derivative of a weighted helicity functional:
the changing weight, viscous pairings, and the signed remainder in the
eighth-moment balance still require estimates. `HelicitySourceTests.lean`
checks source vanishing on the exact parallel heat-flow family and records
that the angular pairing has both signs at the algebraic level.
`HelicitySourceAudit.lean` checks the dependencies. S4 and unconditional
arbitrary-data A/B remain open.

`LocalWeightedDivCurl.lean` and `LocalMixedGradientBudget.lean` now remove
that mixed gradient cost from the angular-source estimate. They first prove
the exact identity for the same real, divergence-free full Fourier velocity:

```text
M4 = E6 - 4*integral |omega|^2 *
       sum_j (omega dot partial_j omega) * ((u dot grad)u)_j,
M4 <= E6 + epsilon*R8 + (4/epsilon)*A2,
A2 = integral |(u dot grad)u|^2,    E6 = integral |omega|^6.
```

The signed integration-by-parts correction is retained. It uses radial
dissipation `R8`, complementary to the preceding angular dissipation
`G8 - R8`. Taking `epsilon = eta^2` gives, for every `eta > 0`,

```text
integral |omega|^4 * |omega dot F_curl|
  <= eta*G8 + E6/eta + 4*A2/eta^3.
```

`LocalAdvectionEnstrophy.lean` constructs the supremum norm `U` of the
actual continuous velocity and proves `A2 <= U^2*integral |omega|^2`,
with the latter integral bounded by the existing Fourier enstrophy.
On the normalized torus it also proves `E6 <= 1 + E8`. These are spatial
estimates, not initial-data bounds for `U` or its time-weighted products.

`LocalHelicityCenterSourceBudget.lean` applies the estimate to the actual
regularized center `rho_delta = (omega dot curl omega)/(delta + |omega|^2)`.
Its material derivative is split exactly into angular forcing, amplitude
feedback, and viscosity. The forcing satisfies

```text
integral |omega|^6 * |(omega dot F_curl)/(delta + |omega|^2)|
  <= eta*G8 + E6/eta + 4*A2/eta^3,    delta > 0.
```

There is no inverse-`delta` constant in this estimate. The feedback and
viscous rates are not discarded or assumed favorable. Controlling them,
the remaining velocity/enstrophy product, and the signed time-integrated
spectral/center remainder is still necessary for S4 and continuation.
`MixedGradientTests.lean` checks `M4 = E6` and zero advection on the exact
parallel heat-flow family, together with its center-source cancellation.
`MixedGradientAudit.lean` audits the declarations and tests.

`LocalHelicityCenterParabolic.lean` now identifies the ordinary Laplacian
inside the actual center's viscous rate. Writing `d = delta + |omega|^2`
and `b = curl omega`, that rate is

```text
Delta rho + sum_j (4*(omega dot partial_j omega)/d)*partial_j rho
          + (2/d)*sum_j (rho*|partial_j omega|^2 - partial_j omega dot partial_j b).
```

Thus the center does not obey a scalar heat equation alone. Its drift,
signed gradient production, angular source, and amplitude feedback are
all retained in the checked material equation.

`Analysis/RegularizedProjectionParabolic.lean` derives the Hessian of the
regularized moving minimum `J = |b - rho*omega|^2 + delta*rho^2`.
For `r = b - rho*omega`, `v = partial_j omega`, and `z = partial_j b`,
the exact correction is

```text
H_j = 2*|z - rho*v|^2 - 2*d*(partial_j rho)^2,
H_j >= -(2/delta)*(r dot v)^2.
```

`LocalHelicityProjectionDiffusion.lean` transfers this to the full Fourier
fields and proves the spatial estimate on the normalized torus:

```text
V = 2*r dot (Delta b - rho*Delta omega) = Delta J - sum_j H_j,
integral V <= (2/delta)*integral sum_j (r dot partial_j omega)^2.
```

The unfavorable bound has no second derivative of `curl omega`, but its
first-derivative product still needs a dynamical budget. The inverse-`delta`
loss is explicit. Scalar sharpness tests rule out a uniform bound for the
bare Hessian, and a divergence-free, curl-compatible algebraic jet has
negative total curvature. That jet is not asserted to be a PDE solution.

`LocalHelicityProjectionEvolution.lean` proves, along the actual unforced
material path, with `S` the strain and `F_curl` the preceding source,

```text
D_t J = -2*r dot S*r - 4*rho*r dot S*omega + 2*r dot F_curl + nu*V.
```

For any scalar `sigma`, the same code isolates the coherent cross-feedback:
writing `tilt = S*omega - sigma*omega`, it uses `r dot omega = delta*rho`
to rewrite `-4*rho*r dot S*omega` as
`-4*delta*rho^2*sigma - 4*rho*r dot tilt`. The first term is favorable
when `sigma >= 0`; the second is bounded by `4*|rho|*|r|*|tilt|`.
Neither small tilt nor a favorable sign of `r dot S*r` is assumed.

The residual-source pairing here is not the already estimated angular
pairing `omega dot F_curl`. No estimate for it, the residual-gradient
product, or the complete signed time remainder is assumed. These results
identify the remaining dynamics; S4 and unconditional A/B remain open.
The material identities use a local fourth Fourier-moment envelope for
the calculus; they do not establish an initial-data bound for that envelope.
`HelicityProjectionAudit.lean` audits this chain and its curvature tests.

`HelicitySourceStrainSplit.lean` separates the same actual source into its
symmetric-gradient and rotation contributions. If `D_m = partial_m omega`
and `S_m` is row `m` of the actual strain matrix, then

```text
F_curl = F_strain + grad(|omega|^2/2),
F_strain = -2*sum_m S_m cross D_m.
```

The generic identity in `Analysis/VorticityJetSource.lean` retains a
`-omega*div(omega)` term before solenoidality is applied. The axial vector
of the actual velocity gradient is identified with the same vorticity;
no independent rotation vector is supplied.

`Analysis/SolenoidalRadialPairing.lean` proves the mixed radial-flux
identity for two continuous differentiable periodic fields. Applying it
to vorticity and curl vorticity, `LocalHelicityRotationFlux.lean` proves

```text
integral |omega|^6 * b dot grad(|omega|^2/2) = 0,
integral |omega|^6 * r dot grad(|omega|^2/2) = Q/8,
Q = centerTransportIntegral(rho_delta, u).
```

The second identity uses the derivative of the actual variable center.
It is not a pointwise cancellation. The code retains the strain-source
combination before taking absolute values and obtains

```text
weightedInviscidRate = weightedStrainRate + Q/4,
signedRemainder = weightedStrainSpectralDefect
                 - 3*weightedInviscidRate + 3*weightedStrainRate.
```

`LocalWeightedProjectionEvolution.lean` supplies the actual material
derivative of `|omega|^6*J`, retaining both the changing weight and viscosity:

```text
D_t(|omega|^6*J) = 6*|omega|^4*(omega dot S*omega)*J
                  + |omega|^6*projectionInviscidRate
                  + nu*(6*|omega|^4*(omega dot Delta omega)*J + |omega|^6*V).
K = integral |omega|^6*J <= 2*G8.
```

The bound for `K` is by dissipation, not by the eighth-moment energy.
Consequently a subtraction of `K` to cancel the transport source does
not by itself provide a coercive corrected energy. The remaining signed
strain terms, weighted diffusion, and time budget remain open.
`VorticityJetSourceTests.lean` checks both signs on curl-compatible
algebraic jets; `HelicityRotationAudit.lean` audits the full new chain.

`Analysis/VorticityStrainProduction.lean` combines the changing sixth-power
weight with the symmetric source before estimating either. Let `P(S)` denote
this combined weighted production, `rho = (omega dot b)/(delta + |omega|^2)`,
`r = b - rho*omega`, and `J = |r|^2 + delta*rho^2`. Curl compatibility gives

```text
P(S) = P(S - sigma*I) - 2*sigma*delta*rho^2*|omega|^6.
```

`LocalCoherentStrainProduction.lean` proves this identity for the actual
strain and vorticity and transfers it to the material equation. The full
shifted strain remains; it is not assumed small. The generic rank-one
normal-strain identity identifies its source as
`-2*c*n cross partial_n(omega)` for `S - sigma*I = c*n tensor n`, retaining
the other normal components in the production formula.

`VorticityStrainProductionTests.lean` checks an expanding-plane-aligned,
trace-free velocity-gradient jet with zero normal vorticity derivative.
For this jet `rho = 0`, `J = 1`, and `P(S) = 6*sigma > 0` when `sigma > 0`.
Thus those instantaneous conditions do not make this weighted functional
nonincreasing. This is a jet-level test, not a constructed NS solution.

`Analysis/WeightedProjectionParabolic.lean` proves the complete weighted
Hessian. Write `a = omega`, `v = partial_j omega`,
`z = partial_j b`, `q = z - rho*v`, and `rho_j = partial_j rho`. Then

```text
C_j = 2*| |a|^3*q + 6*|a|*(a dot v)*r |^2
      + 6*|a|^4*|v|^2*J - 48*|a|^2*(a dot v)^2*J
      + 72*delta*|a|^2*(a dot v)^2*rho^2
      - 2*|a|^6*(delta + |a|^2)*rho_j^2.
```

This completion uses no division by `|a|`. Its lower bound is
`C_j >= -42*|a|^4*|v|^2*J - 2*|a|^6*(delta + |a|^2)*rho_j^2`.
`LocalWeightedProjectionDiffusion.lean` proves for the actual periodic fields

```text
weightedViscousRate = Delta(|omega|^6*J) - sum_j C_j,
integral weightedViscousRate = -integral sum_j C_j,
integral weightedViscousRate
  <= integral (42*|omega|^4*J*|grad omega|^2
               + 2*|omega|^6*(delta + |omega|^2)*|grad rho|^2).
```

The module combines the exact diffusion and coherent-production identities
on the actual material trajectory, retaining rotation and all signed terms.
The spatial integral identities do not yet interchange the time derivative
with the integral of the weighted energy. The local fourth-moment envelope
remains an explicit calculus hypothesis, not an initial-data estimate.

`WeightedProjectionParabolicTests.lean` checks curl-compatible, trace-free
jets with `grad rho = 0` but `sum_j C_j = -30`. Thus even the weighted
curvature is not pointwise nonnegative, and controlling only the center
gradient does not justify discarding the mixed radial cost. This does not
assert a positive spatially integrated viscous rate for an NS solution.
The two displayed diffusion costs still lack a dynamical budget. In
particular, dropping the favorable square is only an upper-bound step,
not a claim that the resulting cost is payable. S4 and unconditional A/B
remain open. `CoherentProjectionAudit.lean` audits this chain and both tests.

### Fixed-band coercivity of the projection correction

`Analysis/QuarticTensorEnergy.lean` reuses the polynomial tensor
`T(a) = |a|^2 a tensor a` and its derivative, proving in every finite
Euclidean dimension

```text
sum_ij T(a)_ij^2 = |a|^8,
sum_ij (DT(a)[v])_ij^2 = 2*|a|^6*|v|^2 + 14*|a|^4*(a dot v)^2.
```

These identities include `a = 0` and have no dimension-count loss.
`QuarticTensorEnergyTests.lean` checks the radial, tangential, and zero-field
cases. `Analysis/UnitTorusPolynomialEnergy.lean` supplies the generic
Parseval multiplier estimate. `FourierPolynomialDifferential.lean` proves
finite-support radius bounds under products and real-part reconstruction,
and the derivative energy estimate with the physical `2*pi` factor.

`FiniteVorticityTensor.lean` constructs the actual tensor of the reconstructed
vorticity. If the velocity coefficients vanish outside a finite set whose
integer frequency vectors have norm at most `R`, this tensor has Fourier
radius at most `4*R`. `FiniteBandProjectionEnergy.lean` proves

```text
integral |grad T(omega)|^2 = 2*G8 + 14*R8,
integral |grad T(omega)|^2 <= (8*pi*R)^2 * E8,
K_delta <= (8*pi*R)^2 * E8,                    delta > 0,

kappa = 48*(8*pi*R)^2 + 1,
delta = nu^2*kappa^2/3,
E8/16 <= E8/8 - (3/kappa)*K_delta <= E8/8,      nu > 0.
```

Here `E8 = integral |omega|^8`, `G8 = integral |omega|^6 |grad omega|^2`,
`R8 = integral |omega|^4 sum_j (omega dot partial_j omega)^2`, and
`K_delta = integral |omega|^6 J` with the regularized projection defect `J`
defined above. The correction uses the same relation between `delta` and
`kappa` as the signed eighth-moment payment, rather than introducing an
independent regularization parameter. No factor counts Fourier modes.

`correctedEnergy_filtered_bounds` applies these size bounds to every
finite-supported multiplier acting on arbitrary velocity coefficients.
It assumes no closed unforced equation for the filtered field. Its actual
subgrid force and curl remain in `LocalFilteredVorticity.lean`.

This repairs coercivity only at a fixed frequency cutoff. A large `kappa`
does not bound the signed strain spectral defect, the correction's evolution,
or transfer between scales. No uniform all-scale time budget follows from
these inequalities. S4 and unconditional A/B remain open.
`FiniteBandProjectionAudit.lean` audits the complete new chain.

### Actual filtered time balance and signed source work

`Analysis/WeightedProjectionVariation.lean` proves the exact first variation
of `W(a,b) = |a|^6 J_delta(a,b)`. With `rho` and `r` as above, its two gradients are

```text
A = 6*|a|^4*J*a - 2*|a|^6*rho*r,
B = 2*|a|^6*r,
DW(a,b)[v,z] = A dot v + B dot z.
```

The time derivative of the minimizing coefficient cancels in this first
variation. Its spatial derivative is still present in `grad B`.
`UnitTorusCurlPairing.lean` proves self-adjointness of curl for actual
continuous periodic derivatives. `UnitTorusProjectionVariation.lean` uses
it to remove the extra curl on an additional vorticity source:

```text
integral DW(omega,curl omega)[f,curl f]
  = integral (A + curl B) dot f.
```

`LocalProjectionSourceWork.lean` constructs this variational gradient from
the actual Fourier field and its spatial jets. For the corrected energy,
the resulting gradient is `H = |omega|^6*omega - (3/kappa)*(A + curl B)`.
This is a signed pairing, not a bound or a claim that the work vanishes.
`WeightedProjectionVariationTests.lean` checks the zero-field response,
opposite radial signs, and the exact nonnegative radial response for
positive regularization.

`FiniteVorticityVariation.lean` derives both vorticity time derivatives from
the actual coefficient equation and differentiates the corrected density.
Write `u_chi = chi*u`, `Pi_P` for sharp output restriction to the finite
support of `chi`, and `N_nu` for the infinite velocity coefficient RHS.
`FilteredProjectionMean.lean` proves the spatial-mean derivative

```text
d/dt (E8(u_chi)/8 - (3/kappa)*K_delta(u_chi))
  = integral H dot curl(Pi_P N_nu(u_chi))
    + integral H dot curl(Pi_P subgridForce(chi,u)).
```

Both resolved and unresolved terms are restricted on their output. The
subgrid term still includes all input frequencies, including both-high
interactions. The filtered field is not treated as a closed Galerkin
solution. The proof of differentiation under the integral uses
`Analysis/CompactMeanContinuousRate.lean` and continuity of the full
solution's actual coefficient RHS; no high-order envelope for the
unfiltered solution is assumed. The local Sobolev bound supplies continuity,
not a global estimate.

`hasDerivAt_normalizedEnergy` identifies this evolution with the
frequency-normalized energy of the preceding section.
`meanCorrectedEnergy_balance` proves its exact initial-time balance,
retaining the signed time integral. Finiteness on a given local interval
does not bound that integral uniformly up to a possible singular time.

The next estimate must control the complete signed work. In particular,
subtracting `3*K_delta/kappa` reverses the sign of its viscous contribution:
the corrected energy receives `+(3*nu/kappa)*integral sum_j C_j`. The
previous lower bound on `C_j` is not an upper bound for this contribution.
No scale-uniform evolution bound or S4 closure follows yet.
`ProjectionMeanAudit.lean` audits the new chain.

### Correct-sign viscous estimate and projected weighted Bernstein bound

`Analysis/WeightedProjectionCurvatureBound.lean` proves, for every positive
`delta` in a real inner-product space,

```text
C_delta(a,b;v,z) <= 70*|a|^4*|b|^2*|v|^2 + 28*|a|^6*|z|^2.
```

There is no inverse regularization, derivative of the minimizing coefficient,
or spatial supremum on the right. The estimate includes `a = 0`.
`LocalProjectionCurvatureBudget.lean` applies it to the actual spatial jets.
With `omega = curl u`, define

```text
D(u) = integral [70*|omega|^4*|curl omega|^2*|grad omega|^2
                + 28*|omega|^6*|grad curl omega|^2].
```

`FilteredProjectionViscousBalance.lean` identifies the viscous coefficients
with the ordinary spatial Laplacian. For the same actual finite-filtered
solution and corrected energy as above, it derives

```text
C'(t) = signed resolved inviscid work + signed subgrid work
        - nu*G8 - 6*nu*R8 + (3*nu/kappa)*integral sum_j C_j,
C'(t) <= signed resolved inviscid work + signed subgrid work
         - nu*G8 - 6*nu*R8 + (3*nu/kappa)*D(u_chi),
                                                   nu >= 0, kappa > 0.
```

The output restrictions remain on both work terms, and the subgrid source
retains all input frequencies. No unfiltered high-order envelope is assumed.
The upper bound repairs the sign issue; it does not pay `D` from `G8`.

For that derivative cost, `Analysis/UnitTorusQuarticSecondEnergy.lean` proves
an integrated scalar coercivity identity. If `v = partial_j f` and
`z = partial_j^2 f` are actual continuous translation derivatives, then

```text
I = integral f^4*v^4,    J = integral f^6*z^2,
L = integral (12*f^2*v^2 + 4*f^3*z)^2,
L = 16*(J-I),           25*I <= 9*J,           J <= (25/256)*L.
```

`ScalarQuarticBernstein.lean` constructs the fourth-power Fourier polynomial,
accounts for its radius `4*R`, and proves

```text
integral f^6*(partial_j^2 f)^2
  <= 25*(2*pi*R)^2 * integral f^6*(partial_j f)^2.
```

`FiniteVorticityProjectedBernstein.lean` constructs the scalar polynomial
`f = e dot omega` from the actual finite-support velocity coefficients and
proves this estimate for every fixed real projection vector `e`. No factor
counts Fourier modes. The projection direction here is spatially constant;
no derivative of an adaptive direction is being suppressed.

The following section completes the vector/mixed-spatial-derivative
transfer and fixed-band absorption of `D`. The signed nonlinear/subgrid
budgets and S4 remain open. The scalar coercivity is not pointwise:
`ProjectionCurvatureBoundTests.lean` checks a
jet where the fourth-power second derivative vanishes while `f^6*z^2 > 0`.
`ProjectionCurvatureAudit.lean` audits the complete new chain.

### Full vector curvature payment and actual viscous absorption

`Analysis/QuadraticProjectionFrame.lean` uses the fixed directions
`d_k = (1,k,k^2)`, `k = 0,...,4`. For positive natural `m,n`, it proves

```text
c_mn*|a|^(2*m)*|z|^(2*n)
  <= sum_k <d_k,a>^(2*m)*<d_k,z>^(2*n)
  <= C_mn*|a|^(2*m)*|z|^(2*n),     c_mn > 0.
```

No union of two planes through the origin contains these five directions.
Compactness on the product of unit spheres gives the uniform lower
constant. `Analysis/UnitTorusProjectionFrameEnergy.lean` transfers scalar
projection estimates to integrals of vector norms.
`FiniteVorticityVectorBernstein.lean` applies this to the actual finite
Fourier vorticity, bounding both `integral |omega|^6*|partial_j^2 omega|^2`
and `integral |omega|^4*|partial_j omega|^4` by universal constants times
`(2*pi*R)^2 * integral |omega|^6*|partial_j omega|^2`.

`Analysis/WeightedMixedDerivative.lean` proves a second integrated
identity. Write `v = partial_j a`, `w = partial_k a`,
`b = partial_j^2 a`, `c = partial_k^2 a`, `h = partial_j partial_k a`.
Subtracting two flux divergences cancels their common third derivative:

```text
integral |a|^6*|h|^2
  <= integral |a|^6*|b|^2 + 7*integral |a|^6*|c|^2
     + 24*integral |a|^4*|v|^4 + 18*integral |a|^4*|w|^4.
```

`FiniteVorticityMixedJets.lean` constructs these jets by Fourier
multipliers and verifies their derivatives and commutations. Summing
the nine mixed bounds, and identifying the gradient of curl vorticity,
`FiniteBandCurvatureCost.lean` proves

```text
exists C_D > 0, forall finite supports P, supported fields u, radii R,
  (forall q in P, |q| <= R) -> D(u) <= C_D*(2*pi*R)^2*G8(u).
```

The constant precedes the field and support quantifiers. There is no
support-cardinality loss, inverse regularization, or supremum gradient.
`FiniteBandProjectionAbsorption.lean` chooses this proved constant and sets

```text
kappa_R = 48*(8*pi*R)^2 + 12*C_D*(2*pi*R)^2 + 1,
delta_R = nu^2*kappa_R^2/3,
C_R(u)  = E8(u)/8 - (3/kappa_R)*K_delta_R(u).
```

For positive viscosity, it proves `E8/16 <= C_R <= E8/8`. The full
viscous contribution is at most `-(3*nu/4)*G8 - 6*nu*R8`.
`FilteredProjectionAbsorption.lean` connects these statements to an
actual infinite solution with a fixed finite filter:

```text
d/dt C_R(u_chi(t)) <= W_R(t) - (3*nu/4)*G8(u_chi(t)) - 6*nu*R8(u_chi(t)),
W_R = signed resolved inviscid work + signed all-input subgrid work.
```

Curvature uses at most a quarter of `nu*G8`, reserving a further half for
the existing regularized coherent-stretch payment without exhausting
`G8`. Every term uses the same `kappa_R` and `delta_R`. Neither work term is
bounded by this theorem. The next obligation is a cutoff-uniform signed
nonlinear budget, including all unresolved inputs and any costs of
changing the cutoff. Fixed-band viscous absorption is not S4 closure or
global regularity.

`FilteredCoherentProjectionBudget.lean` combines the regularized
coherent-stretch inequality with this viscous payment, without changing
the parameters or spending dissipation twice. With `J_R` the existing
signed spectral/center remainder, it proves

```text
d/dt C_R + (nu/4)*G8 + 3*nu*R8 <= Q_R,
Q_R = W_R - stretching(u_chi) - J_R(u_chi)/kappa_R.
```

The module also checks the equivalent expression
`Q_R = W_R + (6/kappa_R)*centeredIntegral`. Thus the reduction is explicit:
renaming the right-hand side has not bounded the nonlinear work. A
cutoff-uniform time-integrated upper bound on this signed quantity is
still required.

`ProjectionFrameEnergyTests.lean` checks why coordinate projections alone
fail and why the mixed estimate cannot be pointwise.
`ProjectionAbsorptionTests.lean` checks the zero-radius case and the
dissipative sign. `ProjectionAbsorptionAudit.lean` audits the chain.

### Actual signed material work and rotation cancellation

`FilteredProjectionNonlinearWork.lean` recombines the resolved and subgrid
terms before removing the auxiliary output restriction. Their sum is
exactly the corrected-gradient pairing with the filtered full inviscid
RHS, independently of the finite set used to record the filter support.
`LocalProjectionTransport.lean` proves that common advection of the
corrected density has zero spatial mean. `SpatialVorticityInviscidRate.lean`
reconstructs both vorticity material rates from the actual momentum RHS.

For `v = filteredVelocity chi u`, let `P_delta(v)` be the weighted
projection material-rate density. `LocalProjectionInviscidWork.lean` and
`FilteredProjectionSourceSplit.lean` prove

```text
W_R = stretching(v) - (3/kappa_R)*integral P_delta_R(v) + SG_R,
SG_R = integral <correctedGradient(v), curl(subgridForce chi u)>.
```

There is no extra output restriction on `SG_R`. Outside the filter support,
the subgrid RHS equals minus the resolved inviscid RHS; the terms cancel
there, rather than vanishing separately. Every spatial Fourier moment
needed for the resolved calculus follows from finite support. The full
input supplies convergence of its nonlinear fibers, not an assumed
high-order uniform bound.

The rotation flux now cancels the center-transport term at exactly their
original coefficients. Write `Z_delta` for the center-transport integral,
`D_kappa` for the signed strain/spectral defect, and `T_delta` for the
integral of amplitude-strain rate plus weighted symmetric-strain
projection rate. `LocalProjectionStrainRate.lean` and
`FilteredProjectionStrainWork.lean` prove

```text
integral P_delta = T_delta + Z_delta/4,
J_delta,kappa    = D_kappa - 3*Z_delta/4,
Q_R             = SG_R - (D_kappa_R(v) + 3*T_delta_R(v))/kappa_R.
```

This identity is substituted into the actual corrected-energy inequality.
No absolute values are taken before cancellation, and neither `Z_delta`
nor the rotation flux is charged again as an independent error.

The sign of the coherent material contribution is also explicit. At each
point, put `a = omega`, `rho = <a,curl omega>/(delta+|a|^2)`,
`r = curl omega - rho*a`, `S = strain`, and let `lambda` be the largest
eigenvalue of the actual `S`. The coherent density is

```text
H_delta = |a|^6 * (4*lambda*|r|^2 + 2*delta*rho^2*lambda
                   + 2*<r,(lambda*I-S)r>) >= 0.
```

`LocalProjectionSpectralRate.lean` constructs this eigenvalue, proves its
continuity and nonnegativity from incompressibility, and supplies the
Rayleigh bound even at eigenvalue collisions. The remaining material
density is exactly the signed normal-alignment rate plus the
symmetric-strain derivative-source rate. Their spatial integrability is
proved. Since the projection correction enters the energy with a minus
sign, discarding `H_delta` gives a valid upper bound on the actual energy
derivative, with no gap or alignment hypothesis.

**Still open:** a cutoff-uniform time-integrated upper bound on the
remaining combination of all-input subgrid work, signed spectral defect,
normal-alignment rate, and strain derivative-source rate. Spatial
continuity, coherent positivity, and rotation cancellation do not supply
that bound or unconditional regularity.

`ProjectionMaterialWorkTests.lean` checks zero inviscid projection work
and zero subgrid work for actual horizontal parallel Fourier flows, and
tests the rotation coefficient. Compatible-jet tests retain both signs
of the pointwise rotation source. `ProjectionMaterialWorkAudit.lean`
checks the dependencies of the new chain.

### Oversized normalization retains stretching: an explicit checked test

`WeightedProjectionRateBound.lean` proves first-variation estimates
independent of every positive regularization parameter. Applied to the
actual fields, `LocalProjectionStrainBound.lean` gives
`abs(T_delta(u)) <= B(u)`, where

```text
B(u) = integral (10*|omega|^6*||S||*|curl omega|^2
                 + 2*|omega|^6*|curl omega|*|strainSource|).
```

This is a finite fixed-field envelope, not a time budget or a bound from
kinetic energy. Keeping that dependence explicit,
`ProjectionCutoffLimit.lean` proves

```text
J_delta,kappa(u) := -(D_kappa(u) + 3*T_delta(u))/kappa,
abs(J_delta,kappa(u) - stretching(u))
  <= (6*abs(longitudinalHelicityIntegral(u)) + 3*B(u))/kappa.
```

Consequently, for the normalization and regularization already used in
the corrected energy,

```text
J_delta_R,kappa_R(u) --> stretching(u),
correctedEnergy(nu,R,u) --> meanEnergy(u)/8
```

as `R` grows, with `u` fixed. Increasing normalization does not by itself
deplete the original stretching.

This conclusion is also proved for the actual `signedWorkRemainder`,
not only an auxiliary expression. `FiniteInviscidSupport.lean` constructs
a symmetric finite filter from the input support and its sumset. It fixes
both the input and its instantaneous full inviscid RHS, so its subgrid
force is exactly zero. `ResolvedProjectionCutoffLimit.lean` supplies the
same limit and a radius admitting that filter for every sufficiently
large `R`. No invariant finite-dimensional trajectory is asserted.

`PositiveStretchingSnapshot.lean` and `PositiveStretchingMean.lean`
construct the explicit, real, divergence-free, mean-zero periodic field

```text
u(x,y,z) = (-sin(2*pi*y), 0,
             sin(2*pi*x) + sin(2*pi*(x+y))).
```

Its actual eighth-moment stretching is strictly positive. The proof
reconstructs the gradient and curl from its six Fourier modes, then uses
one positive convolution path to prove positivity of the spatial mean.
`Analysis/UnitTorusPositiveCoefficient.lean` supplies the reusable
coefficientwise positivity and mean-identification lemmas. No numerical
sampling or unverified finite calculation is used.

For this field, every proposed eventual upper bound
`signedWorkRemainder <= C/kappa_R` fails, for every real constant `C`.
This refutes that decaying-in-normalization estimate, **not** a nonzero
cutoff-uniform time budget, the full geometric route, or global
regularity. A successful argument must use actual dynamics or other
structure beyond making the cutoff oversized. The signed spectral,
misalignment, strain-source, and general subgrid time costs remain open.

`ProjectionCutoffLimitTests.lean` checks the zero-field first variation,
the zero-stretching parallel-flow limit, and the positive actual-field
limit with zero resolved subgrid force. `ProjectionCutoffLimitAudit.lean`
audits the new chain.

### Moving scalar normalization: signed cost and a bounded correction

The multiplier in this result is **fixed**; its input is the actual local
infinite Fourier NS solution, not a closed Galerkin trajectory. Only the
normalization `kappa(t)` and its tied regularization
`delta(t) = nu^2*kappa(t)^2/3` vary.

`Analysis/RegularizedProjectionParameter.lean` derives the full chain
rule. With `a = omega`, `b = curl omega`, minimizing coefficient `rho`,
and residual `r = b - rho*a`, the extra signed density is

```text
M = (3*kappa'/kappa^2)*|a|^6*(|r|^2 - delta*rho^2).
```

`MovingProjectionMean.lean` proves the actual spatial-mean derivative
and exact initial-data time balance, including this term. The proof
constructs continuity from finite filtering and the full NS coefficient
equation. It does not assume the mean derivative or a nonlinear budget.
`MovingProjectionBudget.lean` then establishes

```text
C_R' + nu*G8/4 + 3*nu*R8 <= Q_R + integral M.
```

`LocalProjectionScaleMotion.lean` provides two bounds for the extra work.
The coarse one is `abs(integral M) <= (abs(kappa')/kappa)*C_R`.
Keeping the actual support radius `R0` distinct from the larger
normalization radius gives the stronger estimate

```text
abs(integral M) <= c0*abs(kappa')/kappa^2 * C_R,
c0 = 48*(8*pi*R0)^2.
```

For a positive increasing normalization, its coefficient has integral
at most `c0/kappa(initial)`. Starting at the fixed band's radius makes
this bound at most one, uniformly in that initial radius. The reusable
results in `Analysis/ReciprocalScaleCost.lean` prove the inverse-square
integral identity. `Analysis/LogarithmicScaleCost.lean` separately records
why the coarse logarithmic bound is weaker; it is not an obstruction
to the sharper fixed-band estimate.

`MovingProjectionIntegratingFactor.lean` removes this scalar-motion
coefficient from the actual NS inequality. For `psi = exp(c0/kappa)`,

```text
(psi*C_R)' + psi*(nu*G8/4 + 3*nu*R8) <= psi*Q_R.
1 <= psi <= exp(1) whenever c0 <= kappa.
```

The signed remainder has not been paid. In particular, bounded positive
`psi` does not permit replacing the signed integral of `psi*Q_R` by
`exp(1)` times the signed integral of `Q_R`. A moving multiplier would
also contribute its own derivative source, absent from this fixed-filter
calculation. Uniform control of these nonlinear and adaptive-filter
costs remains required for continuation.

`Analysis/RegularizedProjectionParameterTests.lean` checks both signs
of `M` for equal nonzero inputs, and zero contribution for a constant
normalization. These are algebraic sign tests, not NS trajectories.
`MovingProjectionAudit.lean` audits the new declarations.

### Exact normalization threshold and amplitude-free angular curl

`MonochromaticShearProjection.lean`, `MonochromaticShearCoercivity.lean`,
and `MonochromaticShearEvolution.lean` test the corrected energy on
`u = (0, 0, A exp(-nu*lambda*t) sin(2*pi*x))`, with `lambda = (2*pi)^2`.
This is a constructed solution of the full unforced infinite Fourier
equation, real, transverse, and mean zero. Spatial integration by parts gives

```text
K_delta = G8 = R8,       7*G8 = lambda*E8,
C_delta,kappa = ((7*kappa - 24*lambda)/(56*kappa))*E8.
```

For positive amplitude, regularization and normalization, nonnegativity
holds exactly when `7*kappa >= 24*lambda`. Matching `kappa = lambda`
instead gives `C = -17*E8/56 < 0` at every finite time. This excludes
spectral matching for this globally subtracted correction, not the
previously proved large-normalization coercivity theorem or regularity
of the shear. Increasing regularization does not fix this example:
vorticity and its curl are orthogonal.

The same solution has zero stretching and `G8-R8 = 0`, but `K_delta > 0`.
Consequently no finite multiple of angular dissipation controls the full
projection cost, even on this actual unforced family.

`Analysis/AngularCurlDecomposition.lean` constructs a different quantity,
polynomial at vorticity zeros. With `a = omega` and `D_j = partial_j omega`,

```text
J_j = |a|^2 D_j - <a,D_j> a,
H   = curlJet J = |a|^2 curlJet D - grad(|a|^2/2) cross a,
<a,H> = |a|^2 <a,curlJet D>.
```

`LocalAngularCurlBudget.lean` applies this construction to the actual
vorticity and proves `0 <= integral |omega|^2 |H|^2 <= 2*(G8-R8)`.
It also rewrites the exact weighted stretching identity using `H`,
preserving the signed helicity pairing and the spectral defect. The
new cost vanishes on the shear, as checked alongside the strictly
positive old projection cost in `MonochromaticShearTests.lean`.

The new functional has its own evolution and finite-band coercivity
development below. The old projection evolution is not applied to it.

### Actual angular evolution and a retained radial coercivity margin

`LocalVorticityGradientEvolution.lean` differentiates the actual infinite
Fourier NS equation and the moving evaluation point to obtain the material
rate of each vorticity gradient. It separates viscosity as the ordinary
Laplacian of that reconstructed gradient. A common fourth-moment envelope
justifies these local derivatives; it is not a global initial-data budget.

`Analysis/AngularCurlEvolution.lean` differentiates the angular subtraction
and its squared-amplitude weight. `LocalAngularCurlEvolution.lean` applies
that exact first variation to the actual material vorticity and gradient
rates, retaining both inviscid work and the linear viscous contribution.
Removing radial derivatives does not remove amplitude growth: common
amplitude rate `c` contributes exactly `8*c*K_ang` to the density rate.

`FiniteBandAngularEnergy.lean` retains the radial term in the existing
quartic-tensor Bernstein identity:

```text
K_ang + 16*R8 <= (8*pi*R)^2*E8,
C_ang = E8/8 - (3/kappa)*K_ang,
E8/16 + (48/kappa)*R8 <= C_ang <= E8/8
  whenever kappa > 0 and kappa >= 48*(8*pi*R)^2.
```

`FiniteAngularCurlVariation.lean` and `FilteredAngularMean.lean` derive
the actual spatial-mean evolution for any finite output filter. The
variation uses the filtered full RHS. Resolved and subgrid work are
separated exactly, and the signed integral balance reaches the initial
endpoint. This filtered calculation does not assume a closed Galerkin
evolution or an all-scale high-order envelope for the full solution.

`AngularEvolutionTests.lean` checks that the new correction is positive
on the same unforced shear where the spectrally matched old correction
is negative. It does not assert matched-scale coercivity for other fields.

### Angular viscous curvature paid at a universal finite-band threshold

`Analysis/AngularCurlSecondVariation.lean` gives the exact density Hessian
on value/first-jet variations. `FiniteAngularCurlDiffusion.lean` constructs
the spatial variations from one finite Fourier velocity, commutes the
actual higher jets, and proves that the integrated viscous rate is minus
the curvature integral. The Laplacian, not the curvature, integrates away.

`Analysis/AngularCurlCurvatureBound.lean` proves the explicit upper bound

```text
Hess K_ang[(v,E),(v,E)]
  <= 2016*|a|^4*|v|^2*sum_j |D_j|^2 + 672*|a|^6*sum_j |E_j|^2.
```

`FiniteBandAngularDiffusion.lean` sums the actual coordinate variations
and reuses the vector-weighted Bernstein and mixed-jet estimates. There
is one universal constant `C`, chosen before support, velocity and radius,
such that the curvature integral is at most `C*(2*pi*R)^2*G8`. Thus the
viscous part of the subtracted angular correction is absorbable; it is
not necessary, or valid in general, to assume nonnegative curvature.

`FilteredAngularViscousBalance.exists_coercive_dissipative_threshold`
connects this to the actual infinite NS solution with a finite output
filter. For one universal `L > 0`, `kappa > 0` and
`kappa >= L*(2*pi*R)^2` give simultaneously

```text
E8/16 <= C_ang <= E8/8,
d_t C_ang + (nu/2)*G8 + 6*nu*R8 <= resolved inviscid work + subgrid work.
```

The two work terms are the exact angular-energy variations; the subgrid
term retains all original input frequencies. The result neither evolves
a closed Galerkin surrogate nor imposes a global high-order envelope on
the full solution. The curvature tests give `28` and `-92` on compatible
local second jets; they are not global solution counterexamples.

Still required: uniform, initial-data-controlled signed nonlinear and
subgrid work, any moving-filter costs, and the all-scale continuation
argument. Paying viscosity at this normalization does not control the
nonlinear spectral mismatch at the same normalization.

### Signed angular source pairing and the initial-endpoint inequality

`FiniteAngularSourceWork.lean` constructs the angular variational gradient
from the value, first jets and second jets of the same finite Fourier
velocity. Integration by parts transfers a derivative off the varied
vorticity. If `A_ang` denotes this gradient, the corrected gradient is

```text
F_kappa = |omega|^6 omega - (3/kappa)*A_ang,
work_kappa(v) = integral <F_kappa, curl(restrict_P v)>.
```

The incoming velocity source still appears through its curl. This is not
an estimate free of all source derivatives, nor a norm bound for `F_kappa`.
The checked amplitude test is `integral <F_kappa,omega> = 8*C_ang`.

`FilteredAngularSourceBalance.lean` recombines resolved and subgrid work
before taking absolute values. Their sum is

```text
W_kappa,chi(u) = integral <F_kappa(chi*u), curl(chi*RHS_0(u))>.
```

Here `chi*` means the Fourier multiplier, not physical multiplication.
The full nonlinear input is retained, and this expression has no auxiliary
support-set parameter. `FilteredAngularSourceIntegral.lean` proves continuity
using the actual coefficient equation and finite retained jets, then
integrates the dissipative inequality all the way to the initial endpoint.
For one universal `L > 0`, positive `kappa >= L*(2*pi*R)^2` gives

```text
E8(chi*u(t))/16 + integral_0^t [(nu/2)*G8(chi*u) + 6*nu*R8(chi*u)]
  <= E8(chi*u_0)/8 + integral_0^t W_kappa,chi(u).
```

This is not an initial-data bound on the right-hand source integral.
No all-scale high-order envelope is imposed on the full solution.

`AngularInviscidWorkLimit.lean` tests this same source on the existing real,
divergence-free, positive-stretching three-wave field. A constructed filter
retains the complete instantaneous nonlinear RHS, and the work tends to
the positive ordinary stretching as `kappa` tends to infinity. Consequently
an eventual `C/kappa` upper bound is false. Positive work occurs beyond
every radius-squared normalization threshold at an admissible fixed radius.
The test is a snapshot, not a blowup example, and it does not refute a
nonzero signed time-integrated budget.

The decisive remaining task is to control the signed source integral
uniformly in the output scale, at a normalization compatible with the
proved coercivity and viscous absorption. Enlarging the normalization
alone cannot supply that control.

### Angular transport paid from initial kinetic energy

`FiniteAngularTransport.lean` constructs the actual transport deformation
matrix and proves its divergence-free trace from transverse coefficients.
For the angular variational gradient, periodic integration by parts gives
`integral <A_ang, u.grad omega> = deformationIntegral`, with a positive
sign. `FiniteAngularInviscidWork.lean` therefore gives the exact source split

```text
W = stretching - (3/kappa)*angularStrainWork
      + (3/kappa)*deformationIntegral + fullSubgridWork.
```

All resolved quantities use the retained velocity. The full subgrid
pairing includes outputs outside the retained support, where they cancel
the resolved RHS; those outputs cannot be dropped from only one term.

`FiniteAngularTransportBound.lean` bounds the deformation integral by
`36*M*(G8-R8)`, after radial first-jet cancellation.
`FiniteVelocityGradientEnergy.lean` removes the need to assume `M` for a
fixed filter: Cauchy--Schwarz bounds every retained gradient entry by

```text
M = sqrt(E0 * sum_{q in P} (2*pi*|q|*|chi(q)|)^2).
```

Here `E0` is the full initial kinetic energy. The unforced energy identity
supplies the bound throughout the constructed local solution, not just at
one snapshot. `AngularTransportAbsorption.lean` proves that choosing
`nu*kappa >= 432*M`, together with the existing coercivity threshold,
absorbs the transport work and retains

```text
C_ang' + (nu/4)*G8 + 6*nu*R8
  <= stretching - (3/kappa)*angularStrainWork + fullSubgridWork.
```

For positive viscosity both normalization conditions can be met before
choosing the solution time. The physical local-solution corollary constructs
the moment envelope from real, divergence-free, mean-zero data with eight
continuous coordinate derivatives; no gradient or dissipation budget is
assumed in that corollary. The normalization remains cutoff-dependent.

`FiniteAngularRadialWork.lean` identifies the angular gradient's radial
component pointwise. Its transverse remainder pairs only with
`S*omega - c*omega` for any scalar reference rate `c`, without derivatives
of `c` or division by vorticity. The corresponding actual source identity
retains `8*integral c*C_density`, the signed strain defect and full subgrid
work. Exact alignment does not assign a damping sign to the scalar term;
mean coercivity alone does not bound a spatially weighted corrected density.

Still open: a cutoff-uniform time-integrated bound for the remaining
signed strain/subgrid source, moving-filter costs if used, and the passage
to all-scale continuation. `AngularTransportAudit.lean` audits these
declarations separately from the unconditional global-regularity target.

### Integrated strain/subgrid source and exact rotational work

`FiniteAngularTransportContinuity.lean` supplies joint continuity from the
actual finite-output coefficients. `FilteredAngularStrainIntegral.lean`
integrates the transport-paid inequality to the initial endpoint:

```text
E8(t)/16 + integral_0^t [(nu/4)*G8 + 6*nu*R8]
  <= E8(0)/8 + integral_0^t Phi,
Phi = stretching - (3/kappa)*angularStrainWork + fullSubgridWork.
```

All energy and dissipation quantities here use the retained field. The
normalization satisfies both previously stated conditions. A physical-data
corollary constructs the common moment envelope from real, divergence-free,
mean-zero data with eight continuous coordinate derivatives. The signed
integral of `Phi` is still an unpaid dynamical obligation, not a prescribed
integrable budget. Integrability on the constructed local interval does not
give uniform control approaching a possible maximal endpoint.

`FiniteAngularSkewTransport.lean` identifies the antisymmetric velocity
gradient from its actual vorticity. Its deformation contribution equals
negative weighted longitudinal helicity:

```text
deformationIntegral = symmetricDeformationIntegral - angularHelicityIntegral.
```

Combining this with the existing weighted curl identity gives, for nonzero
normalization and the full actual source,

```text
kappa*W = 3*symmetricDeformationIntegral - 3*angularStrainWork
            - 9*angularHelicityIntegral - weightedStrainSpectralDefect
            + kappa*fullSubgridWork.
```

The helicity coefficient is `9`, not a cancellation to zero. Both rotational
signs are checked on divergence-free local first jets, without claiming
global trajectories for those tests. This identity connects the rotational
transport to the already identified spectral defect; it does not pay either
channel or prove a cutoff-uniform bound. `AngularStrainSourceAudit.lean`
audits the new declarations.

### Polarized angular strain work and bounded-source payment

`VorticityTestedStrainKernel.lean` polarizes the actual Biot--Savart kernel
identity. For a continuous test `f` and the actual vorticity `a`, the
finite strain work is one quarter of the exchanged double integral

```text
P(H,a,b,f,g) = <f cross b,H a> + <g cross a,H b>
                + <a cross b,H(f-g)>.
```

Both `a` and `b` are values of the same vorticity field. The finite strain
series converges to its full physical strain, with no assumed infinite
singular-kernel interchange. `AngularStrainTwoPointWork.lean` applies this
to the actual corrected gradient. Writing `T` for its previously defined
transverse angular gradient and `r = |a|^6 - (24/kappa)*|angularCurl|^2`,

```text
F_kappa = r*a - (3/kappa)*T,
Phi = (1/2)*integral_xy <a cross b,H(r(x)*a-r(y)*b)>
        - (3/(4*kappa))*integral_xy P(H,a,b,T(x),T(y))
        + fullSubgridWork.
```

The complete subgrid term is unchanged. The radial coefficient has no
asserted pointwise sign. The transverse pairing cannot in general be
replaced by its increment term alone; the algebraic endpoint tests are
not counterexamples to an actual-solution dynamical budget.

`FiniteAngularSourceBound.lean` supplies a separate uniform estimate.
For the actual finite vorticity of radius `R`, a continuously differentiable
source satisfying

```text
|f| <= M*|omega|,
|partial_j f| <= M*|partial_j omega| + N*|omega|,
M,N >= 0,
kappa >= 1 + (8*pi*R)^2,
```

has corrected work bounded by

```text
|integral <F_kappa,f>| <= (577*M + 360*N)*E8.
```

The constant is independent of the retained support and radius. The
proof uses the signed first-variation identity and quartic tensor
Bernstein, not a vorticity-gradient supremum. `M` and `N` remain explicit
source bounds. The fixed low-strain application below constructs them from
the actual solution. Applying the estimate to the full strain with
uncontrolled coefficients does not close S4.
Neither this estimate nor the polarized identity controls the complete
signed high-strain/subgrid time integral. `AngularTwoPointAudit.lean`
records the new declarations and their foundational dependencies.

### Actual initial-energy low-strain payment and signed residual integral

`FiniteStrainKineticEnergy.lean` constructs bounds for a fixed finite set
`Q` of source modes from the full kinetic energy `E0`. With unit-torus
Fourier frequencies, the explicit constants are

```text
M_Q = sqrt(E0 * sum_{q in Q} [9*(2*pi)*|q|]^2),
N_Q = sqrt(E0 * sum_{q in Q} [9*(2*pi)^2*|q|^2]^2).
```

They bound the reconstructed strain operator and each of its first spatial
derivatives, respectively. Cauchy--Schwarz uses all input kinetic energy;
the input velocity need not have finite support.

`FiniteLowStrainWork.lean` applies these bounds to

```text
v = chi(D)u,
f(x) = S_Q(u,x)*omega(v,x),
|integral <F_kappa(v),f>| <= (577*M_Q + 360*N_Q)*E8(v).
```

For the actual unforced local solution, `E0` is its initial kinetic energy.
The source modes `Q` and retained modes `P` are independent; no inclusion
or assumption that `chi` is one on `Q` is imposed. The coefficient depends
on `Q` and `E0`, not on `P`, the retained radius, the local Sobolev envelope,
or the solution time. The normalization still must satisfy its explicit
cutoff-dependent conditions.

`LowStrainAngularBalance.lean` retains the exact signed remainder

```text
R_kappa,Q,chi(u) = integral <F_kappa(v), (S(v)-S_Q(u))*omega(v)>
                    + fullSubgridWork(kappa,chi,u).
```

Every subgrid output remains present. In particular, the low strain of the
full velocity is not silently replaced by low strain of the retained one.
`LowStrainResidualIntegral.lean` integrates the paid differential balance:
for `a_Q = 16*(577*M_Q + 360*N_Q)` and
`D(v) = (nu/4)*G8(v) + 6*nu*R8(v)`,

```text
exp(-a_Q*t)*E8(v(t))/16 + integral_0^t exp(-a_Q*s)*D(v(s)) ds
  <= E8(v(0))/8 + integral_0^t exp(-a_Q*s)*R_kappa,Q,chi(u(s)) ds.
```

The exponential weight is independent of the retained cutoff. The
physical-data theorem constructs the local solution and common moment
envelope from real, mean-zero, divergence-free periodic data with eight
continuous coordinate derivatives. It assumes no strain or residual
budget. The new scalar integrating-factor lemma preserves the residual's
sign and is reusable independently of Navier--Stokes.

**Still open:** a cutoff-uniform bound on this joint residual integral
approaching a maximal existence endpoint. Local continuity does not supply
that bound, nor the all-scale passage, spatial BKM estimate or unconditional
A/B theorem. `LowStrainPaymentAudit.lean` checks foundational dependencies,
the empty-source case and preservation of a negative scalar residual.

### Adjoint-filtered full nonlinear residual

`VorticityFilterAdjoint.lean` moves the output filter onto a continuous
real test field, using the Fourier coefficients of the actual vorticity.
Only the filter has finite support; no input interaction is removed.
`FullVelocityRHSReality.lean` proves the reality symmetry of the complete
momentum RHS, including viscosity, directly from the coefficient equation.

For `v = chi(D)u`, let `A = chi(D)^* F_kappa(v)`, with the real part
understood when the symbol is complex. `FullAngularSourceAdjoint.lean`
then identifies the complete inviscid angular source as

```text
sourceWork = integral <A, curl(RHS_0(u))>
           = integral <A, S(u)*omega(u) - u.grad(omega(u))>.
```

All fields on the second line are the full fields. A third summable
absolute velocity moment justifies the curl of the full RHS. On the actual
local solution, the preceding joint residual is exactly

```text
R = integral <A, S(u)*omega(u)> - integral <A, u.grad(omega(u))>
      - (3/kappa)*deformationIntegral(v,v) - lowStrainWork(kappa,Q,u,v).
```

The first integral has the polarized two-point strain representation
against the full vorticity and the transferred test `A`, with all three
signed endpoint terms and factor one quarter retained. Its finite-source
Fourier sums converge to the actual integral at each fixed snapshot.
Transport is not silently cancelled: the transferred test is not generally
a radial multiple of the full vorticity.

`FullResidualIntegral.lean` substitutes this expression into the initial-data
integrating-factor inequality without changing any absorption conditions.
Its physical-data corollary constructs the needed third-moment envelope
from nine continuous coordinate derivatives of arbitrary-amplitude real,
mean-zero, divergence-free periodic initial data. This is local regularity
supplied by the constructor, not an assumed global residual bound.

The signed full-field residual still needs a cutoff-uniform dynamical
estimate approaching the existence endpoint. Fixed-snapshot Fourier
convergence does not justify interchanging an infinite source limit with
that endpoint or with a time integral without further domination.
`FullSourceAdjointAudit.lean` checks the dependencies and complex-filter
regressions. Neither this representation nor its integrated form closes
unconditional global regularity.

### Full nonlinear work with exact gradient cancellation

`FullLambVector.lean` derives `curl(RHS_0(u)) = curl(u cross omega)`
from the actual full Fourier field, its derivative jets and incompressibility.
`VorticityFilterDerivatives.lean` constructs derivatives of the finite
adjoint test. `FullLambSourceWork.lean` transfers curl onto that test,
retaining the complete source as `integral <u, omega cross curl(A)>`.

Let `F = |omega|^6 omega`, `H = A - F`, and `phi = (7/8)|omega|^8`.
`FullLambGradientWork.lean` constructs these fields and proves

```text
Z = omega cross curl(A) - grad(phi)
  = -(omega.grad)F + omega cross curl(H)
sourceWork = integral <u,Z>
|sourceWork(t)| <= sqrt(E_initial) * sqrt(integral |Z(t)|^2).
```

The last inequality holds on the actual unforced local solution with its
common summable third-moment envelope and nonnegative viscosity. The
initial kinetic-energy coefficient has no filter-cardinality factor;
the spatial remainder still depends on the filter and angular parameter.
The jet bound is `|Z| <= 7|omega|^6 |(omega.grad)omega| + |omega||curl(H)|`.
For exact layered jets `partial_j omega = n_j v`, the longitudinal term
is bounded by `7|omega|^6 |<omega,n>| |v|`. Neither this layered structure
nor small normal vorticity is assumed for general solutions.

Incompressibility further identifies the longitudinal term as
`|omega|^4 * (sum_j omega_j B_j - 7 trace(B) omega)`, where
`B_j = |omega|^2 partial_j omega - <omega,partial_j omega> omega`
is the existing polynomial angular jet. This removes radial derivatives
exactly, including at zero amplitude, and is wired to the full vorticity
jets. The amplitude weights and nonlocal mismatch remain uncontrolled.

Gradient subtraction is optional, not a monotonicity theorem for norms.
The minimum of the original and gradient-subtracted spatial bounds is
also proved. Tests exhibit a radial layered jet with raw square `49` and
subtracted square `0`, and a zero test with raw square `0` and subtracted
square `49`. These are local algebraic jets, not NS trajectories.

**Still open:** a dynamically affordable bound on the combined remainder
or the signed residual, uniformly in the cutoffs up to a possible finite
endpoint. The new identity alone does not pay either its longitudinal
derivative or its test-mismatch term from the eighth-moment dissipation.
`FullLambWorkAudit.lean` checks the foundational dependencies.

### Longitudinal evolution, curvature creation, and signed diffusion work

Write `q = (omega.grad)omega`. `FullVorticityGradientTransport.lean`
differentiates the full vorticity equation and
`LocalLongitudinalVorticity.lean` proves its material contraction on the
actual solution and trajectory. `LongitudinalVorticityDiffusion.lean`
constructs the ordinary coordinate Laplacian of `q` and proves

```text
(D_t - nu Delta)q = (q.grad)u + Hess(u)[omega,omega]
                   - 2 nu sum_k ((partial_k omega).grad)(partial_k omega).
```

The material statements retain the common fourth Fourier-moment envelope,
actual unforced solution, and actual material-path hypotheses. The spatial
identities are not formal jets with an assumed Laplacian. The connection
to the preceding octic work is
`(omega.grad)(|omega|^6 omega) = D(a -> |a|^6 a)[q]`.

`LongitudinalCurvatureWork.lean` keeps both inviscid terms together in
the spatial pairing with `q`. Incompressibility of vorticity cancels the
explicit velocity-Hessian contribution against the deformation term
after integration by parts. The full spatial material-rate work is

```text
integral <q,D_t q> + nu sum_k integral |partial_k q|^2
  = -integral <(omega.grad)q, S omega>
    + 2 nu sum_k integral <((partial_k omega).grad)q, partial_k omega>.
```

Here `D_t q` denotes the reconstructed material rate already identified
on the actual trajectory. The ordinary Laplacian pairing and both flux
transfers are proved, not assigned signs by convention.

`LongitudinalVorticityTime.lean` now differentiates the actual vorticity
and its gradient in the uniform continuous-field norm, then differentiates
the spatial energy through their bilinear product and the continuous map
into `L²`. `LongitudinalEnergyBalance.lean` identifies Eulerian and material
rates, removes the transport work by incompressibility, and proves the
initial-endpoint time identity. Smooth real transverse mean-zero periodic
data construct a local solution satisfying it; the common fourth Fourier
moment envelope is constructed, not left as an extra initial-data premise.

`LongitudinalJointFlux.lean` combines the two signed fluxes into

```text
J_j = -omega_j S omega + 2 nu sum_k (partial_k omega)_j partial_k omega,
E = integral |q|^2,   D = sum_j integral |partial_j q|^2,
E(t) + 2 nu integral_0^t D = E(0) + 2 integral_0^t integral sum_j <partial_j q,J_j>.
```

Completing the square gives the local inequality

```text
nu E(t) + nu^2 integral_0^t D
  <= nu E(0) + integral_0^t integral sum_j |J_j|^2.
```

For positive viscosity this absorbs half the longitudinal diffusion,
without separating the contributions inside `J`. The joint-flux square
still requires an initial-data-controlled bound. This unweighted identity
does not by itself pay the octic amplitude weights or nonlocal mismatch.
`LongitudinalEnergyAudit.lean` audits these declarations.

`LongitudinalGradientFlux.lean` improves this inequality by projecting
the full tensor `J` onto the closed `L²` space of actual periodic
gradients. This fixed orthogonal projection `P` preserves the exact
source pairing and gives

```text
integral sum_j <partial_j q,J_j> = <grad q,P J>_L2,
nu E(t) + nu^2 integral_0^t D
  <= nu E(0) + integral_0^t ||P J||_L2^2,
||P J||_L2^2 <= integral sum_j |J_j|^2.
```

Continuity of the projected flux and the initial-endpoint inequality
are derived for the actual local NS solution. Smooth real transverse
mean-zero periodic data construct such a solution and the required
common Fourier envelope. The construction does not assume a global
bound on the projected cost.

`LongitudinalShearFlux.lean` proves strict improvement on the exact
unforced heat evolution of `u = (0,0,A sin(2 pi x))`: for positive
viscosity and amplitude, the raw flux square is positive at every
finite time, while `P J = 0`. Each diagonal flux derivative vanishes,
so the raw tensor does no gradient work. Consequently no constant
can bound the raw flux square by the projected one on this family.
This is a test of the energy estimate, not a blowup example.
`LongitudinalGradientFluxAudit.lean` audits the projection, application,
and shear witness. The weighted, initial-data-controlled time budget
and its connection to the full nonlocal test mismatch remain open.

`PeriodicGradientFluxSymbol.lean` identifies this same Hilbert projection
with the explicit output-frequency multiplier

```text
(P(n) J)_j = n_j / |n|^2 * sum_l n_l J_l.
```

The projection acts on the derivative index, not the vector output
index. Its mean mode is zero. Actual translation jets establish the
single-mode identity; continuous linearity then gives convergent `L²`
series for absolutely summable inputs, including pair-indexed series
with repeated output frequencies. No finite cutoff is introduced.
`PeriodicGradientFluxPair.lean` proves the exact coefficient energy

```text
sum_j |(P(n) J)_j|^2 = |sum_j n_j J_j|^2 / |n|^2,
```

including zero frequency. Here coefficient norms are Euclidean; this
identity does not assert a time-integrated energy budget.

`PeriodicGradientFluxProduct.lean` identifies actual continuous tensor
products with absolutely convergent Fourier pair series before applying
the projection. `LongitudinalViscousFluxFourier.lean` specializes this to
`sum_r (partial_r omega)_j partial_r omega` from the same actual velocity.
With `zeta = 2 pi i`, the projected ordered-pair amplitude for coordinate
derivative `r` and output tensor index `j` is exactly

```text
zeta^2 k_r l_r * (k+l)_j / |k+l|^2
  * (l dot omegaHat(k)) * omegaHat(l).
```

The replacement of `(k+l) dot omegaHat(k)` by `l dot omegaHat(k)` uses
the actual curl's incompressibility. The infinite `L²` series is proved
summable under the second absolute velocity Fourier moment. Conjugate
symmetry identifies its sum with the physical projected viscous tensor.
The full projected flux is the inviscid part of the same snapshot plus
`2 nu` times this tensor; no triangle inequality separates their costs.
`LongitudinalFluxFourierAudit.lean` audits these statements.

The cross-frequency factor exposes the relevant directional cancellation.
It does not yet bound the weighted scale sum or its time integral by
initial data; these remain part of the decisive dynamical obligation.

`PeriodicGradientFluxTriple.lean` and
`LongitudinalInviscidFluxFourier.lean` reconstruct the inviscid part of
this same projected flux as an absolutely convergent triple series.
For inputs `k,l,m`, output `n = k+l+m`, and `zeta = 2 pi i`, its
amplitude is the negative of

```text
zeta * n_j / |n|^2 * ((l+m) dot omegaHat(k))
  * (m dot omegaHat(l)) * uHat(m).
```

The contracted formula is proved from the coordinate series, with
finite and infinite sums interchanged using summability. The squared
norm of the signed inviscid triple series plus the viscous pair series
is exactly `projectedFluxSquare`; neither term is bounded separately.

`LongitudinalFluxParity.lean` supplies a snapshot consistency test.
Writing `A(u)` for the inviscid projected tensor and `B(u)` for the
viscous tensor without its `2 nu` factor, the former is odd and the
latter even under `u -> -u`. Consequently

```text
cost(u) + cost(-u) = 2 * (||A(u)||^2 + 4 nu^2 ||B(u)||^2).
```

At least one sign has joint cost at least the sum of the separate
squared costs. This excludes uniform strict destructive interference
at both initial-data signs. It does not exclude dynamical cancellation:
negating an entire viscous NS trajectory need not give a solution.

`PeriodicGradientFluxAngle.lean` proves the sharp angular estimate
for transverse coefficients `k dot a = l dot b = 0`:

```text
|k+l|^2 * sum_j |(P(k+l)(a tensor b))_j|^2
  <= |l|^2 * |a cross b|^2.
```

The factor involving frequency cannot be discarded. The exact family
`k=(N,0,0)`, `l=(-N,1,0)`, `a=(0,N,0)`, `b=(1,N,0)` saturates this
bound; its projected energy is `N^2+N^4` while its cross-product energy
is `N^2`. Lean refutes any universal constant replacing that frequency
ratio. This is a counterexample to a coefficient estimate, not to NS
regularity. The corresponding viscous pair estimate retains its
physical derivative multiplier. `LongitudinalJointFourierAudit.lean`
audits the new declarations. Initial-data-controlled, weighted time
bounds remain open.

`LerayStretchExchange.lean` uses the actual curl relation to combine
both orders of a stretching interaction. For `L_k` the velocity Leray
projection and `w_k = omegaHat(k)`, it proves

```text
zeta (m dot w_l) uHat(m) + zeta (l dot w_m) uHat(l)
  = (L_l - L_m) (w_l cross w_m),
|(L_l - L_m) a| <= 4 |l+m| / max(|l|,|m|) * |a|.
```

The estimate assumes both input frequencies are nonzero; the algebraic
identity also covers zero modes. The projector difference is small
for nearly opposite inputs, since the Leray symbol is even in frequency.

`LongitudinalExchangeFluxFourier.lean` averages the two orders by an
explicit bijection of the infinite triple index. Summability justifies
the exchange; the resulting series is exactly the actual inviscid
projected flux, and enters the same joint cost with the viscous pairs.
Its averaged coefficient `E_j(k,l,m)` satisfies

```text
sum_j |E_j(k,l,m)|^2
  <= 4 (|l+m| / max(|l|,|m|))^2 * |w_k|^2 * |w_l cross w_m|^2.
```

The outer projection is contractive, so no inverse power of the full
output `|k+l+m|` remains in this estimate. Angular smallness and the inner
low-output gain survive together. This paired inviscid estimate does
not contradict the isolated-pair obstruction above. Fourier-coefficient
alignment is not itself spatial vorticity-direction coherence, and the
estimate supplies no time bound on its amplitude factors. Comparable
inner input/output frequencies still have no small frequency ratio.
`LongitudinalExchangeFluxAudit.lean` audits these declarations.

`FourierVorticityPairDynamics.lean` differentiates the actual Fourier
vorticity cross product along the unforced local NS solution. Write
`w_q = omegaHat(q)`, `N_q = curl(infiniteVelocityRHS 0 u)_q`, and
`gamma_q = nu (2 pi)^2 |q|^2`. Then

```text
C_lm = w_l cross w_m,
R_lm = N_l cross w_m + w_l cross N_m,
d_t C_lm = R_lm - (gamma_l + gamma_m) C_lm.
```

The nonlinear source retains every input frequency. It is not an external
body force, a prescribed alignment rate, or a closed Galerkin evolution.
`FourierStretchingInteractionDynamics.lean` also evolves the outer
amplitude, giving exactly the factor from the exchanged coefficient bound:

```text
F_klm = |w_k|^2 |C_lm|^2,
U_k = 2 Re <w_k,N_k>,
V_lm = 2 Re <C_lm,R_lm>,
W_klm = U_k |C_lm|^2 + |w_k|^2 V_lm,
Gamma_klm = gamma_k + gamma_l + gamma_m,
d_t F_klm + 2 Gamma_klm F_klm = W_klm.
```

`FourierStretchingInteractionBudget.lean` proves continuity from the
actual solution's coefficient continuity and full nonlinear fibers, then
integrates to the true initial endpoint. No common high-order Fourier
envelope is added to these per-triple statements. For positive viscosity
and nonzero inner input frequencies, with
`rho = |l+m| / max(|l|,|m|)`, it obtains

```text
F_klm(t) + 2 Gamma_klm integral_0^t F_klm
  = F_klm(0) + integral_0^t W_klm,
integral_0^t sum_j |E_j(k,l,m)|^2
  <= (2 rho^2 / Gamma_klm) * (F_klm(0) + integral_0^t W_klm).
```

This keeps the nonlinear work signed and evolves the outer amplitude
instead of inserting a supremum bound. It does not bound that work by
initial data. It is also a per-triple coefficient estimate: the squared
norm of the full flux includes interactions between different triples
with the same output frequency. The correlated identities below account
for these cross terms; the initial-data-controlled weighted scale sum
and the resulting global continuation budget remain open.
`FourierStretchingInteractionAudit.lean` audits these statements.

`Analysis/ODE/DampedGramEnergy.lean` and its evolution and series modules
give a correlated energy for differently damped Hilbert-space components.
For positive rates `Gamma_i`, finite families satisfy

```text
Q(x) = sum_i sum_j <x_i,x_j> / (Gamma_i+Gamma_j)
     = integral_0^infinity |sum_i exp(-Gamma_i sigma) x_i|^2 >= 0,
x_i' = r_i - Gamma_i x_i,
Q'(t) + |sum_i x_i(t)|^2
  = 2 sum_i sum_j <r_i(t),x_j(t)> / (Gamma_i+Gamma_j).
```

There is no orthogonality hypothesis or mode-count multiplier. A uniform
positive lower bound on the rates and local summable envelopes yield
absolutely convergent infinite Gram pairings. Dominated convergence
passes the finite time identities to the complete series, and separate
integrability theorems certify the time integrals.

`ExchangedFluxModeDynamics.lean` constructs the actual exchanged flux
mode as a fixed linear image of `w_k tensor (L_l-L_m)(w_l cross w_m)`.
Its derivative has the physical input rate `Gamma_klm`; its source is
constructed by inserting the actual nonlinear curl in each of the three
input slots. `ExchangedFluxGramBudget.lean` applies the correlated identity
to finite partial sums of this full NS evolution.

`ExchangedFluxModeEnvelope.lean` constructs summable mode and source
envelopes from a common third velocity moment on the local interval.
`ExchangedFluxSeriesBudget.lean` then identifies the infinite sum with
the actual spatial projected inviscid flux and proves

```text
fullGramEnergy(t) + integral_0^t |projectedFlux(0,u(tau))|_L2^2
  = fullGramEnergy(u0) + 2 integral_0^t fullGramWork(u(tau)),
fullGramEnergy(t) >= 0.
```

The series omits only identically zero terms with zero first inner curl
frequency. No finite-mode evolution or assumed nonlinear budget is used.
The physical constructor supplies both the local solution and the
convergence envelopes from real, transverse, mean-zero periodic data
with nine continuous coordinate jets. This is a local identity, not a
global estimate. The `0` in `projectedFlux(0,u)` selects the inviscid
part of the flux; the actual evolving solution still has positive viscosity.

`Analysis/ODE/DampedGramHeatRepresentation.lean` realizes the infinite
correlated pairing by an auxiliary heat-time integral and proves its
absolute integrability. `FourierHeatFlow.lean` constructs the actual
multiplier `H_sigma(k) = exp(-gamma_k sigma)`, preserving reality,
transversality, and absolute Fourier moments. The auxiliary parameter
`sigma` is distinct from physical solution time.

`ExchangedFluxVariation.lean`, `ExchangedFluxHeatVariation.lean`, and
`ExchangedFluxHeatRepresentation.lean` identify the full energy and work:

```text
Q(u) = integral_0^infinity |F(H_sigma u)|_L2^2 d sigma,
W(u) = integral_0^infinity
  <V(H_sigma u, H_sigma N(u)), F(H_sigma u)> d sigma,
H_sigma N(u) = N(H_sigma u) + C_sigma(u).
```

Here `F` is the projected inviscid flux, `N` is the full nonlinear velocity
RHS, and `V` is the convergent termwise three-slot flux variation. The
resolved and commutator variation sums converge separately. The proof
does not identify smoothing the nonlinear rate with recomputing it after
smoothing the velocity.

`FourierHeatCommutatorKernel.lean` inserts a division-free Duhamel
factorization into the actual pressure-corrected nonlinear discrepancy.
Writing `D = gamma_(k+l)` and `S = gamma_k + gamma_l`, its multiplier is

```text
exp(-D sigma) - exp(-S sigma)
  = (S-D) integral_0^sigma exp(-D(sigma-r)) exp(-S r) d r,
S-D = -2 nu (2 pi)^2 (k dot l).
```

The kernel integral is nonnegative, but the frequency contraction changes
sign. Orthogonal input frequencies give exact cancellation. Pairing with
an additional positive damping rate `c` and integrating in `sigma` gives
exactly `(S-D)/((c+D)(c+S))`; neither formula divides by `S-D`.

`ExchangedFluxHeatBudget.lean` substitutes both signed channels into the
actual infinite time identity. It proves integrability of the heat work
and of its physical-time integral, and constructs the local balance from
the same admissible physical data. `ExchangedFluxHeatAudit.lean` audits
the generic analysis, actual nonlinear force, and physical-time bridge.

`FourierHeatCommutatorEnergy.lean` and `FourierHeatCommutatorDecay.lean`
combine complementary energy and enstrophy estimates for the actual
commutator. With `E(u) = sum_q |u_q|^2` and
`Omega(u) = sum_q |curl(u)_q|^2`, the retained Gaussian bound is

```text
|C_sigma(u)_q|^2
  <= 2 nu sigma (2 pi |q|)^2 exp(-gamma_q sigma) E(u) Omega(u).
```

`FourierHeatCommutatorTime.lean` consumes the actual unforced identity
`E(t)^2 + 4 nu integral_0^t E Omega = E(0)^2`. Thus each accumulated
coefficient cost is bounded by
`(sigma/2) (2 pi |q|)^2 exp(-gamma_q sigma) E(0)^2`.
`FourierHeatLatticeEnergy.lean` proves convergence of the Gaussian
quadratic output cost. `FourierHeatCommutatorOutputBudget.lean` proves
continuity and the initial-energy bound for the entire output energy at
every fixed positive `sigma`, including construction from physical data.

`Analysis/ExponentialMoments.lean` gives the exact first exponential
moment. `FourierHeatCommutatorParameter.lean` justifies continuity of the
physical-time integral in the heat parameter.
`FourierHeatCommutatorScaleBudget.lean` then proves

```text
sum_q (1 + |q|)^(-2) integral_0^infinity integral_0^t
  |C_sigma(u(tau))_q|^2 d tau d sigma
  <= 2 E(0)^2 / (nu^2 (2 pi)^2) sum_q (1 + |q|)^(-4).
```

Every heat integral and the final weighted series converge. The zero
output is treated separately and vanishes. The actual local solution and
convergence envelopes are constructed from real, transverse, mean-zero
periodic data with eight continuous coordinate jets. The estimate has no
common-envelope size, final-time, or input-count factor. It is a
negative-order velocity-coefficient budget: using it in the signed flux
variation still requires control of the corresponding differentiated
test field. It is not a bound for `fullGramWork`, nor an unweighted
all-heat-parameter energy bound. `FourierHeatCommutatorEnergyAudit.lean`
audits the complete chain.

`ExchangedFluxAdjoint.lean` constructs the three real-linear
velocity-coefficient slots and their Hilbert adjoints. The input curls,
Leray-projector difference, and output gradient projection remain in the
operators. `ExchangedFluxVariationSeries.lean` proves absolute convergence
and exchanges the two inner slots before taking norms.
`ExchangedFluxAdjointSeries.lean` constructs the coefficient test by two
absolutely convergent double sums. `ExchangedFluxAdjointPairing.lean` proves
the exact signed infinite identity

```text
<fluxVariation(u,v), F> = sum_q <v_q, coefficientTest(u,F)_q>,
coefficientTest_q = -sum_(l,m) outerTest_(q,l,m)
                   -2 sum_(k,m) leftTest_(k,q,m).
```

`ExchangedFluxHeatAdjoint.lean` substitutes the actual heat commutator and
`F = projectedFlux(0,H_sigma u)`. Its coefficient pairing is absolutely
convergent, and the heat and physical-time integrability needed for the
full signed balance are proved. Physical periodic data construct the
local solution and that balance without any assumed test-field estimate.

`ExchangedFluxAdjointGeometry.lean` retains the exact projected vorticity
cross product in the outer adjoint bound. The inner adjoint retains the
Leray difference and satisfies, for nonzero inner frequencies,

```text
||differenceCLM_(k,l,m)|| ||curlCoefficientCLM_l||
  <= 12 (2 pi) |l+m|.
```

Thus the input curl derivative is transferred to the pair frequency.
The outer adjoint vanishes when the inner vorticity cross product does;
both adjoints vanish when `m = -l`. These gains precede any summation and
do not prove that coherence persists under the nonlinear evolution.

`Analysis/WeightedInnerProduct.lean` proves reciprocal-weight real
inner-product bounds, including a nonnegative extended-integral version.
`ExchangedFluxHeatDualBudget.lean` applies them over all positive heat
parameters and local physical time. With `A_sigma` the constructed test,
it proves

```text
sum_q integral_sigma integral_tau 2 |<C_sigma,q, A_sigma,q>|
  <= epsilon B(u0,nu) + epsilon^(-1) positiveTestCost,
positiveTestCost = sum_q (1+|q|)^2 integral_sigma integral_tau |A_sigma,q|^2,
B(u0,nu) = 2 E(0)^2 / (nu^2 (2 pi)^2) sum_q (1+|q|)^(-4).
```

The integrals and sums in this last estimate are explicitly nonnegative
extended integrals and sums. The paid commutator cost is identified with
the convergent real integrals above. The test cost is allowed to be
infinite; no finiteness or initial-data bound for it has been established.
The signed identity and this separate absolute-value estimate hold for
the same constructed local physical solution. No interchange with a
Bochner integral of the full absolute coefficient sum is asserted here.
`ExchangedFluxAdjointAudit.lean` audits the adjoints, convergence,
geometric transfer, heat balance, and dual-cost declarations.

`PeriodicTensorFourierFrame.lean` constructs the output coefficients of an
arbitrary tensor Hilbert-space test using the adjoints of the actual
projected Fourier synthesis maps. `Analysis/HilbertSynthesisBound.lean`
transfers synthesis contractivity to a Bessel bound with constant one:

```text
sum_n ||outputCoefficient(F,n)||^2 <= ||F||^2.
```

`ExchangedFluxOutputAdjoint.lean` factors both coefficient adjoints through
these output coefficients. The projected cross-product and pair-frequency
gains remain available before summation. The generic vector-valued
`Analysis/ShiftedSeriesSquareBound.lean` then controls the shifted double
series without an input- or output-frequency count factor.
`ExchangedFluxAdjointSquareSum.lean` applies it to the full combined test:

```text
sum_q ||(1+|q|)^(-1) A_q||^2
  <= [54 (2 pi) (sum_k ||omega_k||)^2]^2 ||F||^2.
```

This negative-order estimate does not pay the positive-order cost above.
`ExchangedFluxAdjointWeightedSum.lean` proves a weighted version. Write
`W_r(k) = (1+|k|)^r ||omega_k||` and
`b_r(n) = (1+|n|)^r ||outputCoefficient(F,n)||`. For each natural `m`,
assuming the absolute velocity moment of order `m+2` and square
summability of `b_(m+1)`, it proves

```text
sum_q ||(1+|q|)^m A_q||^2
  <= [54 (2 pi) (sum_k W_(m+1)(k))^2]^2 sum_n b_(m+1)(n)^2.
```

`ExchangedFluxHeatTestEstimate.lean` substitutes the actual heated
velocity and its projected inviscid stretching flux, with `m=1`, and
passes this bound through the positive heat-parameter and local-time
integrals. `Analysis/LowerIntegralSeries.lean` justifies the inequality
direction without extra measurability assumptions; it does not assert
an integral/series equality. The original initial-energy commutator
payment is connected to this explicit output envelope on the actual
local solution.

Output square summability is a hypothesis of this general weighted
bridge; it is discharged for the actual physical flux below. The
integral of its right-hand side is not bounded dynamically.
The coarse summed estimate uses the uniform
projector bound; it does not yet exploit the sharper pair-frequency gain
to close this debt. Neither the absolute curl moments nor this output
envelope may be treated as controlled by initial kinetic energy.
`ExchangedFluxOutputAdjointAudit.lean` audits these declarations.

`ExchangedFluxAdjointSectors.lean` constructs an exact Fourier-sector
split of that test. The selected outer terms satisfy
`||D_(l,m)(omega_l cross omega_m)|| <= delta ||omega_l|| ||omega_m||`;
the selected inner terms have nonzero inputs and
`|q+m| <= eta |q|`. Every complementary interaction remains in
`remainderTest`, with the signed identity

```text
coefficientTest = selectedTest + remainderTest.
```

`ExchangedFluxSectorSquareSum.lean` retains the geometric factor
`r = delta/36 + 4 eta/3` through the entire weighted lattice sum.
`ExchangedFluxSectorHeatCost.lean` substitutes the actual heated velocity
and projected stretching flux and proves

```text
selectedHeatCost <= r^2 integral_sigma integral_tau heatTestEnvelope.
```

The same input-moment and weighted-output summability hypotheses as in
the coarse envelope estimate are explicit. This is a gain against that
envelope, not a claim that the selected cost is at most `r^2` times the
actual full cost. The envelope may still have infinite integral.
Zero thresholds annihilate the selected test and leave the entire test
in the remainder. Fourier sector dominance, a connection to spatial
pancake coherence, and dynamical control of the complement remain
unproved. The decomposition does not discard the complement or justify
absorption by itself. The selectors are used algebraically; no material
transport identity for them is claimed. `ExchangedFluxSectorAudit.lean` audits the split,
the generalized weighted-series estimate, and the heat-cost transfer.

`Analysis/FiniteEnvelopeSquareBound.lean` allows a fixed finite sum of
shifted envelopes, with no frequency-count factor.
`ExchangedFluxTameAdjoint.lean` uses three channels to put two derivatives
on the output or on one input at a time. If
`W_s = sum_k (1+|k|)^s ||omega_k||` and `K = 54 (2 pi)`, the full test
satisfies the alternative positive-order estimate

```text
sum_q ||(1+|q|) A_q||^2 <= E_tame,
E_tame = 27 K^2 [W_0^4 sum_n b_2(n)^2 + 2 (W_2 W_0)^2 ||F||^2].
```

The selected test has the factor `r^2`, and the exact remainder has the
bound `(1+r)^2 E_tame`. These are regularity-dependent bounds, not
dynamical payments. The derivative placements are less redundant than
the multiplicative estimate, but the numerical constant is different;
neither estimate is asserted to be uniformly smaller.

`ExchangedFluxTameHeatCost.lean` therefore takes the pointwise minimum
of the two envelopes. The full accumulated cost is bounded by its
integral, and the selected cost retains `r^2` times that integral. The
initial-energy payment for the actual local unforced solution is wired
to this minimum envelope. Its general formulation retains input moments
and weighted-output square summability; the latter is constructed below.
No global bound for the minimum-envelope integral or the signed remainder
has been established.
`ExchangedFluxTameAudit.lean` audits the additive analysis and its NS
applications.

`PeriodicTensorFourierWeight.lean` proves that real projected modes pair
only at equal or opposite frequencies. Every even real frequency weight
therefore commutes with the actual output coefficients of a convergent
indexed mode series, including repeated output frequencies. Applying
the already proved Bessel bound to the constructed weighted field gives
weighted square summability without a frequency-count factor.

`ExchangedFluxWeightedOutput.lean` applies this to the exchanged cubic
series. With `w_s(n) = (1+|n|)^s`, it constructs

```text
weightedFlux_s(u) = -sum_p w_s(tripleFrequency(p)) mode(u,p),
outputCoefficient(weightedFlux_s(u),n)
  = w_s(n) outputCoefficient(projectedFlux(0,u),n),
sum_n b_s(n)^2 <= ||weightedFlux_s(u)||^2
  <= [6 embeddingConstant (sum_k W_s(k))^3]^2.
```

The hypotheses are the absolute velocity moment of order `s+1`,
coefficient reality, and incompressibility. The field and its series
convergence are proved, not supplied as a budget assumption. At `s=2`,
the same third-order velocity moment already used by the adjoint
construction supplies the missing output hypothesis, also after heat
smoothing.

`ExchangedFluxConstructedHeatCost.lean` removes that independent
hypothesis from the full and selected minimum-envelope estimates.
Physical periodic data with nine continuous coordinate derivatives
construct one local solution carrying the weighted-output summability,
the exact signed Gram balance, and the initial-energy-plus-envelope dual
bound. The cancellation factor remains unchanged.
`ExchangedFluxWeightedOutputAudit.lean` audits this construction.

**Remaining debt:** the curl moments on the right are not bounded by
initial kinetic energy. Constructing the output series removes a local
regularity hypothesis; it does not pay the heat/time-integrated envelope,
the signed remainder, or the misalignment strain budget dynamically.

`Analysis/IntegerDyadicShell.lean` constructs a disjoint cover of the
nonzero integer lattice by the shells
`2^n <= max_i |q_i| < 2^(n+1)`, with cardinality at most `125 * 2^(3n)`.
It proves the complete extended-sum decomposition and the exact allocation
`sum_n 1/((n+1)*(n+2)) = 1`.

`FourierHeatCommutatorShellBudget.lean` uses the actual coefficient budget
before summing output scales. If `C_sigma(u)` is the nonlinear heat
commutator and `E0 = kineticEnergy(u0)`, then, on every constructed local
unforced solution and for every shell,

```text
sum_{q in shell n} integral_{sigma>0} integral_{0<tau<=t}
  |C_sigma(u(tau))_q|^2
  <= [125 E0^2 / (2 nu^2 (2 pi)^2)] * 2^n.
```

Thus the negative half-derivative shell cost is uniform in `n`. It is
not asserted that these uniform bounds are summable over all shells.
`ExchangedFluxLogarithmicHeatCost.lean` instead sums with the allocation
above. For the actual coefficient test `A_sigma(u)`, define

```text
Llog(t) = sum_n 2^n (n+1)(n+2)
  * sum_{q in shell n} integral_{sigma>0} integral_{0<tau<=t} |A_sigma(u(tau))_q|^2.
absolutePairingCost(t)
  <= epsilon * [125 E0^2 / (2 nu^2 (2 pi)^2)] + epsilon^(-1) * Llog(t).
```

This replaces the old squared-frequency test weight by a single-frequency
weight with a logarithmic correction. `ExchangedFluxLogarithmicHeatBudget.lean`
proves `Llog <= 3 * positiveTestCost` and that the ratio of the new shell
weight to `4^n` tends to zero. It constructs the same physical local
solution for this estimate and the exact signed Gram identity. The test
cost is still an extended nonnegative quantity: no initial-data bound or
global finiteness of `Llog` is asserted. The resolved signed material term
is not part of `absolutePairingCost` and remains in the full balance.
`ExchangedFluxLogarithmicHeatAudit.lean` audits every new declaration.

The signed `fullGramWork` integral remains uncontrolled by initial data.
The joint viscous contribution, route-specific weights, and BKM
continuation budget remain open. `ExchangedFluxGramAudit.lean` audits
the generic and NS-specific declarations.

`LocalMaterialStretching.lean` transfers the strain-square cancellation
to the actual stretching vector `a = S omega` along constructed material
paths. The spin square vanishes on the actual vorticity, giving

```text
D_t a = -(Hess p) omega + d_a,
d_a = nu (Delta S) omega + S (nu Delta omega).
```

`LocalMaterialStretchingFlux.lean` identifies the raw inviscid flux
`J_j = -omega_j a` and proves its pressure-resolved material rate

```text
D_t J_j = -a_j a + omega_j (Hess p) omega
          - (nu Delta omega)_j a - omega_j d_a.
```

The signed contraction against an arbitrary tensor is retained.
`LocalMaterialFluxBalance.lean` proves continuity, integrability, and
the vector and quadratic time identities on every compact subinterval
of the local existence interval. Physical periodic data with nine
continuous coordinate derivatives construct both the local solution
and the material paths; neither is supplied as an extra assumption.
`LocalMaterialStretchingAudit.lean` audits these declarations.

This cancellation was already implicit in the spectral-defect algebra;
the new transfer concerns the actual raw flux used in the longitudinal
estimate. It is not a projected Eulerian Gram estimate. Material
transport does not commute with spatial gradient projection. The
projection-transport commutator, signed pressure work, and viscous
contributions still need a uniform integrated bound.

`PeriodicProjectedTensorJet.lean` constructs the continuous
representative and actual first translation derivatives of the gradient
projection of an indexed Fourier tensor. A frequency-uniform coefficient
bound preserves absolute summability. Spatial derivative commutation and
curl symmetry follow from the explicit symbol, including the zero mode
and repeated output frequencies.

`LongitudinalProjectedTransport.lean` applies this construction to
the actual raw inviscid flux `J_j = -omega_j S omega`. The second
absolute velocity moment supplies all coefficient and derivative
summability. With `F = P J`, the spatial transport work is exactly

```text
<F, (u . grad) J>_L2
  = integral_x sum_{j,k} (partial_j u_k) <F_k, J_j - F_j>.
```

Every field and spatial derivative is constructed from the same
infinite Fourier velocity. The proof uses incompressibility, symmetry
of the projected first derivatives, and orthogonality to an actual
contracted gradient. No derivative of the flux remains on the right,
and the expression vanishes if the orthogonal residual vanishes.
Physical periodic data with eight continuous coordinate derivatives
construct the local solution carrying this identity.
`LongitudinalProjectedTransportAudit.lean` audits the generic analysis,
the projected jets, and the actual-field application.

This resolves the algebraic transport contribution, not its dynamical
payment. The residual is not asserted to be small, and the velocity
gradient has no initial-data-controlled supremum here.

`LocalStretchingFluxTime.lean` differentiates the actual raw cubic flux
in the continuous-field norm and its gradient projection in tensor L2.
The rate contains the actual velocity RHS, not a supplied time derivative.
`StretchingFluxMaterialRate.lean` identifies its material rate with the
pressure Hessian and viscous Laplacians. In the full-gradient formulation,
`a = (omega . grad) u = S omega` and

```text
d_a = sum_j omega_j nu Delta(partial_j u)
      + sum_j (nu Delta omega)_j partial_j u,
M_j = -a_j a + omega_j (Hess p) omega
      - (nu Delta omega)_j a - omega_j d_a.
```

`StretchingFluxProjectedEvolution.lean` proves that the constructed
spatial transport is the ordinary derivative of this flux, then joins
the material rate with the exact deformation-remainder pairing:

```text
(1/2) d_t ||F||_L2^2 = <F, M>_L2 - R,
R = integral_x sum_{j,k} (partial_j u_k) <F_k, J_j - F_j>.
```

`LocalStretchingFluxBalance.lean` proves continuity of the combined
signed work on the closed local existence interval and its exact
integrated balance, including the actual initial data:

```text
||F(t)||_L2^2 = ||F(0)||_L2^2 + 2 integral_0^t (<F, M>_L2 - R).
```

Physical periodic data with nine continuous coordinate derivatives
construct the local solution and the common third absolute Fourier
moment used to justify this identity. This supplies no uniform bound
at a maximal existence time. The remaining task is to bound the signed
combination using the available initial-data budgets and geometric
cancellation, including the pressure and viscous contributions.
`LocalStretchingFluxAudit.lean` audits the declarations.

`PeriodicProjectedTensorDiffusion.lean` proves that the pairing of a
gradient-projected Fourier tensor with its raw second derivative is
exactly the negative squared norm of the projected first derivative.
`StretchingFluxSpatialDiffusion.lean` constructs the ordinary second
derivatives of the cubic stretching flux. With `a = (omega . grad) u`,
its viscous product rule is

```text
M_nu = M_0 + nu (Delta J + 2 C),
C_j = sum_k [(partial_k omega_j) partial_k a
        + omega_j sum_r (partial_k omega_r) partial_k partial_r u].
```

`StretchingFluxProjectedDiffusion.lean` transfers projection commutation
to the entire cubic flux before squaring its norm. It proves
`<F, Delta J> = -D`, where `D = sum_k ||partial_k F||_L2^2 >= 0`.
The mixed term is retained as `X = <F, C>`, without a sign assertion.
`LocalStretchingFluxDissipation.lean` then proves the exact balance

```text
W = <F, M_0> - R + 2 nu X,
||F(t)||_L2^2 + 2 nu integral_0^t D
  = ||F(0)||_L2^2 + 2 integral_0^t W.
```

All fields, spatial derivatives, time integrals, and the initial value
are constructed for the local solution from physical periodic data
with nine continuous coordinate derivatives. The common third absolute
Fourier moment justifies the identity; it is not an initial-data-only
bound at a possible singular time. Viscosity is not asserted to be
purely dissipative for this cubic functional: the mixed work remains.
Controlling the accumulated signed `W` with the available initial-data
budgets and geometric cancellation is still open.
`LocalStretchingFluxDissipationAudit.lean` audits these declarations.

`ExchangedFluxPolarization.lean` and `StretchingFluxVariation.lean`
identify the infinite exchange-symmetric Fourier variation with the
continuous-field product rule followed by the actual gradient projection.
Both equal the exact cubic polarization

```text
V(u,v) = (F(u+v) - F(u-v))/2 - F(v),   F(u) = P J(u).
```

Reality, incompressibility, and first absolute Fourier moments are
retained for both inputs. Absolute summability justifies the series
rearrangements before any pairing. `StretchingFluxHeatWork.lean`
applies the identity to the actual momentum RHS, obtaining both its
material-transport work and its extracted viscous dissipation. The
inviscid resolved work is also expressed as signed spatial integrals
with the actual pressure-Hessian action and projection residual.

For `v = H_sigma u`, this replaces the resolved part of the existing
heat source while keeping the nonlinear smoothing commutator `C_sigma`
and its constructed adjoint test `A_sigma` unchanged:

```text
materialHeatWork(nu,sigma,u)
  = <F(v), M_0(v)> - R(v) + sum_q <C_sigma(q), A_sigma(q)>,
G(t) + integral_0^t ||F(u(tau))||_L2^2
  = G(0) + 2 integral_0^t integral_(sigma>0) materialHeatWork(nu,sigma,u(tau)).
```

The same physical initial data construct the local solution and both
integrals. Auxiliary heat time is not physical solution time, and the
smoothed actual nonlinear rate is not equated with the rate recomputed
after smoothing. This closes the identification between the two work
formulations, not the remaining signed material-work or positive-order
adjoint budget. `StretchingFluxHeatWorkAudit.lean` audits the declarations.

`TwoShearViscousCertificate.lean` checks a reduced spectral certificate
for the mixed viscous obstruction, using the explicit angle-torus field

```text
u(x,y,z) = (sin(y) (1+cos(z))^3, sin(x) (1-cos(z))^3, 0).
```

For general separated profiles `a,b`, write `a'`, `a''` for ordinary
z-derivatives. The first component of `(omega dot grad)((omega dot grad)u)`
has the exact algebraic separation

```text
sin(y) A(z) + sin(y) cos(2x) B(z) + sin(2y) cos(x) C(z),
A = a' b b' + a'' b^2/2,
B = a'' b^2/2,
C = (b ((a')^2 - a a'') - a a' b')/2.
```

The second component exchanges x/y and a/b. The checked heat direction
is `a_t = a''-a`, `b_t = b''-b`, retaining the transverse sine eigenvalue.
Lean proves the ordinary profile derivatives, the three source variations,
all six finite cosine expansions, and positivity of the reduced sum

```text
W = sum_(k in Z) [A_k Adot_k/(1+k^2)
    + (B_k Bdot_k + C_k Cdot_k)/(2(5+k^2))]
  = 16932543012172819 / 351018510581760 > 0,
D = sum_(k in Z) [A_k^2 + (B_k^2+C_k^2)/2]
  = 5565537 / 131072 > 0,   W > D.
```

The sums have support `|k| <= 9`; the Lean definitions include the
negative-frequency multiplicities explicitly. The executable diagnostic
`tools/navier_stokes/projected_flux_viscosity.py` independently computes
the entire 3D rational Fourier convolution, gradient projection, and
heat-direction product rule. It verifies the source and rate coefficients
term by term against the separated polynomials, not only the final sign.
It also evaluates the full inviscid NS tangent and verifies that its work
vanishes: the projected cubic flux and its inviscid variation have
disjoint horizontal frequency parity. Thus the exact diagnostic obtains
the same positive work for the full NS tangent at viscosity one.

**Formal boundary:** `TwoShearViscousWorkCertificate.lean` now identifies
the displayed rational `W` with the actual `TensorL2` heat-variation
pairing, including the unit-torus factor `(2*pi)^8`. It also identifies
the full NS work as `nu * (2*pi)^8 * W`, using the proved inviscid
cancellation. This seals a physical-field counterexample to absorption
of the mixed viscous work by the extracted dissipation alone: the actual
quantities satisfy `2 X > D`. The numerical value displayed for `D`
remains a reduced spectral certificate; its physical identification is
not needed for this strict inequality. The result does not refute global
regularity, Ben's geometric route, or estimates retaining other terms.
`TwoShearViscousCertificateAudit.lean` audits every declaration.

`PeriodicFourierCollection.lean` groups absolutely summable indexed
coefficients by output frequency without changing the reconstructed
field. Its finite-support specialization retains every interaction
with a common output. `PeriodicTensorParseval.lean` then proves the
signed tensor pairing for the actual gradient projection:

```text
<P J, K>_L2 = sum_q Re <div(J)_q, div(K)_q>_C / ((2 pi)^2 |q|^2).
```

The zero output contributes zero, as required by the gradient projection.
The physical divergence coefficient includes `2 pi i`; the two factors
of `2 pi` in the inverse Laplacian are not dropped. The identity includes
all cross terms between interaction triples with the same output.

`StretchingFluxCoefficients.lean` constructs the canonical coefficients
of the actual cubic flux `J_j = -omega_j (omega dot grad)u` and proves
absolute summability, reality, and reconstruction. Cubic polarization
identifies the signed work of the actual three-slot product rule with
the corresponding coefficient pairing. `StretchingFluxSpectralEvolution.lean`
applies this to the full NS tangent and the ordinary heat tangent:

```text
spectralRHSWork(nu,u) = <F, M_nu> - R,
spectralVariationWork(u, Delta u) = 2 X - D,
spectralRHSWork(nu,u) = spectralRHSWork(0,u) + nu (2 X - D).
```

Here `D` and `X` are the already constructed projected gradient
dissipation and mixed work. The module also proves continuity,
time-integrability, and the exact local initial-data balance

```text
||F(u(t))||_L2^2 = ||F(u(0))||_L2^2
  + 2 integral_0^t spectralRHSWork(nu,u(tau)) d tau.
```

Physical data with nine continuous coordinate derivatives construct
the solution and its local moment envelope. This does not make the
envelope a global initial-data bound and does not assign a favorable
sign to the signed work.

`StretchingFluxFiniteCoefficients.lean` proves exact finite evaluation
and triple-sum output support. Fixing the output determines the third
input, reducing each coefficient to two finite input sums.
`TwoShearViscousData.lean` constructs the complementary two-shear Fourier
input, proves both longitudinal cosine expansions, reality, zero mean,
incompressibility, all absolute moments, and finite support of the heat
direction. It instantiates the exact double-sum flux formula. The
witness-specific coefficient evaluation, comparison with
`TwoShearViscousCertificate`, and inviscid parity cancellation are
now proved, as described below.
`StretchingFluxSpectralAudit.lean` audits these additions.

`StretchingFluxMixedCoefficients.lean` constructs the three separate
rate insertions into the physical cubic flux. Their collected
coefficients reconstruct the actual product rule, and their signed
projected pairing is the existing physical work. No polarization
expansion is needed to evaluate these separate slots.

`StretchingFluxHorizontalParity.lean` proves an instantaneous cancellation
for the full infinite NS convolution. If the input is supported on
`(q_0 + q_1) mod 2 = 1`, its inviscid velocity RHS has parity zero.
The cubic flux retains parity one, while its inviscid variation has
parity zero. Thus the actual projected work vanishes. Applied to the
constructed two-shear input, the full NS work satisfies

```text
spectralRHSWork(0,u) = 0,
spectralRHSWork(nu,u) = nu * spectralVariationWork(u, Delta u).
```

This does not assert that the nonlinear solution remains in the odd
sector, or in a finite-dimensional invariant subspace.

`RationalStretchingFlux.lean` proves the exact normalization for imaginary
rational velocity coefficients `u_hat = i a`: the cubic flux coefficient
is `(2 pi)^3` times a rational finite convolution, and its divergence
is `i (2 pi)^4` times the rational divergence coefficient. The rational
calculation is therefore linked to the actual operator, not a proxy.
`TwoShearViscousCoefficientEvaluation.lean` applies it to the constructed
input and checks the first complete vector coefficient:

```text
div(J)_(0,1,1) = i (2 pi)^4 * (-429/1024, 0, 0).
```

The longitudinal input support and its duplicate-free sum enumeration
are also checked. `StretchingFluxParityAudit.lean` audits these additions.

`StretchingFluxFiniteVariation.lean` proves the finite mixed-input
convolution and its exact multiplier variation. The symbol is the sum
of the three input symbols, not the symbol at the output frequency.
`RationalStretchingFluxHeat.lean` specializes this to the heat direction:
the varied flux has factor `(2*pi)^5`, its divergence has `i*(2*pi)^6`,
and the full signed work is `(2*pi)^8` times a finite rational sum.
`RationalStretchingFluxContraction.lean` contracts the two derivative
indices before summation, with an exact zero-slot shortcut.

`TwoShearViscousCoefficientFamilies.lean` and
`TwoShearViscousRemainingFamilies.lean` identify all nonnegative axis,
mixed-horizontal, and pure-third-harmonic source families, and every
heat-rate family needed for their pairing. The third harmonics have
zero source divergence. `TwoShearViscousReflection.lean` proves the
reflection symmetries by reindexing the complete input sums, while
`TwoShearViscousOutputGrid.lean` proves that every possible triple output
lies in the enumerated grid. No negative contribution is discarded.
`TwoShearViscousWorkFamilies.lean` then accounts for all signs and
multiplicities. The final theorem is

```text
spectralRHSWork(nu,u)
  = nu * (2*pi)^8 * 16932543012172819 / 351018510581760 > 0  (nu > 0),
2 * mixedWork(u) > dissipation(u).
```

`StretchingFluxHeatParity.lean` proves a complementary fact about the
heat-integrated formulation. For any real, transverse input of odd
horizontal parity with a summable third Fourier moment, the smoothed
actual inviscid tangent has even parity. Hence its complete signed
pairing with the smoothed cubic flux vanishes, including the nonlinear
heat commutator. Thus `materialHeatWork(nu,sigma,u) = 0` for `sigma >= 0`
and `fullGramWork(nu,u) = 0`. `TwoShearViscousHeatComparison.lean` applies
this to the same witness whose raw work is strictly positive.

This distinction supports retaining the full heat-integrated balance;
it does not prove its arbitrary-data budget. These are instantaneous
identities, and the NS evolution need not preserve odd parity. The
remaining target is the signed physical-time integral of the complete
material/commutator work, followed by the other sectors and continuation.
`TwoShearViscousWorkAudit.lean` audits every new declaration.

`CoherenceCreationSnapshot.lean` supplies real, mean-zero, transverse,
finite Fourier coefficients, hence all absolute Fourier moments. Its
velocity is `(-sin y + sin x sin z, 0, cos x cos z - cos(2x)/2)`, with
angles `2 pi x`, `2 pi y`, `2 pi z`. At the origin the entire first
vorticity jet, polynomial angular jets, angular density, and `q` vanish,
but the actual NS material rate of `q` is `-(2 pi)^4 e_z` for every
viscosity. Thus no pointwise estimate of the curvature source by a
constant times `|q|` can hold even for these admissible data. The snapshot
is not asserted to evolve within a finite-mode invariant subspace and
is not a blowup example or a refutation of global regularity.

**Still open:** controlling the remaining weighted stretching and gradient
fluxes, coupling them to the complete nonlocal test mismatch, and obtaining
the cutoff-uniform time budget. Local coherence cannot simply be assumed
to persist. `LongitudinalVorticityAudit.lean` checks the declarations.

### Exact low-output dyadic reconstruction with actual kernel costs

`PressureDyadicSymbol.lean` replaces both annular cutoffs by the smooth
normalized cutoff `eta`, whose integer dyadic dilates sum to one away from
zero. A globally smooth correction multiplies the existing pressure symbol,
preserving its exact algebra and common compact support.
`PressureDyadicKernel.lean` proves fresh inverse-Fourier moment bounds for
the corrected symbols. No Fourier-kernel norm comparison is inferred from
the pointwise inequality between corrected and original cutoffs.

`PressureDyadicPhysicalKernel.lean` transfers these new scalar-entry kernels
to the original input coordinates and any positive input scale `N`.
`PressureDyadicPartition.lean` proves

```text
rho_n = 2^(-n)/256,
sum_n Fourier(K_(N,rho_n,e;w,v,i))(k,p)
  = eta(k/N) * pressurePair(e,k,p;w,v,i),
                       whenever |k+p| <= N/256,
sum_n integral |K_(N,rho_n,e;i,j,l)|       <= C_0,
sum_n integral |x| |K_(N,rho_n,e;i,j,l)(x)| <= C_1/N.
```

The first statement is an actual `HasSum` identity for the Fourier
transforms of the constructed Schwartz kernels. It includes exact zero
output, where the pressure coefficient vanishes; the annular partition
itself is never asserted to sum to one at zero. The last two statements
include summability and constants uniform in `N`, unit frozen direction,
and all 27 basis entries. `PressureDyadicAudit.lean` checks a nonzero band
coefficient `-48/40768625`, its reconstructed sum `-96/40768625`, and zero
output.

### Corrected periodic operators and continuous full-field action

`PressureDyadicOperatorKernel.lean` assembles the corrected scalar kernels
into a complex-bilinear operator-valued Schwartz kernel.
`PressureDyadicPeriodization.lean` transfers it to the unit six-torus with
the exact lattice Fourier coefficients, summable operator-norm masses,
and summed wrapped first moments bounded by `C/N`. Both input displacements
are accounted for; their combined moment is bounded by twice the Euclidean
first moment. The original overlapping-cutoff family below is unchanged.

`Analysis/BilinearKernelIntegrability.lean` and
`PressureIntegrableKernelAction.lean` establish the actual Bochner action
using only operator-norm integrability of the kernel. Arbitrary continuous
complex fields produce continuous output; no absolute summability of their
Fourier coefficients is assumed. The exact two-input localization identity
and its weighted difference bound hold in this integrable-kernel setting.

`PressureDyadicAction.lean` proves absolute convergence of the actual
output-band actions in the continuous-field supremum norm, with a bound
`C * ||f||_infinity * ||g||_infinity` independent of input scale and unit
frozen direction. The full band sum retains the exact localization identity.
On Fourier monomials it reconstructs the retained low-output pressure
coefficient, including zero output. `PressureDyadicActionAudit.lean` checks
nonzero periodic coefficients, actual nonzero monomial actions, double
imaginary phase, their reconstructed sum, and full-field convergence.

### Full Fourier reconstruction and the signed physical source

`PressureContinuousBilinearAction.lean` packages each integrable kernel as
a continuous bilinear map on continuous fields. Its norm is bounded by
the integral of the kernel's operator norm.
`PressureDyadicBilinearAction.lean` proves that the output-band series
converges absolutely in **bilinear operator norm**, uniformly in input
scale and unit frozen direction; evaluation equals the existing `sumAction`.

The reusable `Analysis/BilinearSeries.lean` justifies the product-indexed
expansion of a bounded bilinear map on two absolutely convergent series.
`Analysis/UnitTorusContinuousFourier.lean` supplies norm-at-most-one
vector-valued Fourier coefficient maps. Applying these to actual continuous
Fourier reconstructions gives `PressureDyadicFourierReconstruction.lean`:
for `|q| <= N/256`,

```text
FourierCoeff(sumAction_N(f,g), q)
  = sum_k chi_N(k) B_e(k,q-k)(a_k,b_(q-k)),
chi_N(k) = normalizedCutoff(k/N).
```

Both input series are full series; the coefficient identity assumes
absolute summability to justify reconstruction, not a uniform moment bound
as an additional operator cost. The zero-output coefficient vanishes by
the pressure symbol, not by asserting a partition of unity at the origin.

`PressureDyadicPhysicalIdentification.lean` applies the identity to the
actual complexified real vorticity of smooth conjugate-symmetric velocity
data. With incompressibility, the physical pressure-tilt coefficient is
exactly

```text
physicalTilt_q = -chi(q) * [FourierCoeff(sumAction_N(omega,omega), q) + complement_q],
complement_q  = sum_k (1-chi_N(k)) B_e(k,q-k)(omega_k,omega_(q-k)).
```

The complementary series is genuinely convergent and retained. Finite
output reconstruction, with every output in the low ball, identifies the
actual spatial pressure channel. `PressureDyadicJointSource.lean` inserts
this decomposition after the existing resolved-pressure/subgrid-pressure
cancellation, preserving the spin, raw-subgrid, transport, and complement
terms in the signed joint alignment source.

This is an exact identity, **not** a bound on the signed time-integrated
source. The original localization budget cannot be substituted through
output-filtered patch products without an additional argument. The
matched-index construction below builds one fixed low-pass filter into the
kernel instead; it does not justify arbitrary filter/patch commutation.

`PressureDyadicReconstructionAudit.lean` checks a nonzero reconstructed
coefficient `-96/40768625`, its nonzero complementary half, and zero output
for arbitrary absolutely summable full inputs. Generic tests also detect
the loss of cross interactions and verify the double-imaginary phase sign.

### Fixed output filter and quarter-geometric input tails

`Analysis/DyadicLowPass.lean` constructs a contractive low-pass multiplier
`psi(x)`: it is one on the unit ball and zero for `|x| >= 4`. The annular
sum defines it away from zero; its zero value is filled with one. The
annular sum agrees with this filled filter when the zero-frequency
amplitude vanishes, as the pressure-tilt symbol does.

`PressureFixedOutputSymbol.lean` matches input scale `N_j = N * 2^j`
with output-band indices `j + m`. The resulting output multiplier is
independent of `j`:

```text
psi_N(q) = psi(256*q/N),
psi_N(q) = 1 for |q| <= N/256,
psi_N(q) = 0 for |q| >= N/64.
```

`PressureFixedOutputAction.lean` constructs the actual continuous bilinear
operator `T_(N,j,e)` by summing those bands in operator norm. For full
absolutely convergent input Fourier series and every output `q`,

```text
FourierCoeff(T_(N,j,e)(f,g), q)
  = psi_N(q) * sum_k eta(k/N_j) B_e(k,q-k)(a_k,b_(q-k)).
```

`PressureFixedOutputPhysical.lean` identifies the actual complexified
vorticity inputs and the exact signed physical coefficient:

```text
physicalTilt_(psi_N,q)
  = -FourierCoeff(T_(N,j,e)(omega,omega), q)
    -psi_N(q) * complement_(N_j,q).
```

The output filter is already inside `T`; the complementary input sector
has not been dropped. `PressureFixedOutputEnvelope.lean` proves common
direction-independent majorants whose output-band mass sum is bounded by
`C0 * 4^(-j)` and whose first-moment sum is bounded by
`(C1/N) * 4^(-j)`.

`PressureFixedOutputLocalization.lean` and
`GaussianRootFixedOutputBudget.lean` retain this gain through the actual
two-input localization, kernel integration, and output-band summation.
For the Gaussian patch residual `R_j = c^2 T_j(omega,omega) -
T_j(c*omega,c*omega)`, with the finite patch family inside the spatial
mixed norm, every high-input tail satisfies

```text
sum_(j >= J) ||R_j||_(L2_x ell2_patch)
  <= (C/N) * 4^(-J) * W^2 * sqrt(6*G),
W >= ||omega||_infinity,
G = integral squaredRootGradientSquare.
```

The kernel constants are independent of the input index and the patch count.
The actual field and patch costs remain visible. The complete high-input
operator and its pointwise joint-source identity are constructed below.
The remaining physical sectors and a time-integrated estimate still need
control. No BKM bound follows from this fixed-field inequality alone.

`PressureFixedOutputAudit.lean` tests a nonzero input index and a transition
output where both cutoff weights equal one half: the reconstructed
coefficient is `-48/40768625`. It also checks zero output, outputs outside
the fixed filter, and the exact matched first-moment scaling.

### Complete high-input operator and finite low-input complement

`Analysis/DyadicHighPass.lean` proves the exact partition, including zero:

```text
H(x) = sum_(j >= 0) eta(2^(-j)*x) = 1 - psi(2*x),
H(x) = 0 for |x| <= 1/2,
H(x) = 1 for |x| >= 2.
```

`PressureHighInputAction.lean` sums `T_(N,j,e)` over `j >= J` in
bilinear operator norm to define `T_(N,>=J,e)`. The sum of operator norms
is at most `C * 4^(-J)`, uniformly in positive `N` and unit `e`.
`PressureHighInputFourier.lean` identifies every Fourier coefficient
for arbitrary absolutely convergent full input series:

```text
FourierCoeff(T_(N,>=J,e)(f,g), q)
  = psi_N(q) * sum_k H(k/N_J) B_e(k,q-k)(a_k,b_(q-k)).
```

`PressureHighInputComplement.lean` constructs the complementary coefficient
as a genuinely finite sum. Its input multiplier is `psi(2*k/N_J)`, which
vanishes for `|k| >= 2*N_J`. An explicit lattice box contains its support.
The fixed output filter also has an explicit finite lattice support.
`Analysis/UnitTorusFourierUniqueness.lean` gives pointwise reconstruction
from these coefficients without assuming arbitrary Fourier series
converge pointwise.

For actual conjugate-symmetric, divergence-free velocity data with
absolutely summable second Fourier moment,
`PressureHighInputJointSource.lean` proves the signed pointwise identity

```text
transversePressure_(psi_N,e)(x)
  = realPart(-T_(N,>=J,e)(omega,omega)(x) - lowInputField_(N,J,e)(x)),
```

and inserts it into the actual joint source at its moving top-strain
direction `e(x)`. Spin, raw subgrid, and transport terms remain explicit.
`GaussianRootHighInputBudget.lean` proves, for the actual finite root-patch
family and its frozen unit directions,

```text
R_(>=J,i) = c_i^2 T_(N,>=J,e_i)(omega,omega)
           - T_(N,>=J,e_i)(c_i*omega,c_i*omega),
||R_(>=J)||_(L2_x ell2_patch) <= (C/N) * 4^(-J) * W^2 * sqrt(6*G).
```

This is the localization of the infinite operator sum itself, not only a
series of upper bounds. The direction-freezing estimate below is a separate
argument; the remaining sector estimates and time control of `W` and `G`
are not supplied by this theorem. The
low-input complement's finiteness likewise does not make its cost uniform
in the input threshold or bounded up to a singular time.

`PressureHighInputAudit.lean` checks a nonzero reconstructed coefficient
`-96/40768625` at threshold zero, the half-sized value `-48/40768625`
after raising the threshold, the complementary input weights, the actual
operator value at a spatial point, and zero output for full inputs.

### Direction freezing with the actual high-input kernel gain

`PressureDirectionSecant.lean` uses the linear-minus-cubic dependence of the
normalized pressure symbol on its direction. A cubic-exact centered
derivative stencil and Simpson identity construct a smooth secant family
with the same compact frequency support. The symbol difference equals the
direction gap times this secant, including coincident directions. Uniform
inverse-Fourier moments follow from this exact identity, not from a
pointwise multiplier comparison.

`PressureDirectionKernel.lean` and `PressureDirectionOperatorKernel.lean`
carry the gain through the physical coordinate changes, finite bilinear
assembly, and actual periodization:

```text
integral |K_(N,rho,e) - K_(N,rho,f)|       <= C0 * rho^2 * |e-f|,
integral |x| |K_(N,rho,e) - K_(N,rho,f)|   <= C1 * (rho/N) * |e-f|.
```

`PressureDirectionAction.lean` sums the actual operators in both output
and input indices, proving

```text
||T_(N,>=J,e) - T_(N,>=J,f)||_bilinear <= C * 4^(-J) * |e-f|.
```

The constant is independent of positive `N`, unit directions, and input
threshold `J`. `PressureDirectionParity.lean` proves the exact reversal
identity `T_(-e) = -T_e` for full continuous fields. Consequently the norm
freezing estimate uses the unoriented distance
`min(|e-f|^2, |e+f|^2)`, not a globally continuous choice of eigenvector sign.

`GaussianRootDirectionFreezing.lean` constructs the actual adaptive root
partition from the strain and vorticity, with `Q = sum_i c_i^4` and its
weighted line error at most `epsilon^2`. At every spatial point,

```text
Q(x) * |T_(N,>=J,e(x))(omega,omega)(x)|^2
  <= 2 * sum_i c_i(x)^4 * |T_(N,>=J,e_i)(omega,omega)(x)|^2
     + 2 * (C * 4^(-J))^2 * ||omega||_infinity^4 * epsilon^2.
```

No patch-count factor enters this transfer. This is a pointwise estimate
for the constructed high-input operator, not yet a signed time-integrated
bound for the full source. The frozen fields still need their localized
coherent/misaligned sector estimates. Making the angular tolerance smaller
also changes the partition-gradient cost in the localization estimate;
the error cannot be treated as arbitrarily small at no other expense.

### Spatial energy of the moving spectral direction

`PressureMovingDirectionEnergy.lean` proves that
`Q(x) * |T_(N,>=J,e(x))(omega,omega)(x)|^2` is continuous and integrable on
the torus under the stated Fourier-moment hypothesis. It does not assume
that the selected signed top eigenvector is measurable. Instead, the
continuous weighted projector controls the weighted line distance, and
oddness of the actual pressure action controls the difference of output
norms. The argument includes vanishing vorticity and spectral collisions.

`GaussianRootMovingPressureBudget.lean` combines this regularity with the
direction-freezing and actual localization bounds. For the constructed
root patches, define

```text
E_moving = integral Q(x) |T_(N,>=J,e(x))(omega,omega)(x)|^2,
E_patch  = integral sum_i |T_(N,>=J,e_i)(c_i omega,c_i omega)(x)|^2,
G        = integral sum_(i,j) |d_j(c_i^2)|^2,
W        = ||omega||_infinity.
```

The checked estimate, with constants uniform in all displayed choices, is

```text
E_moving <= 4 E_patch
            + 24 (C1/N)^2 16^(-J) W^4 G
            +  2 C0^2     16^(-J) W^4 rho^2.
```

The root partition has the same `rho`-dependent temperature in both error
terms. Thus reducing the angular error does not silently discard the
resulting gradient cost. All fields inside `E_patch` are actual continuous
bilinear operator outputs on localized full vorticity, not placeholders
for future kernel bounds. Controlling these outputs by the coherent and
misaligned fields, and bounding all accumulated costs in time, remain
open obligations. This theorem is spatial and does not establish the BKM
integral or unconditional regularity.

`GaussianRootIntegrableKernelBudget.lean` applies the weighted root-patch
difference estimate to these actual kernels, retaining vorticity factors
without inverse vorticity magnitude or an assumed scalar-root gradient.
This makes the per-band localization bound integrable, not dynamically
affordable. The fixed-output high-input sum is now constructed above;
the other frequency sectors and the signed root-weighted dynamical
scale/time budget remain open. The
supremum-norm action bound is not a scale-critical continuation estimate.
This is not global NS regularity.

### Coherent pressure: exact divergence factorization

`PressureCoherentDivergenceSymbol.lean` removes the longitudinal output
factor from the normalized coherent symbol. Write `r = t/128`, let `k`
be the normalized first input, and let the second input be `p = r q - k`.
The resulting smooth symbol `S` satisfies the exact component identity

```text
retained(t,k,q) B_e(k,p)(e,e)_i
  = r S(t,e,i,k,q) (k.e + p.e).
```

The proof includes `r = 0` and vanishing longitudinal frequencies. It
divides by neither the angle nor the ratio. Joint smoothness includes the
varying coherent amplitudes `e,e`; all symbols have the same compact
frequency support. `Analysis/EuclideanCrossProductCalculus.lean` supplies
the reusable joint smoothness of the cross product.

`PressureCoherentDivergenceKernel.lean` constructs the actual inverse
Fourier kernels and proves uniform moments before the coordinate change.
`PressureCoherentDivergencePhysicalKernel.lean` transports them to the
original two-input coordinates and any positive input scale `N`. For
the resulting component kernel `K`, with constants chosen before the
ratio, scale, unit direction, and coordinate,

```text
integral |K(x)|       <= C0 r,
integral |x| |K(x)|   <= C1/N,
retained physical coherent symbol
  = Fourier(K)(k,p) ((k.e + p.e)/N).
```

The mixed channels in `PressureCoherentDivergenceDecomposition.lean`
retain the original `r^2` prefactor. The coherent channel becomes `r S`
times

```text
(k.w - k.R_e(w)) (e.v) + (e.w) (p.v - p.R_e(v)),
R_e(w) = w - (e.w)e.
```

Thus the actual input-divergence defects remain explicit. Setting them
to zero still leaves differentiated transverse inputs, not a free
cancellation. Localization does not in general preserve divergence
freedom.

The displayed Euclidean first-moment bound has no output-ratio decay:
summing that upper bound over all output bands is insufficient. This does
not prove that the actual summed kernel has an infinite first moment.
The periodic wrapped-moment repair is proved below, as are the common
direction/channel-independent envelopes and normalized complex bilinear
channel kernels. Their continuous-field actions and band sums are also
constructed. The actual localized weak derivatives and their Fourier
identities are constructed below, as are the actual L² derivative-input
integrals. Their whole-field identification with the derivative channels
and patch-square-sum transfer remain required. Uniform individual kernel
masses do not alone justify that square-sum estimate.
The full localized coherent/misaligned field estimate and its signed
time-integrated cost remain open.

`PressureCoherentDivergenceAudit.lean` checks joint smoothness, degenerate
ratio handling, longitudinal cancellation without a divergence hypothesis,
the physical Fourier identity, and the uniform scale quantifiers.

### Logarithmic repair of the periodic derivative-kernel moment budget

`Analysis/GeometricMinSeries.lean` proves, for nonnegative `A,D`,

```text
sum_m min(A 2^(-m), D)
  <= D (3 + log(1 + A/D) / log 2).
```

Summability is proved independently, including at `D = 0`. The general
theorem allows every geometric ratio strictly between zero and one.
`Analysis/TruncatedKernelMoment.lean` bounds
`integral min(R,|x|) |K(x)|` by the smaller of `R` times the mass and
the full first moment.

`PressureCoherentDivergenceTruncatedBudget.lean` applies these results to
the actual matched kernels at input scale `N 2^j` and output ratio
`2^(-j-m)/256`. It proves both infinite sums summable, even for arbitrary
band-dependent unit directions. The total truncated moment over inputs
`j >= J` is bounded by

```text
C 2^(-J) / N (3 + log(1 + R N/256) / log 2).
```

`FrequencyPairTruncatedMoment.lean` uses the actual product supremum norm
on the unit frequency-pair torus. Wrapped distance is at most `1/2` and
at most the Euclidean norm of every lift. Weighted periodization therefore
bounds the true wrapped first moment by the Euclidean moment truncated
at `R = 1/2`.

`PressureCoherentDivergencePeriodization.lean` constructs the periodic
scalar component kernels, proves their exact Fourier coefficient
factorization, and obtains

```text
sum_(j >= J,m) integral |K_periodic(j,m)|
  <= C0 2^(-J),
sum_(j >= J,m) integral |q| |K_periodic(j,m)(q)|
  <= C1 2^(-J) / N (3 + log(1 + N/512) / log 2).
```

All constants precede the input scale, tail index, band-dependent unit
directions, and output coordinate. The cap is justified by the periodic
geometry, not an arbitrary cutoff of a whole-space displacement cost.
This repairs the periodic scalar derivative-kernel summation issue;
it neither estimates the full localized field channels nor makes their
costs uniformly affordable in time. `PressureCoherentPeriodicBudgetAudit.lean`
checks the attained wrapped-distance bound, a numerical logarithmic scale,
alternating band directions, and the exact output-frequency normalization.

### Common coherent channels and their integrated field actions

`PressureCoherentDivergenceChannel.lean` constructs seven smooth compactly
supported symbols: the coherent symbol itself, and its three first-input
and three second-input coordinate multiples. One continuous integrable
envelope dominates all their inverse transforms, uniformly in the unit
direction and compact ratio parameter.

`PressureCoherentDivergenceChannelKernel.lean` transports and dilates these
kernels, proving that the differentiated channels' Fourier transforms
are exactly `k_j/N` or `p_j/N` times the base transform. The zero-ratio
case is included. These frequency factors do not silently include the
`2 pi i` factor needed for an actual spatial derivative.

`Analysis/BilinearRankOne.lean` proves the exact norm of the map
`(u,v) -> f(u) g(v) w`. `PressureCoherentDivergenceOperatorKernel.lean`
uses the two longitudinal complex-linear functionals and three output
coordinates to assemble the actual bilinear Schwartz kernels. Unit
directions give coordinate operators of norm one; their common-envelope
bound costs three output coordinates, not an adaptive patch count.

`PressureCoherentDivergenceEnvelope.lean` retains envelope mass `C0 ratio`
and first moment `C1/N`. `PressureCoherentChannelPeriodization.lean`
preserves the actual Fourier coefficients and constructs a single
full-measure domination set for all unit directions and channels. Its
common periodic envelope satisfies

```text
integral M <= C ratio,
integral |q| M(q) <= C min(ratio/2, 1/N).
```

`PressureCoherentChannelEnvelopeBudget.lean` obtains a single domination
set for all matched bands too. Both infinite envelope-cost sums converge:
their mass is at most `C0 2^(-J)` and wrapped first moment is at most
`C1 2^(-J)/N (3 + log(1 + N/512)/log 2)`. These are bounds for common
envelopes, not merely separately chosen direction-dependent kernel norms.

`PressureCoherentChannelAction.lean` integrates these kernels against
arbitrary continuous complex input fields. The nested band sum converges
absolutely in the continuous-field supremum norm, even when direction and
channel vary between bands, and its norm is at most
`C 2^(-J) norm(f) norm(g)`. The exact two-input scalar localization
identity is proved without assuming the localized fields divergence-free.

The weak derivative/divergence fields and their coefficient identities are
constructed in the next section, followed by the actual L² derivative-input
actions. Whole-field channel identification and patch-square-sum error
remain open, as does time control of the resulting costs. `PressureCoherentChannelAudit.lean`
checks the channel count, complex bilinear phase, zero ratio, normalized
input coordinates, arbitrary band choices, and localized continuous inputs.

### Actual localized weak divergence and its derivative budget

`PeriodicVectorWeakDerivative.lean` extends the scalar periodic weak
Fourier derivative to real vector fields with locally Lipschitz lifts.
Its coordinatewise definition is in L² and agrees almost everywhere
with the actual vector derivative. The divergence has zero spatial mean,
but is not assumed pointwise zero. Its Fourier coefficient is
`2 pi i sum_j k_j fhat_j(k)`.

`GaussianRootWeakDivergence.lean` applies this construction to the actual
root-localized vorticities `F_i = c_i omega`. The entire vector `F_i` is
locally Lipschitz; no differentiability of `c_i` at a zero of vorticity is
assumed. Both `partial_j F_i` and `D_i = div F_i` are actual L² fields.
Their weighted energies are integrable and satisfy

```text
integral sum_i c_i^2 D_i^2
  <= 3 sum_j integral sum_i c_i^2 |partial_j F_i|^2.
```

The existing fourth-power-normalized derivative estimate is transferred
to these weak derivatives and to `D_i`, with only the fixed factor three.
The explicit bound retains the Gaussian `tau^-2` cost, `tau log(card centers)`,
projector and gap-factor derivatives, and vorticity-gradient terms. It is
not a bound uniform in all regularizations or up to a singular time.

`PressureCoherentChannelWeakFourier.lean` proves that applying the base
coherent multiplier to the actual weak derivative coefficient is exactly
`2 pi i N` times applying the corresponding input-coordinate channel to
the original field coefficient. Both input slots are treated, and the
derivative's field need only be locally Lipschitz before differentiation.
This is not yet an interchange of an L² derivative with the physical-space
kernel integral; the earlier continuous-input action does not supply that
step automatically.

`PressureWeakDivergenceAudit.lean` checks constant fields, an explicit
nonzero divergence after scalar localization, both input-scale factors,
zero mean for the actual root-localized divergence, and the channel identity
instantiated at the actual root-vorticity derivative.

### Physical pressure actions on weak derivative inputs

`Analysis/WeightedIntegralEnergy.lean` proves weighted Cauchy–Schwarz
without dividing by the weight mass. `Analysis/BilinearTranslatedKernel.lean`
uses measure-preserving translated coordinates to construct the actual
bilinear integral with one L² input and one bounded measurable input.
The integrand is integrable for almost every output point, the output
belongs to L², and changing a kernel or input on a null set changes the
output only on a null set. Both input slots are covered.

`PressureL2KernelAction.lean` specializes this result to the existing
torus `kernelAction`. For continuous `g` and square-integrable `f`,

```text
integral |kernelAction K f g|^2
  <= (integral norm(K))^2 norm(g)_sup^2 integral |f|^2.
```

The coherent kernels admit one constant `C`, independent of the positive
input scale, output ratio, unit direction, channel, and inputs, giving
the bound `C ratio(t)^2 norm(g)_sup^2 integral |f|^2` on the stated ratio
interval. The generic input-difference estimate also provides stability
under L² approximation of the differentiated slot.

`GaussianRootWeakPressureAction.lean` applies the base coherent kernel
to the actual pairs `(partial_j F_i, F_i)` and `(F_i, partial_j F_i)`.
Both outputs are actual L² fields with the displayed energy bound and
no assumption that the weak derivative is continuous. Complexification
preserves the input energy.

The first-coordinate coefficient identities are upgraded to whole-field
identities below. The corresponding second-slot identification remains
required. The weighted patch-square-sum estimate is not a consequence of separate
patchwise bounds: the partition structure must survive that aggregation.
No signed time-integrated budget or singular-time vorticity bound follows
from the present spatial estimates alone.

### Both input-coordinate weak-field identities with uniform scale gain

`Analysis/UnitTorusL2Projection.lean` constructs finite projections using
the actual coefficients of arbitrary L² vector fields and proves their
spatial energy error tends to zero. `Analysis/UnitTorusFourierApproximation.lean`
also supplies uniform finite-polynomial approximation for continuous vector
fields; this is not uniform convergence of ordinary Fourier partial sums.

`PressureL2FourierReconstruction.lean` first holds the second input polynomial
and passes the first input and its derivative to their L² limits. It then
uses uniform density in the continuous second input. The new left and right
continuity estimates in `PressureL2KernelAction.lean` justify both passages
for the actual Bochner integral, modulo spatial null sets.

`PressureCoherentWeakFieldTransfer.lean` consequently proves, for a continuous
real vector field `f` with locally Lipschitz periodic lift and continuous `g`,

```text
(2 pi i N) kernelAction K_first,j f g
  = kernelAction K_base (partial_j f) g       almost everywhere,

integral |kernelAction K_first,j f g|²
  <= C ratio(t)² / (2 pi N)²
       * norm(g)_sup² * integral |partial_j f|².
```

Real inputs and derivatives are complexified in the displayed action.
The derivative is the actual weak coordinate derivative. One constant `C`
works for every positive input scale, `t` in `[0, 1/2]`, unit direction,
coordinate, and admissible inputs. `PressureKernelSwap.lean` exchanges the
two displacement blocks and flips the bilinear inputs by a proved
measure-preserving transformation. This preserves kernel mass and swaps
the Fourier arguments; it does not assume symmetry of the original kernel.
The resulting right-input reconstruction gives the second-coordinate identity
and the corresponding estimate with the second derivative input.
`GaussianRootWeakPressureAction.lean` instantiates both equalities at the
actual localized root-vorticity field.
`PressureWeakFieldAudit.lean` checks the normalization, vanishing of the
constant-input derivative channel, L²-only projection inputs, empty vector
dimension, and the root-field instance.

### Integrated channel patch sums retain the two-point density

`Analysis/BilinearTranslatedFamilyEnergy.lean` bounds the finite sum of
output-square integrals using a common kernel envelope and the actual sum
of shifted input-product squares. Boundedness of the partner inputs proves
integrability but their individual suprema do not enter the displayed bound.
There is no extra factor for the number of patches. Both input slots are
covered, without a symmetry premise.

For the actual root fields `F_i = c_i omega`,
`GaussianRootWeakChannelBudget.lean` defines and proves integrability of

```text
rho_j(y,z) = |omega(z)|² sum_i c_i(z)² |partial_j F_i(y)|².

(2 pi N)² integral_x sum_i |first-channel_i(x)|²
  <= mass(M) integral_x integral_q M(q) rho_j(x-a(q), x-b(q)),

(2 pi N)² integral_x sum_i |second-channel_i(x)|²
  <= mass(M) integral_x integral_q M(q) rho_j(x-b(q), x-a(q)).
```

Here `a,b` are the two actual torus displacements and each patch uses its
frozen unit strain direction. `exists_uniform_channel_sum_envelope`
constructs one envelope carrying both estimates, the uniform mass bound
`mass(M) <= C ratio(t)`, and the capped first moment
`integral |q| M(q) <= C min(ratio(t)/2, 1/N)`.

The new tests check nonzero kernel families, both displacement orders,
second-slot constant-input cancellation, and integrability of the actual
two-point cost. A separate algebraic example shows why pointwise
normalization alone does not permit moving weights between the two points;
it is not a counterexample for an actual root field or PDE solution.

### Gaussian overlap controls the two-point derivative density

`Analysis/ExponentialAmplitudeOverlap.lean` proves the exact product identity
for normalized exponential amplitudes: the product is their total overlap
times the normalized weight at the average score. The overlap is at most
one. `Analysis/GaussianAmplitudeOverlap.lean` identifies that weight as the
Gaussian at the midpoint, since the common score offset cancels.

`Analysis/RootPartitionTwoPointEnergy.lean` uses this identity on the actual
derivatives of `b sqrt(gaussianAmplitude)`, then on the root-vorticity field.
`GaussianRootTwoPointDerivative.lean` instantiates the resulting inequality
at the localized weak coordinate derivatives. Writing `w(x) = |omega(x)|`,
`P` for the Euclidean coordinates of the squared-gap projector, `b` for the
common root-gap factor, and `H(y,z)` for the two-point Gaussian distance
moment, the bound is

```text
rho_j(y,z)
  <= 2 b(z)² w(z)³ w(y)³
       [2 |partial_j b(y)|² + b(y)² |partial_j P(y)|² H(y,z)/tau²]
     + 8 b(z)² b(y)² w(z)³ w(y) |partial_j omega(y)|².

H(y,z) <= 2 |P(y)-P(k)|² + |P(z)-P(k)|² + 3 tau log(card(centres))
         <= 4 |P(y)-P(k)|² + 2 |P(y)-P(z)|² + 3 tau log(card(centres)).
```

The moment bounds require positive temperature and hold for any chosen
centre `k`. They do not require a centre at the midpoint. One full-measure
set of derivative points works for every partner point and chosen centre;
the product-measure translation theorem justifies substituting the two
kernel displacements. The bound has no inverse vorticity norm and remains
valid at vorticity zeros. Its tests include opposite Gaussian centres and
both zero-vorticity positions.

The pointwise theorem does not by itself establish integrability.
`GaussianRootTwoPointIntegral.lean` supplies that step and the channel-energy
comparison below. The powers of vorticity, inverse temperature,
gap/projector derivatives, and logarithmic centre count remain explicit
costs, not dynamically controlled quantities.

### Relative moments preserve the low-output ratio

`Analysis/DensityLinearChange.lean` retains arbitrary scalar observables
under invertible linear density changes. `PressureCoherentRelativeMoment.lean`
uses the exact cancellation

```text
(u + rho^-1 v) - rho^-1 v = u
```

in the two input displacements. Thus the common long translation does not
produce an inverse-ratio loss in their separation. For each prescribed
moment order `m`, one nonnegative integrable envelope dominates all seven
coherent channels and every unit direction on a common full-measure set.
Writing `rho = ratio(t) = t/128`, for `N > 0` and `0 <= t <= 1/2` it satisfies

```text
integral M(q) dq                         <= C_m rho
integral |a(q)-b(q)|^m M(q) dq           <= C_m rho min(2^-m, N^-m)
integral |P(x-a(q))-P(x-b(q))|^2 M(q) dq <= C_2 rho L^2 min(1/4, N^-2)
```

The last line holds for an `L`-Lipschitz field `P`, with integrability
proved explicitly. `FrequencyPairRelativeMoment.lean` transfers the
relative moments to the torus using the wrapped difference, rather than
the sum of the separately wrapped displacements. Tests cover common
translations, the half-period cap, zero output ratio, input-scale squared
decay, and constant fields.

This supplies the bare separation estimate needed by the Gaussian
two-point bound. The full derivative-weighted Gaussian cost is now proved
integrable, but the relative-moment estimate has not yet been used to
quantitatively control all those products. No uniform-in-time Lipschitz
cost or dynamical strain budget is asserted.

### The full two-point cost bounds actual channel energies

`Analysis/BilinearTranslatedCoefficient.lean` preserves integrability of a
translated spatial density multiplied by a continuous two-point
coefficient. `GaussianMomentContinuity.lean` supplies the continuity of the
Gaussian moments, and `RootPartitionTwoPointIntegrability.lean` separates
the derivative cost into three such terms.

`GaussianRootTwoPointIntegral.lean` instantiates this decomposition with
the actual root-gap derivative, squared-gap projector derivative, and
vorticity derivative. With a summable third Fourier moment, each square
is spatially integrable. Compactness bounds coefficients only to establish
integrability; no coefficient supremum replaces the final cost.

Let `B_j(y,z)` be `twoPointBudget`, and let `E_c` denote the sum of the
actual localized channel-output square integrals, multiplied by
`(2*pi*N)^2` (`normalizedChannelEnergy`). One constructed envelope satisfies
the mass and relative-second-moment bounds above and

```text
E_first_j  <= C rho integral_x integral_q M(q) B_j(x-a(q), x-b(q))
E_second_j <= C rho integral_x integral_q M(q) B_j(x-b(q), x-a(q)).
```

Both right-hand integrands are integrable on the product space, and both
inner integrals are genuine on a common full-measure spatial set. Fubini
and the translated almost-everywhere comparison therefore apply. The
envelope simultaneously dominates all seven channels and every unit
direction. Tests include signed coefficients, zero vorticity, and the
zero-output endpoint for both actual channel energies.

This closes the integration step for the fixed-snapshot two-point bound,
not its dynamical affordability. The derivative/vorticity products still
need estimates suitable for the scale sums and signed time-integrated
misalignment budget. In particular, `rho = t/128` is the low-output
parameter here; it is not physical time.

### Field increments replace projector separation in both channel integrals

`SquaredGapProjectorIncrement.lean` converts the collision-safe operator
difference bound to Euclidean coordinate energy. For `P` the weighted
projector coordinates, `omega` the vorticity, and `S` the filtered strain,

```text
|P(y)-P(z)|^2 <= 6 (|omega(y)-omega(z)|/gamma)^2
                + 2400 (|omega(z)| |S(y)-S(z)|/gamma^2)^2.
```

`GaussianRootIncrementBudget.lean` constructs a finite cover of the actual
projector image. With cover radius `epsilon`, positive temperature `tau`,
and `m` centers, the Gaussian moment in the full derivative cost is at most

```text
4 epsilon^2 + 3 tau log(m)
  + 12 (|omega(y)-omega(z)|/gamma)^2
  + 4800 (|omega(z)| |S(y)-S(z)|/gamma^2)^2.
```

There is no positive-gap assumption and no inverse vorticity norm. The
gap-factor, projector, and vorticity derivatives remain in the cost. A
continuous-coefficient extension of the integrability helper proves the
replacement integrable, and both actual normalized channel energies are
bounded by its iterated integral with the appropriate endpoint order.
The regression applies these estimates to constructed centers and the
constructed common pressure envelope.

### Product-weighted increments and the remaining dynamical debt

`Analysis/RadialPower.lean` proves, in a real inner-product space, for every
natural number `n`, with `F_n(a) = ||a||^n a`,

```text
||F_n(a)-F_n(b)||² - ||a||^n ||b||^n ||a-b||²
  = (||a||^n-||b||^n)(||a||^(n+2)-||b||^(n+2)) >= 0.
```

The product-weighted comparison has constant one and includes zeros and
antipodal vectors. For `n=3`, the same module proves local Lipschitz
regularity, differentiability including at zero, and the derivative bound
`||D F_3(w)[v]|| <= 4 ||w||³ ||v||`.

`PeriodicWeightedIncrement.lean` applies this to continuous, locally
Lipschitz periodic real vector fields, using their actual almost-everywhere
coordinate derivatives. It proves integrability and

```text
I_f(y,z) = ||f(y)||³ ||f(z)||³ ||f(y)-f(z)||²,
G8(f)    = integral_x ||f(x)||⁶ sum_j ||D_j f(x)||²,

integral_x I_f(x-a,x-b) <= 48 ||a-b||_torus² G8(f),
integral_x integral_q M(q) I_f(x-a(q),x-b(q))
  <= 48 (integral_q ||a(q)-b(q)||_torus² M(q)) G8(f).
```

Here `M` is nonnegative and integrable with the stated relative second
moment; the translations are measurable. All iterated integrals are
justified by product integrability. The factor 48 is `16 * 3`: the cubic
derivative bound is squared, and the torus uses its wrapped sup norm.
No quantitative Lipschitz constant of `f` appears on the right. This is
not yet an extension to arbitrary Sobolev fields without the stated local
Lipschitz regularity.

`GaussianRootWeightedIncrement.lean` identifies the weak derivatives with
the actual full-vorticity Fourier derivatives and constructs one envelope
for all admissible snapshots, directions, channels and positive input
scales. The bare vorticity-increment bound retains

```text
48 * ratio(t) * C * min(1/4, N^(-2)) * G8(omega).
```

As in the kernel construction, `t` here parametrizes the frequency ratio,
not physical time. The full Gaussian channel cost is **not** the bare
increment. Its coefficient is

```text
A_j(y,z) = 24 B(z)² B(y)² ||D_j P(y)||² / (tau² gamma²).
```

The file proves an exact decomposition of the existing `incrementBudget`
into an explicit `remainderBudget` and `A_j(y,z) I_omega(y,z)`. It proves
the latter is at most `A_j(y,z) ||F_3(omega(y))-F_3(omega(z))||²`, retaining
the full coefficient. If an explicit bound `A_j <= A` is supplied, the
integrated **full** cost is at most the integrated remainder plus
`48 A * relativeSecondMoment(M) * G8(omega)`. Neither a dynamically
affordable `A` nor a time bound on `G8` has been constructed. The remainder
still includes strain increments, local derivatives, localization error
and the Gaussian entropy term. No patch-count or time-uniform estimate
is inferred from this decomposition.

`RadialPowerTests.lean` and `GaussianRootWeightedIncrementAudit.lean` check
zero, constant, coincident, antipodal, positive-defect, endpoint-order,
derivative and exact-cost-splitting cases, and audit the theorem axioms.

#### Restrictions on a proposed higher-moment closure

The candidate eighth-moment dissipation is a useful named debt, not an
already supplied energy budget. Kinetic energy and vorticity enstrophy
have different identities:

```text
(1/2) d/dt ||u||_2²     + nu ||omega||_2²        = 0,
(1/2) d/dt ||omega||_2² + nu ||grad omega||_2²   = integral <omega,S omega>.
```

Consequently `LocalKineticEnergy.energy_identity` is not the `p=2` case
of an `L^p` vorticity identity. At `p=8`, the required identity has stretching
source `integral ||omega||⁶ <omega,S omega>` and includes both `nu G8` and
the additional radial-gradient dissipation. `LocalVorticityEighthEnergy.lean`
now proves that identity for the actual local solution, as detailed below;
an affordable bound on its source remains open. The spatial increment lemma
alone supplies neither. Scaling the bare `G8` at fixed kinetic energy does not by itself
classify the full projector-weighted cost, whose other factors also scale,
or exclude estimates using signed cancellation.

#### Actual eighth-moment energy identity

`LocalVorticityEighthMoment.lean` defines the polynomial energy `|omega|^8`
and derives its frozen-material derivative from the full vorticity equation.
The spatial second-derivative identity retains the full gradient and the
additional radial gradient, without introducing a direction at vorticity
zeros. `LocalVorticityEighthSpatialBalance.lean` proves the polynomial
energy flux has zero periodic divergence and integrates the local balance.

Write

```text
E8(u) = integral |omega|^8,
G8(u) = integral |omega|^6 sum_j |partial_j omega|^2,
R8(u) = integral |omega|^4 sum_j <omega,partial_j omega>^2,
S8(u) = integral |omega|^6 <omega,S_full omega>.
```

The definition of `G8` uses exactly
`GaussianRootWeightedIncrement.weightedPalinstrophyDensity`, not a new
abstract payer. `LocalVorticityEighthContinuity.lean` proves joint continuity
of these densities, including the initial endpoint, from the common third
absolute Fourier-moment envelope. This envelope justifies convergence on
the local interval; it is not a bound uniform at a candidate singular time.

`LocalVorticityEighthEnergy.energy_identity` proves

```text
E8(u(t))/8 + nu integral_0^t G8(u(s)) + 6 nu integral_0^t R8(u(s))
  = E8(u_0)/8 + integral_0^t S8(u(s)).
```

Time integrability is derived using the periodic incompressible material
chain rule and continuity. A reusable endpoint-identity lemma extends
interior balances without a sign restriction on their integrands.
The physical-data theorem constructs a local solution satisfying this
identity from real, transverse, zero-mean periodic data with continuous
coordinate jets through order nine. No smallness or alignment hypothesis
is imposed, and no energy identity is supplied as a structure field.
This is a local periodic theorem, not either global A/B assertion.

An explicitly conditional absorption corollary shows the exact remaining
obligation: if signed stretching satisfies

```text
integral_0^t S8 <= (nu/2) integral_0^t G8 + remainder,
```

then `E8(t)/8 + (nu/2) integral_0^t G8 <= E8(0)/8 + remainder`.
The corollary neither proves this hypothesis nor controls the remainder.
The projector coefficient, strain-increment cost, scale summation and
global continuation still require independent estimates.
`LocalVorticityEighthAudit.lean` checks zero-vorticity, zero-viscosity,
initial-endpoint, sign and numerical-coefficient cases and audits the
generic calculus, local balance and actual-data declarations.

#### Signed exchange representation of the actual stretching source

`Analysis/SignedCrossKernel.lean` proves the exchange identity for an even
continuous kernel on a compact measured space. With `F_n(a)=|a|^n a`,

```text
|a|^n <a cross b,H a> + |b|^n <b cross a,H b>
  = <a cross b,H(F_n(a)-F_n(b))>.
```

The integrated identity includes the factor one half from exchanging
the endpoints. Collinear inputs give zero, including opposite directions
and zeros. Adding any scalar multiple of the identity to `H` changes
nothing. The cross product and signed radial difference are retained
before the separate absolute-value estimate.

`VorticityStretchingKernel.lean` constructs the finite periodic kernel

```text
P_k a = (<k,a>/|k|^2) k,                  P_0 = 0,
H_M(z) = sum_(k in M) Re(exp(2 pi i k.z)) P_k.
```

For real transverse velocity coefficients, its quadratic action on the
full physical vorticity equals the finite reconstruction of the actual
strain. The proof retains the physical Fourier phases and handles the
zero mode. Evenness holds for every finite set `M`; no symmetry assumption
on that set and no separately prescribed strain are required.

`FullStrainFourierSeries.lean` identifies the strain series with the
symmetric derivative of the full velocity and proves convergence over
finite frequency sets from one absolute velocity moment.
`VorticityWeightedStretching.lean` then proves

```text
S8(u) = lim_M (1/2) integral_x integral_y
  <omega(x) cross omega(y),
   H_M(x-y) (F_6(omega(x))-F_6(omega(y)))>.
```

The receiver at each endpoint is the full vorticity throughout. The limit
is outside the signed double integral; this does not assert existence of
an ordinary integrable infinite kernel or exchange that limit with the
double integral. The domination used for the limit depends on the current
absolute velocity moment, and is not a uniform dynamical bound. The
generic theorem applies to every natural radial weight and recovers the
exact `S8` in the preceding energy identity at weight six.

This supplies the actual source expression on which an alignment estimate
must act. It does not bound that expression by `G8`, construct a direction
modulus, or close any time budget. A fixed-line collinearity corollary
annuls the source, but its alignment hypothesis is not asserted for
arbitrary data. `VorticityStretchingAudit.lean` and
`Analysis/SignedCrossKernelTests.lean` check the physical local-solution
interface, exchange factor, zero mode, isotropic cancellation, endpoint
degeneracies and a nonzero signed triple product.

#### Bounded-amplitude payment with a signed high-amplitude remainder

For every natural `n`, `Analysis/RadialPower.lean` proves the pointwise
comparisons, including zero and opposite endpoints,

```text
max(|a|,|b|)^n |a-b| <= 2 |F_n(a)-F_n(b)|,
|F_(2n)(a)-F_(2n)(b)| <= 2 max(|a|,|b|)^n |F_n(a)-F_n(b)|.
```

Combining these with `|a cross b| <= min(|a|,|b|)|a-b|` gives

```text
|<a cross b,H(F_(2n)(a)-F_(2n)(b))>|
  <= 4 min(|a|,|b|) ||H|| |F_n(a)-F_n(b)|^2.
```

`VorticityRadialSourceBound.lean` applies the estimate to the actual
periodic vorticity and finite strain reconstruction. The remaining
smaller-endpoint amplitude is explicit; no vorticity supremum has been
declared controlled. At `n=3`, `PeriodicWeightedIncrement.lean` bounds the
spatial integral of the squared `F_3` increment by `48 |h|^2 G8`.

`VorticityHighAmplitudeSource.lean` defines, for a positive threshold `L`,

```text
m(a,b) = min(|a|,|b|),
theta_L(a,b) = L / max(L,m(a,b)),
Q_M(a,b) = <a cross b,H_M(x-y)(F_6(a)-F_6(b))>,
High_(L,M) = (1/2) integral_x integral_y (1-theta_L(a,b)) Q_M(a,b),
M2(M) = integral_h |h|^2 ||H_M(h)||,
```

where `a=omega(x)` and `b=omega(y)`. The continuous symmetric weight
satisfies `0 <= theta_L <= 1` and `theta_L m <= L`. The high-amplitude
integrand retains its sign and is zero if either endpoint has norm at
most `L`. Haar translation and the weighted increment estimate give

```text
|S8_M - High_(L,M)| <= 96 L M2(M) G8.
```

For `nu>0`, the explicitly constructed
`L_M = nu / (192 (M2(M)+1))` is positive and yields

```text
S8_M <= (nu/2) G8 + High_(L_M,M).
```

These are actual-field statements from a third absolute velocity moment,
reality and transversality, with a regression at a local physical solution.
They do not impose an alignment hypothesis. **The estimate is at each
finite strain cutoff.** No uniform bound on `M2(M)`, positive lower bound
on `L_M` as the cutoff grows, cutoff limit of `High_(L_M,M)`, or dynamical
payment for that signed remainder is proved here. The existing limit of
`S8_M` alone does not supply any of these missing estimates.

#### A resolution-independent increment payment

`Analysis/AnnularRieszKernel.lean` constructs Schwartz inverse Fourier
kernels of the normalized compact annular symbols
`phi(xi) xi_i xi_j / |xi|^2`. A buffered denominator proves global
smoothness without changing the symbol on the annulus. The dyadic
scales start at `1/2`, not `1`, to include the whole lowest nonzero
integer-frequency shell. Their second moments form a geometric series:

```text
lambda_n = 2^n / 2,
integral |x|^2 |k_ij,n(x)| = 4 (1/4)^n C_ij,
integral |x|^2 |sum_(n<N) k_ij,n(x)| <= (16/3) C_ij.
```

`Analysis/UnitTorusLattice.lean` and `UnitTorusPeriodization.lean` provide
dimension-independent lattice geometry, Haar integration, Fourier
coefficient transfer and weighted periodization. Applying them gives
actual periodic scalar kernels whose Fourier coefficients are
`w_N(k) k_i k_j / |k|^2`. The real even weights lie in `[0,1]` and tend
to `1` at every nonzero lattice mode; the zero coefficient is zero.
`Analysis/PeriodicRieszOperator.lean` assembles their real parts and
symmetrizes opposite displacements to construct real even operators
`H_N`, with a single constant independent of `N` and of the velocity:

```text
C = (16/3) sum_ij C_ij,
integral_h |h|^2 ||H_N(h)|| <= C.
```

For the actual periodic vorticity and a third absolute velocity moment,
`VorticityRegularizedIncrement.lean` proves

```text
I_N = integral_h ||H_N(h)|| integral_x |F_3(omega(x))-F_3(omega(x-h))|^2,
I_N <= 48 C G8,
L_nu = nu / (192 (C+1)) > 0                   (nu>0),
2 L_nu I_N <= (nu/2) G8                      (every N).
```

This uniform increment payment now applies to the actual signed source.
`VorticityRegularizedConvolution.lean` and
`VorticityRegularizedQuadratic.lean` identify the integrable real-even
operator acting on the full vorticity, including its exact Fourier series.
`VorticityRegularizedSource.lean` proves that the resulting weighted source
converges to actual stretching. `VorticityRegularizedPairing.lean` proves
the source-receiver exchange identity with joint integrability, without
assuming continuity of the periodized kernel. In particular, with
`F_n(a) = |a|^n a`,

```text
S_(n,N) = (1/2) integral_x integral_y
  <omega(x) cross omega(y), H_N(x-y) (F_n(omega(x))-F_n(omega(y)))>,
S_(6,N) -> S8.
```

`VorticityRegularizedPayment.lean` uses the symmetric weight
`l_L(a,b) = L / max(L,min(|a|,|b|))` and retains the signed remainder
`R_(L,N)` obtained by multiplying the paired integrand by `1-l_L`:

```text
|S_(6,N) - R_(L,N)| <= 2 L I_N,
S_(6,N) <= (nu/2) G8 + R_(L_nu,N)             (every N).
```

The same positive `L_nu` works for all cutoffs and fields. The remainder's
integrand vanishes when either endpoint vorticity norm is at most `L_nu`.
A uniform upper bound `R_(L_nu,N) <= b` would pass to
`S8 <= (nu/2) G8 + b`; this conditional implication is checked and does
not require convergence of the remainder itself. Constructing a signed
time-integrated remainder bound from the unforced dynamics remains open.
The fixed-snapshot domination used for the source limit is not such a
bound. No uniform unweighted kernel mass, vorticity supremum, alignment
modulus or global-in-time palinstrophy bound is inferred.

`Analysis/PeriodicRieszKernelTests.lean` checks normalization, the unit
frequency shell, zero mode, symmetry and dimension-independent moment
uniformity. `VorticityRegularizedAudit.lean` checks the same threshold
at every cutoff for actual local-solution coefficients.
`VorticityRegularizedSourceAudit.lean` checks source convergence, a threshold
chosen before time and cutoff, the zero-endpoint case, and the explicitly
conditional remainder-to-source implication at those same coefficients.
`Analysis/PeriodicRieszOperatorFourierTests.lean` checks zero frequencies,
dimension-independent operator assembly and integrable-kernel convolution.

#### Actual two-point angle dynamics and its spectral-defect cost

`LocalVorticityPairAngle.lean` derives the evolution of the cross product
appearing in that signed source along two actual material trajectories.
Write `a=omega(X(t))`, `b=omega(Y(t))`, `S=S(X(t))`, `T=S(Y(t))`,
`f=nu Delta omega(X(t))`, and `g=nu Delta omega(Y(t))`. Then

```text
c = a cross b,
F = a cross ((T-S)b) + f cross b + a cross g,
c' = -S c + F.
```

The common-strain cancellation uses actual incompressibility and strain
symmetry. Both strain variation and viscosity remain in `F`. For nonzero
endpoints, put `q=|c|^2/(|a|^2|b|^2)` and let `lambda` be the top eigenvalue
of `S`. The checked derivative estimate is

```text
d_S(v) = (lambda |v|^2 - <v,Sv>) / |v|^2,
q' <= 2 (d_S(a)+d_S(b)) q + P,
P = 2 <c,F>/(|a|^2|b|^2)
    - 2 q (<a,f>/|a|^2 + (<b,(T-S)b>+<b,g>)/|b|^2).
```

`TraceFreeStrainAngle.lean` proves the underlying bound
`<v,Sv> >= -2 lambda |v|^2` and the common-strain estimate. Both defects
above refer to the **same strain at the first endpoint**; the difference
from the other strain remains explicit in `P`. No inverse spectral gap or
global direction modulus is used. The actual trajectory theorem uses the
existing local third-moment envelope needed for differentiating full
vorticity; it does not assert such an envelope up to a singular time.

`LocalVorticityPairAngleSymmetric.lean` improves this to endpoint-local
defects by averaging the two exact equations, before taking any bounds:

```text
F_sym = (1/2) (a cross ((T-S)b) + ((S-T)a) cross b)
        + f cross b + a cross g,
c' = -(1/2) (S+T)c + F_sym,
gap_S = lambda_top(S) - lambda_middle(S),
q' <= [2 (d_S(a)+d_T(b)) - (gap_S+gap_T)] q + P_sym,
P_sym = 2 <c,F_sym>/(|a|^2|b|^2)
        - 2 q (<a,f>/|a|^2 + <b,g>/|b|^2).
```

Thus each endpoint's own normalized top spectral defect competes with
the sum of the top gaps. The sharper Rayleigh lower bound is
`<v,Sv> >= (gap_S-2 lambda_top(S)) |v|^2`, since the coefficient equals
the bottom eigenvalue for trace-free three-dimensional strain. The damping
term survives without division by a gap, including at collisions.
No top-eigenvalue difference or exchanged strain defect remains.
`P_sym` is still signed and unpaid; the averaging is not a proof that
strain variation or viscosity is favorable. Dropping the nonnegative gap
terms recovers the weaker pure-growth estimate.

The estimate is not universal damping. The exact rational regression takes
`S=diag(2,-1,-1)`, `a=(3/5,0,4/5)`, `b=(-3/5,0,4/5)`. Both vectors have
unit norm and positive stretching `2/25`, yet their common-strain
squared-angle rate is `24192/15625 > 0`. An actual first-variation witness
is checked. This refutes an angle-monotonicity shortcut for prescribed
strain, not the repaired route or an actual Navier–Stokes solution.

`LocalVorticityPairAngleAudit.lean` checks the derivative and spectral
statements, including the zero-endpoint definition of `q`. The remaining
task is to control the signed perturbation and normalized spectral costs
in the high-amplitude source's time integral. An instantaneous angle
equation, by itself, does not supply this budget or close S4.

#### Signed source evolution: kernel commutator and radial amplification

`LocalPairedStretchEvolution.lean` differentiates the paired source along
two actual material trajectories. Both vorticities are the full solution's
vorticity, not finitely truncated vorticities. Here the kernel is the finite
real-character reconstruction from `VorticityStretchingKernel.lean`, whose
spatial pairing is already identified with `finiteStretching`.
`VorticityKernelTransport.lean` derives its transport from the actual
velocity difference, rather than assuming Fourier-phase derivatives.

At radial exponent six, write `A=|a|^6 a`, `B=|b|^6 b`, `r=A-B`,
`c=a cross b`, and `M=(S+T)/2`. The exact signed identity is

```text
Q = <c,Hr>,
Q' = <c,(Hdot + H M - M H)r>
     + <F_sym,Hr> + <c,H R_rad>,
R_rad = (1/2)(S-T)(A+B)
        + 6|a|^4<a,Sa>a - 6|b|^4<b,Tb>b
        + DF_6(a)[nu Delta a] - DF_6(b)[nu Delta b].
```

`Hdot` is the kernel derivative under the relative material velocity.
The commutator sign is `H M - M H`. Common strain cancels from the
linear-vector part, but radial amplitude growth remains. Even powers are
differentiated through powers of the squared norm, so this unnormalized
identity also applies at zero vorticity.

For `sigma=1-L/max(L,min(|a|,|b|))`, on the strict branch
`L < |a| < |b|`, the actual high-amplitude integrand has derivative

```text
(sigma Q)' = sigma Q' + sigma' Q,
sigma' = L <a,Sa+nu Delta a> / |a|^3.
```

The other strict branch is also checked, with the endpoints exchanged.
No derivative is asserted at a threshold or equal-amplitude interface.
The normalization term is not assumed to be dissipative.

`Analysis/SignedCrossKernelEvolutionTests.lean` checks a precise warning
against transferring angular decay directly to source decay. For common
strain `diag(2,-1,-1)`, unit endpoints `(4/5,0,3/5)` and `(4/5,0,-3/5)`,
and the commuting positive rank-one operator `H=e e^T`, `e=(0,1,1)`,

```text
q' = -24192/15625 < 0,
Q  = 144/125 > 0,
Q' = 19872/3125 > 0.
```

Both values are actual first derivatives of explicitly defined test curves
with the prescribed strain velocities at zero. The generic identity is
`Q' = 6 alpha Q` when the two Rayleigh quotients equal `alpha` and the
fixed kernel commutes with the common strain. This is a prescribed-strain
counterexample to a source-decay shortcut, not a self-consistent fluid
solution or a refutation of the repaired route.

`LocalPairedStretchAudit.lean` checks actual-solution source identification,
empty-cutoff behavior, kernel transport and both strict amplitude branches.
The signed spatial/time estimate is still open. In particular, these
identities do not yet supply a cutoff-uniform transport bound or the
argument needed to pass across amplitude interfaces and integrate.

#### The same annular kernel in the source payment and material derivative

`Analysis/AnnularRieszFourierSupport.lean` proves that the partial annular
multiplier vanishes outside an explicit finite coordinate box.
`Analysis/UnitTorusFourierL1Uniqueness.lean` proves Fourier uniqueness and
finite reconstruction almost everywhere for integrable fields; it does
not assume that the periodization is continuous or square integrable.
`Analysis/PeriodicRieszPolynomial.lean` then constructs the finite real
Fourier representative and identifies it almost everywhere with the
constructed periodized operator. It has exact evenness and satisfies

```text
integral |h|^2 ||H_N(h)|| <= secondMomentBound 3,
```

with the same constant, independent of `N`. Its zero-cutoff kernel is zero.
Spatial integrals involving arbitrary nonlinear tests of `H_N(x-y)` are
unchanged by this replacement. This is deliberately not an assertion that
almost-everywhere equality can be differentiated along arbitrary paths.

`VorticityAnnularKernelTransport.lean` proves smoothness of the lifted
representative and its actual Fourier derivative under relative material
velocity. `VorticityAnnularPolynomialSource.lean` identifies its signed
paired source and high-amplitude remainder with the previous regularized
objects. Thus the existing positive viscosity-dependent threshold pays
the low-amplitude source at every cutoff without changing the constant,
and the paired sources still converge to actual full stretching.

`LocalAnnularStretchEvolution.lean` derives the signed source derivative
along actual material trajectories for this same representative. The
kernel commutator, radial amplification and both viscous terms above
remain present. Both strict amplitude-cutoff branches are also checked.
The common full-vorticity derivative is factored through
`LocalPairedStretchEvolution.hasDerivAt_pairedStretch_path_of_kernel` so
the two kernel realizations use the same actual-solution argument.

`LocalAnnularStretchAudit.lean` checks this connection, the preserved
dissipation threshold and zero-cutoff behavior. The next missing step is
the signed spatial/time estimate, including amplitude interfaces; smooth
finite kernels do not by themselves give a cutoff-uniform derivative
bound or the dynamical misalignment budget.

#### A signed time-integrated remainder is sufficient

`LocalAnnularSourceContinuity.lean` proves continuity of the actual paired
and high-amplitude sources in time, including amplitude interfaces.
`VorticityRegularizedSourceBound.lean` supplies a cutoff-independent local
dominating function for the paired source from the common Fourier envelope.
`LocalAnnularSourceIntegral.lean` uses it to pass the paired-source limit
through the time integral. This is a local dominated-convergence argument,
not a uniform bound on the Fourier envelope near a possible singular time.

For `L_nu = dissipationThreshold nu`, write `R_N(t)` for the existing signed
high-amplitude source. The checked sufficient hypothesis is now only

```text
for every N, integral_0^t R_N(tau) d tau <= remainder.
```

It yields, for the actual periodic local solution,

```text
E8(t)/8 + (nu/2) integral_0^t G8(tau) d tau <= E8(0)/8 + remainder.
```

There is no assumed pointwise remainder envelope and no assumed convergence
of the remainders. Their signs are retained. The local Fourier dominating
constant does not occur in the resulting energy bound. Constructing an
appropriate remainder budget from the unforced dynamics remains open.

`Analysis/HighAmplitudeWeightRegularity.lean` proves that the high-amplitude
weight is globally Lipschitz with constant `1/L`, across both threshold and
equal-amplitude interfaces. `Analysis/RadialPowerRegularity.lean` proves
smoothness of even radial powers on real inner-product spaces, including
at zero. `Analysis/SignedCrossKernelRegularity.lean` combines these facts
with the smooth signed pairing.
`LocalAnnularSourcePathIntegral.lean` then proves absolute continuity of
the actual high-amplitude source along locally Lipschitz spatial paths on
compact interior time intervals, integrability of its total derivative,
and the exact fundamental-theorem-of-calculus identity. No interface-null
assumption is needed. This does not yet identify the derivative on the
interfaces, integrate the material formula in space, or bound its signed
time integral uniformly in the cutoff.

`LocalAnnularSourceIntegralAudit.lean` and
`Analysis/SignedCrossKernelRegularityTests.lean` check the integrated
implication, persistent equal-amplitude paths and foundational dependencies.

#### The explicit material rate includes the cutoff interfaces

`Analysis/DerivativeContact.lean` proves equality of derivatives when two
differentiable real functions touch under a local ordering.
`Analysis/HighAmplitudeWeightChainRule.lean` applies this at a tie: above
threshold the cutoff touches either endpoint branch, so their derivatives
agree wherever the cutoff is differentiable. At or below threshold the
nonnegative cutoff touches zero and its derivative is zero. Absolute
continuity gives the resulting rule almost everywhere without assuming
the threshold or equal-amplitude sets have measure zero.

The rate selects the smaller endpoint above threshold and is zero otherwise.
Endpoint-exchange symmetry is proved under the differentiable-contact
hypotheses. The raw branch-selected algebraic rate is not symmetric for
arbitrary unrelated endpoint derivative data; an explicit regression checks
this distinction.

`LocalAnnularSourcePathChainRule.lean` combines this cutoff rate with the
actual full-vorticity equations and the annular paired-source derivative.
It proves integrability of the full explicit material rate along locally
Lipschitz material paths and the exact signed identity

```text
integral_a^b materialHighAmplitudeRate(t) d t
  = highAmplitudeSourceAlong(b) - highAmplitudeSourceAlong(a).
```

The mean-strain kernel commutator, actual relative-velocity kernel transport,
radial amplitude growth, strain variation and both viscous terms remain.
`LocalCompactMaterialPath.lean` constructs suitable paths through arbitrary
prescribed lifted points from the actual local velocity; their constant
extension outside the compact interior interval does not extend the PDE.
`LocalAnnularMaterialPaths.exists_paths_integrated_source_identity` constructs
both paths and proves the identity for every finite annular cutoff and every
positive amplitude threshold. Path existence and regularity are conclusions,
not additional geometric assumptions.

`Analysis/AbsolutelyContinuousTimeWeight.lean` applies integration by parts
without taking absolute values. The same constructed paths also satisfy

```text
integral_a^b sourceAlong(t) d t
  = (b-a) sourceAlong(a) + integral_a^b (b-t) materialRate(t) d t.
```

Thus the accumulated source, rather than just its endpoint change, is linked
to the explicit signed material rate. Integrability of the weighted rate is
proved, not assumed.

This pathwise theorem does not itself provide a spatial mean balance.
The following weak-transport argument supplies that balance independently;
no measure-preservation theorem for a chosen flow is assumed.

### Signed two-point spatial mean balance

`Analysis/UnitTorusWeakDerivative.lean` and
`Analysis/UnitTorusMaterialBalance.lean` generalize the periodic weak
calculus to arbitrary finite coordinate index types. Rademacher
differentiability descends through the measured fundamental cube, Haar
translation invariance gives integration by parts, and zero divergence
cancels transport. The compact-mean differentiation lemma is shared with
the existing one-point development.

`Analysis/UnitTorusProductTransport.lean` identifies the sum-index torus
with two spatial endpoints, preserves product Haar measure, and proves
that the product velocity's divergence is the sum of the endpoint
divergences. `LocalAnnularMeanBalance.lean` applies this to the actual
full-vorticity source and both actual full velocities. On every compact
interior interval, at each finite annular cutoff and positive threshold,

```text
R_N(t) = (1/2) integral_(x,y) highAmplitudeStretch_(2n)(t,x,y)
R_N(b) - R_N(a) = integral_a^b meanMaterialRate_N(t) d t
integral_a^b R_N(t) d t
  = (b-a) R_N(a) + integral_a^b (b-t) meanMaterialRate_N(t) d t.
```

Here the material rate is the actual derivative along the instantaneous
two-endpoint velocity, not an assumed algebraic source. Its spatial
integrability almost everywhere in time, time integrability, and weighted
time integrability are conclusions. The nonsmooth threshold and
equal-amplitude interfaces are retained.

This theorem concerns the original local solution, not its temporary
constant time extension. `LocalAnnularWeightDifferentiability.lean` proves
the cutoff's frozen material differentiability almost everywhere in
spacetime. `LocalAnnularExplicitRate.lean` then uses straight tangent
curves and the actual vorticity equation to identify the spatial rate with
the full strain/commutator/diffusion formula, including amplitude contacts.
`LocalAnnularExplicitMean.lean` transfers spatial integrability and both
signed integral identities to that explicit formula. The eighth-moment
source uses mean-density index `3` and explicit-rate index `2`.

`LocalAnnularRateDecomposition.lean` separates the actual rate algebraically
into strain, relative-velocity kernel transport, and viscosity times an
endpoint-increment channel. It preserves signs and does not assert that
the viscosity channel is individually nonpositive. At ties the separated
pieces are not independent chain rules; the full rate is what was proved
to equal the material derivative. An exact radial-decay test demonstrates
why decreasing amplitudes alone do not imply a decreasing signed source.

Estimating the combined signed time budget uniformly in cutoff and toward
a maximal existence time remains the decisive open obligation. These local
identities do not supply that bound. `LocalAnnularExplicitAudit.lean` checks
the identification, the integral laws, the algebraic split and zero-cutoff
behavior; `LocalAnnularPathChainRuleAudit.lean` checks constructed paths.

#### Common-translation diffusion without a kernel derivative

`LocalPairedDiffusion.lean` fixes the endpoint separation and translates
both actual full-vorticity fields together. The second derivative splits
into the endpoint-Laplacian contribution and an explicit signed quadratic
curvature in the two vorticity gradients. Periodic integration cancels
the full translation derivative.

`LocalAnnularDiffusion.lean` changes back to the two-endpoint integral and
applies the same finite annular kernel used in the stretching source. It
proves `diffusionSource = -curvatureSource`; the viscous contribution is
therefore `-nu * curvatureSource`. Here index `n = 1` gives the radial
exponent six used by the eighth-moment source. No spatial derivative of the kernel or
receiver truncation appears. The scalar curvature vanishes on the diagonal
and when both vorticities and both gradients lie on one common line.

This calculation concerns the smooth paired source before amplitude
cutoff. It does not justify a second-order chain rule through the cutoff's
threshold or tie surfaces, and does not prove positive curvature or a
uniform dynamical bound. The signed curvature must still be estimated
jointly with the strain and relative-transport channels. The exact radial
second-variation test and zero-annulus tests are checked by
`LocalAnnularDiffusionAudit.lean`.

`LocalAnnularCurvatureIncrement.lean` retains the actual gradient increment
when the two endpoint vorticities agree. With radial exponent six, the
pointwise bound has coefficient fourteen and contains both the transverse
cross product and the gradient increment norm. This is not a bound by the
eighth-moment dissipation alone. Isotropic kernel action vanishes before
estimating the norm.

The same module proves `curvatureSource n N (-u) = -curvatureSource n N u`
for the actual spatial integral. Consequently, a nonnegative-curvature
claim on any negation-closed class of Fourier data would force this source
to vanish throughout that class. The scalar positive-semidefinite rank-one
tests exhibit both curvature signs at equal unit endpoint values; they
are not self-consistent fluid fields. `LocalAnnularCurvatureAudit.lean`
checks these separate levels of evidence.

The exact rational Fourier diagnostic `papers/benxiv/ns_paired_source_heat_sign.py`
uses the smooth divergence-free field
`u = (sin(y), 0, sin(x) + sin(x+y))` on the `2*pi` periodic torus.
Its normalized eighth-moment stretching is `-3289/128`; its derivative
along the viscosity-one heat tangent is `22289/64`. Both signs reverse for
`-u`. This calculation has no quadrature error, but its correspondence to
the Lean integral definitions is not yet proved. It tests the isolated
signed heat channel, not the full nonlinear evolution or growth of the
absolute stretching source. The cutoff-uniform signed budget remains open.

#### Smooth amplitude retention with unchanged low-part payment

`SmoothAmplitudeCutoff.lean` constructs `q_L(a) = |a|^2 / (L^2 + |a|^2)`
and the symmetric pair weight `q_L(a) q_L(b)`. For every positive threshold,
`(1 - q_L(a) q_L(b)) min(|a|, |b|) <= L`; the complement is no larger than
the old low-amplitude weight. Both weights and the even-exponent retained
pairing are smooth, including at zero and equal-amplitude inputs.

`VorticitySmoothAmplitudeSource.lean` uses the actual annular polynomial
kernel and full vorticity. Its complementary source is bounded by
`2 L * incrementIntegral`, so the existing `dissipationThreshold nu`
pays it with exactly `nu / 2 * weightedPalinstrophy`, uniformly in the
annular cutoff and the admissible field. It also proves twice continuous
differentiability along actual common spatial translations.

`LocalSmoothAmplitudeSource.lean` proves time continuity through the initial
endpoint and the same actual L8 energy reduction from a time-integrated,
cutoff-independent upper budget on this smooth retained source. That budget
remains a hypothesis. The first and second rational-weight variations are
explicit in `SmoothAmplitudeCutoffEvolution.lean`; their curvature is signed.

This is an additional, proved-sufficient source split, not an identity with
the original high-amplitude source. It retains nonzero weight below the
threshold. The original split is unchanged, and its unresolved second-order
interface terms are not discarded. The smooth variant permits ordinary
second-order calculus, but its nonlinear derivative costs and their joint
time affordability still require proof. `LocalSmoothAmplitudeAudit.lean`
checks the construction, actual-field payment, local energy reduction and
zero/subthreshold/threshold tests separately.

#### Complete smooth-retention curvature and material channels

`SmoothAmplitudePairingEvolution.lean` makes the full second-order product
rule explicit. For the retained pairing `sigma * Q`, its first-gradient
curvature is `sigma * K_Q + 2 * Dsigma * DQ + K_sigma * Q`.
At equal endpoint values, `Q` and `DQ` vanish, but `K_Q` can survive through
the gradient increment. The exact formula and isotropic-kernel cancellation
are proved. Positive rank-one algebraic tests give both signs even after
retention; they are not claimed to be actual fluid fields.

`LocalSmoothPairedDiffusion.lean` applies both derivatives to the full
vorticity along common spatial translations. Periodicity cancels the
complete second derivative. `LocalSmoothAnnularDiffusion.lean` then proves
`diffusionSource = -curvatureSource` for the actual finite annular kernel,
including all weight-curvature and mixed terms. The diffusion calculation
has no kernel derivative; this does not remove relative-velocity kernel
transport from the material evolution.

`LocalSmoothSourceEvolution.lean` proves the actual local material-path
derivative, including zero and amplitude-tie contacts, and separates strain,
relative kernel transport, and viscosity without absolute values. Its
eighth-moment viscosity channel is exactly `diffusionDensity 1` above.
The common-strain commutator remains visible in `retainedStrainRate`.
The joint time-integrated nonlinear estimate remains to be proved. No bound
on curvature or the signed time budget follows from these identities.
`LocalSmoothDiffusionAudit.lean` audits the actual derivative and spatial
identity separately from the generic algebra and sign tests.

#### Actual signed time identity for smooth retention

`LocalSmoothMeanRegularity.lean` supplies spacetime continuity, a locally
Lipschitz lift, and absolute continuity of the actual two-point spatial
mean on each compact interior time interval. The constant time extension
is a calculus device, not a global NS solution.

`LocalSmoothMeanBalance.lean` identifies the frozen material derivative
pointwise using paths tangent to the full velocity. The existing actual
product velocity is divergence-free; periodic transport then gives the
mean derivative almost everywhere, its endpoint integral identity, and
the exact signed time-weighted source identity.

`LocalSmoothMeanChannels.lean` keeps strain and relative kernel transport
grouped as `nonviscousRate`. Its integrability is derived from the actual
material rate and the continuous diffusion channel, not assumed as a new
budget. After the complete spatial integration-by-parts identity,
`jointRate = integral nonviscousRate - nu * curvatureSource` is the actual
retained-source derivative almost everywhere. For each fixed annular
cutoff and positive amplitude threshold, the checked identity is

```text
integral_a^b retainedSource(t) dt
  = (b-a) retainedSource(a) + integral_a^b (b-t) jointRate(t) dt.
```

Here `a <= b` and `[a,b]` is contained in the local solution's open time
interval. The joint weighted rate is proved integrable; separate absolute
channel payments are not required. This equality is not the required
initial-data-controlled upper estimate. The initial endpoint passage and
uniformity up to a possible finite singular time still need justification
in that estimate. `LocalSmoothMeanAudit.lean` checks these distinctions.

#### Concentration test for an instantaneous energy-only closure

The reproducible symbolic diagnostic
[`ns_eighth_moment_scaling.py`](../../../scripts/ns_eighth_moment_scaling.py)
uses the smooth, rapidly decreasing, divergence-free velocity on `R^3`

```text
u = curl(exp(-|x|^2) (0,x*z,3*x*y))
  = exp(-|x|^2) (-6*x*y^2+2*x*z^2+2*x, 6*x^2*y-3*y, -2*x^2*z+z).
```

Exact rational Gaussian-moment arithmetic gives

```text
S8 = (9959571879362560 / 282429536481) (pi/9)^(3/2) > 0.
```

For `u_r(x)=r^3 u(r^2 x)`, `r>0`, the integral scaling powers are

| Quantity | Definition | Power of `r` |
| --- | --- | --- |
| `K2` | `integral |u|^2` | 0 |
| `Z2` | `integral |omega|^2` | 4 |
| `E8` | `integral |omega|^8` | 34 |
| `G8` | `integral |omega|^6 |grad omega|^2` | 38 |
| `R8` | `integral |omega|^4 sum_j <omega,partial_j omega>^2` | 38 |
| `S8` | `integral |omega|^6 <omega,S omega>` | 39 |

Thus a universal instantaneous inequality
`S8 <= nu (G8+6 R8) + C(K2,nu) Z2 E8`, with a finite constant depending
only on the fixed energy and viscosity, fails under concentration.
Adding `C(K2,nu) E8` does not repair its scaling. The script checks the
curl, divergence, strain, symbolic derivative scaling, and independent
Gaussian integration-by-parts identities; run it with Python and SymPy.

This is a **symbolic initial-data diagnostic, not a Lean-verified
counterexample or a constructed time-evolving NS solution**. Its domain
is `R^3`; no periodic counterexample is asserted. It excludes this
particular energy-only instantaneous ansatz, not a signed time-integrated
bound with appropriate initial-data dependence, a conditional coherence
criterion, or global regularity itself.

#### Endpoint and forcing restrictions

A proposed endpoint argument using `I_(3/2): L²(R³) -> L∞(R³)` cannot use
the strong Hardy--Littlewood--Sobolev bound at that endpoint. For the
unnormalized kernel `|x|^(-3/2)`, the explicit functions

```text
g_epsilon(y) = |y|^(-3/2) 1_{epsilon<|y|<1} / sqrt(log(1/epsilon))
```

have squared `L²` norm `4 pi` but potential at zero
`4 pi sqrt(log(1/epsilon))`. Each potential is continuous near zero, so
this also obstructs an essential-supremum bound, not just point evaluation.
This elementary analytic check is not a Lean declaration in this update.
Moreover a direct global Hölder modulus of exponent greater than one
forces a direction projector to be locally constant on its nonzero region;
it is not an appropriate generic target for arbitrary data.

Uniformity in `p` as `p -> infinity` is not necessary for every continuation
argument. The whole-space one-half-Hölder direction criterion already gives
conditional regularity; see [Beirao da Veiga's review, Theorem 2](https://people.dm.unipi.it/beiraodaveiga/pdf/hbv-116.pdf).
Its hypotheses and domain must be retained in any translation. The missing
step here is proving an adequate dynamical coherence or signed source bound,
not imposing that criterion on arbitrary initial data.

Finally, forcing-insensitive spatial lemmas can be essential parts of an
unforced proof. A forced counterexample excludes only a complete chain whose
**entire** hypotheses it satisfies. Smooth forcing can still permit finite
energy and integrated enstrophy bounds on finite horizons; finiteness of
those quantities alone does not distinguish regularity. The unforced
equation must enter the successful dynamic estimate, but the monotone
kinetic-energy identity is not the only logically possible way to use it.

### A periodic concentration obstruction to an energy-only shortcut

`Analysis/FiniteFourierConcentration.lean` proves a cubic lower bound for
the convolution energy of unit coefficients on an embedded integer
interval. `PeriodicFourierProductConcentration.lean` transfers this through
the actual unit-torus Parseval identity to explicit mean-zero packets:

```text
f_n(x) = exp(2 pi i (2n+1) x_1) sum_{k=0}^{2n} exp(2 pi i k x_1)
integral |f_n|^2 = 2n+1
integral |f_n|^4 >= (n+1)^3.
```

The frequencies lie on one axis between `2n+1` and `4n+1`. Normalization
also constructs mean-zero continuous periodic fields with square energy
exactly one and fourth-power energy larger than any prescribed constant.
Thus no universal constant can bound a product's square energy using
only the two input square energies, even on this finite Fourier class.

This is not a Navier--Stokes blowup construction or a refutation of the
linked dynamical estimate. It rules out discarding all derivative,
frequency, and correlation information when estimating the mixed costs
above. Exploiting that retained structure in the relative-kernel integral,
the scale sums, and the signed time-integrated budget remains necessary.

### One integrable envelope for every frozen pressure direction

`Analysis/CompactFourierEnvelope.lean` strengthens the compact-family
moment estimate to one continuous nonnegative majorant, with any prescribed
integrable spatial moment. It constructs a polynomially decaying envelope
from the already proved uniform inverse-Fourier decay. No supremum is
exchanged with an integral.

`Analysis/DensityLinearChange.lean` transfers nonnegative integrable
densities through linear changes with the exact absolute Jacobian.
`PressureDyadicEnvelope.lean` applies these results to the corrected pressure
symbols and assembles the actual complex-bilinear operator kernels. The
resulting envelope is independent of the unit frozen direction.

`FrequencyPairEnvelope.lean` and `PressurePeriodicEnvelope.lean` periodize
the envelope itself. For each input scale `N > 0` there are nonnegative
measurable functions `M_(N,n)` such that, on one full-Haar-measure set,

```text
for every output band n and every unit direction e:
  ||K_(N,n,e)(q)|| <= M_(N,n)(q).

sum_n integral M_(N,n)             <= C0,
sum_n integral |q| * M_(N,n)(q)     <= C1 / N.
```

Both series are summable. The constants are independent of `N`, the frozen
directions, and adaptive patch count. Before summing, the mass and first
moment retain the gains `ratio²` and `ratio/N`. Summability of the envelope's
lattice translates supplies a common exceptional set even for the uncountable
unit sphere; separate exceptional sets for individual directions are not used.

`GaussianRootEnvelope.lean` uses this kernel envelope in a bound for the actual
Gaussian root-patch localization integrands, with both translated full-vorticity
inputs and the actual center directions. Its final existential theorem includes
the envelope construction and summable costs; kernel domination is not an
additional hypothesis of that theorem. The squared-weight differences remain
on the right-hand side; the spatial translation estimate below now controls
them. The input-scale sum and the signed time-integrated dynamical estimate
remain open. An integrable envelope alone does not imply integrability of
its square, and the spatial estimate below does not make that inference.

`Analysis/CompactFourierEnvelopeTests.lean` and `PressureEnvelopeAudit.lean`
check exact tail values, a nontrivial Jacobian-weighted dilation, the zero-ratio
boundary, and simultaneous domination across an uncountable amplitude family
and all dyadic bands. They also print the new theorem axioms.

### Full spatial translation energy and the inverse-scale localization budget

`Analysis/UnitTorusTranslationEnergy.lean` proves a full translation bound
from finite Fourier gradient-energy estimates using Parseval. It constructs
a norm-preserving real lift of every torus displacement, so the bound uses
wrapped distance. `PeriodicTranslationEnergy.lean` supplies the finite
Fourier bounds from the actual weak derivatives of a locally Lipschitz real
periodic field. In three dimensions,

```text
integral_x |f(x) - f(x-a)|² <= 3 |a|² integral_x sum_j |partial_j f(x)|².
```

`GaussianSquaredRootTranslation.lean` applies this to the squares of the
actual nonnegative root patches. Their summed gradient energy `G` is
integrable and retains the gate-gradient and Gaussian-patch-gradient costs.
There is no derivative of the unsquared scalar root at a vorticity zero.

`GaussianRootSpatialBudget.lean` then proves, for the actual localization
integrands `R_(n,i)(q,x)` and full continuous vorticity `omega`,

```text
sum_n integral_q sqrt(integral_x sum_i |R_(n,i)(q,x)|²)
  <= (C / N) ||omega||_sup² sqrt(6 G).

G = integral_x sum_i sum_j |partial_j (rootPatch_i²)(x)|².
```

The left-hand summands are integrable and their series is summable. The
common pressure envelope is constructed and used only to its first power
after the spatial square root; its first moment supplies `1/N`. The kernel
constant `C` is independent of input scale and adaptive patch count, but
`G` still depends on the gates and patch geometry. The final theorem uses
the actual continuous-map supremum of vorticity, not an assumed field bound.

This is an `L1(q; L2(x; ell2(patches)))` estimate.

`Analysis/ContinuousFieldMinkowski.lean` proves the finite-family integral
and infinite-series triangle inequalities by bundling the components in
one Hilbert space and mapping continuous fields into `L2`.
`PressureLocalizationField.lean` proves Bochner integrability in the
continuous-field norm and identifies its integral with the actual
two-input pressure localization. `PressureDyadicLocalization.lean` proves
convergence to the localization of `PressureDyadicAction.sumAction`.

`GaussianRootOperatorBudget.lean` applies these results to the actual root
patches and full vorticity. Writing `A_(n,i) = integral_q R_(n,i)`, it proves
genuine convergence and the bounds

```text
sqrt(integral_x sum_i |sum_n A_(n,i)(x)|²)
  <= sum_n sqrt(integral_x sum_i |A_(n,i)(x)|²)
  <= (C / N) ||omega||_sup² sqrt(6 G).
```

The first series is identified with the already constructed continuous
pressure output-band sum, not a nonsummable-series default. The finite
patch family has no additional cardinality multiplier. This operator
theorem sums output bands at a fixed input scale. The construction below
additionally sums high input scales for a fixed smooth field, with explicit
regularity costs. The other interaction sectors and the signed
dynamical/time budget remain open. This does not prove global regularity.

`Analysis/UnitTorusTranslationEnergyTests.lean` and
`GaussianRootSpatialAudit.lean` check wrapped representatives, the signed
Fourier translation phase, a nonsmooth norm-corner field, empty-family
defaults, and output-band summability for actual data. All new theorem
axioms are printed for inspection.

`Analysis/ContinuousFieldMinkowskiTests.lean` checks quadratic component
aggregation, non-probability measure normalization, an empty family, and
signed cancellation. `GaussianRootOperatorAudit.lean` checks constant
weights, the empty-family default, actual-data norm summability, and
pointwise series convergence. All 22 new theorem dependencies are audited.

### Bounded adaptive covers and high-input summation

`Analysis/CompactRangeCover.lean` constructs adaptive covers with a common
cardinality bound for all maps into a fixed compact target set. One actual
source point is selected from each occupied target-net ball. The source
map need not be continuous for this cover-size result; its oscillation
does not affect the bound. Range control is essential.

`BoundedGaussianLinePartition.lean` applies this construction to weighted
rank-one projectors. For a vorticity bound `W`, positive gap threshold
`gamma`, and positive line tolerance `rho`, their coordinate norm is at
most `W / gamma`. A cover-size bound `M` is chosen before the filter or
mode set, and every chosen Gaussian temperature is at least

```text
tau_* = rho² / (4 (1 + log M)) > 0.
A = 3 (1 + (W/gamma)² rho² / (2 tau_*²)).
```

`LocalGapGateGradient.lean` proves almost-everywhere differentiability of
the clipped gap gate and the explicit `36 / gamma²` strain-gradient
bound. `UniformGaussianGradientBudget.lean` combines it with the actual
weighted-projector derivatives and constructs patches with

```text
sum_i |gradient(rootPatch_i²)|²
  <= (4 A / gamma²) sum_j |partial_j omega|²
     + ((72 + 1600 A) W² / gamma⁴) sum_j |partial_j S_filtered|²
```

almost everywhere. Exact squared coverage and the prescribed weighted
line-error bound hold for these same patch families.

For filters bounded by one, `UniformStrainGradientBudget.lean` bounds each
strain derivative by
`L = 9 (2 pi)² sum_k (1 + |k|)² |u_hat(k)|`, independently of the finite
mode set. Consequently the integrated patch energy has the common bound

```text
H = (4 A / gamma²) integral_x sum_j |partial_j omega|²
    + ((72 + 1600 A) W² / gamma⁴) 3 L².
```

`GaussianRootInputBudget.exists_uniform_input_budget` uses the actual
continuous vorticity supremum for `W` and proves, for input scales
`N_j = N_0 2^j`,

```text
sum_j ||complete output-band localization at input N_j||_(L2_x ell2_patches)
  <= (2 C / N_0) W² sqrt(6 H).
```

The patch families are constructed, their norms form a genuinely
summable series, and `M` is selected before `N_0` and every contractive
filter sequence. This is a fixed-smooth-field estimate for one pressure
sector. `W`, `L`, and the vorticity-gradient energy are not controlled up
to a candidate singular time; `gamma` and `rho` are not sent to zero.
It is not the dynamical `MisalignmentStrainBudget` or the final theorem.

`Analysis/CompactRangeCoverTests.lean` checks a discontinuous bounded
field, an empty source, uniformity over arbitrary bounded sequences, and
the failure of finite covering for unbounded separated values.
`GaussianRootInputAudit.lean` checks temperatures, input scales, genuine
finite Fourier data, and constructed input-scale summability. Together
they audit 26 new or refactored theorems.

### Replacing the Fourier-moment cost by physical diffusion energy

`FourierMatrixEnergy.lean` applies Parseval to the columns of the actual
matrix reconstruction and bounds its real operator norm by its coefficient
energy, without mode-count or extra dimension multipliers.
`VorticityGradientEnergy.lean` identifies the full physical gradient energy
with its Fourier coefficient sum. Conjugate symmetry is explicit: real-part
projection does not preserve the energy of arbitrary complex data.

For real divergence-free data and every contractive finite Fourier filter,
`StrainGradientEnergy.integral_sum_strainGradient_sq_le` proves

```text
integral_x sum_j ||partial_j S_filtered||_op²
  <= D := integral_x sum_j |partial_j omega|².
```

Thus `GaussianRootDiffusionBudget.exists_uniform_input_diffusion_budget`
strengthens the preceding fixed-field input sum to

```text
Lambda = 4 A / gamma² + (72 + 1600 A) W² / gamma⁴
R := sum_j ||complete output-band localization at input N_0 2^j||
R <= (2 C / N_0) W² sqrt(6 Lambda D).
```

The same theorem constructs every patch family, preserves coverage and
line accuracy, proves genuine summability, and retains the order in which
the cover bound is chosen before all filters and input scales. Smoothness
is required to identify the actual derivatives, but no absolute Fourier
moment occurs in this stronger bound. The earlier moment-based theorem
remains available without reality or incompressibility hypotheses.

For every nonnegative scalar test norm `Y` and positive `epsilon`, the
constructed output sum also satisfies the explicit absorption inequality

```text
R Y <= epsilon D + 6 C² Lambda W⁴ Y² / (epsilon N_0²).
```

`Analysis/SqrtEnergyAbsorption.lean` supplies the elementary sharp
square-root absorption inequality used here. This identifies the remainder;
it does not prove it affordable over time. In particular, a signed term
in the actual evolution must still be identified with the tested operator
output, and its time-dependent cutoff, test norm, vorticity supremum, and
geometric costs must be controlled. None of these are replaced by an
assumed `MisalignmentStrainBudget`.

`GaussianRootDiffusionAudit.lean` checks matrix normalization,
antisymmetric cancellation, a longitudinal-mode refutation when
incompressibility is omitted, filter uniformity, and actual input-family
construction. Together with `Analysis/SqrtEnergyAbsorptionTests.lean`, it
also tests sharp absorption and failure for a negative absorption weight.
The eight examples are checked alongside 25 new or refactored theorem
axiom audits.

### Periodic low-output pressure with wrapped spatial moments

`PressureLowOutputPeriodization.lean` constructs an actual integrable
complex-bilinear kernel on mathlib's unit six-torus. Its Fourier coefficient
at each input-frequency pair is exactly the retained physical pressure
operator, using the same Fourier sign and normalized Haar measure as the
existing pressure-kernel action.

`FrequencyPairPeriodization.lean` reuses the standard lattice geometry and
proves kernel-independent Fourier transfer and contraction of every spatial
moment under periodization. The torus norm measures wrapped distance in the
standard product norm; it is not the norm of the representative in the
half-open unit cube. Consequently the periodic pressure kernels satisfy

```text
integral ||K_T(q)|| dq                         <= C_0 rho²,
integral ||q|| ||K_T(q)|| dq                   <= C_1 rho/N,
integral (||first(q)|| + ||second(q)||) ||K_T(q)|| dq <= C_2 rho/N.
```

The first two constants incur no extra periodization factor. The last
estimate explicitly pays both input-displacement channels with a factor
of two. All three actual costs are summable over the dyadic output bands,
uniformly in input scale and frozen unit direction.

`PressurePeriodizationAudit.lean` checks the periodic seam, a quarter-period
wrapped distance, the attained two-input factor, complex phases, and a
nonzero periodized Fourier entry equal to `-1/130052`.
This closes periodic transfer for the original overlapping low-output bands.
The distinct exact-partition family is supplied above, but its connection
to this periodic operator interface remains open. The other frequency sectors
and root-weighted dynamical scale/time budget remain open; integrability here is not a claim of
pointwise continuity of the orbit sum or global NS regularity.

### Actual complex pressure operators with summable low-output band costs

`PressureOperatorCoordinates.lean` reconstructs the existing continuous
complex-bilinear `pressurePairOperator` from its real-basis entries.
`PressureLowOutputOperatorKernel.lean` assembles the physical scalar kernels
into an operator-valued Schwartz kernel and proves, at every lattice pair,

```text
Fourier(K_(N,rho,e))(k,p) = physicalCutoff_(N,rho)(k,p) * pressurePairOperator(e,k,p).
```

This equality holds as a bilinear operator, hence on arbitrary complex
input vectors, without imposing reality or incompressibility on those vectors.
Generic coordinate assembly bounds its mass and first spatial moment by the
sum of the 27 scalar-entry costs. Consequently,

```text
integral ||K_(N,rho,e)(x)|| dx       <= C_0 rho²,
integral |x| ||K_(N,rho,e)(x)|| dx   <= C_1 rho/N,
```

where the norm is the bilinear operator norm. Constants are independent of
the positive input scale, low-output ratio, and unit frozen direction.
`PressureLowOutputOperatorBudget.lean` proves actual summability of these
operator-norm costs over `rho_n = 2^(-n)/256`; their sums are bounded by a
constant and by a constant divided by `N`, respectively.

`PressureOperatorKernelAudit.lean` checks arbitrary complex input action,
single- and double-imaginary phases, a nonzero low-output pressure entry,
and exact cancellation at opposite frequencies. This closes scalar-to-operator
reconstruction, not the decomposition of the full pressure into bands.
Periodic transfer for these overlapping bands is supplied above. The corrected
partition family is separate; its operator assembly, the other frequency
sectors, and the scale/time-weighted localization budget remain open.

### Physical low-output pressure band costs at every input scale

`PressureLowOutputChange.lean` constructs the spatial change
`(x,y) -> (x-y,rho*y)` and identifies its inverse adjoint with the original
input-frequency change `(k,p) -> (k,(k+p)/rho)`. The inverse spatial map has
operator norm at most `3/rho` for `0 < rho <= 1`. Generic Jacobian-normalized
Schwartz pullback preserves mass and retains this exact first-moment cost.

`PressureLowOutputPhysicalKernel.lean` therefore proves quadratic kernel-mass
smallness and linear first-moment smallness. Its Fourier transform is the
actual retained pressure-pair entry in the original two-input coordinates.
The zero-ratio kernel is zero, consistently with its retained symbol.
`PressureLowOutputScaledKernel.lean` restores any common input scale `N > 0`:

```text
integral |K_(N,rho,e;i,j,l)(x)| dx       <= C_0 rho²,
integral |x| |K_(N,rho,e;i,j,l)(x)| dx   <= C_1 rho/N.
```

The constants are independent of `N`, `0 <= rho <= 1/256`, the unit frozen
direction, and all 27 real-basis entries. Common frequency scaling is
proved to preserve the pressure-pair amplitude, including negative scales.

`PressureLowOutputDyadicBudget.lean` proves actual summability of band-kernel
mass and first moments over `rho_n = 2^(-n)/256`. Their sums are bounded by
a constant and a constant divided by `N`, respectively. This is not yet a
reconstruction theorem for these original overlapping cutoffs. The exact
partition and its new scalar kernels are supplied separately above.
Complex-bilinear reconstruction of the original bands is supplied above;
periodic transfer is also supplied above. The other frequency sectors and
root-weighted scale/time budget remain open. `PressurePhysicalKernelAudit.lean` checks cancellation, orientation,
geometric sums, and a physical Fourier entry equal to `-1/130052`.

### Uniform low-output pressure moments in normalized coordinates

`PressureLowOutputCoordinates.lean` writes the receiver frequency as
`rho * q - k`, exposing the exact factor `rho²` in the pressure-pair symbol.
The identity includes `rho = 0`; it does not assume a small output angle.
`PressureLowOutputCutoff.lean` constructs input/output annuli and buffered
denominators that are globally positive and exactly physical wherever the
retained cutoff is nonzero. The cutoff equals one on the target annuli.

`PressureLowOutputSymbol.lean` constructs the resulting actual complex-valued
Schwartz entries, jointly smooth in the ratio parameter and frozen direction.
`PressureLowOutputKernel.lean` proves uniform moments of their inverse Fourier
transforms. For every natural moment order `m`, one constant controls all 27
real-basis entries, all unit frozen directions, and `0 <= rho <= 1/256`:

```text
integral |x|^m |K_retained(rho,e;i,j,l)(x)| dx <= rho² C_m.
```

These transforms use **input/normalized-output coordinates**, not the original
two-input coordinates. The physical shear/dilation and first-moment loss are
now accounted for by the physical-kernel modules above. Operator assembly and
periodic transfer are also proved above. Exact band decomposition, other
frequency sectors, and the all-scale/time budget remain to be joined.
In particular this is not yet a frequency-uniform bound for
the full physical pressure localization error.
`PressureLowOutputAudit.lean` tests the ratio endpoints, exact cancellation,
receiver collisions outside the cutoff, and a nonzero normalized limiting
symbol; the estimate is not obtained by choosing a zero cutoff.

### Full-field coefficient selection and the retained physical pressure

`PressureKernelCoefficientAction.lean` proves that a finite pressure kernel
acts on arbitrary **continuous full fields** by selecting their retained
Fourier coefficients. No finite-polynomial assumption or Fourier-density
argument is needed for this identification. The proof uses generic
product-Haar integration in `Analysis/FiniteTorusProduct.lean` and the
vector-valued character integral in `Analysis/UnitTorusFourierTranslation.lean`.
The two input frequencies are selected independently before their outputs
are collected.

`FullVorticityFourierCoefficients.lean` proves that the Fourier coefficients
of the complexified **actual real spatial curl** equal `fourierCurl u`.
The first absolute velocity moment justifies differentiation and coefficient
recovery; the original conjugate symmetry is explicitly required to recover
the complex field from its real part. This symmetry is not asserted for
arbitrary complex coefficient arrays.

`GaussianRootPressureIdentification.lean` joins these results to the
weighted localization inequality. If `P_M` is the pressure-Hessian tilt
polynomial computed from original velocity modes in `M`, `omega` is the
full actual vorticity, and `K_M` retains both input sets `M`, it proves

```text
P_M = -B_(K_M)(omega,omega),
|c_i² P_M + B_(K_M)(c_i omega,c_i omega)| <= weighted kernel error.
```

The error is precisely the spatial density displayed below. The localized
inputs remain the actual root-weighted full fields, with no imposed
zero-mean or divergence-free property. Original velocity incompressibility
is required on `M`; original reality symmetry is required at every mode.

This closes the **full-input identification at finite retained pressure
frequencies**. It does not remove the pressure truncation, prove a
frequency-uniform weighted kernel bound, or pay the dynamical budget.
`FullPressureKernelAudit.lean` tests this distinction, retained coefficient
selection, and the failure of unrestricted complexification of real parts.

### Physical pressure kernels and weighted root-cutoff differences

`PressureBilinearOperator.lean` realizes the actual pressure-pair symbol as
a continuous complex-bilinear operator on Euclidean three-vectors. Its
operator norm is at most one for a unit frozen direction. The representation
does not change the coefficient norm or introduce a coordinate-count factor.
`Analysis/FiniteTorusSymbolKernel.lean` constructs finite symbol kernels in
any finite torus dimension; `FinitePressureKernel.lean` specializes this to
the six-dimensional pair torus and proves exact retained Fourier support.

`PressureKernelFourier.lean` identifies the kernel action on finite Fourier
polynomials with the pressure-pair convolution, collecting all colliding
output modes. The original incompressible velocity's pressure-Hessian tilt
polynomial is the **negative** of this kernel action on its Fourier curls.
Kernel supports may contain the input supports strictly.

`Analysis/BilinearKernelLocalization.lean` and `PressureKernelAction.lean`
prove the physical two-input localization identity. Writing `B_K` for the
bilinear kernel action and `y,z` for the two translated input points,

```text
c(x)d(x) B_K(f,g)(x) - B_K(cf,dg)(x)
  = integral [c(x)d(x)-c(y)d(z)] K(x-y,x-z)[f(y),g(z)].
```

The norm bound keeps each cutoff difference with its corresponding input.
For the actual Gaussian root patch `c_i = a_i sqrt(|omega|)`, put

```text
Delta_i(x,y) = |a_i(x)-a_i(y)| sqrt(|omega(y)|) |omega(y)|
             + |a_i(x)| sqrt(|omega(y)|) |omega(x)-omega(y)|.
```

`GaussianRootKernelBudget.lean` proves that

```text
|c_i(x)^2 B_K(omega,omega)(x) - B_K(c_i omega,c_i omega)(x)|
  <= integral |K(x-y,x-z)| *
       [|c_i(x)| Delta_i(x,y) |omega(z)|
        + |c_i(y)| |omega(y)| Delta_i(x,z)].
```

Here `omega` is the actual full vorticity (complexified isometrically),
and `K` is the constructed finite pressure kernel. Integrability is derived
from continuity on the compact torus. No unweighted scalar-root derivative,
inverse vorticity magnitude, or divergence-free condition on the localized
inputs is assumed.

**Open boundaries:** a finite retained kernel is not the untruncated
pressure operator. The full-field coefficient identification is proved above;
removing the pressure truncation, a frequency-uniform weighted kernel bound,
and the summed scale/time budget remain open. The uniform bound on each symbol alone does not give
a uniform kernel mass. The aperture-uniform coherent-stretch kernel is a
different operator and cannot supply this missing pressure estimate without
a proved identification. `PressureKernelAudit.lean` and
`Analysis/BilinearKernelLocalizationTests.lean` check the new theorem axioms
and regression cases, including excluded modes and zero vorticity.

### Root-weighted vorticity and exact fourth-power coverage

`GaussianRootVorticity.lean` constructs scalar root patches `c_i` and
actual weighted fields `c_i * omega` from the existing adaptive Gaussian
cover. Write `kappa` for the gap ramp, `gbar = max(gap, gamma)`, and
`theta_i` for the normalized Gaussian amplitudes, with `sum theta_i² = 1`.
The construction is

```text
c_i = kappa / sqrt(gbar) * sqrt(|omega|) * sqrt(theta_i),
a_i = kappa / sqrt(gbar) * sqrt(theta_i),
c_i * omega = a_i * (sqrt(|omega|) * omega).
```

`GaussianRootPartition.lean` proves

```text
sum c_i⁴ = kappa⁴ |omega|² / gbar² = W4.
```

It retains the old cover's line-freezing error bound without adding a
patch-count factor. The real lifts of the weighted vorticities are locally
Lipschitz, including at zero vorticity. `Analysis/RadialSquareRoot.lean`
proves the needed generic radial regularity and an actual zero derivative
at the origin. **The scalar root patch itself is not asserted to be locally
Lipschitz or to have a square-integrable derivative.**

`GaussianRootDifferentiation.lean` proves, Haar almost everywhere, the
actual coordinate derivative bound

```text
|d(c_i * omega)|² <= 2 |d a_i|² |omega|³ + 8 a_i² |omega| |d omega|².
```

`GaussianRootDifference.lean` also bounds the weighted two-point cutoff
difference `|c_i(x)-c_i(y)| |omega(y)|` using scalar-factor and vorticity
differences, with no inverse vorticity magnitude. The finite pressure-kernel
integration of this estimate is proved above.

`Analysis/SquaredWeightLocalization.lean` gives another estimate that avoids
derivatives of the scalar roots. For real `a,b,c` with `b*c >= 0`, it proves

```text
(a-b*c)² <= (a-b²)² + (a-c²)².
```

The difference between the right and left sides equals
`(a-b²-c²+b*c)² + 2*b*c*(b-c)²`. Applying this with `a=c_i(x)²` and summing
controls the squared bilinear localization errors by

```text
L² |omega(y)|² |omega(z)|² *
  (sum_i (c_i(x)²-c_i(y)²)² + sum_i (c_i(x)²-c_i(z)²)²),
```

provided each patch's bilinear operator has norm at most `L` at that input
pair. There is no additional patch-count multiplier.
`GaussianSquaredRootLocalization.lean` instantiates this for the actual
nonnegative Gaussian roots. Their squares satisfy `c_i² = kappa*p_i`, where
`p_i` are the original Gaussian patches, and their real lifts are locally
Lipschitz, including at vorticity zeros. The actual coordinate derivatives
satisfy, Haar almost everywhere,

```text
sum_i |d(c_i²)|² <= 2 |d kappa|² sum_i p_i² + 2 kappa² sum_i |d p_i|².
```

The generic product estimate is in `Analysis/ScaledPartitionDerivative.lean`.
The gate and patch-gradient costs remain explicit. The common integrable
pointwise kernel envelope is now constructed in `PressurePeriodicEnvelope.lean`
and applied in `GaussianRootEnvelope.lean`, as described above. It comes from
uniform Fourier decay, not merely from the integral bounds for the individual
kernels. The weighted translation estimates and signed time-integrated
dynamical budget are not discharged here.
`Analysis/SquaredWeightLocalizationTests.lean` and
`GaussianSquaredRootAudit.lean` check the sharp zero-weight case, the
failure for opposite-sign weights, nonzero complex errors, actual product
derivatives, and vorticity-zero endpoints, and audit the theorem axioms.

`Analysis/RootPartitionEnergy.lean` and `GaussianRootEnergy.lean` prove a
summed weighted derivative bound for the actual fields, Haar almost
everywhere. For `b = kappa / sqrt(gbar)`, coordinate-projector map `M`,
and any selected center `M_k`, put `E_N = |M-M_k|² + tau log(N)`. Then

```text
sum c_i² |d(c_i * omega)|²
  <= 2 b² (d b)² |omega|⁴
   + b⁴ E_N |d M|² |omega|⁴ / (2 tau²)
   + 8 b⁴ |omega|² |d omega|².
```

The proof differentiates the **squares** of the root factors and uses the
Gaussian normalization's exact cross-term cancellation. There is no added
linear patch-count multiplier. The existing logarithmic count/temperature
dependence and actual gap-factor and projector derivatives are retained;
this is not a scale-uniform bound.

The added gap ramp is paid for explicitly in `QuarticGapTiltWeight.lean`.
The source split still uses the actual joint nonviscous remainder; its
collision cost becomes `(1-kappa⁴) 2 |R| |omega|²`, which equals the old
cost plus `kappa² (1-kappa²) 2 |R| |omega|²`. The old and new weights agree
where the gate is one. The transition cost is not declared small.

This repairs the **weight factorization and weighted-field regularity**.
It does not justify applying the scalar-cutoff gradient estimate below
to `c_i`. The weighted physical commutator above avoids that step, but its
compatible Fourier limit and scale/time-uniform cost bounds remain open. No
unconditional regularity theorem follows. `GaussianRootAudit.lean` and
`Analysis/RadialSquareRootTests.lean` audit these statements and boundaries.

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
two-input estimate does not by itself supply the earlier Gaussian quadratic
weight estimate. The root construction above supplies a fourth-power
factorization for a quartic-gated variant with its added collision cost
retained. Its weighted commutator, cutoff Fourier-l1 cost, scale-uniform
field norms, and time-integrated inverse-gap budget remain open analytic
work. No unconditional regularity theorem is claimed.
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
