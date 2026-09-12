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

The dependencies guide the work, not a rigid chronological schedule:
counterexamples to a proposed S3 or S4 estimate can require revising S2.
Imported fluid-equation results must retain their domain, forcing, and
regularity hypotheses. A genuine route obstruction is a result to record
and use to repair the attack, not a completed regularity proof.

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
