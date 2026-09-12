# Analysis

Reusable analysis, independent of any particular fluid construction.

## Checked modules

| Module | Mathematical content | Scope |
| --- | --- | --- |
| `CompactMeanDerivative.lean` | Differentiation under a compact probability-space mean and preservation of uniform sectional Lipschitz bounds | Joint continuity, locally uniform sectional bounds, and almost-everywhere differentiability; shared with the periodic material-balance applications |
| `UnitTorusWeakDerivative.lean` | Measured fundamental-cube transfer, weak coordinate differentiation, periodic integration by parts, and incompressible transport cancellation | Arbitrary finite index type; locally Lipschitz real lifts, not globally smooth scalar fields |
| `UnitTorusMaterialBalance.lean` | Almost-everywhere material chain rule, spatial mean balance, and a signed time-weighted identity | Finite-dimensional unit torus; time integrability is proved, no measure-preserving flow is assumed |
| `UnitTorusProductTransport.lean` | Two-endpoint coordinates, product velocity divergence, and exact product-Haar integration | Independent finite endpoint index types; applies the mean balance to pair observables |
| `IntegralContinuousTest.lean` | Continuous test functions determine an integrable complex density almost everywhere | Borel spaces with bounded continuous approximations to closed-set indicators; no continuity or square-integrability hypothesis on the density |
| `UnitTorusFourierL1Uniqueness.lean` | Fourier uniqueness and finite polynomial reconstruction almost everywhere for integrable complex fields | Any finite-dimensional unit torus; uses density of the Fourier span in continuous functions |
| `AnnularRieszFourierSupport.lean` | Explicit finite coordinate box containing every nonzero partial annular multiplier | Arbitrary finite dimension, including zero cutoff |
| `PeriodicRieszPolynomial.lean` | Continuous real even finite Fourier representative, identified almost everywhere with the constructed Riesz periodization | Exact nonlinear spatial-integral replacement and the same cutoff-independent second-moment bound; no pathwise differentiation of almost-everywhere equality |
| `CrossProductEvolution.lean` | Matrix action on cross products, differentiation, and the normalized squared-angle derivative | Real dimension three; normalization derivative requires nonzero endpoints |
| `CrossProductStrain.lean` | Exact separation of common-strain angle evolution from signed strain-difference and endpoint-force terms | No angle damping assumed; a rational growing-angle first-variation test is checked in `CrossProductStrainTests.lean` |
| `SymmetricCrossProductStrain.lean` | Averaging of both endpoint strain decompositions, with an exact signed angle derivative | Preserves both endpoint forces; no top-eigenvalue comparison or time budget assumed |
| `RadialPowerEvolution.lean` | Exact derivatives of even radial powers, including at zero, and their strain/amplitude decomposition | Real inner product spaces; no division by the vector norm |
| `SignedCrossKernelEvolution.lean` | Signed derivative of a moving radial cross-kernel pairing, retaining the kernel commutator and radial amplification | Actual differentiable inputs and kernel; no sign or growth bound assumed |
| `SignedCrossKernelRateDecomposition.lean` | Exact strain, moving-kernel and endpoint-increment channels, with linear viscosity factor and radial homogeneity | Algebraic decomposition of a fixed selected rate; no separate chain rules or sign assertions for individual channels |
| `RadialPowerCurvature.lean` | Explicit second variation of even radial powers of degree at least five, including zeros | Real inner product spaces; nonnegative integer norm powers |
| `SignedCrossKernelCurvature.lean` | Fixed-kernel second variation, linear endpoint acceleration, signed first-gradient curvature, and exact coherent-line vanishing | Smooth paired source before amplitude cutoff; no positive-curvature hypothesis |
| `SignedCrossKernelCurvatureIncrement.lean` | Endpoint/gradient increment factorization, equal-value transverse gradient bound, isotropic cancellation and oddness under simultaneous negation | Retains gradient misalignment even when endpoint values agree; no sign or integrated affordability claim |
| `UnitTorusContinuousRate.lean` | A continuous translation derivative has zero periodic mean | Any finite-dimensional unit torus; compactness derives the needed derivative bound |
| `UnitTorusPairIntegration.lean` | Exact change from two endpoints to one endpoint and their separation | Continuous real pair observables and normalized Haar measure |
| `HighAmplitudeWeightEvolution.lean` | Derivative of the symmetric high-amplitude weight on either strict smaller-endpoint branch | Positive threshold, above-threshold endpoint and strict ordering; reuses the norm derivative in the attributed `ODE/QuadraticFormBound.lean` port |
| `IntegrableKernelPairing.lean` | Integrable scalar kernels define bounded functionals on continuous fields | Compact domains with measurable open sets; no kernel continuity or uniform mass hypothesis |
| `UnitTorusFourierReal.lean` | Fourier coefficients under conjugation, reversal, real-part extraction and real-even symmetrization | Any finite-dimensional unit torus; integrability retained where addition is used |
| `UnitTorusIntegrableConvolution.lean` | Convolution of an integrable kernel with a uniformly convergent Fourier series | No continuity of the kernel; actual `HasSum` in the continuous-field norm |
| `PeriodicRieszOperatorFourier.lean` | Real-even scalar entries reconstruct the actual operator and retain its exact annular Fourier symbol | Arbitrary finite dimension; includes zero modes |
| `SignedCrossKernelIntegrable.lean` | Signed source-receiver exchange and low/high-amplitude splitting for integrable kernels | Explicit joint integrability; no continuity or boundedness of the kernel assumed |
| `BilinearKernelIntegrability.lean` | Integrable operator kernels act on bounded strongly measurable fields; compact continuous fields supply all needed bounds | Real or complex normed spaces; kernel continuity and absolute input Fourier summability are not required |
| `WeightedIntegralEnergy.lean` | Weighted Cauchy–Schwarz and the squared norm of an actual Bochner integral bounded by mass times weighted energy | Nonnegative integrable weights, including zero mass; almost-everywhere strongly measurable inputs |
| `BilinearTranslatedKernel.lean` | Bilinear L¹ kernels acting on one L² input and one bounded measurable input, in either slot; almost-everywhere integrability, representative independence, and an L² input-difference estimate | Measurable additive commutative groups with a right-invariant s-finite measure; actual translated integrals, no input Fourier-summability hypothesis |
| `BilinearCoefficientSums.lean` | Coordinatewise convergent coefficient sums reconstruct a convergent series of bilinear operators | Independent finite Euclidean input and output index sets; actual `HasSum`, not a formal series |
| `BilinearRankOne.lean` | Continuous bilinear map `(u,v) -> f(u) g(v) w` with exact norm `norm(f) norm(g) norm(w)` | Any nontrivially normed scalar field and normed input/output spaces; no finite-dimensionality assumption |
| `DyadicAnnulus.lean` | Finite overlap, dyadic invariance, positivity, and punctured smoothness of the annulus normalizer | Any real normed space admitting smooth bumps; the normalizer lies between one and three away from zero |
| `DyadicAnnulusPartition.lean` | Smooth exact dyadic partition, compact support, and one-sided reconstruction in the punctured unit ball | Zero excluded from the partition identity; all annular bands vanish there |
| `DyadicAnnulusCorrection.lean` | Globally smooth bounded multiplier realizing the normalization on annular support | Extends the reciprocal normalizer by one near zero without changing an annularly supported symbol |
| `DyadicHighPass.lean` | The exact one-sided high-input annular sum and its low-pass complement | Valid at zero; zero on the half-unit ball, one beyond radius two, and one half at unit norm |
| `WeightedSeries.lean` | Bounded scalar weighting and exact complementary splitting of absolutely convergent Banach-space series | Any normed scalar field; signed or complex weights are allowed |
| `GeometricMinSeries.lean` | Summability, finite-cutoff bounds, and logarithmic optimization for `sum min(A q^m, D)`; dominated sequences and a second dyadic index | Nonnegative costs, any geometric ratio strictly between zero and one; includes zero fixed cost and both iterated summability claims |
| `TruncatedKernelMoment.lean` | Integrability and simultaneous mass/first-moment control of `integral min(R, norm x) norm(K x)` | Any Borel normed domain and normed codomain, arbitrary measure, nonnegative cap |
| `OddMapLineEstimate.lean` | Squared-norm freezing for odd maps with a Lipschitz estimate on unit directions, including finite weighted families | Normed additive groups; uses the smaller of the two oriented distances and introduces no family-size factor |
| `OddMapWeightedContinuity.lean` | Continuity of weighted output norms controlled by a continuous comparison field | The unit direction need not be measurable; the weighted unoriented-line estimate is explicit, including at zero weight |
| `FundamentalDomainPeriodization.lean` | Measurable orbit sums, exact character-integral transfer, and invariant-weight mass contraction on a fundamental domain | Countable measure-preserving additive actions; the unweighted core is shared with the existing coherent-kernel development |
| `EuclideanBilinearCoordinates.lean` | Exact coordinate reconstruction of continuous bilinear maps and operator norm bounded by the sum of absolute entries | Real or complex Euclidean spaces with independent finite input and output index sets |
| `SchwartzBilinearKernel.lean` | Scalar-entry assembly into bilinear-operator-valued Schwartz kernels, exact Fourier identity, and every operator-norm moment bound | Complex Euclidean input/output spaces; any finite Euclidean spatial dimension; bilinear, not sesquilinear |
| `SchwartzLinearChange.lean` | Absolute-Jacobian pullback, exact Fourier inverse-adjoint identity, mass preservation, and inverse-map spatial-moment cost | Finite-dimensional real inner-product spaces; arbitrary invertible continuous linear changes |
| `SchwartzDilation.lean` | Exact dilation Jacobian, Fourier argument, and every spatial moment | Positive or negative nonzero real scales; absolute Jacobian handles orientation |
| `CompactSchwartzFamily.lean` | Uniform Schwartz seminorms, inverse-Fourier decay, and every spatial kernel moment from joint smoothness and common compact support | Compact parameter sets in real normed spaces; Fourier kernels in any finite Euclidean dimension; no assumed continuity in the Schwartz topology |
| `SmoothAnnulus.lean` | Smooth annular cutoffs, exact larger buffers, and positive regularized squared-norm denominators | Any real normed space admitting smooth bumps; compact support in finite dimensions |
| `ODE/QuadraticFormBound.lean` | Dissipative forced-ODE comparison, positive integrating factors, additional exponential growth, interval-only forcing, and source-envelope estimates | Any real inner product space; no completeness or finite-dimensionality assumption |
| `ODE/AbsolutelyContinuousComparison.lean` | Dissipative comparison with an almost-everywhere equation and integrable forcing | Absolutely continuous paths; allows corners and eigenvalue collisions |
| `ODE/VariableGronwall.lean` | Scalar comparison by the exponential of the actual growth integral | Arbitrary finite interval; interior derivatives; coefficient and solution may have either sign |
| `LogarithmicScaleBound.lean` | Explicit scale selection and elimination of a logarithmic/high-frequency cutoff | Any positive real decay exponent; sharp estimate requires no sign assumption on the low or logarithmic costs |
| `SimpleImplicitRoot.lean` | A continuous simple root of a smooth scalar equation is smooth | Real Banach parameter space; derived from mathlib's implicit-function theorem |
| `OperatorQuadraticForm.lean` | Two derivatives of a moving operator quadratic form, retaining all cross terms | Any real inner product space; no completeness or dimension assumption |
| `IdempotentDerivatives.lean` | First-order tangent identity, second-order quadratic correction, material-minus-diffusion constraint, and signed diagonal defect blocks | Derivatives in a real normed algebra; diagonal block identities in any ring |
| `SpectralRelationDerivatives.lean` | First and second derivatives of `SP = μP`, and principal parabolic diffusion cancellation | Any real normed algebra; no eigenvector choices or commutativity assumption |
| `KernelCrossTerm.lean` | A linear cross term is unbounded on the kernel when its transverse pairing is nonzero | Any real inner product space and continuous linear map; rules out projected-square-only absorption |
| `OrthogonalProjectionParabolic.lean` | Signed diagonal defects, completed gradient square, complementary-gradient cross term, and off-diagonal Young bound | Any real inner product space and finite family of symmetric projector tangents; no completeness or dimension assumption |
| `OrthogonalProjectionWeightedDiffusion.lean` | Two-sector weighted completion, inverse-weight frame cost, and weighted off-diagonal Young bound | Any real inner product space; identities require nonzero weight, dissipation applications require a weight in `(0,1]` |
| `SecondDerivative.lean` | Local second-derivative linearity, constant-vector multiplication/subtraction, and nonnegative second derivative at a continuous local minimum | Real scalar parameters and normed-space values; the minimum sign uses Lean's total derivative |
| `PositiveOperatorKernelCurvature.lean` | Second-order positivity coupling operator curvature, the mixed derivative, and vector-gradient energy at a kernel vector | Any real inner product space; local `C²` regularity, positivity, and symmetry only |
| `RankOneCommutator.lean` | Exact rank-one commutator, arbitrary scalar-shift cancellation, transverse-residual norm bound, and commutation on an eigenvector | Any real inner product space and symmetric bounded operator; no completeness or dimension assumption |
| `OrthonormalOperatorBound.lean` | Squared operator norm bounded by the sum of squared images of an orthonormal basis, with no dimension factor | Real or complex inner-product domain with a finite orthonormal basis; arbitrary normed codomain |
| `IntegralEndpointEstimate.lean` | Extends an integral inequality from interior time pairs to both endpoints | Continuous energy and integrable signed source and dissipation; integrands need not be continuous |
| `FiniteConvolutionEnergy.lean` | Weighted finite Young inequality for a two-input vector kernel, collecting coincident outputs before squaring | Additive commutative group of modes; arbitrary normed additive codomain; no explicit cardinality loss |
| `FiniteGroupedConvolutionEnergy.lean` | Weighted Young inequality with arbitrarily indexed source shifts, including coincident shifts | No injectivity of the source-to-frequency map; costs the actual l1 source weights and l2 receiver energy |
| `FiniteFiberLinearMap.lean` | Distributes a family of linear maps through finite grouped coefficient sums | Any semiring and modules; exact grouping with an explicit covering set |
| `NormalizationStability.lean` | Radius-weighted Lipschitz bound for normalization, including zero reference and target vectors | Any real normed vector space; division only when the application has a positive reference radius |
| `FiniteTwoChannelConvolutionEnergy.lean` | Two separable kernel channels retained independently through convolution energy | Nonnegative source/receiver weights; an l1 source norm and l2 receiver norm in each channel |
| `FiniteMultiplierLocalization.lean` | Exact localization commutator, symbol-variation energy estimate, and small-symbol/tail split | Any normed scalar field and normed vector space; finite supports; all unfavorable modes retained |
| `FiniteVectorConvolution.lean` | Linearity and l1/l2 Young bounds for actual collected scalar-vector convolution | Normed scalar field and normed vector space; arbitrary finite covering output set |
| `FiniteCharacterConvolution.lean` | Evaluating collected convolution equals the product of character evaluations | Any multiplicative character of the additive mode group; arbitrary normed vector codomain |
| `FiniteSumEnergy.lean` | Squared-norm Cauchy--Schwarz for finite linear combinations and its cardinality specialization | Normed scalar field and normed vector codomain; the unweighted version needs only a normed additive group |
| `FiniteCoefficientEnergy.lean` | Nonnegativity, constant scaling, and two-, three-, and finite-sum energy bounds | Arbitrary finite index sets and normed scalar fields; cardinality is explicit where used |
| `QuadraticWeightStability.lean` | Weighted integral stability under L² perturbations and composition of squared approximation errors | Continuous complex amplitudes on compact spaces with finite Borel measures; both error channels remain explicit |
| `LocallyLipschitz.lean` | Finite sums, finite products of coordinates, algebra multiplication, and real scalar multiplication | Local Lipschitz maps on pseudometric spaces; no global constant required |
| `LocallyLipschitzDifferentiability.lean` | Rademacher theorem by compact-ball exhaustion; strong measurability of derivatives of continuous parameter families at fixed parameters | Finite-dimensional real domain and codomain for Rademacher, any additive Haar measure; complete normed codomain and second-countability of either parameter space or codomain for the parameter lemma |
| `FiniteExponentialWeights.lean` | Normalized exponential weights and square-root amplitudes, entropy bound, and mean-cost localization | Any nonempty finite family; the localization temperature is positive |
| `ExponentialAmplitudeDerivative.lean` | Actual normalization derivative, variance identity, common-rate cancellation, and orthogonal radial/angular energy split | Finite scalar score families |
| `GaussianPartitionEnergy.lean` | Gaussian square partitions and derivative energy controlled by their mean squared distance | Real inner product spaces; no compact-support claim |
| `NormScaledGaussianPartition.lean` | Exact norm-squared coverage and total-derivative bounds including zero-amplitude points | Real inner product spaces; differentiability at a norm corner is not assumed |
| `GaussianPartitionRegularity.lean` | Smooth normalized factors and locally Lipschitz norm-scaled amplitudes | Real inner product spaces; supplies genuine almost-everywhere derivatives via Rademacher |
| `EuclideanOperatorCoordinates.lean` | Hilbert matrix coordinates, operator-norm comparison, and rank-one normalization | Finite-dimensional Euclidean operators; no ambient matrix-norm instance changes |
| `EuclideanCrossProduct.lean` | Cross-product bilinearity, cyclic triple product, Lagrange identity, and sharp norm bound | Real three-dimensional Euclidean space, transporting mathlib's coordinate cross product into the L2 norm |
| `EuclideanCrossProductCalculus.lean` | Joint smoothness of the cross product in both inputs | Real three-dimensional Euclidean space; includes varying coherent directions |
| `UnitTorusFourierEnergy.lean` | Parseval, finite-set Bessel bounds, and character coefficient orthogonality for actual measurable functions | Any finite-dimensional unit torus with normalized Haar measure; `MemLp` rather than continuity suffices for the energy bounds |
| `UnitTorusFourierApproximation.lean` | Finite Fourier projections and vanishing total physical L² error for finite families | Continuous complex fields on any finite-dimensional unit torus; neither uniform convergence nor absolute coefficient summability is assumed |
| `UnitTorusFourierUniqueness.lean` | Banach-valued continuous fields are determined by their Fourier coefficients; finite coefficient support gives exact pointwise reconstruction | Derived from scalar L² completeness, full support of Haar measure, and separating continuous linear functionals; no pointwise convergence assumption |

The compact-family and annulus modules construct actual normalized low-output
pressure kernels in `StochasticLagrangian/PressureLowOutputKernel.lean`.
The moment constants remain uniform as the output/input ratio tends to zero.
`SchwartzLinearChange.lean` and `SchwartzDilation.lean` account for the
physical-coordinate and common-frequency-scale costs. The corresponding
low-output pressure band kernels retain quadratic mass smallness and linear
first-moment smallness; these costs are summable over dyadic output ratios.
`EuclideanBilinearCoordinates.lean` and `SchwartzBilinearKernel.lean`
assemble these scalar entries into the actual complex pressure operator,
preserving both gains with the explicit finite coordinate cost.
`EuclideanBilinearCoordinatesTests.lean` checks complex phases, independent
input-coordinate selection, exact reconstruction, and Fourier assembly.
`SchwartzLinearChangeTests.lean` checks orientation, six-dimensional
Jacobian scaling, mass preservation, and first-moment scaling.
`CompactSchwartzFamilyTests.lean` checks the annular boundaries and a
nonconstant amplitude-parameter family. These are new derivations from
mathlib, not external-source ports.

`FundamentalDomainPeriodization.lean` isolates the kernel-independent core
previously housed in the coherent-stretching application and adds weighted
mass transfer. The NS frequency-pair application uses wrapped torus distance,
not the norm of a chosen cell representative, to bound every wrapped spatial
moment by the corresponding Euclidean moment. Its first moment pays the
two physical input-displacement channels with an explicit factor of two.

`TruncatedKernelMoment.lean` and `GeometricMinSeries.lean` handle a kernel
family whose first-moment bound lacks geometric decay while its mass
still decays. Taking the smaller cost gives a summable truncated moment
with an explicit logarithmic loss. In the periodic NS application, bounded
wrapped distance converts this into a true wrapped first-moment budget.
The general truncation lemma does not imply an untruncated whole-space
first-moment bound. Tests include a sharp finite-cutoff example, a
non-dyadic ratio, zero cost, and displacement-cap saturation.

The Gaussian modules construct derivative-controlled spatial NS patches.
Their localization cost is the nearest squared distance plus `τ log N`,
not a factor `N`. The logarithmic cost and inverse-temperature derivative
loss remain explicit. `GaussianPartitionTests.lean`, imported by the main
test module, checks uniform weights, sharp variance, common-rate cancellation,
the zero-amplitude norm corner, and the attained dimension factor. These
modules are new derivations from mathlib, not new external-source ports.

The unit-torus modules transfer mathlib's Hilbert-basis Fourier convergence
to physical integral errors and actual finite projections. The NS weak
derivative identity then gives a simultaneous derivative-energy bound for
the same approximation coefficients. `UnitTorusFourierTests.lean` checks
retained modes, opposite frequencies, and the nonzero error from omitting
a unit character. No pointwise coverage property is inferred from L²
convergence.

`ODE/QuadraticFormBound.lean` is used by
`FluidDynamics/NavierStokes/StochasticLagrangian/LocalVorticityDiffusion.lean`.
That application supplies the actual material vorticity equation and proves
continuity of its viscous source from a common third Fourier-moment envelope.
It retains the scalar strain growth hypothesis explicitly. It is a local
estimate, not an unconditional global regularity theorem.

`AbsolutelyContinuousComparison.lean` extends this interface and reuses its
norm-derivative lemma. `LocalSpectralResidualBudget.lean` applies the extension
to the actual material spectral residual. Absolute continuity and source
integrability are proved from the local PDE solution, including at eigenvalue
collisions; the source size remains a dynamical problem.

The scalar logarithmic estimate is not itself a logarithmic gradient bound or
a BKM theorem. The spatial estimates that would instantiate its hypotheses
must still be proved for the domain and function spaces of the application.

The simple-root theorem is used to construct smooth bottom spectral
projectors through collisions of the two top strain eigenvalues. The
quadratic-form and idempotent calculus then supplies the actual local
bottom-vorticity diffusion identity. In particular, a projector's
material-minus-diffusion rate has a quadratic correction and cannot be
treated as an ordinary tangent rate. The spectral-relation calculus now
cancels the actual principal strain diffusion, retaining the mixed gradient
term. `KernelCrossTerm` isolates why the remaining vorticity-gradient
cross term cannot generally be absorbed by a projected gradient alone.
`OrthogonalProjectionParabolic` proves the alternative exact decomposition:
retain a completed square and isolate the complementary-gradient pairing.
The actual Navier--Stokes application proves the required symmetry and
parabolic defect, instead of assuming that the parabolic rate is tangent.
The weighted extension completes both sector gradient squares. It exposes
the exact inverse-weight cost rather than claiming that a small weight
makes complementary-sector transfer free. The Navier--Stokes application
proves the weighted energy's actual material derivative and Laplacian.
The local-minimum sign lemma also supplies nonnegative top-eigenvalue
curvature without differentiating a choice of eigenvector. The actual
spectral-defect application combines this sign with the quadratic-form
product rule to cancel principal strain and vorticity diffusion.
Testing the positive gap operator on an affine vector curve through a
kernel vector then pays the aligned part of the mixed gradient. The
remaining NS diffusion cost contains only transverse vorticity, with
positive constant regularization still required to pay that cost.
The rank-one commutator identities identify the Fourier pressure-tilt
kernel. A transverse-plane regression has a nonzero commutator but zero
action on the leading direction, distinguishing the full commutator from
the off-diagonal block needed to control that direction.
The orthonormal-basis operator bound supplies a pressure-Hessian `L²`
estimate with no frequency-count factor; a rank-one projection attains
the general bound in the regression suite.
The finite convolution estimate supplies the localization commutator's
energy bound without replacing weighted sums by a mode count. Its
multiplier extension keeps the small-symbol main energy separate from
an explicit tail and the commutator. These estimates do not assert that
the cutoff-weight sums or angular tails are uniformly controlled.
These modules are new derivations using mathlib, not additional adaptations
from the external source below.

`DyadicAnnulusTests.lean` checks exact support endpoints, the zero mode,
unit-frequency weights of one half, very small frequencies, negative inputs,
and smoothness. The original unnormalized bands sum to two at a unit
frequency; they are not silently treated as an exact partition.

`BilinearKernelIntegrabilityTests.lean` checks a genuinely discontinuous
operator-valued indicator kernel, proves its action on constants has integral
six, and proves the kernel is not continuous. Thus this interface is not
silently routed through a kernel-continuity assumption. It also audits the
public integrability and coefficient-sum theorems.

`Tests.lean` checks a path with a nondifferentiable corner, a forced trajectory
crossing zero, a negative growth coefficient, an exponent other than one
quarter, a simple root through a collision of other roots, a moving
quadratic form with nonzero cross terms, a nontrivial rank-one kernel
obstruction, two opposite nonzero diagonal defect blocks, a completed square
with a nonzero tangent swapping two orthogonal sectors, a half-weight
completion and an attained nonzero frame cost, a flat quartic minimum,
constant-vector second-derivative linearity, and the axioms
of the public comparison theorems.
The positive-operator test uses `A(t) = [[t²,t],[t,1]]`: its second-order
form at the kernel direction and increment `(0,-1)` attains zero with
three nonzero terms `2 - 4 + 2`. This checks the mixed-term coefficient.
The convolution tests collect two inputs at the same output, exhibit a
nonzero one-shift commutator, and check that a constant cutoff commutes.
The finite-sum tests attain the scalar Cauchy--Schwarz and three-term
energy factors. In the elliptic pressure application the counted index
is a spatial coordinate, not a Fourier mode or adaptive patch.
The local Lipschitz tests include a nonsmooth scalar factor, a
vector-valued map with a corner, and a parameter-dependent derivative.
The derivative lemmas supply almost-everywhere coordinate derivatives
and measurable derivative energy for the NS spectral cutoff, without
assuming an everywhere differentiable eigenvector selection.

## Provenance and changes

The original three modules (`QuadraticFormBound`, `VariableGronwall`, and
`LogarithmicScaleBound`) adapt selected arguments from
[OpenAI/NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538),
revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`:

- `NavierStokes/ViscousPropagator.lean`: the general inner-product-space estimates,
  excluding construction-specific two-mode equations and existence machinery.
- `Euler/OrdinaryVariableGronwall.lean`: the integrating-factor argument,
  restated directly with ordinary interval integrals and arbitrary endpoints.
- `Euler/LogarithmicCutoffOptimization.lean`: the scale-choice argument,
  generalized to every positive exponent with a sharper intermediate bound.

All adapted files retain Apache-2.0 attribution and modification notices.
The license text is in the repository-root `LICENSES/Apache-2.0.txt`.
Other MeTTapedia files retain their existing licenses. The adaptations target
MeTTapedia's Lean 4.31.0/mathlib version; they do not require the source
repository's Lean 4.34.0-rc2 toolchain.

The local Lipschitz and parameter-derivative lemmas are new derivations
from mathlib's compactness, Rademacher, and measurable-derivative APIs,
not adaptations from either external fluid construction.
The finite-sum and coefficient-energy lemmas likewise derive directly
from norm inequalities and finite Cauchy--Schwarz in mathlib.

## Further translation work

This is a selective integration in progress, not an import of the complete
source library. The following candidates have not been ported:

- Whole-space logarithmic gradient and Sobolev estimates: useful for BKM and
  other PDE work, but the whole-space `L²` hypotheses do not apply to a
  nonzero periodic lift. A periodic version needs its own spatial proof.
- Periodic PDE uniqueness: useful for identifying constructed local solutions;
  this is distinct from finite-dimensional ODE uniqueness. Adapt the viscosity
  and regularity hypotheses explicitly.
- Solenoidal localization and smooth locally finite sums: useful for PDE
  extension and patching. Separate generic gluing statements from the
  particular blowup geometry, reusing mathlib's local-finiteness API.
- Sobolev products, interpolation, heat smoothing, and parameter-dependent
  estimates: compare definitions and dependency costs before selecting each
  reusable statement. A construction-specific wrapper is not automatically
  a general theorem with the same name.

For the Navier--Stokes application, the remaining decisive obligation is a
scale-critical dynamical misalignment/strain budget for the actual unforced
solution. The imported estimates do not supply that bound.

## Verification

From the Lean package directory:

```sh
lake build Mettapedia.Analysis.Tests
lake build Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialVorticityAudit
lake build Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectAudit
```
