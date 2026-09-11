# Analysis

Reusable analysis, independent of any particular fluid construction.

## Checked modules

| Module | Mathematical content | Scope |
| --- | --- | --- |
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
| `FiniteTwoChannelConvolutionEnergy.lean` | Two separable kernel channels retained independently through convolution energy | Nonnegative source/receiver weights; an l1 source norm and l2 receiver norm in each channel |
| `FiniteMultiplierLocalization.lean` | Exact localization commutator, symbol-variation energy estimate, and small-symbol/tail split | Any normed scalar field and normed vector space; finite supports; all unfavorable modes retained |
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
| `UnitTorusFourierEnergy.lean` | Parseval, finite-set Bessel bounds, and character coefficient orthogonality for actual measurable functions | Any finite-dimensional unit torus with normalized Haar measure; `MemLp` rather than continuity suffices for the energy bounds |
| `UnitTorusFourierApproximation.lean` | Finite Fourier projections and vanishing total physical L² error for finite families | Continuous complex fields on any finite-dimensional unit torus; neither uniform convergence nor absolute coefficient summability is assumed |

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

The first module is used by
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
