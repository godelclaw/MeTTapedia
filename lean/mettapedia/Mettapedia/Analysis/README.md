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
These modules are new derivations using mathlib, not additional adaptations
from the external source below.

`Tests.lean` checks a path with a nondifferentiable corner, a forced trajectory
crossing zero, a negative growth coefficient, an exponent other than one
quarter, a simple root through a collision of other roots, a moving
quadratic form with nonzero cross terms, a nontrivial rank-one kernel
obstruction, two opposite nonzero diagonal defect blocks, and the axioms
of the public comparison theorems.

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
