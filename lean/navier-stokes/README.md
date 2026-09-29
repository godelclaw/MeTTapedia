# Navier–Stokes upstream integration

This package uses Lean 4.34.0-rc2 to import the existing OpenAI and
Alpöge–Buckmaster fluid-analysis libraries directly. It is a migration and
integration surface, not another copy of their mathematical developments
and not a completed regularity proof.

The existing MeTTapedia sources are available through `MettapediaFluid` with
`srcDir = ../mettapedia`. The repository's other Lean packages keep their own
toolchains. Compatibility of an existing module with this package must be
checked explicitly; adding the source root does not certify its migration.
The shared library also includes the existing Markov-category kernel interface
imported by the Navier–Stokes semigroup module, and the GSLT linear boundary
reduction and compatibility theorems in `Mettapedia.GSLT.Dynamics`. Its costed
history interface uses the existing `GSLT.Core.LooseRelationEquipment`.

## Pinned dependencies

- OpenAI/NavierStokesAndEuler:
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
- tristanbuckmaster/fluid_lean, package `euler-blowup`:
  `d0124689230b58b4f86e7b90ac59de06404b3b6b`.
- mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`, the upstream
  Lean 4.34.0-rc2 revision.

The explicit mathlib requirement comes last so that its shared transitive
dependency versions take precedence over the older EulerBlowup manifest.

Upstream sources remain in their original package with their original
attribution and licenses. `MettapediaNS.UpstreamAudit` imports the actual
pressure-commutator, viscous-propagator, and arbitrary-positive-viscosity
periodic uniqueness theorems and prints their axioms. It also imports the
existing coherent-pair estimate from the canonical MeTTapedia source tree.
It does not replace their analytic hypotheses with assumptions about the
desired global regularity conclusion.

## Boundary reduction and hidden histories

The imported [linear Schur reduction](../mettapedia/Mettapedia/GSLT/Dynamics/README.md)
retains the affine contribution of internal forcing. Its constrained extension
also retains the equation generating that forcing from the reconstructed
interior. It provides no nonlinear Navier–Stokes inverse or stability bound.

`MettapediaNS.FilteredHistory` uses `InfiniteFilteredEquation` and
`FourierRelaxation` to derive the following identities from the existing
`LocalInfiniteVelocitySolution`. For a static bounded Fourier multiplier `P`,
write `v = P u`, `w = u-v`, and let `R` be the full viscous coefficient RHS:

```text
v' = R(v) + F_P(u)      F_P is the actual pressure-corrected subgrid force
w' = (I-P) R(u)         the hidden modes obey the same unforced evolution
```

`forcing_eq_subgrid` proves that any claimed force in the first equation
equals `F_P(u)`. `reconstructs_unforced_coefficient` proves the converse
coefficient equation when that equality, `P(v+w)=v`, absolute convergence of
the convolution, and the hidden evolution hold. It asserts no existence of
such hidden modes, spatial smoothness, or whole-space realization.

`hidden_mode_history` additionally retains the complete signed history:

```text
exp(d_q t) w_q(t)
  = w_q(0) + (1-P_q) integral_0^t exp(d_q s) N_q(u(s)) ds,
d_q = 4 pi^2 nu |q|^2.
```

Here `N` uses every nonlinear parent and the Leray projection. Time is
physical time. The complex phases, the original hidden datum, and the
coupling to the full field remain. Moving filters would add their time
derivative. Constructing a Schur inverse on a suitable space of these
histories and bounding repeated regeneration remain open.

This distinguishes three embedding questions. Reproducing an exact velocity
on an open region requires matching its differential equation, up to a
pressure gradient; reproducing an angular mean or Fourier observation permits
an effective Reynolds/subgrid force; reproducing an approximate singular
mechanism needs quantitative control of the approximation and its history.
These are different claims.

There is an analytic obstruction to exact local reproduction of the specific
OpenAI construction by an unforced flow: its axial component is zero on an
open annular region and nonzero on the axis inside the same fixed ball at
sufficiently late times. Spatial analyticity of a smooth unforced viscous
solution and the identity theorem exclude such agreement on that ball,
regardless of changes outside it. This inference uses Theorem 2.1,
Remark 2.6 and Claim A.3 of
[Constantin–Ignatova–Vicol](https://arxiv.org/pdf/2609.20803v1).
It is not a Lean theorem here, and does not exclude approximate reproduction
or reproduction of selected observations. Their Theorem 1.1 separately
excludes singularity for an exact shrinking axisymmetric core with its stated
anisotropic mean bounds and analytic forcing, including zero forcing.

The geometric route continues to target the interaction between a coherent
part and its complement. The common-axis estimate and mixed-axis obstruction
in `papers/ns_forced_tail_budget.tex` must be read together: coherent depletion
is controlled for the stated class; a full-datum bound on signed regeneration
through the complement is still required. Boundary elimination must preserve
the stretching observable and its resource accounting, not only velocity.

## Bellman certificates on actual fluid histories

`MettapediaNS.WholeSpaceHistoryBridge` instantiates
`GSLT.Dynamics.BoundaryBellman` with actual smooth, unforced `NSEvolution`
segments on `ℝ³`. Each segment retains its full initial and final velocities,
positive physical duration, and viscosity. Compatible segments concatenate
to another actual evolution. The window state also retains elapsed time.

For each derivative order `n`, `production_integral` identifies the signed
cost with the literal PDE energy production:

```text
cost_n(segment) = integral_segment production_n dt = E_n(end) - E_n(start).
cost_n(segment) + R(end) <= R(start).
```

The second line is the certificate obligation. Composition cancels the
intermediate reserves, without granting a new initial allowance at each seam.
The kinetic case `n = 0` has the proved certificate `R = 0`, by the unforced
energy inequality (`kinetic_bounds`, `kinetic_history_cost_nonpos`).

For `n = 1`, `orderEnergy_le_of_reserve` derives a gradient-energy bound at
every time from a nonnegative reserve certificate for all admissible segments
in the finite window. `hasNSEvolution_of_bellman` then applies the existing
whole-space continuation theorem. Its hypothesis requires such a real-valued
reserve for each horizon, over all full velocity states. The initial value
depends on the full datum. Existence of this stronger certificate is open;
it is not established by the composition theorem or the kinetic-energy case.
A more restricted certificate may instead use a proved reachable-state space.

This cost is ordinary signed order-energy production including full viscous
dissipation. It is not identified with the auxiliary caloric renewal or the
transported-frame energy. Those observables need their own production and
comparison theorems. Likewise, no identification with a Schrödinger bridge
optimizer is asserted. The framework permits such a later consumer while
keeping its fluid realization and analytic bound as explicit obligations.

The next concrete geometric observable is recorded in
[`labs/transported_frame_metric.py`](labs/transported_frame_metric.py) and
`StochasticLagrangian.TransportedFrameMetric`. A transported vector and its
positive frame tensor have an inverse-metric quadratic form whose explicit
strain terms cancel, leaving a nonpositive diffusion square and the exact
forcing term. Its regularized negative logarithm satisfies a drifted HJB
identity with a nonnegative geometric source. The Lean module proves the
finite matrix algebra; the stochastic realization and parabolic comparison
are analytic. Exact unforced shear and Beltrami tests retain the physical
equation and pressure. A bound on the changing metric in the actual
vorticity direction remains open, so this observable is not yet a reserve
for the ordinary order-one production.

`StochasticLagrangian.TransportedFrameDirection` checks the scalar quotient
and HJB algebra needed for that comparison. The metric diffusion loss enters
the physical-to-metric ratio with a positive sign. A logarithmic scalar
renormalization cancels this term from both sides of the corresponding HJB
barrier, leaving the ordinary physical stretching obligation. The exact lab
`transported_frame_direction.py` supplies smooth periodic unforced initial
data with positive stretching and pressure-driven stretching production at
a point where the metric diffusion cost is zero. This excludes a proposed
local payment by that cost alone; full-datum reserves and joint tensor,
pressure and history corrections remain open. The existing
`LocalMaterialStretching.hasDerivAt_stretchingAlong` supplies an actual
material-evolution identity for this retained stretching variable.

## Checked applications and semantic interfaces

| Module | Reused mathematics | Exact remaining boundary |
| --- | --- | --- |
| `MettapediaNS.WholeSpaceBKM` | OpenAI's actual vorticity norm, norm-path continuity, and logarithmic gradient estimate. The adapter proves equality with the existing spatial essential supremum, including its extended value, and applies the estimate to the existing transported-velocity interface. | Euclidean smooth fields with actual L² jets; the physical-time vorticity budget and the required realization of the velocity remain obligations. A nonzero periodic lift is not a whole-space L² field. |
| `MettapediaNS.WholeSpaceViscousFlow` | OpenAI's smoothing operators, bounded regularized transport, global Lipschitz Picard theorem, time integrals and smooth-field algebra; the Laplacian and dissipation identity of `WholeSpaceViscousEnergy`. A bounded quadratic field conserving energy plus a bounded dissipative linear field has a global forward flow with nonincreasing norm (truncation by a ball retraction, which keeps the energy balance). For every smoothing operator `S` the regularized viscous term `ν S Δ S` is bounded on `L²` with `⟪u, ν S Δ S u⟫ = -ν ∑ᵢ ‖∂ᵢ S u‖²`, so the regularized Navier–Stokes equation has global forward `L²` solutions, and smooth regularized evolutions with all `L²` jets exist from every smooth solenoidal datum on every interval. The viscous term contributes `-2ν` times the smoothed dissipation to every integer-order energy production, so the upstream tame estimate gives `H³` and all-order bounds on the regularized Euler lifespan of the datum, uniform in the smoothing and the viscosity (`regularizedViscous_all_order`). On solenoidal fields `‖S Δ S A − Δ A‖ ≤ 6 ε M` with the upstream regularization error `ε` (`viscous_error`), and the regularized viscous evolutions are Cauchy in continuous `L²` as the smoothing is removed (`regularizedViscous_cauchy`). Along OpenAI's smooth limit the Laplacians converge with the second-order word paths, the regularized derivatives converge to `P(-(u·∇)u) + ν Δu`, and the limit satisfies the Navier–Stokes equations at every point with the constructed pressure: every smooth solenoidal field with all derivatives in `L²` starts a smooth Navier–Stokes evolution on `ℝ³`, for every `ν ≥ 0`, on the regularized Euler time of its `H³` energy (`exists_local_nsEvolution`). Two such evolutions separate in `L²` at most like `exp (K t)` with `K` a gradient bound (the viscous term only helps; `NSEvolution.l2_stability`), so evolutions with the same initial velocity agree (`NSEvolution.velocity_eq_of_initial`). | Local existence and uniqueness. Maximal lifespans and the continuation criteria are in the two rows below; nothing here bounds a solution beyond its local interval. |
| `MettapediaNS.WholeSpaceNSContinuation` | OpenAI's Helmholtz projection, derivative-word constraints, interval concatenation, strong-time lifting, variable-coefficient Gronwall estimate and `H³` transport estimate. The Laplacian of a solenoidal field is solenoidal, so the `L²` time derivative of every smooth evolution is `-P((u·∇)u) + ν Δu`, a function of its velocity alone, and its pressure is the canonical Helmholtz pressure (`NSEvolution.derivative_toLp_projected`, `NSEvolution.pressureForce_eq`). Evolutions restrict to shorter intervals, two evolutions that meet glue to one (`NSEvolution.concatenate`), and every evolution extends by the local existence time of its final velocity (`NSEvolution.exists_extension`). Data therefore have smooth evolutions on every finite interval or a finite maximal lifespan (`global_or_lifespan`), and the evolutions on shorter intervals agree (`NSLifespan.evolution_agrees`). The gradient supremum is a continuous path and its time integral controls the `H³` energy, the viscous term only helping (`NSEvolution.h3_energy_gradientIntegral`). The local existence time depends only on the `H³` energy, so a bounded gradient integral would give a uniform restart time and an evolution past a finite maximal time: at a finite maximal time the gradient integrals are unbounded, and so is the gradient on every final segment (`NSLifespan.gradientIntegral_unbounded`, `NSLifespan.gradient_unbounded_near_endpoint`). No rescaling is used, so the viscosity is never changed. | Whole-space `SmoothL2Field` data with all derivatives in `L²`, `ν ≥ 0`. This is continuation, not a bound: nothing here controls the gradient of any solution. |
| `MettapediaNS.WholeSpaceNSBlowup` | OpenAI's transport cancellation, pressure pairing, vorticity norms, whole-space logarithmic gradient estimate, logarithmic Gronwall argument and nonnegative improper integrals; the spatial essential-supremum identification of `MettapediaNS.WholeSpaceBKM`. The kinetic energy of every smooth evolution does not increase (`NSEvolution.l2_norm_le`), so the logarithmic estimate bounds the gradient integral by the vorticity integral (`NSEvolution.gradientIntegral_of_vorticity_bound`) and the vorticity integrals are unbounded at a finite maximal time (`NSLifespan.vorticityIntegral_unbounded`). The evolutions on shorter intervals define one smooth solution on the half-open maximal interval, with continuous jets (`NSLifespan.maximalField_eq_evolution`, `NSLifespan.maximalField_jet_continuous`), and the route's spatial essential-supremum integrand of its curl has infinite extended integral over that interval (`NSLifespan.spatialEssentialSupNorm_lintegral_eq_top`). Hence data have smooth evolutions on every finite interval or blow up in this sense at a finite time (`global_or_vorticity_blowup`), and bounds on the vorticity integrals on every finite horizon give global existence (`hasNSEvolution_of_vorticityIntegral_bound`). | The Beale–Kato–Majda criterion on `ℝ³` for the smooth `L²` class. The finite-horizon vorticity bound for arbitrary data is the open estimate; this module supplies none. |
| `MettapediaNS.WholeSpaceTimeSmooth` | OpenAI's strong-time lifting (a pointwise time derivative with continuous jets gives the `L²` derivative of every derivative word, and an `L²` derivative gives pointwise derivatives up to the endpoints), jet continuity of products with Sobolev-embedded coefficients, and the Helmholtz projection. The time-derivative relation is preserved by sums, linear maps, directional derivatives, the Leray projection and the Laplacian, and the advection field obeys the product rule (`TimeDeriv.advection`). The velocity of every smooth evolution has the pressure-free right-hand side as its time derivative, so by induction it has time derivatives of every order, each a path of smooth fields with continuous jets (`NSEvolution.isTimeSmooth`); so does the pressure force. | Time regularity of a given evolution; it bounds nothing. |
| `MettapediaNS.WholeSpaceJointSmooth` | The mean value inequality and Sobolev embedding. A path with a time derivative defines a function of space and time whose derivative within `ℝ³ × [0, T]`, at every point including the endpoints, is the spatial derivative plus the time derivative (`hasFDerivWithinAt_joint`). In coordinates this derivative is built from paths that are again smooth in time, and induction gives `C^∞` on `ℝ³ × [0, T]` (`contDiffOn_joint_infty`). The velocity and the pressure force of every smooth evolution are `C^∞` in space and time (`NSEvolution.velocity_contDiffOn`). | Smoothness of a given evolution on its interval. |
| `MettapediaNS.WholeSpacePressurePotential` | OpenAI's radial potential of smooth gradient fields. Time derivatives of gradient paths are gradients, since the gradient fields form a closed subspace. The radial potential has an explicit derivative within `ℝ³ × [0, T]`; its time part is paid uniformly along the radial segment by the mean value inequality. The scalar pressure of every smooth evolution is `C^∞` in space and time, with gradient the pressure force (`NSEvolution.scalarPressure_contDiffOn`, `NSEvolution.scalarPressure_gradient`). | Smoothness of a given evolution's pressure. |
| `MettapediaNS.WholeSpaceOfficialStatement` | The official whole-space statement (A) with zero force, `OfficialWholeSpaceProblem.WholeSpaceStatementA`, adapted from Formal Conjectures like the periodic target. Rapidly decaying data are smooth `L²` fields, since every derivative is bounded by a multiple of `(1 + |x|)⁻⁴` (`memLp_of_decay`). Evolutions on `[0, n + 1]` agree by uniqueness and glue into a velocity and a scalar pressure that are `C^∞` on `ℝ³ × [0, ∞)`, solve the equation with the one-sided time derivative at time zero (`global_navier_stokes`), and have kinetic energy at most that of the data. Global existence of the smooth evolutions therefore gives statement (A) (`wholeSpaceStatementA_of_global`), and so do finite-horizon bounds on the vorticity integrals (`wholeSpaceStatementA_of_vorticityIntegral_bound`). | Conditional. The finite-horizon vorticity bound for arbitrary data is the open estimate. |
| `MettapediaNS.WholeSpaceOrderEnergy` | OpenAI's derivative words, transport-commutator recursion, transport cancellation and pressure orthogonality (`eulerRhs_pairing`), the `L⁶` Sobolev inequality for smooth `L²` fields and `L⁴` interpolation; mathlib's Hölder inequality. The energy `Eₙ = Σ_{|w|=n} ‖∂_w u‖²` of the derivatives of order exactly `n` has, for the literal Navier–Stokes right-hand side, the exact production `-2 Σ ⟪[∂_w, u·∇]u, ∂_w u⟫ - 2ν Eₙ₊₁` (`orderProduction_navierStokesRhs`). The commutators of words of length two and three are expanded into three and seven advection terms (`transportCommutator_two`, `transportCommutator_three`), each paired by Hölder's inequality with exponents `4, 4, 2` in the order that keeps the estimate linear (`advection_bound_442`, `advection_bound_424`, `advection_bound_244`). With `‖f‖₄⁴ ≤ ‖f‖₂ ‖f‖₆³` and `‖f‖₆² ≤ 3S² Σᵢ ‖∂ᵢf‖₂²`, the squared `L⁴` norms of order `n` sum to at most `(9ⁿ · 27 S⁶ Eₙ Eₙ₊₁³)^(1/4)` (`quarticEnergy_pow_four_le`), and a fourth-power absorption gives, when `E₁ ≤ Z`, `production₂ ≤ -ν E₃ + M(ν, Z) E₂` and `production₃ ≤ -ν E₄ + (M₃(ν, Z) + G (1 + E₂)(1 + E₃)) E₃` with explicit constants (`orderProduction_two_le`, `orderProduction_three_le`). | Inequalities for one smooth solenoidal field; they bound no evolution by themselves. |
| `MettapediaNS.WholeSpaceEnstrophyContinuation` | OpenAI's variable-coefficient Grönwall estimate and interval integrals; the lifespans and restart argument of `MettapediaNS.WholeSpaceNSContinuation`. Along a smooth evolution with `ν > 0` whose gradient energy `E₁ = ‖∇u‖₂²` stays below `Z`, the energy does not increase, `E₂` grows at most like `exp(M t)` (`NSEvolution.orderEnergy_two_le`), `ν ∫ E₃` is bounded (`NSEvolution.dissipation_three_le`), `E₃` obeys Grönwall's inequality with a rate whose integral these two facts bound (`NSEvolution.orderEnergy_three_le`), and the `H³` energy is bounded on every finite horizon by an explicit constant (`NSEvolution.wordEnergy_three_le`). The local existence time depends only on the `H³` energy, so at a finite maximal time the gradient energies are unbounded (`NSLifespan.not_orderOne_bounded`, `NSLifespan.orderOne_unbounded`), which is Leray's criterion. Finite-horizon bounds on the gradient energy give global evolutions (`hasNSEvolution_of_orderOne_bound`) and the official statement (A) (`WholeSpaceOfficial.wholeSpaceStatementA_of_orderOne_bound`). | Conditional, with `ν > 0`. The target is subcritical: a finite-horizon bound on `‖∇u‖₂` for arbitrary data, the quantity the enstrophy identity controls. No such bound is proved. |
| `MettapediaNS.WholeSpaceBetchov` | OpenAI's integration by parts for smooth `L²` fields, advection product rule and solenoidal derivative words; the trace algebra and middle-eigenvalue inequality of `MiddleEigenvalueAlgebra`. For a smooth solenoidal field with all derivatives in `L²` and gradient `A a b = ∂_b u_a`, the square and cube traces are divergences of fluxes that are sums of products of two smooth `L²` fields, so `∫ tr(A²) = 0` and `∫ tr(A³) = 0` (`integral_trSq_eq_zero`, `integral_trCube_eq_zero`; Betchov's identity on `ℝ³`). The order-one production is `-2 ∫ Σ A_ji A_kj A_ki - 2ν E₂` (`orderProduction_one_eq`); with Betchov's identity it equals `-(8/3) ∫ tr(S³) - 2ν E₂`, and `-(4/3) tr(S³) ≤ 2 max(λ₁, 0) |S|²` gives production at most `2 K E₁` whenever `K ≥ 0` bounds the middle strain eigenvalue (`orderProduction_one_le`). Along evolutions the gradient energy is at most `E₁(0) exp(2 ∫ K)` (`NSEvolution.orderEnergy_one_le_of_middle`), so continuous majorants of the positive middle eigenvalue with bounded time integrals give global evolutions (`hasNSEvolution_of_middle_bound`) and the official statement (A) (`WholeSpaceOfficial.wholeSpaceStatementA_of_middle_bound`). | Conditional, with `ν > 0`: the same sheet-forming strain criterion as `MiddleEigenvalueCriterion` on the torus. The criterion is stated with continuous majorants of the middle eigenvalue on each closed interval. No bound on the middle eigenvalue is proved. |
| `MettapediaNS.WholeSpaceViscousEnergy` | OpenAI's derivative-word fields, whole-space integration by parts, and nonlinear H³ energy estimate. The constructed Laplacian is identified with mathlib's actual Laplacian; its production is exactly minus twice the derivative-word dissipation. The full unforced NS right-hand side therefore retains the same nonlinear bound with dissipation on the left. | These are spatial right-hand-side identities and estimates. A time-dependent solution must still supply its actual evolution and regularity, and the gradient/vorticity coefficient must be controlled. |
| `MettapediaNS.AlmostOrthogonality` | Direct semantic aliases of Alpöge–Buckmaster's C*-ring and Hilbert-space Cotlar–Stein theorems. Neither proof is copied or reimplemented. | Both adjoint cross-product bounds and the row/column majorant bounds must be established for the actual localized operators. |
| `MettapediaNS.QuadraticSingularIntegral` | Alpöge–Buckmaster's sharp-truncation, smooth-truncation, and principal-value `L^p` bounds. The adapter constructs the angular hypotheses for the explicit kernels `x_i*x_j / ‖x‖^5` (`i ≠ j`) and `(x_i² - x_j²) / ‖x‖^5`, using mathlib's orthogonal changes of variables and compactness. | Whole-space inputs: bounded compactly supported fields for the truncations, smooth compactly supported fields for the principal value, finite `p > 1`. The constants are independent of the truncation radii; the smooth version also permits every cutoff satisfying the stated support/range conditions. The modules below identify and assemble the actual whole-space strain on smooth compactly supported sources. Periodic transfer, weighted costs, and physical-time control remain separate obligations. |
| `MettapediaNS.WholeSpaceBiotSavart` | Alpöge–Buckmaster's proved `potential_theory_R3` and actual Newtonian Biot–Savart construction. Its velocity is smooth and in `L²`; for divergence-free vorticity, its divergence vanishes and its curl recovers that vorticity in both OpenAI's and the pancake route's APIs. The actual velocity-gradient entries are represented using the imported Newtonian gradient kernel on source derivatives. | Smooth compactly supported vorticity on `ℝ³`. The modules below supply the trace-free Hessian identification, derivative-free component bounds, full strain assembly, and all `L²` velocity jets for divergence-free inputs. General admissible data, physical-time evolution, and the signed budget remain separate obligations. |
| `MettapediaNS.NewtonianHessianPrincipalValue` | The upstream regularized Newtonian potential, integration by parts, convergence against test functions, and principal-value integrability. These identify the actual off-diagonal Newtonian Hessians and differences of diagonal Hessians with the upstream principal-value operators, including the factor `-3/(4π)`. The previously imported `L^p` estimates now bound those actual derivatives by the undifferentiated source norm. | Smooth compactly supported scalar sources on `ℝ³`, finite `p > 1`. Radial cancellation removes the local term for these trace-free components; no such cancellation is asserted for an individual diagonal entry. Full-strain assembly is supplied below. General-data/periodic transfer, weighted projector costs, and signed physical-time control remain open. |
| `MettapediaNS.WholeSpaceStrain` | The existing pancake `strainRateApply` is identified with mathlib's self-adjoint part of the actual Biot–Savart gradient. Its entries are explicit combinations of the imported principal-value operators: local isotropic terms cancel before estimation. All nine entries and the complete operator satisfy `L^p` bounds by the undifferentiated vorticity norm. Assembly uses OpenAI's multilinear coordinate estimate, mathlib's isometric currying, and its finite-sum `L^p` inequality. | Smooth compactly supported vorticity on `ℝ³`, finite `p > 1`; the constant is independent of the source. Actual `MemLp` is also proved. This supplies no `L^∞` endpoint, derivative-weighted projector estimate, general-data/periodic extension, or signed physical-time budget. |
| `MettapediaNS.WholeSpacePressure` | OpenAI's smooth Helmholtz pressure field, normalized radial scalar potential, and preservation of solenoidality by actual derivative words. The constructed pressure is an actual smooth scalar gradient, and the full viscous right-hand side is divergence-free for solenoidal input. The H³ production estimate no longer takes an independently supplied pressure or gradient-space hypothesis. | An actual `SmoothL2Field` input is required. The module constructs a spatial NS right-hand side, not a solution trajectory. No physical-time equation or budget is assumed to follow from the construction. |
| `MettapediaNS.WholeSpaceBiotSavartRegularity` | OpenAI's `smoothL2Field_of_curl_compact` applies directly to the smooth finite-energy Biot–Savart velocity constructed using Alpöge–Buckmaster. Every actual Fréchet derivative is in `L²`, and the closed solenoidal-space condition is proved. The existing spatial BKM estimate and viscous H³ production bound now apply with velocity jets and pressure both constructed from the source. | Smooth compactly supported divergence-free vorticity on `ℝ³`. Compact vorticity is not asserted to persist under viscous evolution. General-data extension, actual time evolution, weighted projector costs, and the signed physical-time bound remain open. The constant time path in the BKM notation represents one spatial slice only. |
| `MettapediaNS.ForcedPathEnergy` | OpenAI's smooth-field time differentiation and variable Grönwall estimate; the whole-space Betchov and order-two energy estimates. The force adds at most `2 √Eₙ(u) √Eₙ(f)` to the order-`n` production. A nonnegative continuous majorant `K` of the middle strain eigenvalue gives `1 + E₁(t) ≤ (1 + E₁(0)) exp ∫(2K + √E₁(f))`; a bound on `E₁` gives the analogous order-two estimate. Uniform integral bounds for `K` and uniform force bounds give energy bounds independent of shorter slab endpoints. | Actual forced smooth `L²` paths with all spatial jets continuous in time. The middle-eigenvalue integral remains a hypothesis. |
| `MettapediaNS.ForcedCandidatePancake`, `MettapediaNS.OpenAISolutionPancake` | OpenAI's compact smooth time fields turn each candidate's actual velocity, pressure and force into a `ForcedPath` on every compact slab starting at `1/2`. Smooth compact forcing has uniformly bounded order-one and order-two energies across time one. A uniform middle-eigenvalue integral would then bound `E₁` and `E₂`; the existing whole-space `H²` embedding and the candidate's kinetic-energy bound would bound speed, contradicting its blow-up (`no_uniform_middle_majorants`). The second module applies this theorem to the actual fields constructed by `NavierStokesR3.theorem_1_1` for every positive viscosity. | No family of nonnegative continuous middle-eigenvalue majorants on the slabs exhausting `[1/2, 1)` has uniformly bounded integrals. The theorem excludes budget derivations that also apply to smooth compactly supported forcing. It proves no unforced budget and does not identify a literal middle-eigenvalue essential-supremum integral. |
| `MettapediaNS.ForcedSignedBudget` | Integration by parts gives the actual gradient-energy force work `-2 ⟪u, Δf⟫`, bounded in absolute value by `6 √E₀(u) √E₂(f)`. The exact integrated energy balance retains signed nonlinear production, viscosity and force work separately. Bounded kinetic energy and smooth compact forcing give a finite force allowance independent of the shorter slab. The constructed candidate has unbounded gradient energy, so even signed nonlinear production minus full viscous dissipation has no uniform upper allowance (`no_uniform_signed_production_budget`). The theorem applies directly to `NavierStokesR3.theorem_1_1` for every positive viscosity. | Full-field statement on the slabs exhausting `[1/2, 1)`. The continuous production path is identified with `-2 ∫ cubicSelf(∇u)`. Its coefficient `c = 2ν` subtracts full dissipation and `c = ν` subtracts half. This module has no frequency projector and supplies no unforced budget. |
| `MettapediaNS.ForcedCandidateVorticity` | Alpöge–Buckmaster's Green representation, Newtonian derivative commutation, and gradient kernel; mathlib's Hölder inequality and local integrability of `‖z‖^(-α)`, `α < 3`. A smooth, compactly supported, divergence-free velocity is proved equal to the Biot–Savart velocity of its own curl. For `p > 3` and compact `K`, one constant gives `‖v(x)‖ ≤ C (∫ ‖curl v‖^p)^(1/p)` for all such velocities supported in `K`. Applied to every whole-space candidate of OpenAI's Theorem 1.1 (`CandidateProperties`), `∫ ‖curl u(t)‖^p` is unbounded for `0 < t < 1`, including the eighth moment. | The statement is proved for every candidate satisfying the problem statement's properties; `MettapediaNS.OpenAISolutionVorticity` applies it to the constructed solution. The candidates are forced. The theorem excludes bounds on these moments, finite up to the singular time, whose derivations also hold for smooth compactly supported forcing. It does not bound any unforced solution. |
| `MettapediaNS.OpenAISolutionVorticity` | OpenAI's `NavierStokesR3.theorem_1_1`, imported with its full construction (rebuilt here; its axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`). | For every positive viscosity, the constructed forced solution has no global finite-energy competitor and an unbounded eighth vorticity moment before time one. This is a statement about forced solutions; it bounds no unforced solution. Importing the construction adds about 520 upstream modules to this target's first build. |
| `MettapediaNS.OpenAIPeriodicWiener` | OpenAI's periodic corollary (`NavierStokes.PeriodicPaper.periodic_corollary`), imported with its construction, and the Fourier inversion of smooth one-periodic fields from the periodic Fourier development. The velocity Wiener norm of the coefficients dominates the real field, so along every periodic candidate the velocity Wiener norm of the time slices is unbounded arbitrarily close to time one. | For the unforced problem, a bound on this norm along tame solutions gives the official periodic statement (`FourierCascadeContraction.periodicStatementB_of_velocityWienerBound`). The forced periodic candidates, whose force is smooth, violate the corresponding bound, so a derivation of that bound must use the absence of forcing. This bounds no unforced solution. Importing the periodic Fourier development adds its modules to this target's first build. |
| `MettapediaNS.OpenAIPulseSeeds` | OpenAI's reference pulse envelope (`NavierStokes.PrimaryPulseBounds.referenceP`) and its Gaussian bounds (`NavierStokes.GaussianEnvelope.reference_gaussian_bounds`). Each primary pulse starts from the seed `referenceP lam u L 0`, which lies between `exp(-u·maxSlope·L/8)` and `exp(-u·minSlope·L/8)`; the amplification from seed to midpoint is at least `exp(u·minSlope·L/8)`, and once the slot length exceeds a multiple of `log(1/Q)` the seed is at most `Q^N`. | The construction's slots have length of order `log²(1/Q)` in a band of scale `Q`, so the seeds it plants are smaller than every power of the band scale. The amplitude equation is linear: by uniqueness of linear solutions, the solution started from any seed `σ e₁` is `σ / P(0)` times the constructed pulse at every time of the slot (`seeded_eq_smul_fundamental`), hence at least `|σ| exp(u·minSlope·L/8)` times its size (`norm_seeded_ge`). A seed that is only polynomially small in the band scale is amplified super-polynomially beyond the constructed pulse. This is a statement about the forced construction; it bounds no unforced solution. |
| `MettapediaNS.SwirlBudget` | OpenAI's Navier–Stokes residual (`NavierStokesR3.ProblemStatement.navierStokesResidual`) and its operators; mathlib's product and chain rules. At every point where the velocity is twice differentiable in space and differentiable in time, the angular momentum density `Γ = x₀u₁ − x₁u₀` about the third axis satisfies `∂ₜΓ + (u·∇)Γ = ν(ΔΓ − 2ω₃) − (x₀∂₁p − x₁∂₀p) + (x₀f₁ − x₁f₀)`, with `f` the residual and `ω₃` the axial vorticity (`swirl_identity`). The angular derivative of a C¹ function is its derivative along the rotations about the axis, so its integral over every circle about the axis vanishes (`integral_angularDeriv_rot`, `integral_angularDerivative_rot`). Mathlib's second-derivative test gives a nonpositive second derivative at every local maximum (`deriv_deriv_nonpos_of_isLocalMax`, `secondDeriv_nonpos_of_isLocalMax`); for an axisymmetric flow the pressure's angular derivative vanishes and, at a critical point of the swirl off the axis, so does the axial vorticity (`axialVorticity_eq_zero_of_critical`), so at every such spatial local maximum `∂ₜΓ ≤ x₀f₁ − x₁f₀` (`deriv_swirl_le_torque_of_isLocalMax`). Maximizing `Γ − εt` over a compact region of space-time gives the maximum principle: for an axisymmetric flow whose force has nonpositive torque and whose swirl is nonpositive outside a compact set, the swirl never exceeds its initial maximum (`swirl_le_of_axisymmetric`). | The pressure drops out of the averaged swirl, and the force enters only through its torque. An axisymmetric unforced flow cannot increase its maximal swirl, so a collapse whose maximal swirl grows must break axisymmetry and draw that growth from the torque of its non-axisymmetric part; `MettapediaNS.AveragedSwirl` treats the averaged swirl of a flow with no symmetry. The identity is pointwise; it bounds no solution. |
| `MettapediaNS.AveragedSwirl` | The swirl identity and angular averaging of `MettapediaNS.SwirlBudget`; mathlib's parametric interval integrals, second-derivative test and compactness bounds. For a flow with no symmetry, integrate the swirl over the circles about the axis. At every spatial local maximum of that circle integral off the axis, `∂ₜ∮Γ ≤ −∮(u·∇)Γ + ∮(x₀f₁ − x₁f₀)` (`deriv_circleInt_swirl_le`). Along the circle the pressure's angular derivative integrates to zero; the Laplacian of the swirl integrates to a nonpositive number, since the second derivatives of the circle integral along the coordinate lines are nonpositive and the trace is invariant under the rotations (`integral_laplacian_nonpos`, `sum_rot_basis`); and the axial vorticity integrates to zero, because `x₀∂₀Γ + x₁∂₁Γ = r²ω₃ + ∂_θ(x₀u₀ + x₁u₁)` holds for every velocity (`fderiv_swirl_horiz`, `integral_axialVorticity_eq_zero`). Maximizing the tilted average over a compact region of space-time gives the swirl budget: if at every spatial maximum the averaged advection and torque are at most `g(t)` for a continuous `g ≥ 0`, the circle integral of the swirl never exceeds its initial maximum plus `∫₀ᵗ g` (`circleInt_swirl_le_budget`). The rotation-equivariant mean velocity `ū` commutes with the rotations (`meanVel_rot`), so at a maximum it carries no net swirl in (`integral_fderiv_meanVel_eq_zero`): only the fluctuation `u − ū` does (`deriv_circleInt_swirl_le_fluct`). The circle integral is differentiable and invariant under the rotations (`hasFDerivAt_circleInt`, `circleInt_rot`), so every point of a maximizing circle is a maximum (`isLocalMax_circleInt_rot`) and the torque at the peak is the fluctuation term `−∮(u′·∇)Γ′`, with `Γ′` the deviation of the swirl from its circle average (`deriv_circleInt_swirl_le_reynolds`). | The circle-averaged swirl can grow at its maxima only through the averaged advection of the swirl and the averaged torque, and its maximum can grow only by the time integral of these at the running maximum. For an axisymmetric flow the averaged advection vanishes at the maximum; in general it is the angular momentum that the non-axisymmetric part carries into the maximum. Hypotheses: a space-time `C²` velocity, a pressure `C¹` in space and a force continuous in space at the given time. It bounds no solution by itself. |
| `MettapediaNS.CirculationFlux` | The circle integrals, rotation-equivariant mean and Reynolds form of `MettapediaNS.AveragedSwirl`; mathlib's parametric interval integrals, fundamental theorem of calculus and `C¹` criterion. The circle integral of the swirl is the circulation around the circle, and it equals the flux of axial vorticity through the disk the circle bounds: `∮Γ = ∫₀¹ s r² (∮ ω₃ over the circle of radius s r) ds` (`circleInt_swirl_eq_flux`), because the radial derivative of the circulation is `s r² ∮ω₃` plus an angular derivative (`fderiv_swirl_ray`, `hasDerivAt_circleInt_ray`). The mean velocity is `C¹` (`hasFDerivAt_meanVel`, `contDiff_meanVel`) and its swirl is the averaged swirl (`swirlSlice_meanVel`). Since `(U·∇)U = ∇(|U|²/2) − U × ω`, the advection of the swirl is an angular derivative minus the swirl of the vortex force (`fderiv_swirl_self`), so around every circle `−∮(U·∇)Γ = ∮Γ(U × ω)`, with `Γ(U × ω) = r (U_z ω_r − U_r ω_z)` the rate at which `U` sweeps vortex lines across the circle (`circleInt_advection_eq_vortexForce`). At every spatial local maximum of the averaged swirl off the axis, `∂ₜ∮Γ ≤ ∮Γ(u × ω) + ∮(x₀f₁ − x₁f₀)` (`deriv_circleInt_swirl_le_vortexForce`) and, with `u′ = u − ū` and `ω′ = curl u′`, `∂ₜ∮Γ ≤ ∮Γ(u′ × ω′) + ∮(x₀f₁ − x₁f₀)` (`deriv_circleInt_swirl_le_eddyFlux`). | The largest axial vortex flux through a disk about the axis grows only as fast as the fluctuation velocity carries fluctuation vorticity across the disk's rim, plus the torque of the force; the axisymmetric part of the flow cannot raise it. Hypotheses as in `MettapediaNS.AveragedSwirl`. It bounds no solution by itself: the sign and size of the eddy vortex flux are the open dynamical question. |
| `MettapediaNS.HelicalPhaseSelection` | Integer phase counts for two parents and their conjugates. With angular indices `2k,2(k+1)` and common positive axial index one, a product with zero angular index and nonzero axial index uses at least `2k+1` factors (`minimum_order_adjacent`). The `(2,4)` and `(6,8)` cases have explicit sharp witnesses of orders three and seven; below order seven, every angular mean from the latter pair has axial index zero (`axial_zero_before_seven`). | Finite arithmetic only. It proves neither that an allowed interaction coefficient is nonzero nor a statement about a PDE solution. The amplitude-derivative application and its restricted-family history estimates are analytic results in the symmetry-defect note, described in the labs README. |
| `MettapediaNS.HelicalHighModeFeedback` | Finite algebraic sign certificates: the circulation heat bracket is positive for real angular index at least five (`circulationHeatBracket_pos`), and the rational negative-pressure allowance is less than one for real angular index at least six (`pressureAllowanceRatio_lt_one`). | The heat-resolvent identities, full signed enstrophy interpretation, and short unforced evolution estimates remain analytic arguments in the symmetry-defect note. This module proves no PDE bound. |
| `MettapediaNS.HelicalParentMomentum` | Pressure cancellation in the tangential/axial scalar equations at a critical circulation circle (`hasDerivAt_momentum`), conservation of the squared modulus for the resulting rotation ODE (`normSq_eq_initial`), and the Gram inequality controlling that momentum by the two velocity components (`momentum_normSq_le`). | Scalar ODE and algebra only. The cylindrical linearized Euler interpretation and the absence of a parent-history bound uniform in time and viscosity are analytic arguments in the symmetry-defect note. No nonlinear remainder or recurrent cascade is controlled. |
| `MettapediaNS.WholeSpacePressureRecovery` | OpenAI's instantaneous weak pressure identities, Fourier `H³` bound, Riesz Poisson identity, and harmonic-functional uniqueness identify the constructed Helmholtz pressure gradient with the double-Riesz pairing of the actual velocity tensor on every compact smooth scalar test. The required instantaneous equation is realized by an explicit affine tangent with the actual constructed viscous right-hand side. | Smooth solenoidal `SmoothL2Field` inputs on `ℝ³`. The tangent satisfies the equation at time one only; no solution on a time interval is asserted. The test identity is not a physical-time estimate. |
| `MettapediaNS.WholeSpacePressureFlux` | The constructed-pressure test identity discharges OpenAI's generic compact-flux identification theorem. Its complete cutoff-flux estimate, including the localized Sobolev term and heat-kernel commutator term, then bounds the actual scalar pressure flux. The `L³` membership and tensor `L¹` bound are supplied using upstream Sobolev estimates and mathlib integrability. | The flux identity permits every compact smooth cutoff. The quantitative application uses the upstream radial weight with `R ≥ 1`; its constant is independent of `R` but depends on the velocity slice's `L²` and `L³` norms. This is neither a uniform physical-time bound nor an estimate for arbitrary anisotropic pancake/projector weights. All-scale summation and the signed misalignment budget remain open. |

`MettapediaNS.RieszDoubleCommutator` applies OpenAI's heat-kernel
commutator twice and its Riesz self-adjointness once. The resulting signed
quadratic localization defect retains the squared difference of the
multiplier `φ²` before taking norms. For `0 ≤ φ ≤ 1` with Lipschitz bound
`L/R`, its kernel has majorant
`C max(2L,1)² |x-y|⁻³ min(|x-y|/R,1)²`.
This is bounded by `C max(2L,1)² R⁻¹` times the **existing upstream radial
kernel to the power `2/3`**. Mathlib's power change of exponent and Hölder
inequality therefore give actual section integrability for `L²` sources
and an `R^(-3/2)` pointwise bound. No radial integration theorem, Fourier
operator, or heat representation is reimplemented.

For Schwartz tests representing `f`, `φ² f`, and `φ⁴ f`, the checked defect is
`∫(φ² f) T(φ² f) - ∫(φ⁴ f) Tf`, where `T` is the actual upstream double
Riesz transform. Its norm is at most
`C max(2L,1)² R^(-3/2) ‖f‖₁ ‖f‖₂` with a source-independent constant.
The identity is bilinear and gives the usual real quadratic-form identity
on real tests. This differs from the single-commutator `L¹`-`L⁴` estimate;
the bounds have different source norms and are not pointwise comparable
without further assumptions. Matching this defect to the full signed NS
residual, extending beyond the test class, controlling moving projectors,
and paying the scale/time coefficients remain obligations.

`MettapediaNS.PressureLocalizationDifference` handles distinct source and
receiver fields. Write `χ = φ²` and `P(g,ψ) = ∫ g Tψ`. For actual Schwartz
tests `ψh = χψ` and `ψhh = χ²ψ`, it proves the exact decomposition

```text
P(χ²g,ψ) - P(g,χ²ψ)
  = [P(g,χ²ψ) - 2P(χg,χψ) + P(χ²g,ψ)]
      - 2[P(g,χ²ψ) - P(χg,χψ)].
```

The first bracket is the double commutator and is bounded by
`C₂(L,R) ‖g‖₁ ‖ψ‖₂`, with `C₂` proportional to `R^(-3/2)`.
The second is a first commutator, bounded using OpenAI's existing theorem
by `C₁(L,R) ‖g‖₁ ‖χψ‖₄`, with `C₁` proportional to `R^(-3/4)`.
The complete bound retains both terms. For `g = u_i u_j`, the localized
source is literally the tensor of `χu`, and the upstream finite-energy
tensor estimate gives `‖g‖₁ ≤ ∫|u|²`. No claim is made that `χu` is
divergence-free or that the first commutator vanishes.

`MettapediaNS.WholeSpaceUnforcedEnergy` supplies the initial-data resource
for this source on an actual unforced `ClassicalH3Solution`. It specializes
OpenAI's `difference_rate_le` with both transported field and transporting
velocity equal to `u`, and zero deformation operator. Its generic pressure
orthogonality theorem removes the pressure work; pressure-gradient `L²`
membership is derived from the equation. OpenAI's Grönwall theorem then gives
`∫|u(t)|² ≤ ∫|u₀|²` throughout the given lifespan. Thus the second pressure
difference is bounded by `C₂(L,R) ‖u₀‖₂² ‖ψ‖₂`, including a checked sum over
all nine tensor components. No energy inequality or later-time bound is
assumed in the solution class. The module neither constructs nor extends
the lifespan. The first commutator, the actual material pressure-Hessian
receiver tests, adaptive cutoff costs, periodic transfer, and the signed
all-scale/time budget remain obligations.

`MettapediaNS.WholeSpaceStretchingFlux` constructs the cubic flux and its
gradient projection from an actual `SmoothL2Field` velocity, using upstream
vorticity, field products, advection, and the genuine Helmholtz projection.
Writing `ω = curl u` and `s = (ω·∇)u`, the flux is `J_ja = -ω_j s_a`.
Projection acts on the spatial index `j`: each column is the complement of
the upstream solenoidal projection. The resulting field `F` and the receiver
`B_ab = ω_b Σ_j ω_j F_ja` have all actual `L²` jets by the imported field
algebra. Neither is an independently supplied estimate or field.

`MettapediaNS.PressureHessianReceiver` identifies the corresponding complete
spatial pressure work with canonical Riesz pairings of `u_i u_j` against
`∂a∂b(η B_ab)`. It uses the upstream compact integration-by-parts theorem
and the previously identified constructed Helmholtz pressure. Every index is
included. For a smooth compact cutoff, the differentiated test is exactly

```text
∂a∂b(η B) = η ∂a∂b B + (∂aη)(∂b B) + (∂bη)(∂a B) + B ∂a∂bη.
```

`MettapediaNS.PressureHessianLocalization` constructs the difference between
this actual test and `η ∂a∂b B` in the upstream Schwartz space. With
`η = φ⁴`, the full localization difference is **twice the first commutator
minus the second difference plus the cutoff-derivative pressure pairing**.
Both multiplier relations required by the earlier estimates are proved for
the constructed Hessian tests. The initial-energy estimate therefore applies
to the second difference with its actual Hessian-test `L²` norm; it does not
bound that norm, remove the first commutator, or pay the three derivative
remainder terms. These are whole-space spatial identities, not an evolution
theorem or an identification of the auxiliary-heat/periodic receiver. The
input-scale heat weights, moving geometry, signed physical-time budget, and
unconditional continuation remain open.

`MettapediaNS.GaussianHeatCovariance` identifies OpenAI's literal Gaussian
product defect `R_ij = Hτ(u_i u_j) - (Hτu)_i (Hτu)_j` with mathlib's
covariance bilinear form, for arbitrary ordinary whole-space `L²` velocities.
Its quadratic form is nonnegative. `GaussianHeatEnergy` applies OpenAI's
parameter-integral theorem to obtain the global `L²` contraction and mathlib's
convolution integral theorem to prove the exact identity

```text
∫ trace(Rτ) = ∫ |u|² - ∫ |Hτu|² ≤ ∫ |u|².
```

`GaussianHeatIncrement` uses mathlib's variance bound after subtraction of a
constant, OpenAI's actual `L²` translation increment, its Bochner realization,
and its widened-Gaussian quadratic majorant. For actual `SmoothL2Field`
velocities it proves

```text
∫ trace(Rτ) ≤ (2τ) 2^(3/2) ‖A.derivative.toLp‖².
```

This derivative norm is the `L²` norm of the actual Fréchet derivative with
its operator norm. No spatial supremum of that derivative is used. The
separate energy bound is composed with `WholeSpaceUnforcedEnergy` to bound
the stress trace by initial energy along every given unforced H³ lifespan,
uniformly in `τ > 0`. The Gaussian convention has generator `Δ/4`; physical
heat time `νσ` corresponds to `τ = 4νσ`. Although the translation theorem is
imported from `OrdinaryMollifier`, its statement is about ordinary translations;
the compact mollifier from that module is not substituted for the Gaussian.
`GaussianHeatPairing` identifies the full signed contraction with the
Gaussian expectation of a quadratic form on centered velocity. Consequently

```text
Rτ : M = E[⟨u - Hτu, M(u - Hτu)⟩],
Rτ : M = Rτ : sym(M),
|∫ Rτ : M| ≤ sup_x ‖M(x)‖ ∫ trace(Rτ).
```

The pointwise one-sided quadratic bound is also retained, including a
negative upper bound when applicable. There is no component-count factor.
`GaussianHeatWeakStress` constructs the weak action of `-P div Rτ` by
applying OpenAI's actual solenoidal projection to the receiver first. It
proves integrability and bounds this signed action using the energy or
heat-scale trace bounds above. Only the symmetric derivative contributes;
the actual projected receiver derivative remains an explicit cost. No
`L∞` boundedness of the Leray projection is asserted.

`GaussianHeatFourier` directly applies OpenAI's
`fourierIntegral_gaussian_real` and the existing MeTTapedia
`UnitTorusPeriodization.mFourierCoeff_periodize`. The result identifies the
periodized Gaussian's exact multiplier at **every** lattice frequency:
`exp(-π²τ|n|²)`. It also proves the literal Gaussian averaging identity for
plane waves, which are not whole-space `L²` functions. Neither Gaussian
Fourier analysis nor periodization is reimplemented.

`GaussianHeatTorus` identifies the literal whole-space Gaussian average of
a continuous periodic lift with convolution by that periodized kernel.
It then applies the existing integrable-convolution theorem and mathlib's
Fourier reconstruction to obtain the exact series for inputs with summable
Fourier coefficients. No whole-space `L²` assumption is imposed on a periodic
lift. The shared periodization proof now handles arbitrary invariant scalar
tests with integrable weighted kernels; its previous unit-character theorem
is a specialization, not a second unfolding proof. Periodization integrability
also uses the existing mass bound instead of requiring Schwartz regularity.

These results do not pay the evolving projected receiver derivative,
establish a physical-time dissipation bound in this interface, or identify
the full periodic/input-scale Gram work with the spatial stress action.
The existing canonical Fourier heat-source split, heat-commutator
energy/enstrophy bounds, and signed coefficient-adjoint/Duhamel
representation are retained, not reimplemented. Their migration to this
toolchain is a separate compatibility task.

A 21-file shared compatibility slice now passes selected-module builds on both
Lean 4.31.0 and Lean 4.34.0-rc2. It covers angular-curl continuity, radial
kernel moments and correlations, the exact Fourier triad, normalized
Schwartz-kernel decay, annular charts, dyadic rescaling, and frozen-frame
kernel transfer. It also covers buffered annular transfer, quadratic Fourier
support, the physical forcing-continuity lemma, and the physical Laplacian.
The two generalized periodization modules are also checked on both versions.
The compatibility adjustments concern elaboration and mathlib lemma names;
theorem statements are unchanged. This does not yet certify the
entire `ExchangedFluxHeatAdjoint` dependency chain on the newer toolchain.

`WholeSpaceBKM.h3_energyProduction_add_dissipation_le_spatialBKMIntegrand`
combines the first two applications: the actual viscous energy production
is controlled by the existing spatial BKM integrand and the actual higher
velocity norm. This does not establish integrability up to a singular time.

`NS.Lit.CZ.truncated_Lp_uniform`, `pvOp_Lp`, and
`smoothTruncate_Lp_uniform` in `Lit/CZ/CZCore/Homogeneous.lean` are now
checked imports and used by the quadratic-kernel applications above.
Their proofs cover general positive dimension; the current concrete
applications use dimension three. None of these estimates provides an
`L^∞` endpoint or the global signed time-integrated misalignment budget.

## Reuse policy

Before a new general-analysis proof, check mathlib, the existing MeTTapedia
development, and the relevant OpenAI and Alpöge–Buckmaster developments.
Prefer direct application, then a representation adapter or a generalization
of an existing proof. Record the exact missing hypothesis before undertaking
new mathematics. Toolchain differences are migration tasks, not a reason to
reprove an available theorem.

Ben's coherence/pancake mechanism remains the research target. Auxiliary
norms, functionals, and interfaces may be improved to use established theory.

## Reproducible Fourier calculations

The [exact Fourier interaction lab](labs/README.md) checks explicit
trigonometric data using the complete Leray-projected quadratic source and
rational arithmetic. It covers equal initial sources with opposite cubic
corrections to later production, mixed interactions escaping a generated
frequency chain, and a cyclic-shear cancellation that ends at the next
order. These are executable algebra checks, not Lean certificates or
physical-time budget estimates.

## Build

```sh
lake update
lake exe cache get
bash scripts/prepare-upstreams.sh
lake build MettapediaNS
lake env lean MettapediaNS/UpstreamAudit.lean
```

This target checks the imported theorem surface and adapters listed above. The
arbitrary-data dynamical budget and unconditional continuation theorem remain
separate mathematical obligations.

The selected target has been checked on Lean 4.34.0-rc2. OpenAI's source
tree is unchanged. EulerBlowup declares Lean 4.32.2 and mathlib 4.32.0;
the Cotlar–Stein dependency chain compiles unchanged on the newer toolchain.
The larger homogeneous-kernel dependency chain needs exactly five order-
lemma name updates in `Marcinkiewicz.lean` and `Homogeneous.lean`, recorded
in `patches/euler-blowup-lean-4.34.patch`. The potential-theory dependency
chain additionally needs one scoped elaboration setting around the existing
`Cm24.L2_6_III_Fc` proof in `Cm24/S2/Master.lean`, recorded in
`patches/euler-blowup-potential-lean-4.34.patch`. No statement or mathematical
argument is changed. `scripts/prepare-upstreams.sh` checks the pinned
revision and applies these patches idempotently, refusing a conflicting patch.
Run it after dependency setup; it never resets upstream files. The upstream
files and their Apache-2.0 license remain in their original package.
This does not certify the entire EulerBlowup development.
Upstream and existing local sources emit deprecation/unused-variable
warnings; these are not proof failures.

The shared `SpatialBKMIntegrand` source needs only a compatibility adjustment
to six continuity/measurability applications. Its mathematical statements
are unchanged; no new supremum construction is introduced.
The adjusted source also passes its original Lean 4.31.0 target. The
235-declaration integration audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; there are no additional analytic axioms in those proofs.
