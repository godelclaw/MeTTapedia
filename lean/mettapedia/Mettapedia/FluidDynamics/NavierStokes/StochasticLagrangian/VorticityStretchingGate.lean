import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ConstantinIyerRepresentation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The vorticity-stretching gate of the stochastic-Lagrangian representation

Under the stochastic-Lagrangian representation of the incompressible
Navier–Stokes equations, the vorticity satisfies the averaged Cauchy formula
`ω(t) = 𝔼[(DX_t)(ω₀ ∘ A_t)]`, so its sup-norm is controlled by moments of
the flow Jacobian: `‖ω(t)‖_∞ ≤ 𝔼‖DX_t‖_∞ · ‖ω₀‖_∞`.  The continuation
criterion of Beale–Kato–Majda type then reduces to the single analytic
estimate

`∫₀ᵀ 𝔼‖DX_t‖_∞ dt < ∞`,

which this file pins as the named proposition
`StochasticStretchingEstimate`.

**Status: open.**  The Jacobian evolves by
`dJ = ∇u(X_t) J dt + noise`; the drift `∇u` term is the vorticity-stretching
difficulty, and no published work closes this estimate for general
three-dimensional data — global results in this line exist only under
smallness of the data, in two dimensions, for large viscosity, or for
modified systems.  Under the representation this gate carries the content of
the Clay Millennium problem on 3D Navier–Stokes regularity; nothing in this
repository proves it, and the frozen-strain model
(`Mettapedia.FluidDynamics.NavierStokes.FrozenStrainModel`) shows that
stochastic covariance alone cannot: over frozen strains the amplification
admits no uniform bound.

What **is** proved here (the consumer side, all mechanical): given the
averaged-Cauchy bound as a hypothesis field, the gate implies that the
Beale–Kato–Majda integrand `t ↦ ‖ω(t, x)‖` is interval-integrable with
`∫₀ᵀ ‖ω(t,x)‖ dt ≤ ‖ω₀‖_∞ ∫₀ᵀ 𝔼‖DX_t‖_∞ dt`, and a time-uniform Jacobian
bound gives a time-uniform vorticity bound.  Combined with the pushdown
theorem (`TransportedMomentumData.navierStokes_of_transportedMomentum`),
this makes the representation a conditional route with exactly one named
analytic input (`stochasticLagrangian_conditional_route`).

## References

* J. T. Beale, T. Kato, A. Majda, *Remarks on the breakdown of smooth
  solutions for the 3-D Euler equations*, Comm. Math. Phys. **94** (1984),
  61–66 (the `∫₀ᵀ ‖ω‖_∞ dt` continuation criterion).
* P. Constantin, G. Iyer, *A stochastic Lagrangian representation of the
  three-dimensional incompressible Navier–Stokes equations*,
  Comm. Pure Appl. Math. **61** (2008), 330–345. arXiv:math/0511067.
* G. Iyer, *A stochastic Lagrangian proof of global existence of the
  Navier–Stokes equations for flows with small Reynolds number*,
  Ann. Inst. H. Poincaré Anal. Non Linéaire **26** (2009), 181–189
  (the shape precedent: control of the gate implies continuation).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

section Curl

/-- Coordinate curl of a vector field on `R3`. -/
def curlField (u : R3 → R3) (x : R3) : R3 :=
  EuclideanSpace.single 0
      (fderiv ℝ u x (EuclideanSpace.single 1 1) 2 -
        fderiv ℝ u x (EuclideanSpace.single 2 1) 1) +
    EuclideanSpace.single 1
      (fderiv ℝ u x (EuclideanSpace.single 2 1) 0 -
        fderiv ℝ u x (EuclideanSpace.single 0 1) 2) +
    EuclideanSpace.single 2
      (fderiv ℝ u x (EuclideanSpace.single 0 1) 1 -
        fderiv ℝ u x (EuclideanSpace.single 1 1) 0)

/-- Constant fields have zero curl. -/
theorem curlField_const (c : R3) (x : R3) :
    curlField (fun _ => c) x = 0 := by
  unfold curlField
  rw [fderiv_fun_const]
  ext b
  simp

end Curl

section GateData

/-- Averaged-Cauchy vorticity data: a finite noise model, a per-sample
sup-norm envelope for the flow Jacobian, a vorticity field, and the averaged
Cauchy-formula bound tying them together.  The Cauchy bound is the model
form of `‖ω(t)‖ ≤ 𝔼‖DX_t‖ · ‖ω₀‖_∞`; in the representation it follows from
`ω(t) = 𝔼[(DX_t)(ω₀ ∘ A_t)]`, which is not re-derived here. -/
structure StochasticCauchyVorticityData (Ω : Type*) [Fintype Ω] where
  /-- Finite probability weights of the noise samples. -/
  prob : FiniteProbability Ω
  /-- Per-sample sup-norm envelope of the flow Jacobian at each time. -/
  jacobianBound : ℝ → Ω → ℝ
  jacobianBound_nonneg : ∀ t ω, 0 ≤ jacobianBound t ω
  /-- The vorticity field. -/
  vorticity : ℝ → R3 → R3
  /-- The vorticity is a.e.-strongly-measurable in time at each point. -/
  vorticity_time_aestronglyMeasurable : ∀ x,
    MeasureTheory.AEStronglyMeasurable (fun t => vorticity t x)
      MeasureTheory.volume
  /-- Sup bound of the initial vorticity. -/
  initialBound : ℝ
  initialBound_nonneg : 0 ≤ initialBound
  /-- The averaged Cauchy-formula bound. -/
  cauchy_bound : ∀ t x, ‖vorticity t x‖ ≤
    (∑ ω, prob.weight ω * jacobianBound t ω) * initialBound

namespace StochasticCauchyVorticityData

variable {Ω : Type*} [Fintype Ω] (D : StochasticCauchyVorticityData Ω)

/-- The expected Jacobian envelope `t ↦ 𝔼‖DX_t‖`. -/
def expectedJacobianBound (t : ℝ) : ℝ :=
  ∑ ω, D.prob.weight ω * D.jacobianBound t ω

theorem expectedJacobianBound_nonneg (t : ℝ) :
    0 ≤ D.expectedJacobianBound t :=
  Finset.sum_nonneg fun ω _ =>
    mul_nonneg (D.prob.weight_nonneg ω) (D.jacobianBound_nonneg t ω)

/-- Restated Cauchy bound through the expected envelope. -/
theorem vorticity_le (t : ℝ) (x : R3) :
    ‖D.vorticity t x‖ ≤ D.expectedJacobianBound t * D.initialBound :=
  D.cauchy_bound t x

end StochasticCauchyVorticityData

/-- **The vorticity-stretching gate** (named analytic input; OPEN): the
expected Jacobian envelope is interval-integrable on `[0, T]`,
`∫₀ᵀ 𝔼‖DX_t‖_∞ dt < ∞`.  This is the Beale–Kato–Majda-type continuation
criterion of the stochastic-Lagrangian representation; with the `∇u` drift
in the Jacobian evolution it is the three-dimensional vorticity-stretching
problem, open for general data.  Nothing in this repository proves it for
any data class beyond explicit bounded envelopes.

A sharper geometric input reaching the same Beale–Kato–Majda endpoint —
the scale-local pancake strain budget isolated from the 2026-07-03 dyadic
repair analysis — is `ScaleLocalPancakeStrainBudget` in
`DyadicPancakeClosure.lean`, with the conditional chain
`stochasticLagrangian_conditional_route_of_pancakeBudget`.  This gate is
not superseded: the two are open inputs at different levels of the same
route (coarse Jacobian envelope vs. isolated stretching geometry). -/
def StochasticStretchingEstimate {Ω : Type*} [Fintype Ω]
    (D : StochasticCauchyVorticityData Ω) (T : ℝ) : Prop :=
  IntervalIntegrable D.expectedJacobianBound MeasureTheory.volume 0 T

end GateData

section Consumers

namespace StochasticCauchyVorticityData

variable {Ω : Type*} [Fintype Ω] (D : StochasticCauchyVorticityData Ω)

/-- A time-uniform expected-Jacobian bound gives a time-uniform vorticity
bound (the sup-norm consumer of the gate). -/
theorem vorticity_uniform_bound_of_jacobian_bound {T C : ℝ}
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, D.expectedJacobianBound t ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : R3,
      ‖D.vorticity t x‖ ≤ C * D.initialBound := by
  intro t ht x
  calc ‖D.vorticity t x‖ ≤ D.expectedJacobianBound t * D.initialBound :=
        D.vorticity_le t x
    _ ≤ C * D.initialBound :=
        mul_le_mul_of_nonneg_right (hC t ht) D.initialBound_nonneg

/-- Under the gate, the Beale–Kato–Majda integrand `t ↦ ‖ω(t,x)‖` is
interval-integrable on `[0, T]`. -/
theorem bkm_integrand_intervalIntegrable {T : ℝ}
    (hgate : StochasticStretchingEstimate D T) (x : R3) :
    IntervalIntegrable (fun t => ‖D.vorticity t x‖)
      MeasureTheory.volume 0 T := by
  have hmaj : IntervalIntegrable
      (fun t => D.expectedJacobianBound t * D.initialBound)
      MeasureTheory.volume 0 T := hgate.mul_const _
  apply hmaj.mono_fun ((D.vorticity_time_aestronglyMeasurable x).norm.restrict)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (D.expectedJacobianBound_nonneg t)
      D.initialBound_nonneg)]
  exact D.vorticity_le t x

/-- Under the gate, the Beale–Kato–Majda integral is controlled by the gate
integral: `∫₀ᵀ ‖ω(t,x)‖ dt ≤ ‖ω₀‖_∞ · ∫₀ᵀ 𝔼‖DX_t‖ dt`. -/
theorem bkm_integral_bound {T : ℝ} (hT : 0 ≤ T)
    (hgate : StochasticStretchingEstimate D T) (x : R3) :
    ∫ t in (0 : ℝ)..T, ‖D.vorticity t x‖ ≤
      D.initialBound * ∫ t in (0 : ℝ)..T, D.expectedJacobianBound t := by
  have hmaj : IntervalIntegrable
      (fun t => D.expectedJacobianBound t * D.initialBound)
      MeasureTheory.volume 0 T := hgate.mul_const _
  calc ∫ t in (0 : ℝ)..T, ‖D.vorticity t x‖
      ≤ ∫ t in (0 : ℝ)..T, D.expectedJacobianBound t * D.initialBound := by
        apply intervalIntegral.integral_mono_on hT
          (D.bkm_integrand_intervalIntegrable hgate x) hmaj
        intro t _
        exact D.vorticity_le t x
    _ = D.initialBound * ∫ t in (0 : ℝ)..T, D.expectedJacobianBound t := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext t
        ring

end StochasticCauchyVorticityData

end Consumers

section ConditionalRoute

/-- **The conditional route skeleton of the stochastic-Lagrangian
representation.**  Given
* momentum-transport data `D` (velocity + gauge with the averaged
  frame-transport equation), and
* averaged-Cauchy vorticity data `V` whose vorticity is the curl of `D`'s
  velocity,
if the vorticity-stretching gate holds on `[0, T]`, then simultaneously:

1. the velocity satisfies the Navier–Stokes equations with the explicit
   representation pressure (the pushdown theorem, unconditional), and
2. the Beale–Kato–Majda integrand `t ↦ ‖curl u(t, x)‖` is
   interval-integrable on `[0, T]` with its integral controlled by the gate
   integral.

Every step of this statement is machine-checked; the *only* analytic input
is the named gate `StochasticStretchingEstimate` — which is open, and is
where the difficulty of the Millennium problem lives under this
representation.  This theorem therefore expresses the repaired route as a
conditional machine, not as progress on the gate itself. -/
theorem stochasticLagrangian_conditional_route
    (D : TransportedMomentumData) {Ω : Type*} [Fintype Ω]
    (V : StochasticCauchyVorticityData Ω)
    (hlink : ∀ t x, V.vorticity t x = curlField (D.u t) x)
    {T : ℝ} (hT : 0 ≤ T)
    (hgate : StochasticStretchingEstimate V T) :
    (∀ t x, deriv (fun s => D.u s x) t + fderiv ℝ (D.u t) x (D.u t x) +
        gradField (D.pressure t) x = D.ν • coordLaplacian (D.u t) x) ∧
    (∀ x : R3,
      IntervalIntegrable (fun t => ‖curlField (D.u t) x‖)
        MeasureTheory.volume 0 T ∧
      ∫ t in (0 : ℝ)..T, ‖curlField (D.u t) x‖ ≤
        V.initialBound * ∫ t in (0 : ℝ)..T, V.expectedJacobianBound t) := by
  constructor
  · exact fun t x => D.navierStokes_of_transportedMomentum t x
  · intro x
    have hfun : (fun t => ‖curlField (D.u t) x‖) =
        fun t => ‖V.vorticity t x‖ := by
      funext t
      rw [hlink t x]
    rw [hfun]
    exact ⟨V.bkm_integrand_intervalIntegrable hgate x,
      V.bkm_integral_bound hT hgate x⟩

end ConditionalRoute

end NavierStokes
end FluidDynamics
end Mettapedia
