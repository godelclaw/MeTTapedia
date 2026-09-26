import NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The swirl identity: how pressure and force enter the angular momentum

The angular momentum density about the third axis is `Γ = x₀ u₁ - x₁ u₀`,
which in cylindrical coordinates is `r u_θ`. Along any velocity and pressure
whose Navier–Stokes residual is `f`, at every point where the velocity is
twice differentiable in space and differentiable in time,

```text
∂ₜΓ + (u · ∇)Γ = ν (ΔΓ - 2 ω₃) - (x₀ ∂₁p - x₁ ∂₀p) + (x₀ f₁ - x₁ f₀),
```

with `ω₃ = ∂₀u₁ - ∂₁u₀` the axial vorticity. The pressure enters only through
its angular derivative, which averages to zero around the axis, and the force
only through its torque. For an axisymmetric unforced flow this is the swirl
equation `∂ₜΓ + u·∇Γ = ν (∂ᵣ² - r⁻¹∂ᵣ + ∂_z²) Γ`, whose maximum principle
bounds the swirl by its initial maximum. In the breakdown construction for the
forced problem, the maximal swirl of the axisymmetric background grows without
bound near the singular point, while the force and its torque vanish there to
every order; its growth is supplied by the angular average of the torque of
the oscillatory pulses.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SwirlBudget

open Filter Topology
open _root_.NavierStokes.ProblemStatement

/-- The unit coordinate vectors. -/
abbrev e (i : Fin 3) : Space := coordinateVector i

theorem e_apply (i j : Fin 3) : (e i) j = if j = i then 1 else 0 := by
  simp [e, coordinateVector, PiLp.single_apply]

/-- The angular momentum density about the third axis of a velocity slice. -/
def swirlSlice (U : Space → Space) (y : Space) : ℝ := y 0 * U y 1 - y 1 * U y 0

/-- The axial vorticity `∂₀u₁ - ∂₁u₀`. -/
def axialVorticity (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  spatialDerivative u t x (e 0) 1 - spatialDerivative u t x (e 1) 0

/-- The angular derivative `x₀ ∂₁p - x₁ ∂₀p` of the pressure. -/
def angularDerivative (p : PressureField) (t : ℝ) (x : Space) : ℝ :=
  x 0 * fderiv ℝ (fun y : Space ↦ p (t, y)) x (e 1) -
    x 1 * fderiv ℝ (fun y : Space ↦ p (t, y)) x (e 0)

/-- The torque of a force about the third axis. -/
def torque (f : VelocityField) (t : ℝ) (x : Space) : ℝ := x 0 * f (t, x) 1 - x 1 * f (t, x) 0

section Slice

variable {U : Space → Space} {y : Space}

theorem hasFDerivAt_coord (i : Fin 3) (y : Space) :
    HasFDerivAt (fun z : Space ↦ z i) (EuclideanSpace.proj i : Space →L[ℝ] ℝ) y :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt

theorem hasFDerivAt_comp_coord (hU : DifferentiableAt ℝ U y) (i : Fin 3) :
    HasFDerivAt (fun z ↦ U z i) ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ U y)) y :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hU.hasFDerivAt

/-- The first derivative of the swirl of a slice. -/
theorem fderiv_swirlSlice_apply (hU : DifferentiableAt ℝ U y) (v : Space) :
    fderiv ℝ (swirlSlice U) y v =
      y 0 * (fderiv ℝ U y v) 1 + U y 1 * v 0 - (y 1 * (fderiv ℝ U y v) 0 + U y 0 * v 1) := by
  have h := ((hasFDerivAt_coord 0 y).mul (hasFDerivAt_comp_coord hU 1)).sub
    ((hasFDerivAt_coord 1 y).mul (hasFDerivAt_comp_coord hU 0))
  have h' : HasFDerivAt (swirlSlice U) _ y := h
  rw [h'.fderiv]
  simp [smul_eq_mul]

/-- The second derivative of the swirl of a slice along a coordinate direction. -/
theorem fderiv_fderiv_swirlSlice (hU : ContDiffAt ℝ 2 U y) (i : Fin 3) :
    fderiv ℝ (fun z ↦ fderiv ℝ (swirlSlice U) z (e i)) y (e i) =
      y 0 * (fderiv ℝ (fun z ↦ fderiv ℝ U z (e i)) y (e i)) 1 +
        2 * ((e i) 0 * (fderiv ℝ U y (e i)) 1) -
      (y 1 * (fderiv ℝ (fun z ↦ fderiv ℝ U z (e i)) y (e i)) 0 +
        2 * ((e i) 1 * (fderiv ℝ U y (e i)) 0)) := by
  -- differentiability near the point
  have hev : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ U z :=
    (hU.eventually (by simp)).mono fun z hz ↦ hz.differentiableAt (by norm_num)
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) y :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fun z ↦ fderiv ℝ U z (e i)) y :=
    hDU.clm_apply (differentiableAt_const _)
  have hUy : DifferentiableAt ℝ U y := hU.differentiableAt (by norm_num)
  -- the first derivative is eventually the explicit expression
  have heq : (fun z ↦ fderiv ℝ (swirlSlice U) z (e i)) =ᶠ[𝓝 y]
      (fun z ↦ z 0 * (fderiv ℝ U z (e i)) 1 + U z 1 * (e i) 0 -
        (z 1 * (fderiv ℝ U z (e i)) 0 + U z 0 * (e i) 1)) :=
    hev.mono fun z hz ↦ fderiv_swirlSlice_apply hz (e i)
  rw [heq.fderiv_eq]
  -- differentiate the explicit expression
  have hDc : ∀ j : Fin 3, HasFDerivAt (fun z ↦ (fderiv ℝ U z (e i)) j)
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ (fun z ↦ fderiv ℝ U z (e i)) y)) y :=
    fun j ↦ (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hD.hasFDerivAt
  have h := ((((hasFDerivAt_coord 0 y).mul (hDc 1)).add
      ((hasFDerivAt_comp_coord hUy 1).mul_const ((e i) 0))).sub
    (((hasFDerivAt_coord 1 y).mul (hDc 0)).add
      ((hasFDerivAt_comp_coord hUy 0).mul_const ((e i) 1))))
  have h' : HasFDerivAt (fun z ↦ z 0 * (fderiv ℝ U z (e i)) 1 + U z 1 * (e i) 0 -
      (z 1 * (fderiv ℝ U z (e i)) 0 + U z 0 * (e i) 1)) _ y := h
  rw [h'.fderiv]
  simp [smul_eq_mul]
  ring

end Slice

/-- **The swirl identity.** At a point where the velocity is twice
differentiable in space and differentiable in time, and the Navier–Stokes
residual equals `f`, the swirl satisfies
`∂ₜΓ + (u·∇)Γ = ν (ΔΓ - 2ω₃) - (x₀∂₁p - x₁∂₀p) + (x₀f₁ - x₁f₀)`. -/
theorem swirl_identity {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
    {t : ℝ} {x : Space} (hu : ContDiffAt ℝ 2 (fun y ↦ u (t, y)) x)
    (ht : DifferentiableAt ℝ (fun s ↦ u (s, x)) t)
    (hres : NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) x) t +
        fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x (u (t, x)) =
      ν * ((∑ i : Fin 3, fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) x (e i)) -
          2 * axialVorticity u t x) - angularDerivative p t x + torque f t x := by
  have hUx : DifferentiableAt ℝ (fun y ↦ u (t, y)) x := hu.differentiableAt (by norm_num)
  -- the time derivative
  have hT : deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) x) t =
      x 0 * (temporalDerivative u t x) 1 - x 1 * (temporalDerivative u t x) 0 := by
    have hd : HasDerivAt (fun s ↦ u (s, x)) (temporalDerivative u t x) t :=
      ht.hasFDerivAt.hasDerivAt
    have hc : ∀ j : Fin 3, HasDerivAt (fun s ↦ u (s, x) j) ((temporalDerivative u t x) j) t :=
      fun j ↦ HasFDerivAt.comp_hasDerivAt t (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt hd
    have h2 : HasDerivAt (fun s ↦ x 0 * u (s, x) 1 - x 1 * u (s, x) 0)
        (x 0 * (temporalDerivative u t x) 1 - x 1 * (temporalDerivative u t x) 0) t :=
      HasDerivAt.sub (HasDerivAt.const_mul (x 0) (hc 1)) (HasDerivAt.const_mul (x 1) (hc 0))
    exact HasDerivAt.deriv h2
  -- the advection term
  have hA : fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x (u (t, x)) =
      x 0 * (advection u t x) 1 - x 1 * (advection u t x) 0 := by
    rw [fderiv_swirlSlice_apply hUx]
    simp only [advection, spatialDerivative]
    ring
  -- the Laplacian
  have hL : ∑ i : Fin 3, fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) x (e i) =
      x 0 * (spatialLaplacian u t x) 1 - x 1 * (spatialLaplacian u t x) 0 +
        2 * axialVorticity u t x := by
    rw [Fin.sum_univ_three, fderiv_fderiv_swirlSlice hu 0, fderiv_fderiv_swirlSlice hu 1,
      fderiv_fderiv_swirlSlice hu 2]
    simp only [e_apply, spatialLaplacian, spatialDerivative, axialVorticity, Fin.sum_univ_three]
    simp
    ring
  -- the components of the residual
  have hr : ∀ j : Fin 3, (temporalDerivative u t x) j + (advection u t x) j -
      ν * (spatialLaplacian u t x) j + fderiv ℝ (fun y : Space ↦ p (t, y)) x (e j) = f (t, x) j := by
    intro j
    have h := congrArg (fun v : Space ↦ v j) hres
    simp only [NavierStokesR3.ProblemStatement.navierStokesResidual, pressureGradient] at h
    fin_cases j <;> simpa [Fin.sum_univ_three, e_apply, smul_eq_mul] using h
  rw [hT, hA, hL]
  unfold angularDerivative torque
  linear_combination (x 0) * hr 1 - (x 1) * hr 0

end Mettapedia.FluidDynamics.NavierStokes.SwirlBudget
