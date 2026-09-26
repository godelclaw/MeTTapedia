import NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

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
its angular derivative `x₀ ∂₁p - x₁ ∂₀p`, which is the derivative along the
rotations about the axis, so its integral over every circle about the axis
vanishes; the force enters only through its torque. For an axisymmetric unforced flow this is the swirl
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

section Average

/-- Rotation by the angle `φ` about the third axis. -/
def rot (φ : ℝ) (x : Space) : Space :=
  !₂[Real.cos φ * x 0 - Real.sin φ * x 1, Real.sin φ * x 0 + Real.cos φ * x 1, x 2]

/-- The generator of the rotations, `(-x₁, x₀, 0)`. -/
def angular (x : Space) : Space := !₂[-x 1, x 0, 0]

theorem rot_zero (x : Space) : rot 0 x = x := by
  ext i
  fin_cases i <;> simp [rot]

theorem rot_two_pi (x : Space) : rot (2 * Real.pi) x = x := by
  ext i
  fin_cases i <;> simp [rot]

theorem hasDerivAt_rot (φ : ℝ) (x : Space) :
    HasDerivAt (fun φ ↦ rot φ x) (angular (rot φ x)) φ := by
  have h0 : HasDerivAt (fun φ ↦ Real.cos φ * x 0 - Real.sin φ * x 1)
      (-(Real.sin φ * x 0 + Real.cos φ * x 1)) φ :=
    HasDerivAt.congr_deriv (HasDerivAt.sub (HasDerivAt.mul_const (Real.hasDerivAt_cos φ) (x 0))
      (HasDerivAt.mul_const (Real.hasDerivAt_sin φ) (x 1))) (by ring)
  have h1 : HasDerivAt (fun φ ↦ Real.sin φ * x 0 + Real.cos φ * x 1)
      (Real.cos φ * x 0 - Real.sin φ * x 1) φ :=
    HasDerivAt.congr_deriv (HasDerivAt.add (HasDerivAt.mul_const (Real.hasDerivAt_sin φ) (x 0))
      (HasDerivAt.mul_const (Real.hasDerivAt_cos φ) (x 1))) (by ring)
  have h2 : HasDerivAt (fun _ : ℝ ↦ x 2) 0 φ := hasDerivAt_const _ _
  have hv : HasDerivAt (fun φ ↦ ![Real.cos φ * x 0 - Real.sin φ * x 1,
      Real.sin φ * x 0 + Real.cos φ * x 1, x 2])
      ![-(Real.sin φ * x 0 + Real.cos φ * x 1), Real.cos φ * x 0 - Real.sin φ * x 1, 0] φ := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  have hL := HasFDerivAt.comp_hasDerivAt φ
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt) hv
  have hL' : HasDerivAt (fun φ ↦ rot φ x) ((EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![-(Real.sin φ * x 0 + Real.cos φ * x 1), Real.cos φ * x 0 - Real.sin φ * x 1, 0]) φ := hL
  refine HasDerivAt.congr_deriv hL' ?_
  ext i
  fin_cases i <;> simp [angular, rot]

/-- The angular derivative `x₀ ∂₁g - x₁ ∂₀g` of a scalar field. -/
def angularDeriv (g : Space → ℝ) (x : Space) : ℝ := fderiv ℝ g x (angular x)

theorem angular_eq (x : Space) : angular x = x 0 • e 1 - x 1 • e 0 := by
  ext i
  fin_cases i <;> simp [angular, e_apply]

theorem angularDeriv_eq (g : Space → ℝ) (x : Space) :
    angularDeriv g x = x 0 * fderiv ℝ g x (e 1) - x 1 * fderiv ℝ g x (e 0) := by
  rw [angularDeriv, angular_eq, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **Angular derivatives average to zero around the axis.** -/
theorem integral_angularDeriv_rot {g : Space → ℝ} (hg : ContDiff ℝ 1 g) (x : Space) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), angularDeriv g (rot φ x) = 0 := by
  have hd : ∀ φ : ℝ, HasDerivAt (fun φ ↦ g (rot φ x)) (angularDeriv g (rot φ x)) φ := by
    intro φ
    have hg' : HasFDerivAt g (fderiv ℝ g (rot φ x)) (rot φ x) :=
      (hg.differentiable (by norm_num) (rot φ x)).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt φ hg' (hasDerivAt_rot φ x)
  have hcont : Continuous (fun φ ↦ angularDeriv g (rot φ x)) := by
    have hrot : Continuous (fun φ : ℝ ↦ rot φ x) :=
      continuous_iff_continuousAt.mpr fun φ ↦ (hasDerivAt_rot φ x).continuousAt
    have hang : Continuous angular := by
      have : angular = fun y : Space ↦ y 0 • e 1 - y 1 • e 0 := funext angular_eq
      rw [this]
      fun_prop
    have hf : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
    exact (hf.comp hrot).clm_apply (hang.comp hrot)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun φ _ ↦ hd φ)
    (hcont.intervalIntegrable _ _), rot_two_pi, rot_zero, sub_self]

/-- **The pressure drops out of the averaged swirl equation.** The angular
derivative of the pressure averages to zero over every circle about the axis. -/
theorem integral_angularDerivative_rot {p : PressureField} {t : ℝ}
    (hp : ContDiff ℝ 1 (fun y : Space ↦ p (t, y))) (x : Space) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), angularDerivative p t (rot φ x) = 0 := by
  have e : ∀ y, angularDerivative p t y = angularDeriv (fun y : Space ↦ p (t, y)) y := fun y ↦ by
    rw [angularDeriv_eq]
    rfl
  simp only [e]
  exact integral_angularDeriv_rot hp x

end Average

end Mettapedia.FluidDynamics.NavierStokes.SwirlBudget
