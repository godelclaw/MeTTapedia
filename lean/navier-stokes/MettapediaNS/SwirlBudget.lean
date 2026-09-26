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
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

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
vanishes; the force enters only through its torque.

For an axisymmetric flow, at every spatial local maximum of the swirl off the
axis, the gradient of the swirl vanishes, its Laplacian is nonpositive, the
angular derivative of the pressure vanishes, and so does the axial vorticity,
since `x₀ ∂₀Γ + x₁ ∂₁Γ = r² ω₃` there. Hence `∂ₜΓ ≤ x₀ f₁ - x₁ f₀` at such
maxima: without a force the swirl cannot grow at its maxima, which is the
pointwise core of the swirl maximum principle. Maximizing `Γ - ε t` over a
compact region of space-time turns it into the maximum principle: for an
axisymmetric flow whose force has nonpositive torque and whose swirl is
nonpositive outside a compact set, the swirl never exceeds its initial
maximum.

In the breakdown construction for the forced problem, the maximal swirl of the
axisymmetric background grows without bound near the singular point, while the
force and its torque vanish there to every order; its growth is supplied by the
angular average of the torque of the oscillatory pulses.
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

section MaximumPrinciple

/-- **At a local maximum the second derivative is nonpositive.** Otherwise
the second-derivative test would make the point a local minimum as well, the
function would be locally constant, and its second derivative would vanish. -/
theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x₀ : ℝ} (hmax : IsLocalMax f x₀)
    (hc : ContinuousAt f x₀) : deriv (deriv f) x₀ ≤ 0 := by
  by_contra h
  push Not at h
  have hmin : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos h (IsLocalMax.deriv_eq_zero hmax) hc
  have hconst : f =ᶠ[𝓝 x₀] fun _ ↦ f x₀ :=
    (Filter.Eventually.and hmax hmin).mono fun y hy ↦ le_antisymm hy.1 hy.2
  have hderiv : deriv f =ᶠ[𝓝 x₀] fun _ ↦ 0 :=
    hconst.eventuallyEq_nhds.mono fun y hy ↦ by rw [hy.deriv_eq]; simp
  rw [hderiv.deriv_eq] at h
  simp at h

theorem hasDerivAt_line (x v : Space) (s : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • v) v s := by
  have h := HasDerivAt.const_add x (HasDerivAt.smul_const (hasDerivAt_id s) v)
  simpa using h

/-- **At a local maximum every second directional derivative is nonpositive.** -/
theorem secondDeriv_nonpos_of_isLocalMax {g : Space → ℝ} {x : Space} (hg : ContDiffAt ℝ 2 g x)
    (hmax : IsLocalMax g x) (v : Space) : fderiv ℝ (fun y ↦ fderiv ℝ g y v) x v ≤ 0 := by
  have hx0 : (fun s : ℝ ↦ x + s • v) 0 = x := by simp
  have hcont : ContinuousAt (fun s : ℝ ↦ g (x + s • v)) 0 :=
    ContinuousAt.comp_of_eq hg.continuousAt (hasDerivAt_line x v 0).continuousAt hx0
  have hmax' : IsLocalMax (fun s : ℝ ↦ g (x + s • v)) 0 := by
    have h1 : IsLocalMax g ((fun s : ℝ ↦ x + s • v) 0) := by rw [hx0]; exact hmax
    exact IsLocalMax.comp_continuous h1 (hasDerivAt_line x v 0).continuousAt
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ g (x + s • v) := by
    have ht : Tendsto (fun s : ℝ ↦ x + s • v) (𝓝 0) (𝓝 x) := by
      have := (hasDerivAt_line x v 0).continuousAt.tendsto
      simpa using this
    exact ht.eventually hev
  have hd1 : deriv (fun s : ℝ ↦ g (x + s • v)) =ᶠ[𝓝 0] fun s ↦ fderiv ℝ g (x + s • v) v :=
    hev'.mono fun s hs ↦ HasDerivAt.deriv (HasFDerivAt.comp_hasDerivAt s hs.hasFDerivAt
      (hasDerivAt_line x v s))
  have hDg : DifferentiableAt ℝ (fun y ↦ fderiv ℝ g y v) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hd2 : deriv (fun s : ℝ ↦ fderiv ℝ g (x + s • v) v) 0 =
      fderiv ℝ (fun y ↦ fderiv ℝ g y v) x v :=
    HasDerivAt.deriv (HasFDerivAt.comp_hasDerivAt_of_eq 0 hDg.hasFDerivAt
      (hasDerivAt_line x v 0) hx0.symm)
  have h := deriv_deriv_nonpos_of_isLocalMax hmax' hcont
  rw [hd1.deriv_eq, hd2] at h
  exact h

/-- A velocity that commutes with the rotations about the third axis at time `t`. -/
def AxisymmetricVelocity (u : VelocityField) (t : ℝ) : Prop :=
  ∀ φ y, u (t, rot φ y) = rot φ (u (t, y))

/-- A pressure invariant under the rotations about the third axis at time `t`. -/
def AxisymmetricPressure (p : PressureField) (t : ℝ) : Prop := ∀ φ y, p (t, rot φ y) = p (t, y)

theorem hasDerivAt_rot_zero (x : Space) : HasDerivAt (fun φ ↦ rot φ x) (angular x) 0 := by
  have h := hasDerivAt_rot 0 x
  rwa [rot_zero] at h

/-- The angular derivative of an axisymmetric pressure vanishes. -/
theorem angularDerivative_eq_zero {p : PressureField} {t : ℝ} {x : Space}
    (hp : AxisymmetricPressure p t) (hd : DifferentiableAt ℝ (fun y ↦ p (t, y)) x) :
    angularDerivative p t x = 0 := by
  have h1 : HasDerivAt (fun φ ↦ p (t, rot φ x)) (fderiv ℝ (fun y ↦ p (t, y)) x (angular x)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 hd.hasFDerivAt (hasDerivAt_rot_zero x) (rot_zero x).symm
  have h2 : HasDerivAt (fun φ ↦ p (t, rot φ x)) 0 0 := by
    have e : (fun φ ↦ p (t, rot φ x)) = fun _ ↦ p (t, x) := funext fun φ ↦ hp φ x
    rw [e]
    exact hasDerivAt_const _ _
  have h3 := h1.unique h2
  have e : angularDerivative p t x = angularDeriv (fun y ↦ p (t, y)) x := by
    rw [angularDeriv_eq]
    rfl
  rw [e]
  exact h3

/-- The angular derivative of an axisymmetric velocity is its rotation generator. -/
theorem fderiv_angular_eq {u : VelocityField} {t : ℝ} {x : Space}
    (hu : AxisymmetricVelocity u t) (hd : DifferentiableAt ℝ (fun y ↦ u (t, y)) x) :
    fderiv ℝ (fun y ↦ u (t, y)) x (angular x) = angular (u (t, x)) := by
  have h1 : HasDerivAt (fun φ ↦ u (t, rot φ x)) (fderiv ℝ (fun y ↦ u (t, y)) x (angular x)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 hd.hasFDerivAt (hasDerivAt_rot_zero x) (rot_zero x).symm
  have h2 : HasDerivAt (fun φ ↦ u (t, rot φ x)) (angular (u (t, x))) 0 := by
    have e : (fun φ ↦ u (t, rot φ x)) = fun φ ↦ rot φ (u (t, x)) := funext fun φ ↦ hu φ x
    rw [e]
    exact hasDerivAt_rot_zero _
  exact h1.unique h2

/-- **At a critical point of the swirl of an axisymmetric velocity, off the
axis, the axial vorticity vanishes**: `x₀ ∂₀Γ + x₁ ∂₁Γ = r² ω₃`. -/
theorem axialVorticity_eq_zero_of_critical {u : VelocityField} {t : ℝ} {x : Space}
    (hu : AxisymmetricVelocity u t) (hd : DifferentiableAt ℝ (fun y ↦ u (t, y)) x)
    (hcrit : fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x = 0) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    axialVorticity u t x = 0 := by
  have hE := fderiv_angular_eq hu hd
  rw [angular_eq, map_sub, map_smul, map_smul] at hE
  have hE0 := congrArg (fun v : Space ↦ v 0) hE
  have hE1 := congrArg (fun v : Space ↦ v 1) hE
  simp only [angular, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hE0 hE1
  have hC0 := fderiv_swirlSlice_apply hd (e 0)
  have hC1 := fderiv_swirlSlice_apply hd (e 1)
  rw [hcrit] at hC0 hC1
  simp only [e_apply] at hC0 hC1
  simp at hE0 hE1 hC0 hC1
  have key : (x 0 ^ 2 + x 1 ^ 2) * axialVorticity u t x = 0 := by
    unfold axialVorticity spatialDerivative
    linear_combination (-x 0) * hC0 - x 0 * hE0 - x 1 * hE1 + (-x 1) * hC1
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hr
  · exact h

theorem contDiffAt_swirlSlice {U : Space → Space} {x : Space} (hU : ContDiffAt ℝ 2 U x) :
    ContDiffAt ℝ 2 (swirlSlice U) x := by
  have c0 : ContDiffAt ℝ 2 (fun z : Space ↦ z 0) x :=
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have c1 : ContDiffAt ℝ 2 (fun z : Space ↦ z 1) x :=
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have u0 : ContDiffAt ℝ 2 (fun z ↦ U z 0) x :=
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff.contDiffAt.comp x hU
  have u1 : ContDiffAt ℝ 2 (fun z ↦ U z 1) x :=
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).contDiff.contDiffAt.comp x hU
  exact ContDiffAt.sub (ContDiffAt.mul c0 u1) (ContDiffAt.mul c1 u0)

/-- **The pointwise core of the swirl maximum principle.** For an axisymmetric
flow with Navier–Stokes residual `f` and nonnegative viscosity, at every
spatial local maximum of the swirl off the axis, the swirl grows no faster
than the torque of the force: `∂ₜΓ ≤ x₀ f₁ - x₁ f₀`. Without a force, the
swirl cannot increase at its maxima. -/
theorem deriv_swirl_le_torque_of_isLocalMax {ν : ℝ} (hν : 0 ≤ ν) {u : VelocityField}
    {p : PressureField} {f : VelocityField} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ 2 (fun y ↦ u (t, y)) x) (ht : DifferentiableAt ℝ (fun s ↦ u (s, x)) t)
    (hres : NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (hmax : IsLocalMax (swirlSlice (fun y ↦ u (t, y))) x)
    (haxi : AxisymmetricVelocity u t) (hpaxi : AxisymmetricPressure p t)
    (hp : DifferentiableAt ℝ (fun y ↦ p (t, y)) x) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) x) t ≤ torque f t x := by
  have hid := swirl_identity hu ht hres
  have hUx : DifferentiableAt ℝ (fun y ↦ u (t, y)) x := hu.differentiableAt (by norm_num)
  have hcrit : fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x = 0 := IsLocalMax.fderiv_eq_zero hmax
  have hadv : fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x (u (t, x)) = 0 := by
    rw [hcrit]
    rfl
  have hlap : ∑ i : Fin 3, fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) x
      (e i) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ secondDeriv_nonpos_of_isLocalMax (contDiffAt_swirlSlice hu) hmax (e i)
  have hω := axialVorticity_eq_zero_of_critical haxi hUx hcrit hr
  have hθ := angularDerivative_eq_zero hpaxi hp
  rw [hadv, hω, hθ] at hid
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hν hlap]

/-- The swirl of the time slices, as a function on space-time. -/
def swirlField (u : VelocityField) (z : ℝ × Space) : ℝ := swirlSlice (fun y ↦ u (z.1, y)) z.2

theorem continuousOn_swirlField {u : VelocityField} {S : Set (ℝ × Space)} (hu : ContinuousOn u S) :
    ContinuousOn (swirlField u) S := by
  have c : ∀ i : Fin 3, ContinuousOn (fun z : ℝ × Space ↦ u z i) S := fun i ↦
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu)
  have d : ∀ i : Fin 3, ContinuousOn (fun z : ℝ × Space ↦ z.2 i) S := fun i ↦
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp continuous_snd).continuousOn
  exact ContinuousOn.sub (ContinuousOn.mul (d 0) (c 1)) (ContinuousOn.mul (d 1) (c 0))

/-- **The swirl maximum principle for axisymmetric flows.** Let the velocity
be continuous on `[0, T] × ℝ³`, with swirl nonpositive outside a compact set
`K`, twice differentiable in space and differentiable in time on `(0, T]`,
axisymmetric with axisymmetric pressure, and with a force whose torque is
nonpositive. Then the swirl never exceeds its initial maximum `M₀ ≥ 0`. In
particular, without a force the maximal swirl of an axisymmetric flow cannot
grow. -/
theorem swirl_le_of_axisymmetric {ν : ℝ} (hν : 0 ≤ ν) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {T M₀ : ℝ} {K : Set Space} (hK : IsCompact K) (hM₀ : 0 ≤ M₀)
    (hcont : ContinuousOn u (Set.Icc 0 T ×ˢ Set.univ))
    (hout : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∉ K, swirlSlice (fun y ↦ u (t, y)) x ≤ 0)
    (hinit : ∀ x, swirlSlice (fun y ↦ u (0, y)) x ≤ M₀)
    (hreg : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, ContDiffAt ℝ 2 (fun y ↦ u (t, y)) x ∧
      DifferentiableAt ℝ (fun s ↦ u (s, x)) t ∧ DifferentiableAt ℝ (fun y ↦ p (t, y)) x)
    (hres : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (haxi : ∀ t ∈ Set.Ioc (0 : ℝ) T, AxisymmetricVelocity u t)
    (hpaxi : ∀ t ∈ Set.Ioc (0 : ℝ) T, AxisymmetricPressure p t)
    (htorque : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, torque f t x ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, swirlSlice (fun y ↦ u (t, y)) x ≤ M₀ := by
  intro t ht x
  by_contra hlt
  push Not at hlt
  set Γ₀ := swirlSlice (fun y ↦ u (t, y)) x with hΓ₀
  have hT : 0 ≤ T := ht.1.trans ht.2
  -- the tilt
  set ε : ℝ := (Γ₀ - M₀) / (2 * (T + 1)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  set G : ℝ × Space → ℝ := fun z ↦ swirlField u z - ε * z.1 with hG
  have hGc : ContinuousOn G (Set.Icc 0 T ×ˢ Set.univ) :=
    (continuousOn_swirlField hcont).sub (continuousOn_const.mul continuous_fst.continuousOn)
  -- the tilted swirl exceeds `M₀` at `(t, x)`
  have hGtx : M₀ < G (t, x) := by
    have h1 : ε * t ≤ (Γ₀ - M₀) / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [ht.1, ht.2]
    show M₀ < swirlField u (t, x) - ε * t
    have : swirlField u (t, x) = Γ₀ := rfl
    linarith
  have hxK : x ∈ K := by
    by_contra hx
    have := hout t ht x hx
    linarith
  -- a maximum of the tilted swirl on the compact region
  have hcpt : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨z, hz, hmax⟩ := hcpt.exists_isMaxOn ⟨(t, x), ⟨ht, hxK⟩⟩
    (hGc.mono (Set.prod_mono subset_rfl (Set.subset_univ K)))
  obtain ⟨ts, xs⟩ := z
  have hts : ts ∈ Set.Icc (0 : ℝ) T := hz.1
  have hxs : xs ∈ K := hz.2
  have hGz : M₀ < G (ts, xs) := lt_of_lt_of_le hGtx (hmax ⟨ht, hxK⟩)
  -- the maximum is at a positive time
  have hts0 : 0 < ts := by
    rcases eq_or_lt_of_le hts.1 with h | h
    · exfalso
      have h1 : G (ts, xs) = swirlSlice (fun y ↦ u (0, y)) xs := by
        simp only [hG, swirlField, ← h, mul_zero, sub_zero]
      have := hinit xs
      linarith
    · exact h
  have hts' : ts ∈ Set.Ioc (0 : ℝ) T := ⟨hts0, hts.2⟩
  set Γs := swirlSlice (fun y ↦ u (ts, y)) xs with hΓs
  have hGs : G (ts, xs) = Γs - ε * ts := rfl
  have hΓpos : 0 < Γs := by nlinarith
  -- off the axis
  have hr : xs 0 ^ 2 + xs 1 ^ 2 ≠ 0 := by
    intro h
    have h0 : xs 0 = 0 := by nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 1)]
    have h1 : xs 1 = 0 := by nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 1)]
    have : Γs = 0 := by simp [hΓs, swirlSlice, h0, h1]
    linarith
  -- a spatial maximum
  have hsmax : IsLocalMax (swirlSlice (fun y ↦ u (ts, y))) xs := by
    refine IsMaxOn.isLocalMax (s := Set.univ) (fun y _ ↦ ?_) Filter.univ_mem
    show swirlSlice (fun y ↦ u (ts, y)) y ≤ Γs
    by_cases hy : y ∈ K
    · have := hmax (show ((ts, y) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hts, hy⟩)
      simp only [Set.mem_ofPred_eq] at this
      have e : G (ts, y) = swirlSlice (fun y ↦ u (ts, y)) y - ε * ts := rfl
      linarith
    · have := hout ts hts y hy
      linarith
  -- the pointwise core at the maximum
  obtain ⟨hu2, htd, hpd⟩ := hreg ts hts' xs
  have hcore := deriv_swirl_le_torque_of_isLocalMax hν hu2 htd (hres ts hts' xs) hsmax
    (haxi ts hts') (hpaxi ts hts') hpd hr
  have hcore' : deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) xs) ts ≤ 0 :=
    hcore.trans (htorque ts hts' xs)
  -- the time derivative from the left is at least `ε`
  set g : ℝ → ℝ := fun s ↦ swirlSlice (fun y ↦ u (s, y)) xs with hg
  have hgd : DifferentiableAt ℝ g ts := by
    have h0 : DifferentiableAt ℝ (fun s ↦ u (s, xs) 0) ts :=
      DifferentiableAt.comp ts (ContinuousLinearMap.differentiableAt
        (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ)) htd
    have h1 : DifferentiableAt ℝ (fun s ↦ u (s, xs) 1) ts :=
      DifferentiableAt.comp ts (ContinuousLinearMap.differentiableAt
        (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ)) htd
    exact DifferentiableAt.sub (DifferentiableAt.const_mul h1 (xs 0))
      (DifferentiableAt.const_mul h0 (xs 1))
  have hlim := HasDerivAt.tendsto_slope_zero_left (DifferentiableAt.hasDerivAt hgd)
  have hev : ∀ᶠ h in 𝓝[<] (0 : ℝ), ε ≤ h⁻¹ • (g (ts + h) - g ts) := by
    have hmem : Set.Ioo (-ts) 0 ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [hmem] with h hh
    have hsIcc : ts + h ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hh.1], by linarith [hh.2, hts.2]⟩
    have hle := hmax (show ((ts + h, xs) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hsIcc, hxs⟩)
    simp only [Set.mem_ofPred_eq] at hle
    have e1 : G (ts + h, xs) = g (ts + h) - ε * (ts + h) := rfl
    have e2 : G (ts, xs) = g ts - ε * ts := rfl
    have hdiff : g (ts + h) - g ts ≤ ε * h := by linarith
    rw [smul_eq_mul, ← div_eq_inv_mul, le_div_iff_of_neg hh.2]
    linarith
  have hge : ε ≤ deriv g ts := ge_of_tendsto hlim hev
  have : deriv g ts = deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) xs) ts := rfl
  linarith

end MaximumPrinciple

end Mettapedia.FluidDynamics.NavierStokes.SwirlBudget
