import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder

/-!
# Vector Calculus R3: PressureObstructions

Pressure-gradient compatibility and vorticity obstruction lemmas for the momentum equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped Gradient
open scoped Laplacian
open scoped BigOperators
open scoped ContDiff

section VectorCalculusR3

/-- The smoothness order `C^∞` used for concrete NS fields is at least `C²`. -/
theorem two_le_contDiff_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top)

/-- Over the real field, the minimal smoothness needed for symmetric second
derivatives is also available from `C^∞`. -/
theorem minSmoothness_two_le_contDiff_infty : minSmoothness ℝ 2 ≤ ∞ := by
  simpa using two_le_contDiff_infty

/-- View the spatial pressure gradient as a velocity field on `ℝ × ℝ^3`. -/
def pressureGradientVelocityField (p : NSPressureField) : NSVelocityField :=
  fun t x => spatialPressureGradient p t x

/-- The vector field that a pressure gradient must equal in the concrete
momentum equation:
\[
  \nabla p = \nu \Delta u - \partial_t u - (u\cdot\nabla)u.
\]
This isolates the exact-gradient compatibility burden from the rest of the
momentum identity. -/
def momentumPressureResidual (ν : ℝ) (u : NSVelocityField) : NSVelocityField :=
  fun t x =>
    ν • spatialLaplacian u t x - timeVelocityDerivative u t x -
      spatialConvection u t x

/-- A coordinate derivative of the gradient of a smooth scalar field is the
corresponding second Fréchet derivative. -/
theorem fderiv_gradient_component_eq_second_fderiv
    {f : NSSpace → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (x : NSSpace) (coord comp : Fin 3) :
    (fderiv ℝ (fun y : NSSpace => gradient f y) x
        (EuclideanSpace.single coord (1 : ℝ))) comp =
      fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x
        (EuclideanSpace.single coord (1 : ℝ))
        (EuclideanSpace.single comp (1 : ℝ)) := by
  let ecoord : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  let ecomp : NSSpace := EuclideanSpace.single comp (1 : ℝ)
  have hfdiff : DifferentiableAt ℝ (fun y : NSSpace => fderiv ℝ f y) x := by
    exact ((hf.contDiffAt (x := x)).fderiv_right (m := 1)
      two_le_contDiff_infty).differentiableAt one_ne_zero
  have hgrad_diff : DifferentiableAt ℝ (fun y : NSSpace => gradient f y) x := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ NSSpace).symm.differentiableAt.comp x hfdiff
  have hproj :
      fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x =
        (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).comp
          (fderiv ℝ (fun y : NSSpace => gradient f y) x) := by
    change
      fderiv ℝ ((EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ) ∘
          fun y : NSSpace => gradient f y) x =
        (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).comp
          (fderiv ℝ (fun y : NSSpace => gradient f y) x)
    have hraw :=
      fderiv_comp x (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).differentiableAt hgrad_diff
    rw [(EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).fderiv] at hraw
    exact hraw
  have hvec_scalar :
      (fderiv ℝ (fun y : NSSpace => gradient f y) x ecoord) comp =
        fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x ecoord := by
    simpa [ContinuousLinearMap.comp_apply, ecoord] using
      (congrArg (fun L : NSSpace →L[ℝ] ℝ => L ecoord) hproj).symm
  have hcomp_eq :
      (fun y : NSSpace => (gradient f y) comp) =
        fun y : NSSpace => fderiv ℝ f y ecomp := by
    funext y
    have hinner : inner ℝ ecomp (gradient f y) = fderiv ℝ f y ecomp := by
      rw [inner_gradient_right (𝕜 := ℝ) (f := f) (x := ecomp) (y := y)]
      simp
    have hcoord : inner ℝ ecomp (gradient f y) = (gradient f y) comp := by
      change inner ℝ (EuclideanSpace.single comp (1 : ℝ)) (gradient f y) = (gradient f y) comp
      rw [EuclideanSpace.inner_single_left]
      simp
    exact hcoord.symm.trans hinner
  have hscalar :
      fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x ecoord =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x ecoord := by
    rw [hcomp_eq]
  have happly :
      fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x ecoord =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x ecoord ecomp := by
    have h :
        fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x =
          (ContinuousLinearMap.apply ℝ ℝ ecomp).comp
            (fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x) := by
      change
        fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ ecomp) ∘
            fun y : NSSpace => fderiv ℝ f y) x =
          (ContinuousLinearMap.apply ℝ ℝ ecomp).comp
            (fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x)
      have hraw := fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ ecomp).differentiableAt hfdiff
      rw [(ContinuousLinearMap.apply ℝ ℝ ecomp).fderiv] at hraw
      exact hraw
    simpa [ContinuousLinearMap.comp_apply, ecoord] using
      congrArg (fun L : NSSpace →L[ℝ] ℝ => L ecoord) h
  calc
    (fderiv ℝ (fun y : NSSpace => gradient f y) x
        (EuclideanSpace.single coord (1 : ℝ))) comp
        = (fderiv ℝ (fun y : NSSpace => gradient f y) x ecoord) comp := by rfl
    _ = fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x ecoord := hvec_scalar
    _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x ecoord := hscalar
    _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x ecoord ecomp := happly
    _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x
        (EuclideanSpace.single coord (1 : ℝ))
        (EuclideanSpace.single comp (1 : ℝ)) := by rfl

/-- A coordinate derivative of an arbitrary smooth pressure-gradient field is
the corresponding mixed second derivative of the pressure slice. -/
theorem spatialDerivativeComponent_pressureGradientVelocityField
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (pressureGradientVelocityField p) t x coord comp =
      fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => p t z) y) x
        (EuclideanSpace.single coord (1 : ℝ))
        (EuclideanSpace.single comp (1 : ℝ)) := by
  let f : NSSpace → ℝ := fun z => p t z
  change (fderiv ℝ (fun y : NSSpace => gradient f y) x
        (EuclideanSpace.single coord (1 : ℝ))) comp = _
  exact fderiv_gradient_component_eq_second_fderiv
    (f := f) (smoothSpaceTimePressure_contDiff_spatialSlice hp t) x coord comp

/-- The spatial curl/vorticity of an arbitrary smooth pressure-gradient field
vanishes. This is a structural integrability obstruction, not a property of a
particular pressure ansatz. -/
theorem spatialVorticity_pressureGradientVelocityField
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (pressureGradientVelocityField p) t x = 0 := by
  let f : NSSpace → ℝ := fun z => p t z
  have hf : ContDiff ℝ ∞ f := smoothSpaceTimePressure_contDiff_spatialSlice hp t
  have hsymm : IsSymmSndFDerivAt ℝ f x := by
    exact (hf.contDiffAt (x := x)).isSymmSndFDerivAt minSmoothness_two_le_contDiff_infty
  ext i
  fin_cases i
  · simp [spatialVorticity, spatialDerivativeComponent_pressureGradientVelocityField hp,
      nsCoord0, nsCoord1, nsCoord2]
    exact sub_eq_zero.mpr (hsymm.eq (EuclideanSpace.single nsCoord1 (1 : ℝ))
      (EuclideanSpace.single nsCoord2 (1 : ℝ)))
  · simp [spatialVorticity, spatialDerivativeComponent_pressureGradientVelocityField hp,
      nsCoord0, nsCoord1, nsCoord2]
    exact sub_eq_zero.mpr (hsymm.eq (EuclideanSpace.single nsCoord2 (1 : ℝ))
      (EuclideanSpace.single nsCoord0 (1 : ℝ)))
  · simp [spatialVorticity, spatialDerivativeComponent_pressureGradientVelocityField hp,
      nsCoord0, nsCoord1, nsCoord2]
    exact sub_eq_zero.mpr (hsymm.eq (EuclideanSpace.single nsCoord0 (1 : ℝ))
      (EuclideanSpace.single nsCoord1 (1 : ℝ)))

/-- A velocity field with nonzero vorticity somewhere cannot be represented as
the spatial gradient of any smooth pressure field. -/
theorem not_exists_smoothPressure_pressureGradientVelocityField_eq_of_spatialVorticity_ne_zero
    {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace, spatialVorticity u t x ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧ pressureGradientVelocityField p = u := by
  rintro ⟨p, hp, hpu⟩
  rcases hcurl with ⟨t, x, hne⟩
  apply hne
  rw [← hpu]
  exact spatialVorticity_pressureGradientVelocityField hp t x

/-- Any pressure satisfying the concrete momentum equation has gradient equal
to the exact pressure residual `ν Δu - ∂ₜu - (u · ∇)u`. -/
theorem pressureGradientVelocityField_eq_momentumPressureResidual_of_momentumEquation
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField}
    (hmom : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) :
    pressureGradientVelocityField p = momentumPressureResidual ν u := by
  funext t x
  have h := hmom t x
  unfold pressureGradientVelocityField momentumPressureResidual
  calc
    spatialPressureGradient p t x =
        (timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x) -
            timeVelocityDerivative u t x - spatialConvection u t x := by
      abel
    _ = ν • spatialLaplacian u t x -
          timeVelocityDerivative u t x - spatialConvection u t x := by
      rw [h]

/-- Therefore the exact pressure residual of any smooth-pressure momentum
solution is curl-free. -/
theorem spatialVorticity_momentumPressureResidual_of_momentumEquation
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (hmom : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  rw [← pressureGradientVelocityField_eq_momentumPressureResidual_of_momentumEquation hmom]
  exact spatialVorticity_pressureGradientVelocityField hp t x

/-- If the concrete pressure residual has nonzero curl somewhere, no smooth
pressure can repair the momentum equation for that velocity field. -/
theorem not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
    {ν : ℝ} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rintro ⟨p, hp, hmom⟩
  rcases hcurl with ⟨t, x, hne⟩
  exact hne (spatialVorticity_momentumPressureResidual_of_momentumEquation hp hmom t x)

/-- The explicit constant velocity field matches the corresponding constant
initial data at time `0`. -/
theorem matchesInitialVelocity_constantVelocityField
    (c : NSSpace) :
    MatchesInitialVelocity (constantInitialVelocity c) (constantVelocityField c) := by
  intro x
  rfl

/-- The steady linear shear field matches the corresponding linear shear
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearVelocityField
    (a : ℝ) :
    MatchesInitialVelocity (linearShearInitialVelocity a) (linearShearVelocityField a) := by
  intro x
  rfl

/-- The steady field `u(t,x) = (a * x₁, 0, b)` matches the corresponding
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearVerticalDriftVelocityField
    (a b : ℝ) :
    MatchesInitialVelocity
      (linearShearVerticalDriftInitialVelocity a b)
      (linearShearVerticalDriftVelocityField a b) := by
  intro x
  rfl

/-- The steady field `u(t,x) = (a * x₁, b, 0)` matches the corresponding
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) :
    MatchesInitialVelocity
      (linearShearHorizontalDriftInitialVelocity a b)
      (linearShearHorizontalDriftVelocityField a b) := by
  intro x
  rfl

/-- The steady field `u(t,x) = (a * x₁, b, c)` matches the corresponding
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearFullDriftVelocityField
    (a b c : ℝ) :
    MatchesInitialVelocity
      (linearShearFullDriftInitialVelocity a b c)
      (linearShearFullDriftVelocityField a b c) := by
  intro x
  rfl

/-- The damped sinusoidal heat-shear field matches the corresponding initial
datum at time `0`. -/
theorem matchesInitialVelocity_heatShearVelocityField
    (ν a k : ℝ) :
    MatchesInitialVelocity
      (heatShearInitialVelocity a k)
      (heatShearVelocityField ν a k) := by
  intro x
  simp [heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar]

/-- The heat-shear family with streamwise drift matches its declared initial
data at time `0`. -/
theorem matchesInitialVelocity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) :
    MatchesInitialVelocity
      (heatShearStreamwiseDriftInitialVelocity a k d)
      (heatShearStreamwiseDriftVelocityField ν a k d) := by
  intro x
  simp [heatShearStreamwiseDriftVelocityField, heatShearStreamwiseDriftInitialVelocity,
    heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord0]

/-- The heat-shear family with vertical drift matches its declared initial
data at time `0`. -/
theorem matchesInitialVelocity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) :
    MatchesInitialVelocity
      (heatShearVerticalDriftInitialVelocity a k c)
      (heatShearVerticalDriftVelocityField ν a k c) := by
  intro x
  simp [heatShearVerticalDriftVelocityField, heatShearVerticalDriftInitialVelocity,
    heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity]

/-- The heat-shear family with full drift matches its declared initial data at
time `0`. -/
theorem matchesInitialVelocity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) :
    MatchesInitialVelocity
      (heatShearFullDriftInitialVelocity a k d c)
      (heatShearFullDriftVelocityField ν a k d c) := by
  intro x
  simp [heatShearFullDriftVelocityField, heatShearFullDriftInitialVelocity,
    heatShearStreamwiseDriftVelocityField, heatShearStreamwiseDriftInitialVelocity,
    heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord0]
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
