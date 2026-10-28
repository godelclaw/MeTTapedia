import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrderPart1

/-!
# Vector Calculus R3: FirstOrder

First-order spatial, temporal, divergence, and pressure-gradient identities.
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
theorem initialSpatialDivergence_const_smul
    (a : ℝ) (u₀ : NSInitialVelocity) (x : NSSpace) :
    initialSpatialDivergence (a • u₀) x = a * initialSpatialDivergence u₀ x := by
  rw [initialSpatialDivergence]
  rw [fderiv_const_smul_field]
  simp
  rw [← Finset.mul_sum]
  rfl

/-- Divergence of initial data commutes with addition. -/
theorem initialSpatialDivergence_add
    {u₀ v₀ : NSInitialVelocity} {x : NSSpace}
    (hu : DifferentiableAt ℝ u₀ x) (hv : DifferentiableAt ℝ v₀ x) :
    initialSpatialDivergence (u₀ + v₀) x =
      initialSpatialDivergence u₀ x + initialSpatialDivergence v₀ x := by
  rw [initialSpatialDivergence, initialSpatialDivergence, initialSpatialDivergence]
  rw [fderiv_add hu hv]
  simp [Finset.sum_add_distrib]

/-- Divergence of zero initial data is zero. -/
theorem initialSpatialDivergence_zero (x : NSSpace) :
    initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
  simp [initialSpatialDivergence]

/-- Divergence of constant initial velocity data is zero. -/
theorem initialSpatialDivergence_constantInitialVelocity
    (c : NSSpace) (x : NSSpace) :
    initialSpatialDivergence (constantInitialVelocity c) x = 0 := by
  unfold initialSpatialDivergence constantInitialVelocity
  simp [fderiv_const_apply]

/-- Divergence of the concrete linear shear initial data is zero. -/
theorem initialSpatialDivergence_linearShearInitialVelocity
    (a : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearInitialVelocity a) x = 0 := by
  have hf :
      fderiv ℝ (linearShearInitialVelocity a) x = linearShearMap a := by
    simp [linearShearInitialVelocity, linearShearMap]
  rw [initialSpatialDivergence, hf, Fin.sum_univ_three]
  simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- Divergence of the initial data `x ↦ (a * x₁, 0, b)` is zero. -/
theorem initialSpatialDivergence_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearVerticalDriftInitialVelocity a b) x = 0 := by
  rw [linearShearVerticalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearInitialVelocity a).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Divergence of the initial data `x ↦ (a * x₁, b, 0)` is zero. -/
theorem initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearHorizontalDriftInitialVelocity a b) x = 0 := by
  rw [linearShearHorizontalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearInitialVelocity a).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord1 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Divergence of the initial data `x ↦ (a * x₁, b, c)` is zero. -/
theorem initialSpatialDivergence_linearShearFullDriftInitialVelocity
    (a b c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearFullDriftInitialVelocity a b c) x = 0 := by
  rw [linearShearFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The damped sinusoidal initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearInitialVelocity
    (a k : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearInitialVelocity a k) x = 0 := by
  have hslice :
      (fun y : NSSpace => heatShearInitialVelocity a k y) =
        fun y : NSSpace => heatShearVelocityField 0 a k 0 y := by
    funext y
    simp [heatShearVelocityField, heatShearInitialVelocity, heatShearScalar,
      heatShearInitialScalar]
  simpa [initialSpatialDivergence, spatialDivergence, spatialFDeriv, hslice] using
    (spatialDivergence_heatShearVelocityField (ν := 0) a k 0 x : _)

/-- The heat-shear datum with streamwise drift is divergence free. -/
theorem initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearStreamwiseDriftInitialVelocity a k d) x = 0 := by
  rw [heatShearStreamwiseDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The heat-shear datum with vertical drift is divergence free. -/
theorem initialSpatialDivergence_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearVerticalDriftInitialVelocity a k c) x = 0 := by
  rw [heatShearVerticalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The heat-shear datum with full drift is divergence free. -/
theorem initialSpatialDivergence_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearFullDriftInitialVelocity a k d c) x = 0 := by
  rw [heatShearFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Pressure gradient commutes with addition. -/
theorem spatialPressureGradient_add
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (p + q) t x =
      spatialPressureGradient p t x + spatialPressureGradient q t x := by
  unfold spatialPressureGradient
  change gradient ((fun y : NSSpace => p t y) + fun y : NSSpace => q t y) x = _
  rw [gradient, fderiv_add hp hq]
  simp [gradient]

/-- Pressure gradient commutes with constant scalar multiplication. -/
theorem spatialPressureGradient_const_smul
    (a : ℝ) (p : NSPressureField) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (a • p) t x = a • spatialPressureGradient p t x := by
  unfold spatialPressureGradient
  change gradient (a • fun y : NSSpace => p t y) x = _
  rw [gradient, fderiv_const_smul_field]
  simp [gradient]

/-- Pressure gradient commutes with sign flip. -/
theorem spatialPressureGradient_neg
    (p : NSPressureField) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (-p) t x = -spatialPressureGradient p t x := by
  simpa using spatialPressureGradient_const_smul (-1 : ℝ) p t x

/-- Pressure gradient commutes with subtraction. -/
theorem spatialPressureGradient_sub
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (p - q) t x =
      spatialPressureGradient p t x - spatialPressureGradient q t x := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [spatialPressureGradient_add (p := p) (q := -q) hp hq.neg]
  rw [spatialPressureGradient_neg]

/-- Pressure gradient commutes with real linear combinations. -/
theorem spatialPressureGradient_linearCombination
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (a • p + b • q) t x =
      a • spatialPressureGradient p t x + b • spatialPressureGradient q t x := by
  rw [spatialPressureGradient_add (hp.const_smul a) (hq.const_smul b)]
  rw [spatialPressureGradient_const_smul, spatialPressureGradient_const_smul]

/-- Pressure gradient of the zero field is zero. -/
theorem spatialPressureGradient_zero (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (0 : NSPressureField) t x = 0 := by
  simp [spatialPressureGradient]

/-- Pressure gradient of a spatially constant pressure field is zero. -/
theorem spatialPressureGradient_const
    (c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ : NSTime => fun _ : NSSpace => c) t x = 0 := by
  unfold spatialPressureGradient
  simp

/-- Pressure gradient of a time-only pressure field is zero on every spatial
slice. -/
theorem spatialPressureGradient_timeOnly
    (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x = 0 := by
  unfold spatialPressureGradient
  simp

/-- Any affine combination of a spatially constant pressure and a time-only
pressure is still time-only, hence has zero spatial gradient on every slice. -/
theorem spatialPressureGradient_affineConstantTimeOnly
    (a b c : ℝ) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
  change
    spatialPressureGradient
      (fun s : NSTime => fun _ : NSSpace => a • c + b • π s) t x = 0
  simpa [smul_eq_mul] using
    spatialPressureGradient_timeOnly (fun s : NSTime => a • c + b • π s) t x

/-- The spatial gradient of the coordinate-linear pressure field
`p(t,x) = c * x₀` is the constant vector `c e₀`. -/
theorem spatialPressureGradient_coord0Linear
    (c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t x =
      EuclideanSpace.single nsCoord0 c := by
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (EuclideanSpace.single nsCoord0 c) =
        c • (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    simp [EuclideanSpace.inner_single_left, nsCoord0]
  unfold spatialPressureGradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [hdual]
  refine
    (((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).hasFDerivAt.const_smul c).congr_of_eventuallyEq ?_)
  filter_upwards with y
  simp [smul_eq_mul]

/-- The compensating pressure field `p(t,x) = -(a * b) * x₀` has constant
spatial gradient `-(a * b) e₀`. -/
theorem spatialPressureGradient_linearShearHorizontalDriftPressureField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      EuclideanSpace.single nsCoord0 (-(a * b)) := by
  rw [spatialPressureGradient_congr_at
    (p := linearShearHorizontalDriftPressureField a b)
    (q := fun _ : NSTime => fun y : NSSpace => (-(a * b)) * y nsCoord0)
    (t := t) (x := x)]
  · exact
    spatialPressureGradient_coord0Linear (-(a * b)) t x
  · intro y
    change -(a * b * y nsCoord0) = (-(a * b)) * y nsCoord0
    ring
end VectorCalculusR3
end NavierStokes
end FluidDynamics
end Mettapedia
