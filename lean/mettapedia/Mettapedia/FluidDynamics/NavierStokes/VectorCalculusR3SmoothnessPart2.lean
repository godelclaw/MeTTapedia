import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3SmoothnessPart1

/-!
# Vector Calculus R3: Smoothness

Smoothness, application, and initial-data facts for the concrete shear families.
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
theorem coord0Embedding_apply
    (z : ℝ) :
    coord0Embedding z = EuclideanSpace.single nsCoord0 z := by
  ext i
  fin_cases i <;>
    simp [coord0Embedding, nsCoord0, ContinuousLinearMap.smulRight_apply]

/-- The damped sinusoidal initial datum is given coordinatewise by
`x ↦ (a * sin (k * x₁), 0, 0)`. -/
theorem heatShearInitialVelocity_apply
    (a k : ℝ) (x : NSSpace) :
    heatShearInitialVelocity a k x =
      EuclideanSpace.single nsCoord0 (a * Real.sin (k * x nsCoord1)) := by
  simp [heatShearInitialVelocity, heatShearInitialScalar, coord0Embedding_apply]

/-- Zero amplitude collapses the heat-shear initial datum to the zero field. -/
theorem heatShearInitialVelocity_zero_of_amplitude_zero
    (k : ℝ) :
    heatShearInitialVelocity 0 k = (0 : NSInitialVelocity) := by
  funext x
  simp [heatShearInitialVelocity, heatShearInitialScalar, coord0Embedding_apply]

/-- Zero wave number collapses the heat-shear initial datum to the zero field. -/
theorem heatShearInitialVelocity_zero_of_wavenumber_zero
    (a : ℝ) :
    heatShearInitialVelocity a 0 = (0 : NSInitialVelocity) := by
  funext x
  simp [heatShearInitialVelocity, heatShearInitialScalar, coord0Embedding_apply]

/-- The damped sinusoidal heat-shear field is given coordinatewise on every time
slice by
`x ↦ (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`. -/
theorem heatShearVelocityField_apply
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearVelocityField ν a k t x =
      EuclideanSpace.single nsCoord0
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) := by
  simp [heatShearVelocityField, heatShearScalar, coord0Embedding_apply, mul_assoc]

/-- The general time-amplitude shear ansatz is given coordinatewise on every
time slice by `x ↦ (A t * sin (k * x₁), 0, 0)`. -/
theorem amplitudeShearVelocityField_apply
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    amplitudeShearVelocityField A k t x =
      EuclideanSpace.single nsCoord0 (A t * Real.sin (k * x nsCoord1)) := by
  simp [amplitudeShearVelocityField, coord0Embedding_apply]

/-- The heat-shear datum with streamwise drift is given coordinatewise by
`x ↦ (d + a * sin (k * x₁), 0, 0)`. -/
theorem heatShearStreamwiseDriftInitialVelocity_apply
    (a k d : ℝ) (x : NSSpace) :
    heatShearStreamwiseDriftInitialVelocity a k d x =
      EuclideanSpace.single nsCoord0 (d + a * Real.sin (k * x nsCoord1)) := by
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDriftInitialVelocity, constantInitialVelocity,
      heatShearInitialVelocity_apply, nsCoord0, add_comm]

/-- The heat-shear family with streamwise drift is given coordinatewise on
every time slice by `x ↦ (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`.
-/
theorem heatShearStreamwiseDriftVelocityField_apply
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearStreamwiseDriftVelocityField ν a k d t x =
      EuclideanSpace.single nsCoord0
        (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) := by
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDriftVelocityField, constantVelocityField,
      heatShearVelocityField_apply, nsCoord0, add_comm]

/-- The heat-shear datum with vertical drift is given coordinatewise by
`x ↦ (a * sin (k * x₁), 0, c)`. -/
theorem heatShearVerticalDriftInitialVelocity_apply
    (a k c : ℝ) (x : NSSpace) :
    heatShearVerticalDriftInitialVelocity a k c x =
      EuclideanSpace.single nsCoord0 (a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearVerticalDriftInitialVelocity, constantInitialVelocity,
    heatShearInitialVelocity_apply]

/-- The heat-shear family with vertical drift is given coordinatewise on every
time slice by `x ↦ (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
theorem heatShearVerticalDriftVelocityField_apply
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearVerticalDriftVelocityField ν a k c t x =
      EuclideanSpace.single nsCoord0
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearVerticalDriftVelocityField, constantVelocityField,
    heatShearVelocityField_apply]

/-- The heat-shear datum with full drift is given coordinatewise by
`x ↦ (d + a * sin (k * x₁), 0, c)`. -/
theorem heatShearFullDriftInitialVelocity_apply
    (a k d c : ℝ) (x : NSSpace) :
    heatShearFullDriftInitialVelocity a k d c x =
      EuclideanSpace.single nsCoord0 (d + a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearFullDriftInitialVelocity, constantInitialVelocity,
    heatShearStreamwiseDriftInitialVelocity_apply]

/-- Vanishing streamwise drift reduces full-drift heat shear to the vertical-drift
subfamily. -/
theorem heatShearFullDriftInitialVelocity_zero_streamwiseDrift
    (a k c : ℝ) :
    heatShearFullDriftInitialVelocity a k 0 c =
      heatShearVerticalDriftInitialVelocity a k c := by
  funext x
  simp [heatShearFullDriftInitialVelocity, heatShearStreamwiseDriftInitialVelocity,
    heatShearVerticalDriftInitialVelocity, constantInitialVelocity]

/-- Vanishing vertical drift reduces full-drift heat shear to the streamwise-drift
subfamily. -/
theorem heatShearFullDriftInitialVelocity_zero_verticalDrift
    (a k d : ℝ) :
    heatShearFullDriftInitialVelocity a k d 0 =
      heatShearStreamwiseDriftInitialVelocity a k d := by
  funext x
  simp [heatShearFullDriftInitialVelocity, heatShearStreamwiseDriftInitialVelocity,
    constantInitialVelocity]

/-- Vanishing both extra drifts reduces full-drift heat shear to the base
heat-shear family. -/
theorem heatShearFullDriftInitialVelocity_zero_drifts
    (a k : ℝ) :
    heatShearFullDriftInitialVelocity a k 0 0 =
      heatShearInitialVelocity a k := by
  funext x
  ext i
  fin_cases i <;>
    simp [heatShearFullDriftInitialVelocity_apply,
      heatShearInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- The heat-shear family with full drift is given coordinatewise on every
time slice by `x ↦ (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
theorem heatShearFullDriftVelocityField_apply
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearFullDriftVelocityField ν a k d c t x =
      EuclideanSpace.single nsCoord0
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearFullDriftVelocityField, constantVelocityField,
    heatShearStreamwiseDriftVelocityField_apply]

/-- Linear shear initial velocity data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearInitialVelocity
    (a : ℝ) :
    smoothInitialVelocityData (linearShearInitialVelocity a) := by
  simpa [smoothInitialVelocityData, linearShearInitialVelocity] using
    (linearShearMap a).contDiff

/-- Initial velocity data `x ↦ (a * x₁, 0, b)` are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) :
    smoothInitialVelocityData (linearShearVerticalDriftInitialVelocity a b) := by
  simpa [linearShearVerticalDriftInitialVelocity] using
    smoothInitialVelocityData_add
      (smoothInitialVelocityData_linearShearInitialVelocity a)
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 b))

/-- Initial velocity data `x ↦ (a * x₁, b, 0)` are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) :
    smoothInitialVelocityData (linearShearHorizontalDriftInitialVelocity a b) := by
  simpa [linearShearHorizontalDriftInitialVelocity] using
    smoothInitialVelocityData_add
      (smoothInitialVelocityData_linearShearInitialVelocity a)
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord1 b))

/-- Initial velocity data `x ↦ (a * x₁, b, c)` are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearFullDriftInitialVelocity
    (a b c : ℝ) :
    smoothInitialVelocityData (linearShearFullDriftInitialVelocity a b c) := by
  simpa [linearShearFullDriftInitialVelocity] using
    smoothInitialVelocityData_add
      (smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b)
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 c))

/-- The damped sinusoidal initial datum is smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearInitialVelocity
    (a k : ℝ) :
    smoothInitialVelocityData (heatShearInitialVelocity a k) := by
  have hscalar : ContDiff ℝ ∞ (heatShearInitialScalar a k) := by
    exact contDiff_congr_global
      ((Real.contDiff_sin.comp
        ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.const_smul k)).const_smul a)
      (by intro x; rfl)
  exact smoothInitialVelocityData_of_contDiff
    (contDiff_congr_global (coord0Embedding.contDiff.comp hscalar) (by intro x; rfl))

/-- Initial velocity data `x ↦ (d + a * sin (k * x₁), 0, 0)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) :
    smoothInitialVelocityData (heatShearStreamwiseDriftInitialVelocity a k d) := by
  simpa [heatShearStreamwiseDriftInitialVelocity] using
    smoothInitialVelocityData_add
      (smoothInitialVelocityData_heatShearInitialVelocity a k)
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord0 d))

/-- Initial velocity data `x ↦ (a * sin (k * x₁), 0, c)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) :
    smoothInitialVelocityData (heatShearVerticalDriftInitialVelocity a k c) := by
  simpa [heatShearVerticalDriftInitialVelocity] using
    smoothInitialVelocityData_add
      (smoothInitialVelocityData_heatShearInitialVelocity a k)
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 c))

/-- Initial velocity data `x ↦ (d + a * sin (k * x₁), 0, c)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) :
    smoothInitialVelocityData (heatShearFullDriftInitialVelocity a k d c) := by
  simpa [heatShearFullDriftInitialVelocity] using
    smoothInitialVelocityData_add
      (smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d)
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 c))

/-- The steady linear shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearVelocityField
    (a : ℝ) :
    smoothSpaceTimeVelocity (linearShearVelocityField a) := by
  exact smoothSpaceTimeVelocity_of_contDiff_uncurried
    (contDiff_congr_global ((linearShearMap a).contDiff.comp contDiff_snd)
      (by intro tx; rfl))

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearVerticalDriftVelocityField
    (a b : ℝ) :
    smoothSpaceTimeVelocity (linearShearVerticalDriftVelocityField a b) := by
  simpa [linearShearVerticalDriftVelocityField] using
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_linearShearVelocityField a)
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b))

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) :
    smoothSpaceTimeVelocity (linearShearHorizontalDriftVelocityField a b) := by
  simpa [linearShearHorizontalDriftVelocityField] using
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_linearShearVelocityField a)
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b))

/-- The steady field `u(t,x) = (a * x₁, b, c)` is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearFullDriftVelocityField
    (a b c : ℝ) :
    smoothSpaceTimeVelocity (linearShearFullDriftVelocityField a b c) := by
  simpa [linearShearFullDriftVelocityField] using
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b)
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c))

/-- The damped sinusoidal heat-shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearVelocityField
    (ν a k : ℝ) :
    smoothSpaceTimeVelocity (heatShearVelocityField ν a k) := by
  have htime : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1)) := by
    exact contDiff_congr_global
      (Real.contDiff_exp.comp
        ((contDiff_fst : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.1)).const_smul
          (-(ν * k ^ (2 : ℕ)))))
      (by
        intro tx
        congr 1)
  have hspace : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.sin (k * tx.2 nsCoord1)) := by
    have hcoord : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2 nsCoord1) := by
      exact contDiff_congr_global
        ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.comp contDiff_snd)
        (by intro tx; rfl)
    exact contDiff_congr_global
      (Real.contDiff_sin.comp (hcoord.const_smul k))
      (by intro tx; rfl)
  have hscalar : ContDiff ℝ ∞ (fun tx : NSSpacetime =>
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1) * Real.sin (k * tx.2 nsCoord1)) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm] using
      ((htime.mul hspace).const_smul a)
  have hmap :
      spaceTimeVelocityMap (heatShearVelocityField ν a k) =
        fun tx : NSSpacetime =>
          coord0Embedding
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1) * Real.sin (k * tx.2 nsCoord1)) := by
    funext tx
    simp [spaceTimeVelocityMap, heatShearVelocityField, heatShearScalar, mul_assoc]
  rw [smoothSpaceTimeVelocity, hmap]
  exact coord0Embedding.contDiff.comp hscalar

/-- The heat-shear family with streamwise drift is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) :
    smoothSpaceTimeVelocity (heatShearStreamwiseDriftVelocityField ν a k d) := by
  simpa [heatShearStreamwiseDriftVelocityField] using
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k)
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d))

/-- The heat-shear family with vertical drift is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) :
    smoothSpaceTimeVelocity (heatShearVerticalDriftVelocityField ν a k c) := by
  simpa [heatShearVerticalDriftVelocityField] using
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k)
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c))

/-- The heat-shear family with full drift is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) :
    smoothSpaceTimeVelocity (heatShearFullDriftVelocityField ν a k d c) := by
  simpa [heatShearFullDriftVelocityField] using
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d)
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c))

/-- The compensating pressure field `p(t,x) = -(a * b) * x₀` is smooth on
`ℝ × ℝ^3`. -/
theorem smoothSpaceTimePressure_linearShearHorizontalDriftPressureField
    (a b : ℝ) :
    smoothSpaceTimePressure (linearShearHorizontalDriftPressureField a b) := by
  have hp := smoothSpaceTimePressure_coord0Linear (-(a * b))
  rw [smoothSpaceTimePressure] at hp
  exact smoothSpaceTimePressure_of_contDiff_uncurried
    (contDiff_congr_global hp
      (by
        intro tx
        simp [linearShearHorizontalDriftPressureField]))
end VectorCalculusR3
end NavierStokes
end FluidDynamics
end Mettapedia
