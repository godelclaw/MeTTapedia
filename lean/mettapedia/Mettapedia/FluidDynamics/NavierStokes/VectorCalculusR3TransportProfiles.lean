import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity

/-!
# Vector Calculus R3: Transport Profiles

This module contains transported heat-shear profile formulas, reductions to
subfamilies, and smoothness results for transported heat-shear fields.
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

theorem heatShearTransportInitialVelocity_apply
    (a k b : ℝ) (x : NSSpace) :
    heatShearTransportInitialVelocity a k b x =
      EuclideanSpace.single nsCoord0 (a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord1 b := by
  simp [heatShearTransportInitialVelocity, heatShearInitialVelocity,
    heatShearInitialScalar, constantInitialVelocity, coord0Embedding_apply]

/-- The transported heat-shear field has the explicit coordinate formula
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, 0)`. -/
theorem heatShearTransportVelocityField_apply
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearTransportVelocityField ν a k b t x =
      EuclideanSpace.single nsCoord0
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) +
        EuclideanSpace.single nsCoord1 b := by
  simp [heatShearTransportVelocityField, heatShearTransportScalar,
    constantVelocityField, coord0Embedding_apply, mul_assoc]

/-- The transported arbitrary-amplitude shear field has the explicit coordinate
formula `u(t,x) = (A t * sin (k * (x₁ - b * t)), b, 0)`. -/
theorem amplitudeShearTransportVelocityField_apply
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    amplitudeShearTransportVelocityField A k b t x =
      EuclideanSpace.single nsCoord0 (A t * Real.sin (k * (x nsCoord1 - b * t))) +
        EuclideanSpace.single nsCoord1 b := by
  simp [amplitudeShearTransportVelocityField, constantVelocityField,
    coord0Embedding_apply]

/-- Initial data `x ↦ (d + a * sin (k * x₁), b, c)` for the transported
full-drift heat-shear branch. -/
theorem heatShearTransportFullDriftInitialVelocity_apply
    (a k b d c : ℝ) (x : NSSpace) :
    heatShearTransportFullDriftInitialVelocity a k b d c x =
      EuclideanSpace.single nsCoord0 (d + a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord1 b +
        EuclideanSpace.single nsCoord2 c := by
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftInitialVelocity, heatShearTransportInitialVelocity,
      heatShearInitialVelocity, heatShearInitialScalar, constantInitialVelocity,
      coord0Embedding_apply, nsCoord0, nsCoord1, nsCoord2, add_left_comm, add_comm]

/-- Vanishing transport speed reduces transported full-drift heat shear to the
non-transport full-drift subfamily. -/
theorem heatShearTransportFullDriftInitialVelocity_zero_transport
    (a k d c : ℝ) :
    heatShearTransportFullDriftInitialVelocity a k 0 d c =
      heatShearFullDriftInitialVelocity a k d c := by
  funext x
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftInitialVelocity_apply,
      heatShearFullDriftInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- Vanishing extra streamwise and vertical drifts reduces transported
full-drift heat shear to the transported heat-shear subfamily. -/
theorem heatShearTransportFullDriftInitialVelocity_zero_drifts
    (a k b : ℝ) :
    heatShearTransportFullDriftInitialVelocity a k b 0 0 =
      heatShearTransportInitialVelocity a k b := by
  funext x
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftInitialVelocity_apply,
      heatShearTransportInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- The transported full-drift heat-shear field has the explicit coordinate
formula
`u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, c)`. -/
theorem heatShearTransportFullDriftVelocityField_apply
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearTransportFullDriftVelocityField ν a k b d c t x =
      EuclideanSpace.single nsCoord0
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) +
        EuclideanSpace.single nsCoord1 b +
        EuclideanSpace.single nsCoord2 c := by
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField, coord0Embedding_apply,
      nsCoord0, nsCoord1, nsCoord2, add_left_comm, add_comm, mul_assoc]

/-- Initial velocity data `x ↦ (a * sin (k * x₁), b, 0)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearTransportInitialVelocity
    (a k b : ℝ) :
    smoothInitialVelocityData (heatShearTransportInitialVelocity a k b) := by
  simpa [heatShearTransportInitialVelocity] using
    (smoothInitialVelocityData_heatShearInitialVelocity a k).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord1 b))

/-- The transported heat-shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearTransportVelocityField
    (ν a k b : ℝ) :
    smoothSpaceTimeVelocity (heatShearTransportVelocityField ν a k b) := by
  have htime : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1)) := by
    simpa [smul_eq_mul, mul_assoc] using
      (Real.contDiff_exp.comp (contDiff_fst.const_smul (-(ν * k ^ (2 : ℕ)))))
  have hphase : ContDiff ℝ ∞
      (fun tx : NSSpacetime => tx.2 nsCoord1 - b * tx.1) := by
    have hcoord : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2 nsCoord1) := by
      simpa using
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.comp contDiff_snd
    exact hcoord.sub (contDiff_fst.const_smul b)
  have hspace : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.sin (k * (tx.2 nsCoord1 - b * tx.1))) := by
    simpa [smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp (hphase.const_smul k))
  have hscalar : ContDiff ℝ ∞ (fun tx : NSSpacetime =>
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1) *
        Real.sin (k * (tx.2 nsCoord1 - b * tx.1))) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm] using
      ((htime.mul hspace).const_smul a)
  have hosc :
      smoothSpaceTimeVelocity
        (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) := by
    simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, heatShearTransportScalar, mul_assoc] using
      coord0Embedding.contDiff.comp hscalar
  simpa [heatShearTransportVelocityField] using
    hosc.add (smoothSpaceTimeVelocity_constantVelocityField
      (EuclideanSpace.single nsCoord1 b))

/-- Initial velocity data `x ↦ (d + a * sin (k * x₁), b, c)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity
    (a k b d c : ℝ) :
    smoothInitialVelocityData (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  simpa [heatShearTransportFullDriftInitialVelocity] using
    (smoothInitialVelocityData_heatShearTransportInitialVelocity a k b).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c))

/-- The transported full-drift heat-shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) :
    smoothSpaceTimeVelocity (heatShearTransportFullDriftVelocityField ν a k b d c) := by
  simpa [heatShearTransportFullDriftVelocityField] using
    (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c))

end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
