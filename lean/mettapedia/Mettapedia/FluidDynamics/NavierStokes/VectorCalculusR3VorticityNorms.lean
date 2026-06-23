import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity

/-!
# Vector Calculus R3: VorticityNorms

Pointwise vorticity norm formulas and envelope bounds for concrete shear families.
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

/-- The steady linear shear field has vorticity norm exactly `|a|`. -/
theorem norm_spatialVorticity_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (linearShearVelocityField a) t x‖ = |a| := by
  rw [spatialVorticity_linearShearVelocityField]
  simp [EuclideanSpace.norm_single]

/-- Adding constant drifts to steady linear shear does not change the vorticity
norm. -/
theorem norm_spatialVorticity_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (linearShearFullDriftVelocityField a b c) t x‖ = |a| := by
  rw [spatialVorticity_linearShearFullDriftVelocityField]
  simp [EuclideanSpace.norm_single]

/-- Exact pointwise vorticity norm for the damped sinusoidal heat-shear field. -/
theorem norm_spatialVorticity_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearVelocityField ν a k) t x‖ =
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        |Real.cos (k * x nsCoord1)| * |k| := by
  rw [spatialVorticity_heatShearVelocityField]
  simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]

/-- The heat-shear vorticity norm is bounded by its damped amplitude envelope,
uniformly in the oscillatory phase. -/
theorem norm_spatialVorticity_heatShearVelocityField_le_exp_abs
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearVelocityField ν a k) t x‖ ≤
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
  rw [norm_spatialVorticity_heatShearVelocityField]
  calc
    |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          |Real.cos (k * x nsCoord1)| * |k|
        ≤ |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * 1 * |k| := by
          gcongr
          simpa using Real.abs_cos_le_one (k * x nsCoord1)
    _ = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
          ring

/-- Exact pointwise vorticity norm for transported heat shear.  The transport
speed only shifts the phase. -/
theorem norm_spatialVorticity_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportVelocityField ν a k b) t x‖ =
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
  rw [spatialVorticity_heatShearTransportVelocityField]
  simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]

/-- Transported heat-shear vorticity has the same damped amplitude envelope as
the untransported heat-shear field. -/
theorem norm_spatialVorticity_heatShearTransportVelocityField_le_exp_abs
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportVelocityField ν a k b) t x‖ ≤
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
  rw [norm_spatialVorticity_heatShearTransportVelocityField]
  calc
    |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          |Real.cos (k * (x nsCoord1 - b * t))| * |k|
        ≤ |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * 1 * |k| := by
          gcongr
          simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
    _ = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
          ring

/-- Exact pointwise vorticity norm for transported full-drift heat shear. -/
theorem norm_spatialVorticity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportFullDriftVelocityField ν a k b d c) t x‖ =
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
  rw [spatialVorticity_heatShearTransportFullDriftVelocityField]
  simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]

/-- Full-drift transported heat shear has the same damped vorticity envelope as
the drift-free transported branch. -/
theorem norm_spatialVorticity_heatShearTransportFullDriftVelocityField_le_exp_abs
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportFullDriftVelocityField ν a k b d c) t x‖ ≤
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
  rw [norm_spatialVorticity_heatShearTransportFullDriftVelocityField]
  calc
    |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          |Real.cos (k * (x nsCoord1 - b * t))| * |k|
        ≤ |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * 1 * |k| := by
          gcongr
          simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
    _ = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
          ring
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
