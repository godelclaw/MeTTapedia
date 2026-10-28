import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3LocalOperators
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3VorticityNorms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Heat-Shear Energy Core for Uniform-Vorticity Continuation

This module contains the base heat-shear kinetic-energy density, lateral
scaling, and nonintegrability/finite-energy obstruction for the undrifted
heat-shear field. Drift and transport variants live in sibling modules.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Kinetic-energy density carried by the heat-shear initial profile
`x ↦ (a * sin (k * x₁), 0, 0)`. -/
def heatShearKineticEnergyDensity (a k : ℝ) : NSSpace → ℝ :=
  fun x => (a * Real.sin (k * x nsCoord1)) * (a * Real.sin (k * x nsCoord1))

/-- The heat-shear kinetic-energy density is continuous on `ℝ^3`. -/
theorem continuous_heatShearKineticEnergyDensity
    (a k : ℝ) :
    Continuous (heatShearKineticEnergyDensity a k) := by
  have hcoord : Continuous fun x : NSSpace => x nsCoord1 := by
    simpa using (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).continuous
  have hsin : Continuous fun x : NSSpace => Real.sin (k * x nsCoord1) := by
    change Continuous (Real.sin ∘ fun x : NSSpace => k * x nsCoord1)
    exact Real.continuous_sin.comp (continuous_const.mul hcoord)
  exact (continuous_const.mul hsin).mul (continuous_const.mul hsin)

/-- An anisotropic scaling that expands only the `x₀` and `x₂` directions by
`2`, leaving the heat-shear density unchanged while multiplying Haar measure by
`1 / 4`. -/
def heatShearLateralScaling : NSSpace →ₗ[ℝ] NSSpace :=
  Matrix.toEuclideanLin (Matrix.diagonal ![(2 : ℝ), 1, 2])

/-- The heat-shear lateral scaling fixes the `x₁` coordinate. -/
theorem heatShearLateralScaling_apply_coord1
    (x : NSSpace) :
    heatShearLateralScaling x nsCoord1 = x nsCoord1 := by
  rw [heatShearLateralScaling, Matrix.toLpLin_apply]
  simp [Matrix.mulVec, nsCoord1]

/-- The heat-shear kinetic-energy density is invariant under the lateral
scaling that stretches only `x₀` and `x₂`. -/
theorem heatShearKineticEnergyDensity_comp_heatShearLateralScaling
    (a k : ℝ) :
    (fun x => heatShearKineticEnergyDensity a k (heatShearLateralScaling x)) =
      heatShearKineticEnergyDensity a k := by
  funext x
  simp [heatShearKineticEnergyDensity, heatShearLateralScaling_apply_coord1]

/-- The lateral-scaling determinant is `4`. -/
theorem det_heatShearLateralScaling :
    LinearMap.det heatShearLateralScaling = 4 := by
  rw [heatShearLateralScaling, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_three]
  have h0 : (![2, 1, 2] (0 : Fin 3) : ℝ) = 2 := by rfl
  have h1 : (![2, 1, 2] (1 : Fin 3) : ℝ) = 1 := by rfl
  have h2 : (![2, 1, 2] (2 : Fin 3) : ℝ) = 2 := by rfl
  rw [h0, h1, h2]
  norm_num

/-- Nontrivial heat-shear initial data have nonintegrable kinetic-energy
density on `ℝ^3`.  The proof uses the exact determinant-`4` Haar-scaling
identity coming from stretching only the `x₀` and `x₂` directions. -/
theorem not_integrable_heatShearKineticEnergyDensity
    {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ MeasureTheory.Integrable (heatShearKineticEnergyDensity a k) := by
  intro hInt
  let x1 : NSSpace := EuclideanSpace.single nsCoord1 ((Real.pi / 2) / k)
  have hnonneg : ∀ x, 0 ≤ heatShearKineticEnergyDensity a k x := by
    intro x
    dsimp [heatShearKineticEnergyDensity]
    nlinarith [sq_nonneg (a * Real.sin (k * x nsCoord1))]
  have hx1 : heatShearKineticEnergyDensity a k x1 ≠ 0 := by
    have hx1coord : x1 nsCoord1 = (Real.pi / 2) / k := by
      simp [x1, nsCoord1]
    have hkπ : k * ((Real.pi / 2) / k) = Real.pi / 2 := by
      field_simp [hk]
    have hsin : Real.sin (k * x1 nsCoord1) = 1 := by
      rw [hx1coord, hkπ, Real.sin_pi_div_two]
    dsimp [heatShearKineticEnergyDensity]
    rw [hsin]
    simpa using (mul_ne_zero ha ha)
  have hpos : 0 < ∫ x, heatShearKineticEnergyDensity a k x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x1)
      (continuous_heatShearKineticEnergyDensity a k)
      hInt hnonneg hx1
  let I : ℝ := ∫ x, heatShearKineticEnergyDensity a k x
  have hcomp :
      ∫ x, heatShearKineticEnergyDensity a k (heatShearLateralScaling x) = I := by
    calc
      ∫ x, heatShearKineticEnergyDensity a k (heatShearLateralScaling x)
          = ∫ x, heatShearKineticEnergyDensity a k x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact congrArg (fun f : NSSpace → ℝ => f x)
                (heatShearKineticEnergyDensity_comp_heatShearLateralScaling a k)
      _ = I := by rfl
  have hdet : LinearMap.det heatShearLateralScaling ≠ 0 := by
    rw [det_heatShearLateralScaling]
    norm_num
  have hmap :
      MeasureTheory.Measure.map heatShearLateralScaling
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) =
        ENNReal.ofReal ((4 : ℝ)⁻¹) •
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace)) (f := heatShearLateralScaling)
      hdet]
    simp [det_heatShearLateralScaling]
  have hchange :
      ∫ x, heatShearKineticEnergyDensity a k (heatShearLateralScaling x) =
        ((4 : ℝ)⁻¹) * I := by
    calc
      ∫ x : NSSpace, heatShearKineticEnergyDensity a k (heatShearLateralScaling x)
          = ∫ y : NSSpace, heatShearKineticEnergyDensity a k y ∂
              MeasureTheory.Measure.map heatShearLateralScaling
                (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
              symm
              exact MeasureTheory.integral_map
                (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
                (heatShearLateralScaling.continuous_of_finiteDimensional.aemeasurable)
                ((continuous_heatShearKineticEnergyDensity a k).aestronglyMeasurable)
      _ = ((4 : ℝ)⁻¹) * I := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [I]
  have hEq : I = ((4 : ℝ)⁻¹) * I := by
    simpa [hcomp] using hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  linarith

/-- The initial kinetic-energy density of the heat-shear datum is the explicit
oscillatory density `(a * sin (k * x₁))²`. -/
theorem initialKineticEnergyDensity_heatShearInitialVelocity
    (a k : ℝ) :
    initialKineticEnergyDensity (heatShearInitialVelocity a k) =
      heatShearKineticEnergyDensity a k := by
  funext x
  have hs :
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
        heatShearKineticEnergyDensity a k x := by
    rw [heatShearKineticEnergyDensity]
    calc
      (|a| * |Real.sin (k * x.ofLp 1)|) ^ (2 : ℕ) =
          |a * Real.sin (k * x.ofLp 1)| ^ (2 : ℕ) := by
            rw [abs_mul]
      _ = a * Real.sin (k * x.ofLp 1) * (a * Real.sin (k * x.ofLp 1)) := by
            simpa [pow_two] using (sq_abs (a * Real.sin (k * x.ofLp 1)))
  rw [initialKineticEnergyDensity, heatShearInitialVelocity_apply]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [nsCoord0, nsCoord1, hs]

/-- On each time slice, the damped heat-shear field carries the same
oscillatory kinetic-energy density with the amplitude rescaled by the heat
factor `exp (-(ν * k²) * t)`. -/
theorem kineticEnergyDensity_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) :
    kineticEnergyDensity (heatShearVelocityField ν a k) t =
      heatShearKineticEnergyDensity
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  calc
    kineticEnergyDensity (heatShearVelocityField ν a k) t =
      initialKineticEnergyDensity (heatShearInitialVelocity A k) := by
        funext x
        simp [kineticEnergyDensity, initialKineticEnergyDensity, A,
          heatShearVelocityField_apply, heatShearInitialVelocity_apply]
    _ = heatShearKineticEnergyDensity A k :=
      initialKineticEnergyDensity_heatShearInitialVelocity A k
    _ = heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k := by
        simp [A]

/-- A nontrivial damped heat-shear field is not spatially integrable on `ℝ^3`
with respect to the kinetic-energy density on any time slice. -/
theorem not_integrable_kineticEnergyDensity_heatShearVelocityField
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (heatShearVelocityField ν a k) t) := by
  intro hInt
  have hA :
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≠ 0 := by
    exact mul_ne_zero ha (Real.exp_ne_zero _)
  have hIntHeat :
      MeasureTheory.Integrable
        (heatShearKineticEnergyDensity
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)) k) := by
    simpa [kineticEnergyDensity_heatShearVelocityField ν a k t] using hInt
  exact not_integrable_heatShearKineticEnergyDensity hA hk hIntHeat

/-- Therefore a nontrivial damped heat-shear field never satisfies the
concrete global bounded-energy predicate on `ℝ^3`. -/
theorem not_boundedKineticEnergy_heatShearVelocityField
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ boundedKineticEnergy (heatShearVelocityField ν a k) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVelocityField
      (ν := ν) (a := a) (k := k) ha hk 0 (hbound 0).1

/-- On every nonnegative slab, a nontrivial damped heat-shear field also fails
the finite-time bounded-energy predicate. -/
theorem not_boundedKineticEnergyUpTo_heatShearVelocityField
    {ν a k T : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVelocityField ν a k) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact
    not_integrable_kineticEnergyDensity_heatShearVelocityField
      (ν := ν) (a := a) (k := k) ha hk 0 ((hbound 0 le_rfl hT).1)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
