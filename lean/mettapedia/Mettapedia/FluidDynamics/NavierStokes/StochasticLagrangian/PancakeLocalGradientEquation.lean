import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialViscousDifferentiation

/-!
# The ordinary Eulerian velocity-gradient equation

The equation is obtained by differentiating the same constructed local
momentum equation. Advection, pressure, and viscosity remain actual
spatial derivatives, and the quadratic gradient term retains its sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalGradientEquation

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeInfiniteFourierDerivative
open PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian PancakeInfiniteSpatialPressure
open PancakeInfinitePressureHessian PancakeCoefficientLimitEquation PancakeLocalPressureEquation
open PancakeSpatialGradientDifferentiation PancakeSpatialViscousDifferentiation
open PancakeVelocityGradientEnvelope PancakeLocalVelocityGradientTime
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity
open PancakeHigherLocalVelocity PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet

local notation "T3" => UnitAddTorus (Fin 3)

theorem coordinateDerivative_velocityRHS_eq (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (j : Fin 3) (x : T3) :
    coordinateDerivative (fullFourierField id (infiniteVelocityRHS nu u)) j x =
      -spatialTransport (fullFourierField id u)
          (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x -
        gradientProduct (fullFourierField id u) j x -
        (fun i ↦ spatialHessian (spatialPressure u) x i j) +
        (nu : ℂ) • spatialLaplacian
          (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hr := hasDerivAt_fullFourierField_shift_zero (infiniteVelocityRHS nu u)
    (summable_firstMoment_velocityRHS nu u hu) j x
  have hp := ((hasDerivAt_spatialAdvection_shift u hu2 j x).neg.sub
    (hasDerivAt_spatialGradient_pressure_shift u hu2 j x)).add
      ((hasDerivAt_spatialLaplacian_shift u hu j x).const_smul (nu : ℂ))
  simp_rw [fullVelocityRHS_eq_spatial_pressure nu u hu2 hd] at hr
  have he := hr.unique hp
  rw [he]
  abel

theorem spatialField_gradient_equation {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients τ) k ≤ g k)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ coordinateDerivative (spatialField s τ) j x)
      (-spatialTransport (spatialField s t) (fun y ↦ coordinateDerivative (spatialField s t) j y) x -
        gradientProduct (spatialField s t) j x -
        (fun i ↦ spatialHessian (spatialPressure (s.coefficients t)) x i j) +
        (nu : ℂ) • spatialLaplacian (fun y ↦ coordinateDerivative (spatialField s t) j y) x) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have h := spatialField_gradient_time_space s g hg hSum hu j t ht x
  rwa [coordinateDerivative_velocityRHS_eq nu _ hm (s.transverse t) j x] at h

/-- The matrix is built from ordinary coordinate derivatives of the velocity. -/
def spatialVelocityGradient (u : T3 → VelocityCoefficient) (x : T3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ coordinateDerivative u j x i

/-- Transport of a matrix field, using ordinary derivatives of each column. -/
def matrixTransport (u : T3 → VelocityCoefficient)
    (a : T3 → Matrix (Fin 3) (Fin 3) ℂ) (x : T3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ spatialTransport u (fun y m ↦ a y m j) x i

def matrixLaplacian (a : T3 → Matrix (Fin 3) (Fin 3) ℂ) (x : T3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ spatialLaplacian (fun y m ↦ a y m j) x i

theorem gradientProduct_eq_matrixSquare (u : T3 → VelocityCoefficient)
    (x : T3) (i j : Fin 3) :
    gradientProduct u j x i = (spatialVelocityGradient u x * spatialVelocityGradient u x) i j := by
  simp only [gradientProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mul_apply, spatialVelocityGradient]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem spatialField_velocityGradient_equation {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients τ) k ≤ g k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ spatialVelocityGradient (spatialField s τ) x)
      (-matrixTransport (spatialField s t) (spatialVelocityGradient (spatialField s t)) x -
        spatialVelocityGradient (spatialField s t) x * spatialVelocityGradient (spatialField s t) x -
        spatialHessian (spatialPressure (s.coefficients t)) x +
        (nu : ℂ) • matrixLaplacian (spatialVelocityGradient (spatialField s t)) x) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := (hasDerivAt_pi.mp (spatialField_gradient_equation s g hg hSum hu j t ht x)) i
  simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    spatialVelocityGradient, matrixTransport, matrixLaplacian, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, gradientProduct_eq_matrixSquare] using h

theorem exists_physical_local_gradient_equation (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        ⇑(spatialField s 0) = f ∧
        ∀ t, t ∈ Set.Ioo (0 : ℝ) T → ∀ x,
          HasDerivAt (fun τ ↦ spatialVelocityGradient (spatialField s τ) x)
            (-matrixTransport (spatialField s t) (spatialVelocityGradient (spatialField s t)) x -
              spatialVelocityGradient (spatialField s t) x * spatialVelocityGradient (spatialField s t) x -
              spatialHessian (spatialPressure (s.coefficients t)) x +
              (nu : ℂ) • matrixLaplacian (spatialVelocityGradient (spatialField s t)) x) t := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hd hzero
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)
  exact ⟨T, hT, B, hB, s, spatialField_initial hT.le f hc s,
    spatialField_velocityGradient_equation s g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalGradientEquation
