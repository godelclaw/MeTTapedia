import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialGradientRegularity

/-!
# The actual local strain equation with its signed quadratic source

Symmetrizing the constructed velocity-gradient equation cancels the
strain-spin cross terms. Transport and diffusion act on the actual strain,
and pressure is the Hessian constructed from the same velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalStrainEquation

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeLocalGradientEquation PancakeMatrixDifferentialSymmetry PancakeSpatialGradientRegularity
open PancakeFilteredStrainDynamics PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeHigherLocalVelocity
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet

local notation "T3" => UnitAddTorus (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

def skewSymmetrize (a : M3) : M3 := (1 / 2 : ℂ) • (a - a.transpose)

def spatialStrain (u : T3 → VelocityCoefficient) (x : T3) : M3 :=
  symmetrize (spatialVelocityGradient u x)

def spatialSpin (u : T3 → VelocityCoefficient) (x : T3) : M3 :=
  skewSymmetrize (spatialVelocityGradient u x)

theorem symmetrize_square (a : M3) :
    symmetrize (a * a) = symmetrize a * symmetrize a + skewSymmetrize a * skewSymmetrize a := by
  change (1 / 2 : ℂ) • (a * a + (a * a).transpose) =
    ((1 / 2 : ℂ) • (a + a.transpose)) * ((1 / 2 : ℂ) • (a + a.transpose)) +
      ((1 / 2 : ℂ) • (a - a.transpose)) * ((1 / 2 : ℂ) • (a - a.transpose))
  rw [Matrix.transpose_mul]
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem spatialStrain_symmetric (u : T3 → VelocityCoefficient) (x : T3) :
    (spatialStrain u x).transpose = spatialStrain u x := by
  ext i j
  change (1 / 2 : ℂ) * (spatialVelocityGradient u x j i + spatialVelocityGradient u x i j) =
    (1 / 2 : ℂ) * (spatialVelocityGradient u x i j + spatialVelocityGradient u x j i)
  ring

theorem spatialSpin_skew (u : T3 → VelocityCoefficient) (x : T3) :
    (spatialSpin u x).transpose = -spatialSpin u x := by
  ext i j
  change (1 / 2 : ℂ) * (spatialVelocityGradient u x j i - spatialVelocityGradient u x i j) =
    -((1 / 2 : ℂ) * (spatialVelocityGradient u x i j - spatialVelocityGradient u x j i))
  ring

theorem spatialField_strain_equation {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients τ) k ≤ g k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ spatialStrain (spatialField s τ) x)
      (-matrixTransport (spatialField s t) (spatialStrain (spatialField s t)) x -
        (spatialStrain (spatialField s t) x * spatialStrain (spatialField s t) x +
          spatialSpin (spatialField s t) x * spatialSpin (spatialField s t) x) -
        spatialHessian (spatialPressure (s.coefficients t)) x +
        (nu : ℂ) • matrixLaplacian (spatialStrain (spatialField s t)) x) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have hm2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hm
  have ha (y : T3) (m : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ spatialVelocityGradient (spatialField s t) (y + PancakeFourierTranslationCurve.coordinateShift m h)) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_velocityGradient_shift _ hm2 m y)
  have hda (y : T3) (m n : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ matrixCoordinateDerivative (spatialVelocityGradient (spatialField s t)) m
        (y + PancakeFourierTranslationCurve.coordinateShift n h)) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_matrixDerivative_gradient_shift _ hm m n y)
  have hp : symmetrize (spatialHessian (spatialPressure (s.coefficients t)) x) =
      spatialHessian (spatialPressure (s.coefficients t)) x := by
    change (1 / 2 : ℂ) • (_ + (spatialHessian (spatialPressure (s.coefficients t)) x).transpose) = _
    rw [spatialHessian_pressure_symmetric _ hm2 x]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have h := hasDerivAt_symmetrize _ _ t
    (spatialField_velocityGradient_equation s g hg hSum hu t ht x)
  simp only [map_add, map_sub, map_neg, map_smul, symmetrize_square, hp,
    ← matrixTransport_symmetrize _ _ x (ha x), ← matrixLaplacian_symmetrize _ ha hda x] at h
  exact h

theorem exists_physical_local_strain_equation (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        ⇑(spatialField s 0) = f ∧
        ∀ t, t ∈ Set.Ioo (0 : ℝ) T → ∀ x,
          HasDerivAt (fun τ ↦ spatialStrain (spatialField s τ) x)
            (-matrixTransport (spatialField s t) (spatialStrain (spatialField s t)) x -
              (spatialStrain (spatialField s t) x * spatialStrain (spatialField s t) x +
                spatialSpin (spatialField s t) x * spatialSpin (spatialField s t) x) -
              spatialHessian (spatialPressure (s.coefficients t)) x +
              (nu : ℂ) • matrixLaplacian (spatialStrain (spatialField s t)) x) t := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hd hzero
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)
  exact ⟨T, hT, B, hB, s, spatialField_initial hT.le f hc s,
    spatialField_strain_equation s g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalStrainEquation
