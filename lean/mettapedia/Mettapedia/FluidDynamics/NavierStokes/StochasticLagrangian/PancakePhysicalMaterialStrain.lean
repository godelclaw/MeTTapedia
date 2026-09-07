import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialFlow

/-!
# Material strain evolution constructed from physical initial data

One local solution and one material flow are produced from the initial
field. Every trajectory obeys the ordinary strain equation of that same
solution, with no independent material-evolution hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalMaterialStrain

open scoped ComplexConjugate NNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeLocalMaterialFlow PancakeLocalMaterialStrain PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeHigherLocalVelocity PancakeContinuousCoordinateJet
open PancakeArbitraryDataBlocks PancakeLocalGradientEquation PancakeLocalStrainEquation
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem exists_physical_material_strain (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
      ∃ Φ : X3 → ℝ → X3,
        ⇑(spatialField s 0) = f ∧
        (∀ x, Φ x 0 = x) ∧
        (∀ x t, t ∈ Set.Icc (0 : ℝ) T →
          HasDerivWithinAt (Φ x) (liftedVelocity s t (Φ x t)) (Set.Icc (0 : ℝ) T) t) ∧
        (∃ L : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith L (fun x ↦ Φ x t)) ∧
        ∀ x t, t ∈ Set.Ioo (0 : ℝ) T →
          HasDerivAt (fun τ ↦ spatialStrain (spatialField s τ) (torusPoint (Φ x τ)))
            (-(spatialStrain (spatialField s t) (torusPoint (Φ x t)) *
                  spatialStrain (spatialField s t) (torusPoint (Φ x t)) +
                spatialSpin (spatialField s t) (torusPoint (Φ x t)) *
                  spatialSpin (spatialField s t) (torusPoint (Φ x t))) -
              spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (Φ x t)) +
              (nu : ℂ) • matrixLaplacian (spatialStrain (spatialField s t)) (torusPoint (Φ x t))) t := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hd hzero
  have hu1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu τ hτ q)
  obtain ⟨Φ, h0, hΦ, L, hL⟩ := exists_materialFlow s g hg hSum hu1 hT.le
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)
  refine ⟨T, hT, B, hB, s, Φ, spatialField_initial hT.le f hc s, h0, hΦ, ⟨L, hL⟩, ?_⟩
  intro x t ht
  exact strain_material s g hg hSum hu (Φ x) (fun τ hτ ↦
    (hΦ x τ ⟨hτ.1.le, hτ.2.le⟩).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)) t ht

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalMaterialStrain
