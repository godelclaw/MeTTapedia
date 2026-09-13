import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVelocityGradientEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransportBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularInviscidWork

/-!
# Transport deformation absorbed using initial kinetic energy

For a fixed finite output filter, the normalization may be chosen before
the solution time from its derivative cutoff weight, viscosity and initial
kinetic energy. This pays the angular transport commutator without assuming
a global velocity-gradient bound. Strain work and the full subgrid pairing
remain signed and unestimated. The normalization is not cutoff-uniform.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AngularTransportAbsorption

open scoped ComplexConjugate
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open PancakeFilteredStrainDynamics PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open LocalVorticityEighthMoment InfiniteConvectionEnergy LocalKineticEnergy
open FiniteVelocityGradientEnergy FiniteAngularTransport FiniteAngularInviscidWork
open FilteredAngularSourceBalance FiniteBandAngularEnergy

/-- Both normalization requirements can be met using only the fixed filter,
initial energy and positive viscosity, before selecting the solution time. -/
theorem exists_normalization (L R ν E : ℝ) (hν : 0 < ν)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) :
    ∃ κ : ℝ, 0 < κ ∧ L * (2 * Real.pi * R) ^ 2 ≤ κ ∧
      432 * Real.sqrt (derivativeCutoffWeight P χ * E) ≤ ν * κ := by
  let A := max 0 (L * (2 * Real.pi * R) ^ 2)
  let M := Real.sqrt (derivativeCutoffWeight P χ * E)
  have hA : 0 ≤ A := le_max_left _ _
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hd : 0 ≤ 432 * M / ν := by positivity
  refine ⟨1 + A + 432 * M / ν, by positivity, ?_, ?_⟩
  · have h := le_max_right 0 (L * (2 * Real.pi * R) ^ 2)
    change L * (2 * Real.pi * R) ^ 2 ≤ A at h
    linarith only [h, hd]
  · have h : 432 * M / ν ≤ 1 + A + 432 * M / ν := by linarith only [hA]
    have hh := (div_le_iff₀ hν).mp h
    nlinarith only [hh]

theorem deformation_le_dissipation (ν κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hpay : 432 * M ≤ ν * κ) (P : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) (hB : ∀ x j k, |velocityDerivative u j k x| ≤ M) :
    (3 / κ) * deformationIntegral u u ≤ (ν / 4) * weightedPalinstrophy u := by
  have hc : 108 * M / κ ≤ ν / 4 := (div_le_iff₀ hκ).2 (by nlinarith only [hpay])
  calc
    _ ≤ (3 / κ) * |deformationIntegral u u| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ (3 / κ) * (36 * M * (weightedPalinstrophy u - radialDissipation u)) :=
      mul_le_mul_of_nonneg_left (abs_deformationIntegral_le P u u hu M hM hB) (by positivity)
    _ = (108 * M / κ) * (weightedPalinstrophy u - radialDissipation u) := by ring
    _ ≤ (108 * M / κ) * weightedPalinstrophy u :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (radialDissipation_nonneg u)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (weightedPalinstrophy_nonneg u)

theorem deformation_le_of_kineticEnergy (ν κ : ℝ) (hκ : 0 < κ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hχ : ∀ q, q ∉ P → χ q = 0)
    (u : FourierVelocity) (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2))
    (E : ℝ) (hE : kineticEnergy u ≤ E)
    (hpay : 432 * Real.sqrt (derivativeCutoffWeight P χ * E) ≤ ν * κ) :
    (3 / κ) * deformationIntegral (filteredVelocity χ u) (filteredVelocity χ u) ≤
      (ν / 4) * weightedPalinstrophy (filteredVelocity χ u) := by
  apply deformation_le_dissipation ν κ _ hκ (Real.sqrt_nonneg _) hpay P _
    (fun q hq ↦ by simp [filteredVelocity, hχ q hq])
  exact fun x j k ↦ abs_velocityDerivative_le_sqrt_energy P χ hχ u hu E hE j k x

/-- The common moment envelope justifies the energy identity; the payment
constant itself contains neither that envelope nor the local Sobolev bound. -/
theorem deformation_solution_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 ≤ ν)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (κ : ℝ) (hκ : 0 < κ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hχ : ∀ q, q ∉ P → χ q = 0)
    (hpay : 432 * Real.sqrt (derivativeCutoffWeight P χ * kineticEnergy u₀) ≤ ν * κ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (3 / κ) * deformationIntegral (filteredVelocity χ (s.coefficients t))
      (filteredVelocity χ (s.coefficients t)) ≤
        (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) :=
  deformation_le_of_kineticEnergy ν κ hκ P χ hχ _ (local_kineticEnergy s t ht).1
    _ (energy_le_initial s hν g hg hSum hu t ht) hpay

/-- A physical mean-zero local solution supplies the moment envelope used
above. The final statement has no assumed gradient or dissipation budget. -/
theorem exists_physical_local_transport_absorption (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (PancakeArbitraryDataBlocks.torusFourierVelocity f q) = 0)
    (hzero : PancakeArbitraryDataBlocks.torusFourierVelocity f 0 = 0)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hχ : ∀ q, q ∉ P → χ q = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (PancakeArbitraryDataBlocks.torusFourierVelocity f) T B,
        ∀ κ : ℝ, 0 < κ →
          432 * Real.sqrt (derivativeCutoffWeight P χ *
            kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f)) ≤ ν * κ →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            (3 / κ) * deformationIntegral (filteredVelocity χ (s.coefficients t))
              (filteredVelocity χ (s.coefficients t)) ≤
                (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun κ hκ hpay t ht ↦
    deformation_solution_le s hν.le g hg hSum hu κ hκ P χ hχ hpay t ht⟩

theorem exists_coercive_strain_subgrid_threshold :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (g : Wavevector → ℝ), (∀ q, 0 ≤ g q) → Summable g →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) →
      ∀ (κ : ℝ), 0 < κ → ∀ (P : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      (∀ q, χ (-q) = conj (χ q)) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → L * (2 * Real.pi * R) ^ 2 ≤ κ →
      432 * Real.sqrt (derivativeCutoffWeight P χ * kineticEnergy u₀) ≤ ν * κ →
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (meanEnergy (filteredVelocity χ (s.coefficients t)) / 16 ≤
          correctedEnergy κ (filteredVelocity χ (s.coefficients t)) ∧
        correctedEnergy κ (filteredVelocity χ (s.coefficients t)) ≤
          meanEnergy (filteredVelocity χ (s.coefficients t)) / 8) ∧
      deriv (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ))) t +
          (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
          6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
        stretching (filteredVelocity χ (s.coefficients t)) -
          (3 / κ) * angularStrainWork (filteredVelocity χ (s.coefficients t)) +
            fullSubgridWork κ χ (s.coefficients t) := by
  obtain ⟨L, hL, hbound⟩ := exists_coercive_source_threshold
  refine ⟨L, hL, ?_⟩
  intro ν T B u₀ s hν hB g hg hSum hu κ hκ P χ hcut C hχ hχr R hP hscale hpay t ht
  have h := hbound s hν hB κ hκ P χ hcut C hχ R hP hscale t ht
  have hd := deformation_solution_le s hν g hg hSum hu κ hκ P χ hcut hpay t (Set.Ioo_subset_Icc_self ht)
  rw [sourceWork_solution_eq s κ P χ hcut C hχ hχr t (Set.Ioo_subset_Icc_self ht)] at h
  exact ⟨h.1, by linarith only [h.2, hd]⟩

end Mettapedia.FluidDynamics.NavierStokes.AngularTransportAbsorption
