import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticCorrectedEnergy

/-!
# Initial-endpoint balance for the corrected eighth moment

Continuity of the actual fields extends the interior estimate to time zero.
The common Fourier envelope is a local regularity hypothesis, not a uniform
bound at a maximal existence time. The signed residual is still unpaid.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalOcticEndpointBalance

open MeasureTheory Set Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget LocalOcticDiffusion LocalOcticMeanBalance
open UnitTorusProductTransport LocalOcticCorrectedEnergy
open LocalVorticityEighthMoment (meanEnergy weightedPalinstrophy)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

private theorem continuousOn_productMean (f : ℝ → T6 → ℝ)
    (hf : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ f z.1 z.2)) :
    ContinuousOn (fun t ↦ ∫ x : T6, f t x) (Icc 0 T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun t : Icc (0 : ℝ) T ↦ ∫ x : T6, f t x)
  have hi := continuous_parametric_integral_of_continuous (μ := (volume : Measure T6))
    (f := fun t : Icc (0 : ℝ) T ↦ f t) hf isCompact_univ
  simpa only [Measure.restrict_univ] using hi

include hSum hu in
theorem continuous_velocity_spaceTime :
    Continuous (fun z : Icc (0 : ℝ) T × T3 ↦ LocalMeanAlignmentBalance.velocity (s.coefficients z.1) z.2) := by
  have hc : Continuous (fun t : Icc (0 : ℝ) T ↦ fullFourierField id (s.coefficients t)) := by
    refine LocalVorticityDiffusion.continuous_fullFourierField_of_norm_le _
      (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) g hSum ?_
    intro t q
    calc
      _ ≤ fourierMoment 0 (s.coefficients t) q := by
        simpa only [fourierMoment, pow_zero, one_mul] using
          PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean (s.coefficients t q)
      _ ≤ g q := (fourierMoment_mono _ (by omega : 0 ≤ 3) q).trans (hu t t.2 q)
  exact PancakeDyadicDirectionEvolution.complexRealPartEuclideanCLM.continuous.comp
    (continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd))

include hSum hu in
theorem continuousOn_correlation (N : ℕ) :
    ContinuousOn (fun t ↦ LocalOcticCorrelation.correlation N (s.coefficients t)) (Icc 0 T) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hx := hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2))
    (continuous_fst.prodMk (continuous_leftPoint.comp continuous_snd))
  have hy := hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2))
    (continuous_fst.prodMk (continuous_rightPoint.comp continuous_snd))
  have hk : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ PeriodicRadialRiesz.tensor N
      (leftPoint z.2 - rightPoint z.2)) := (PeriodicRadialRiesz.continuous_tensor N).comp
    ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))
  have hd := OcticKernelCorrelation.continuous_density hk hx hy
  have hi := continuousOn_productMean (fun t ↦ LocalOcticMeanBalance.density N (s.coefficients t)) hd
  apply hi.congr
  intro t ht
  exact (integral_density_eq N _ (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)))).symm

include hSum hu in
set_option synthInstance.maxHeartbeats 80000 in
theorem continuousOn_nonviscousMeanRate (N : ℕ) :
    ContinuousOn (fun t ↦ meanRate N 0 (s.coefficients t)) (Icc 0 T) := by
  have hu2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu2
  have hS := LocalAlignmentContinuity.continuous_fullStrainOperator_parametric
    (fun t : Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) g hSum (fun t ↦ hu2 t t.2)
  have hv := continuous_velocity_spaceTime s g hSum hu
  have hl : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) :=
    continuous_fst.prodMk (continuous_leftPoint.comp continuous_snd)
  have hr : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) :=
    continuous_fst.prodMk (continuous_rightPoint.comp continuous_snd)
  have hx := hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl
  have hy := hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr
  have hdx := (hS.clm_apply hw).comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl
  have hdy := (hS.clm_apply hw).comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr
  have hvel := (hv.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl).sub
    (hv.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr)
  have hsep : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ leftPoint z.2 - rightPoint z.2) :=
    (continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd)
  have hK := (PeriodicRadialRiesz.continuous_tensor (d := 3) N).comp hsep
  have hD0 : Continuous (UnitTorusPeriodization.periodize
      (RadialRieszRegularization.tensorDerivative (d := 3) N) : T3 → R3 →L[ℝ] R3 →L[ℝ] R3) :=
    UnitTorusSchwartzLattice.continuous_periodize _
  have hD := (hD0.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ leftPoint z.2 - rightPoint z.2) hsep).clm_apply hvel
  have hc := (OcticKernelCorrelation.continuous_endpointRate hK hx hy hdx hdy).add
    (OcticKernelCorrelation.continuous_density hD hx hy)
  apply continuousOn_productMean (fun t ↦ explicitRate N 0 (s.coefficients t))
  dsimp only [Pi.add_def, Function.comp_def] at hc
  simpa only [explicitRate, LocalOcticCorrelation.fieldRate, OcticKernelCorrelation.materialRate,
    zero_smul, add_zero, Pi.add_apply, Function.comp_def] using hc

include hSum hu in
theorem continuousOn_pureContribution (N : ℕ) :
    ContinuousOn (fun t ↦ pureContribution N (s.coefficients t)) (Icc 0 T) := by
  let f (t : ℝ) (x : T6) := pureDensity (PeriodicRadialRiesz.tensor N) (s.coefficients t)
    (leftPoint x) (rightPoint x)
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hl : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) :=
    continuous_fst.prodMk (continuous_leftPoint.comp continuous_snd)
  have hr : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) :=
    continuous_fst.prodMk (continuous_rightPoint.comp continuous_snd)
  have hx := hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl
  have hy := hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr
  have hgl (j : Fin 3) := (LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum hu j).comp
    (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl
  have hgr (j : Fin 3) := (LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum hu j).comp
    (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr
  have hk : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ PeriodicRadialRiesz.tensor N
      (leftPoint z.2 - rightPoint z.2)) := (PeriodicRadialRiesz.continuous_tensor N).comp
    ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))
  have hc : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ f z.1 z.2) := by
    change Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ ∑ j : Fin 3,
      OcticKernelCorrelation.pureCurvature (PeriodicRadialRiesz.tensor N (leftPoint z.2 - rightPoint z.2))
        (fullVorticity (s.coefficients z.1) (leftPoint z.2))
        (fullVorticity (s.coefficients z.1) (rightPoint z.2))
        (LocalSpatialVorticityJets.fullCurlGradient (s.coefficients z.1) j (leftPoint z.2))
        (LocalSpatialVorticityJets.fullCurlGradient (s.coefficients z.1) j (rightPoint z.2)))
    apply continuous_finsetSum
    intro j _
    exact OcticKernelCorrelation.continuous_pureCurvature hk hx hy (hgl j) (hgr j)
  apply (continuousOn_productMean f hc).congr
  intro t ht
  have hm := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht))
  exact (UnitTorusProductTransport.integral_pair _
    ((continuous_pureDensity _ (PeriodicRadialRiesz.continuous_tensor N) _ hm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm

include hSum hu in
theorem continuousOn_energy (N : ℕ) (ε : ℝ) :
    ContinuousOn (fun t ↦ energy N ε (s.coefficients t)) (Icc 0 T) :=
  ((LocalVorticityEighthMoment.continuousOn_meanEnergy s g hSum hu).div_const 8).add
    ((continuousOn_correlation s g hSum hu N).const_mul ε)

include hSum hu in
theorem continuousOn_residual (N : ℕ) (ε : ℝ) :
    ContinuousOn (fun t ↦ residual N nu ε (s.coefficients t)) (Icc 0 T) :=
  (LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu).add
    (((continuousOn_nonviscousMeanRate s g hSum hu N).sub
      ((continuousOn_pureContribution s g hSum hu N).const_mul nu)).const_mul ε)

include hg hSum hu in
/-- An initial-endpoint estimate with the actual signed residual, not a budget assumption. -/
theorem energy_add_half_dissipation_le (N : ℕ) (ε : ℝ) (hnu : 0 ≤ nu) (hε : |ε| ≤ 1 / 576)
    (hT : 0 < T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    energy N ε (s.coefficients t) + nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤
      energy N ε u₀ + ∫ τ in (0 : ℝ)..t, residual N nu ε (s.coefficients τ) := by
  have h := intervalIntegral.endpoint_estimate_of_interior (C := 0) hT
    (continuousOn_energy s g hSum hu N ε)
    ((LocalVorticityEighthMoment.continuousOn_weightedPalinstrophy s g hSum hu).const_mul (nu / 2))
    (continuousOn_residual s g hSum hu N ε)
    (fun a b ha hab hb ↦ by
      simpa only [intervalIntegral.integral_const_mul, add_zero] using
        LocalOcticCorrectedEnergy.energy_add_half_dissipation_le s g hg hSum hu a b hab.le
          (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩) N ε hnu hε) t ht
  simpa only [intervalIntegral.integral_const_mul, add_zero, s.initial] using h

include hg hSum hu in
theorem meanEnergy_add_half_dissipation_le (N : ℕ) (ε : ℝ) (hnu : 0 ≤ nu) (hε : |ε| ≤ 1 / 576)
    (hT : 0 < T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 16 +
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤
      3 * meanEnergy u₀ / 16 + ∫ τ in (0 : ℝ)..t, residual N nu ε (s.coefficients τ) := by
  have hsmall : |ε| ≤ 1 / 144 := hε.trans (by norm_num)
  have hm (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients τ)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ))
  have hlo := (energy_bounds N ε (s.coefficients t) (hm t ht) hsmall).1
  have hhi := (energy_bounds N ε (s.coefficients 0) (hm 0 ⟨le_rfl, hT.le⟩) hsmall).2
  rw [s.initial] at hhi
  have he := energy_add_half_dissipation_le s g hg hSum hu N ε hnu hε hT t ht
  linarith only [hlo, hhi, he]

/-- Admissible periodic data construct the local solution and its corrected estimate.
The residual is the explicit expression above; no bound for it is a field of the witness. -/
theorem exists_physical_local_corrected_estimate (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, star (f x i) = f x i)
    (hd : ∀ q, modeDot q (PancakeArbitraryDataBlocks.torusFourierVelocity f q) = 0)
    (hzero : PancakeArbitraryDataBlocks.torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (PancakeArbitraryDataBlocks.torusFourierVelocity f) T B,
        ∀ N : ℕ, ∀ ε : ℝ, |ε| ≤ 1 / 576 → ∀ t ∈ Icc (0 : ℝ) T,
          meanEnergy (s.coefficients t) / 16 +
            nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤
          3 * meanEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f) / 16 +
            ∫ τ in (0 : ℝ)..t, residual N nu ε (s.coefficients τ) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 3 nu hnu f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun N ε hε t ht ↦
    meanEnergy_add_half_dissipation_le s g hg hSum hu N ε hnu.le hε hT t ht⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalOcticEndpointBalance
