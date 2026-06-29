import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMHighNormContinuation

/-!
# Regression checks for the BKM high-norm continuation assembly
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

theorem BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope_regression
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope) :
    BKMLogSobolevGradientControlFromEnvelope := by
  exact BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope hAffine

theorem BKMLogSobolevAffinePointwiseFromEnvelope_of_schwartzHighNormEnvelope_and_biotSavart_regression
    (hHighNorm : BKMFiniteTimeWitnessSchwartzHighNormEnvelopeFromBKMData)
    (hBiotSavart : BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate) :
    BKMLogSobolevAffinePointwiseFromEnvelope := by
  exact
    BKMLogSobolevAffinePointwiseFromEnvelope_of_schwartzHighNormEnvelope_and_biotSavart
      hHighNorm hBiotSavart

theorem BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate_of_vorticityToGradient_regression
    (hSlice : BKMSchwartzSliceVorticityToGradientAffineLogEstimate) :
    BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate := by
  exact
    BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate_of_vorticityToGradient
      hSlice

theorem BKMAnalyticContinuationLemma_of_components_regression
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticContinuationLemma := by
  exact BKMAnalyticContinuationLemma_of_components hDefect hLog hHigh

theorem BKMAffineLogSobolevAnalyticComponentsClosed_implies_BKMAnalyticComponentsClosed_regression
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    BKMAnalyticComponentsClosed := by
  exact h.implies_BKMAnalyticComponentsClosed

theorem BKMAnalyticComponentsClosed_implies_BKMAnalyticContinuationLemma_regression
    (h : BKMAnalyticComponentsClosed) :
    BKMAnalyticContinuationLemma := by
  exact h.implies_BKMAnalyticContinuationLemma

theorem BKMAnalyticComponentsClosed_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (h : BKMAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons

theorem BKMAffineLogSobolevAnalyticComponentsClosed_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons

theorem BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_of_components_regression
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma := by
  exact
    BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_of_components
      hAffine hHigh

theorem BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (h : BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons hDefect

theorem normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_constant_regression
    {ν G T : ℝ} {u : NSVelocityField}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t G) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        gronwallBound (normalizedVorticityEnstrophyAt u 0) (2 * G) 0 (t - 0) := by
  exact
    normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_constant
      hcont hGrowth

theorem continuousOn_normalizedVorticityEnstrophyAt_of_timePairingDerivativeAt_regression
    {T : ℝ} {u : NSVelocityField}
    (hTime :
      ∀ t, t ∈ Set.Icc 0 T →
        vorticityEnstrophyTimePairingDerivativeAt u t) :
    ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
      (Set.Icc 0 T) := by
  exact continuousOn_normalizedVorticityEnstrophyAt_of_timePairingDerivativeAt hTime

theorem normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_majorized_regression
    {ν K T : ℝ} {u : NSVelocityField} {G : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t))
    (hGle : ∀ t, t ∈ Set.Ico 0 T → G t ≤ K) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        gronwallBound (normalizedVorticityEnstrophyAt u 0) (2 * K) 0 (t - 0) := by
  exact
    normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_majorized
      hcont hGrowth hGle

theorem normalizedVorticityEnstrophyAt_mul_exp_neg_antiderivative_le_initial_regression
    {ν T : ℝ} {u : NSVelocityField} {G A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * G t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t * Real.exp (-(A t)) ≤
        normalizedVorticityEnstrophyAt u 0 * Real.exp (-(A 0)) := by
  exact
    normalizedVorticityEnstrophyAt_mul_exp_neg_antiderivative_le_initial
      hcont hAcont hAderiv hGrowth

theorem normalizedVorticityEnstrophyAt_le_initial_mul_exp_antiderivative_regression
    {ν T : ℝ} {u : NSVelocityField} {G A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * G t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        normalizedVorticityEnstrophyAt u 0 * Real.exp (A t - A 0) := by
  exact
    normalizedVorticityEnstrophyAt_le_initial_mul_exp_antiderivative
      hcont hAcont hAderiv hGrowth

theorem bkmScalarLogGronwallFactor_mul_exp_neg_antiderivative_le_initial_regression
    {T : ℝ} {F R A : NSTime → ℝ}
    (hFcont : ContinuousOn F (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hFnonneg : ∀ t, t ∈ Set.Icc 0 T → 0 ≤ F t)
    (hRnonneg : ∀ t, t ∈ Set.Ico 0 T → 0 ≤ R t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (R t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        ∃ D : ℝ,
          HasDerivWithinAt F D (Set.Ici t) t ∧
            D ≤ R t *
              (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t) :
    ∀ t, t ∈ Set.Icc 0 T →
      (1 + Real.log (Real.exp (1 : ℝ) + F t)) * Real.exp (-(A t)) ≤
        (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (-(A 0)) := by
  exact
    bkmScalarLogGronwallFactor_mul_exp_neg_antiderivative_le_initial
      hFcont hAcont hFnonneg hRnonneg hAderiv hGrowth

theorem bkmScalarLogGronwallFactor_le_initial_mul_exp_antiderivative_regression
    {T : ℝ} {F R A : NSTime → ℝ}
    (hFcont : ContinuousOn F (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hFnonneg : ∀ t, t ∈ Set.Icc 0 T → 0 ≤ F t)
    (hRnonneg : ∀ t, t ∈ Set.Ico 0 T → 0 ≤ R t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (R t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        ∃ D : ℝ,
          HasDerivWithinAt F D (Set.Ici t) t ∧
            D ≤ R t *
              (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t) :
    ∀ t, t ∈ Set.Icc 0 T →
      1 + Real.log (Real.exp (1 : ℝ) + F t) ≤
        (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (A t - A 0) := by
  exact
    bkmScalarLogGronwallFactor_le_initial_mul_exp_antiderivative
      hFcont hAcont hFnonneg hRnonneg hAderiv hGrowth

theorem bkmScalarLogGronwallValue_le_exp_initial_logFactor_mul_exp_antiderivative_regression
    {T : ℝ} {F R A : NSTime → ℝ}
    (hFcont : ContinuousOn F (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hFnonneg : ∀ t, t ∈ Set.Icc 0 T → 0 ≤ F t)
    (hRnonneg : ∀ t, t ∈ Set.Ico 0 T → 0 ≤ R t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (R t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        ∃ D : ℝ,
          HasDerivWithinAt F D (Set.Ici t) t ∧
            D ≤ R t *
              (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t) :
    ∀ t, t ∈ Set.Icc 0 T →
      F t ≤
        Real.exp
          ((1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
            Real.exp (A t - A 0)) := by
  exact
    bkmScalarLogGronwallValue_le_exp_initial_logFactor_mul_exp_antiderivative
      hFcont hAcont hFnonneg hRnonneg hAderiv hGrowth

theorem normalizedVorticityEnstrophyAt_le_exp_of_logSobolevGradientControlled_regression
    {ν T C : ℝ} {u : NSVelocityField} {Ω H A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le_enstrophy :
      ∀ t, t ∈ Set.Icc 0 T → H t ≤ normalizedVorticityEnstrophyAt u t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * C * (1 + Ω t)) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t
          (bkmLogSobolevGradientEnvelope C Ω H t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        Real.exp
          ((1 + Real.log
              (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
            Real.exp (A t - A 0)) := by
  exact
    normalizedVorticityEnstrophyAt_le_exp_of_logSobolevGradientControlled
      hcont hAcont hC hΩ_nonneg hH_nonneg hH_le_enstrophy
      hAderiv hGrowth

theorem normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance_regression
    {ν T C : ℝ} {u : NSVelocityField} {Ω H A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hν : 0 ≤ ν)
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le_enstrophy :
      ∀ t, t ∈ Set.Icc 0 T → H t ≤ normalizedVorticityEnstrophyAt u t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * C * (1 + Ω t)) (Set.Ici t) t)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hBal :
      ∀ t, t ∈ Set.Ico 0 T → vorticityEnstrophyBalanceAt ν u t)
    (hStretchInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        Real.exp
          ((1 + Real.log
              (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
            Real.exp (A t - A 0)) := by
  exact
    normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance
      hcont hAcont hν hC hΩ_nonneg hH_nonneg hH_le_enstrophy
      hAderiv hLog hBal hStretchInt hEnstrophyInt

theorem normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance_of_antiderivative_bounded_regression
    {ν T C Amax : ℝ} {u : NSVelocityField} {Ω H A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hν : 0 ≤ ν)
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le_enstrophy :
      ∀ t, t ∈ Set.Icc 0 T → H t ≤ normalizedVorticityEnstrophyAt u t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * C * (1 + Ω t)) (Set.Ici t) t)
    (hA_le : ∀ t, t ∈ Set.Icc 0 T → A t ≤ Amax)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hBal :
      ∀ t, t ∈ Set.Ico 0 T → vorticityEnstrophyBalanceAt ν u t)
    (hStretchInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        Real.exp
          ((1 + Real.log
              (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
            Real.exp (Amax - A 0)) := by
  exact
    normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance_of_antiderivative_bounded
      hcont hAcont hν hC hΩ_nonneg hH_nonneg hH_le_enstrophy
      hAderiv hA_le hLog hBal hStretchInt hEnstrophyInt

theorem BKMLogControlWitnessEnstrophyGronwallDataFromWitness_of_scalarGronwallData_velocitySchwartz_regression
    (hScalar : BKMLogControlWitnessScalarGronwallDataFromWitness)
    (hVelocitySlices :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  finiteTimeWitnessVelocitySchwartzSlices W)
    (hTimePairing :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  t ∈ Set.Ico 0 T →
                    vorticityEnstrophyTimePairingDerivativeAt W.velocity t) :
    BKMLogControlWitnessEnstrophyGronwallDataFromWitness := by
  exact
    BKMLogControlWitnessEnstrophyGronwallDataFromWitness_of_scalarGronwallData_velocitySchwartz
      hScalar hVelocitySlices hTimePairing

theorem BKMLogControlWitnessEnstrophyGronwallDataFromWitness_of_primitiveDominationData_velocitySchwartz_closedTimePairing_regression
    (hPrimitive : BKMLogControlWitnessPrimitiveDominationDataFromWitness)
    (hVelocitySlices :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  finiteTimeWitnessVelocitySchwartzSlices W)
    (hTimePairing :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  t ∈ Set.Icc 0 T →
                    vorticityEnstrophyTimePairingDerivativeAt W.velocity t) :
    BKMLogControlWitnessEnstrophyGronwallDataFromWitness := by
  exact
    BKMLogControlWitnessEnstrophyGronwallDataFromWitness_of_primitiveDominationData_velocitySchwartz_closedTimePairing
      hPrimitive hVelocitySlices hTimePairing

theorem BKMHighNormContinuationFromLogControl_of_enstrophyGronwallData_and_boundedEnstrophyBridge_regression
    (hData : BKMLogControlWitnessEnstrophyGronwallDataFromWitness)
    (hBridge : BKMBoundedEnstrophyContinuationBridge) :
    BKMHighNormContinuationFromLogControl := by
  exact
    BKMHighNormContinuationFromLogControl_of_enstrophyGronwallData_and_boundedEnstrophyBridge
      hData hBridge

theorem BKMHighNormContinuationFromLogControl_of_scalarGronwallData_velocitySchwartz_and_boundedEnstrophyBridge_regression
    (hScalar : BKMLogControlWitnessScalarGronwallDataFromWitness)
    (hVelocitySlices :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  finiteTimeWitnessVelocitySchwartzSlices W)
    (hTimePairing :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  t ∈ Set.Ico 0 T →
                    vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (hBridge : BKMBoundedEnstrophyContinuationBridge) :
    BKMHighNormContinuationFromLogControl := by
  exact
    BKMHighNormContinuationFromLogControl_of_scalarGronwallData_velocitySchwartz_and_boundedEnstrophyBridge
      hScalar hVelocitySlices hTimePairing hBridge

theorem BKMHighNormContinuationFromLogControl_of_primitiveDominationData_velocitySchwartz_closedTimePairing_and_boundedEnstrophyBridge_regression
    (hPrimitive : BKMLogControlWitnessPrimitiveDominationDataFromWitness)
    (hVelocitySlices :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  finiteTimeWitnessVelocitySchwartzSlices W)
    (hTimePairing :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  t ∈ Set.Icc 0 T →
                    vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (hBridge : BKMBoundedEnstrophyContinuationBridge) :
    BKMHighNormContinuationFromLogControl := by
  exact
    BKMHighNormContinuationFromLogControl_of_primitiveDominationData_velocitySchwartz_closedTimePairing_and_boundedEnstrophyBridge
      hPrimitive hVelocitySlices hTimePairing hBridge

theorem BKMContinuation_reduced_to_analytic_components_regression :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityPointwiseEnstrophyDerivativeClosed ∧
            BKMVorticityRawBalanceIntegrabilitySchwartzClosed ∧
              BKMVorticityScalarSchwartzTimePairingDerivativeClosed ∧
                BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed ∧
                  BKMVorticityRawBalanceFromStandardEquationClosed ∧
                    BKMVorticityTransportCancellationAlgebraClosed ∧
                      BKMVorticityTransportCancellationSchwartzClosed ∧
                        BKMVorticityDiffusionIntegrationByPartsSchwartzClosed ∧
                          BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed ∧
                            BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed ∧
                              BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed ∧
                                BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed ∧
                                  BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed ∧
                                    BKMVorticityEnstrophyBalanceAssemblyClosed ∧
                            BKMVorticityEnstrophyAprioriEstimateClosed ∧
                              BKMVorticityEnstrophyGradientGrowthClosed ∧
                                BKMVorticityEnstrophyLogSobolevGrowthClosed ∧
                                  BKMVorticityEnstrophyAffineLogGrowthClosed ∧
                                    BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed ∧
                                      BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed ∧
                                        BKMVorticityStretchingAffineLogIntegralBoundClosed ∧
                                          BKMLogSobolevAffineReductionClosed ∧
                                            BKMLogSobolevGrowthEstimateClosed ∧
                                              (BKMAnalyticComponentsClosed →
                                                ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) ∧
                                                (BKMAffineLogSobolevAnalyticComponentsClosed →
                                                  ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact BKMContinuation_reduced_to_analytic_components

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
