import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMResidualCurlExpansion
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMLogSobolevControl

/-!
# BKM one-lemma analytic reduction

The local vorticity-stretching estimates are closed in Lean.  The remaining
unproved BKM continuation work is isolated here as one explicit analytic lemma:
finite-energy smooth data, a finite-time witness, the pressure-free
residual-curl vorticity equation, and an integrable vorticity envelope on a
nonnegative slab yield the global output.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- The vorticity-stretching part of the BKM route is no longer a missing
analytic dependency: uniform gradient and vorticity bounds give both the
stretching-vector and enstrophy-production bounds on the same slab. -/
def BKMVorticityStretchingEstimateClosed : Prop :=
  ∀ (u : NSVelocityField) (T G B : ℝ),
    uniformSpatialGradientOperatorBoundUpTo u T G →
      uniformVorticityBoundUpTo u T B →
        (0 ≤ G * B ∧
          ∀ t x, 0 ≤ t → t ≤ T →
            ‖vorticityStretchingTerm u t x‖ ≤ G * B) ∧
        (0 ≤ G * (B * B) ∧
          ∀ t x, 0 ≤ t → t ≤ T →
            |vorticityStretchingPower u t x| ≤ G * (B * B))

/-- Checked proof of the BKM vorticity-stretching estimate package. -/
theorem BKMVorticityStretchingEstimateClosed_proved :
    BKMVorticityStretchingEstimateClosed := by
  intro u T G B hG hB
  exact
    ⟨uniform_vorticityStretchingTerm_boundUpTo hG hB,
      uniform_vorticityStretchingPower_boundUpTo hG hB⟩

/-- Single remaining analytic BKM continuation lemma.

Analytically, this is where the residual-curl expansion defect is proved to
vanish, turning the residual-curl equation into the standard
transport/diffusion/stretching vorticity equation.  It is then combined with
the log-Sobolev/Biot-Savart gradient-control interface, the high-norm/enstrophy differential
inequality, and the continuation/Gronwall closure.  The statement is
deliberately phrased over the existing explicit finite-time witness,
residual-curl equation, and integrable vorticity-envelope API, so it has the
same boundary as the repaired BKM target while forcing the proof through the
vorticity layer. -/
def BKMAnalyticContinuationLemma : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
                vorticityResidualCurlEquationOn ν W.velocity T →
                  (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
                    vorticityEnvelopeOn W.velocity T Ω ∧
                      integrableVorticityEnvelopeOn Ω T B) →
                    ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- The repaired nonnegative-horizon BKM target is reduced to the single
analytic lemma above.  No global regularity theorem is asserted without that
lemma as an input. -/
theorem BKMAnalyticContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (hBKM : BKMAnalyticContinuationLemma) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  intro ν u₀ T hT hν hsmooth hdiv hfinite W hEnv
  exact hBKM ν u₀ T hT hν hsmooth hdiv hfinite W
    W.vorticityResidualCurlEquationOn hEnv

/-- Route-facing packet: the stretching estimate is closed, and the remaining
repaired BKM target is exactly downstream of `BKMAnalyticContinuationLemma`. -/
theorem BKMContinuation_reduced_to_single_analytic_lemma :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityPointwiseEnstrophyDerivativeClosed ∧
            BKMVorticityRawBalanceFromStandardEquationClosed ∧
              BKMVorticityTransportCancellationAlgebraClosed ∧
                BKMVorticityTransportCancellationSchwartzClosed ∧
                  BKMVorticityDiffusionIntegrationByPartsSchwartzClosed ∧
                    BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed ∧
                      BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed ∧
                        BKMVorticityEnstrophyBalanceAssemblyClosed ∧
                            BKMVorticityEnstrophyAprioriEstimateClosed ∧
                              BKMVorticityEnstrophyGradientGrowthClosed ∧
                                BKMVorticityEnstrophyLogSobolevGrowthClosed ∧
                                  BKMVorticityEnstrophyAffineLogGrowthClosed ∧
                                    BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed ∧
                                      BKMLogSobolevAffineReductionClosed ∧
                                        BKMLogSobolevGrowthEstimateClosed ∧
                                          (BKMAnalyticContinuationLemma →
                                            ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact
    ⟨BKMVorticityStretchingEstimateClosed_proved,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      BKMStandardVorticityGrowthEstimateClosed_proved,
      BKMVorticityPointwiseEnstrophyDerivativeClosed_proved,
      BKMVorticityRawBalanceFromStandardEquationClosed_proved,
      BKMVorticityTransportCancellationAlgebraClosed_proved,
      BKMVorticityTransportCancellationSchwartzClosed_proved,
      BKMVorticityDiffusionIntegrationByPartsSchwartzClosed_proved,
      BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed_proved,
      BKMVorticityEnstrophyBalanceAssemblyClosed_proved,
      BKMVorticityEnstrophyAprioriEstimateClosed_proved,
      BKMVorticityEnstrophyGradientGrowthClosed_proved,
      BKMVorticityEnstrophyLogSobolevGrowthClosed_proved,
      BKMVorticityEnstrophyAffineLogGrowthClosed_proved,
      BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed_proved,
      BKMLogSobolevAffineReductionClosed_proved,
      BKMLogSobolevGrowthEstimateClosed_proved,
      BKMAnalyticContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
