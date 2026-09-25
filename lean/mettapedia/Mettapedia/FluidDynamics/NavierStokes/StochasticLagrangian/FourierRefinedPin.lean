import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierRelaxation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MisalignmentRefinedPin

/-!
# The refined pin on actual solutions gives the official statement

The sharpest pin of the pancake route demands a time-integrable envelope only
for the misalignment share of the pancake stretching, the coherent share being
bounded through the aperture-gain interface. On the relaxation data of an
actual tame solution, with the relaxation inequality proved, that pin
together with the coercive and residual sector estimates, all with gains
summing below one and constants uniform on bounded horizons, gives the
official periodic existence-and-smoothness statement.

The hypothesis is the route's open input in its exact current form; nothing
in it is assumed beyond what the route itself names.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierRefinedPin

open Set
open PeriodicFourierTriad FourierTameContinuation FourierRegularityEquivalence
open FourierRelaxation MisalignmentRefinedPin OfficialPeriodicProblem

/-- The pancake-sector estimate is monotone in the gain. -/
theorem pancakeSectorEstimate_of_le (D : DyadicVorticityStretchingData) {C ε ε' : ℝ}
    (h : PancakeSectorEstimate D C ε) (hε : ε ≤ ε') : PancakeSectorEstimate D C ε' := by
  unfold PancakeSectorEstimate at h ⊢
  have hI : 0 ≤ ∫ t in (0 : ℝ)..D.T, D.highBlockSum t :=
    intervalIntegral.integral_nonneg D.T_nonneg fun t _ ↦ D.highBlockSum_nonneg t
  calc ∫ t in (0 : ℝ)..D.T, D.pancakeStretchSum t ≤ C + ε * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t := h
    _ ≤ C + ε' * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t := by
        gcongr

/-- **The refined pin on actual solutions gives the official statement.** For
every viscosity, admissible datum and horizon, suppose the vorticity source of
every tame solution admits a sector split whose pancake share has a
coherent/misalignment split with coherent gain at most `γ` and a misalignment
budget `(B, ε)`, and whose coercive and residual shares obey their sector
estimates, with `γ + ε + εc + εr < 1` and constants uniform over the horizon.
Then the official periodic statement holds. -/
theorem periodicStatementB_of_misalignmentBudget (m : ℕ) (hm : 7 ≤ m) (Q : ℕ)
    (h : ∀ nu : ℝ, ∀ hnu : 0 < nu, ∀ u₀ : FourierVelocity, Admissible m u₀ → ∀ H, 0 < H →
      ∃ γ B ε Cc εc Cr εr : ℝ, γ + ε + εc + εr < 1 ∧
        ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ τ, ∀ hτ : τ ∈ Ico (0 : ℝ) T,
          ∃ sp : SectorSplit nu Q c.coefficients τ,
            ∃ split : CoherentMisalignmentSplitData (relaxData hm hnu c Q hτ sp),
              split.coherentGain ≤ γ ∧
              MisalignmentStrainBudget (relaxData hm hnu c Q hτ sp) split B ε ∧
              CoerciveSectorEstimate (relaxData hm hnu c Q hτ sp) Cc εc ∧
              ResidualSectorEstimate (relaxData hm hnu c Q hτ sp) Cr εr) :
    PeriodicStatementB := by
  refine periodicStatementB_of_sectorEstimates m hm Q fun nu hnu u₀ hadm H hH ↦ ?_
  obtain ⟨γ, B, ε, Cc, εc, Cr, εr, hsum, hall⟩ := h nu hnu u₀ hadm H hH
  refine ⟨B, γ + ε, Cc, εc, Cr, εr, by linarith, fun T hT c τ hτ ↦ ?_⟩
  obtain ⟨sp, split, hγ, hbud, hcoh, hres⟩ := hall T hT c τ hτ
  refine ⟨sp, ?_, hcoh, hres⟩
  exact pancakeSectorEstimate_of_le _
    (pancakeSectorEstimate_of_scaleLocalStrainBudget _
      (scaleLocalPancakeStrainBudget_of_misalignmentBudget _ split hbud))
    (by linarith)

end Mettapedia.FluidDynamics.NavierStokes.FourierRefinedPin
