import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairEnvelope

/-! Almost-everywhere linearity of integrable frequency-pair periodization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodizationLinearity

open MeasureTheory FrequencyPairPeriodization FrequencyPairEnvelope PancakeBilinearPeriodization
open Mettapedia.Analysis.FundamentalDomainPeriodization

local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
theorem ae_summable_norm_orbit (K : E6 → E) (hKm : Measurable K) (hK : Integrable K) :
    ∀ᵐ q : T6, Summable (fun g : StandardFrequencyPairLattice ↦
      ‖K (g +ᵥ unitTorusFrequencyPairRepresentative q)‖) := by
  simpa only [norm_norm] using ae_summable_envelope_orbit (fun x ↦ ‖K x‖) hKm.norm hK.norm

theorem periodize_sub_ae (K L : E6 → E) (hKm : Measurable K) (hLm : Measurable L)
    (hK : Integrable K) (hL : Integrable L) :
    periodize (fun x ↦ K x - L x) =ᵐ[volume] fun q ↦ periodize K q - periodize L q := by
  filter_upwards [ae_summable_norm_orbit K hKm hK, ae_summable_norm_orbit L hLm hL] with q hk hl
  exact hk.of_norm.tsum_sub hl.of_norm

end Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodizationLinearity
