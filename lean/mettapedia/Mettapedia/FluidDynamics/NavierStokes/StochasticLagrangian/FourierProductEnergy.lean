import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTracePatchEnergy

/-!
# Physical product estimates for collected Fourier coefficients

Parseval converts convolution energy into the integral of a product.
A physical supremum bound on one factor controls the other factor's
coefficient energy, with no Fourier cardinality or Wiener-norm loss.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierProductEnergy

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeMisalignmentEnergyBridge
open PancakeFiniteFourierLocalization PressureTracePatchEnergy
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem scalarEnergy_eq_integral (P : Finset Wavevector) (c : Wavevector → ℂ) :
    scalarEnergy P c = ∫ x : T3, ‖finiteScalarFourierReconstruction P c x‖ ^ 2 := by
  simpa only [scalarEnergy, Complex.normSq_eq_norm_sq] using
    (integral_normSq_finiteScalarFourierReconstruction P c).symm

theorem scalarEnergy_convolution_eq_integral (P K : Finset Wavevector) (c b : Wavevector → ℂ) :
    scalarEnergy (finiteCutoffOutputModes P K) (scalarConvolution P K c b) =
      ∫ x : T3, ‖finiteScalarFourierReconstruction P c x‖ ^ 2 *
        ‖finiteScalarFourierReconstruction K b x‖ ^ 2 := by
  rw [scalarEnergy_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [scalarReconstruction_convolution, norm_mul, mul_pow]

theorem scalarEnergy_convolution_le (P K : Finset Wavevector) (c b : Wavevector → ℂ)
    (B : ℝ) (hB : ∀ x : T3, ‖finiteScalarFourierReconstruction K b x‖ ≤ B) :
    scalarEnergy (finiteCutoffOutputModes P K) (scalarConvolution P K c b) ≤
      B ^ 2 * scalarEnergy P c := by
  have hc := (continuous_finiteScalarFourierReconstruction P c).norm.pow 2
  have hb := (continuous_finiteScalarFourierReconstruction K b).norm.pow 2
  have hi : Integrable (fun x : T3 ↦ ‖finiteScalarFourierReconstruction P c x‖ ^ 2) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hleft : Integrable (fun x : T3 ↦ ‖finiteScalarFourierReconstruction P c x‖ ^ 2 *
      ‖finiteScalarFourierReconstruction K b x‖ ^ 2) :=
    (hc.mul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun x : T3 ↦ B ^ 2 * ‖finiteScalarFourierReconstruction P c x‖ ^ 2) :=
    hi.const_mul _
  rw [scalarEnergy_convolution_eq_integral, scalarEnergy_eq_integral, ← integral_const_mul]
  apply integral_mono hleft hright (fun x ↦ ?_)
  have h := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)
    (sq_nonneg ‖finiteScalarFourierReconstruction P c x‖)
  exact h.trans_eq (mul_comm _ _)

end Mettapedia.FluidDynamics.NavierStokes.FourierProductEnergy
