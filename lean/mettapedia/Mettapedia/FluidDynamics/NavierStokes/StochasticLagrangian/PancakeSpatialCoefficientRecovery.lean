import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevSpaceTime
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicOperatorKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier integrals recover the constructed spatial field's coefficients

Absolute summability permits integration of the reconstructed series.
Character orthogonality then recovers the original coefficient at every
frequency, with the unit-torus Haar normalization.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialCoefficientRecovery

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeArbitraryDataBlocks
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakePhysicalFourierDerivative PancakePeriodicOperatorKernel

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_fullFourierField_component (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖u k‖)) (q : Wavevector) (i : Fin 3) :
    UnitAddTorus.mFourierCoeff (fun x ↦ fullFourierField id u x i) q = u q i := by
  have hs : Summable (fun k ↦ ‖u k i‖) :=
    hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_le_pi_norm (u k) i)
  have hint (k : Wavevector) :
      Integrable (fun x : T3 ↦ UnitAddTorus.mFourier (-q+k) x * u k i) := by
    have hc : Continuous (fun x : T3 ↦ UnitAddTorus.mFourier (-q+k) x * u k i) := by fun_prop
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (Set.univ : Set T3))
  have hn (k : Wavevector) :
      (∫ x : T3, ‖UnitAddTorus.mFourier (-q+k) x * u k i‖) = ‖u k i‖ := by
    simp only [norm_mul, norm_character, one_mul, integral_const, probReal_univ, one_smul]
  have he := integral_tsum_of_summable_integral_norm hint (by simpa only [hn] using hs)
  have hchar (k : Wavevector) (x : T3) :
      UnitAddTorus.mFourier (-q) x * UnitAddTorus.mFourier k x =
        UnitAddTorus.mFourier (-q+k) x :=
    UnitAddTorus.mFourier_add.symm
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [smul_eq_mul, fullFourierField_component id u hu, id_eq,
    ← tsum_mul_left, ← mul_assoc, hchar]
  rw [← he]
  simp_rw [integral_mul_const, integral_mFourier]
  simp [neg_add_eq_zero]

theorem torusFourierVelocity_fullFourierField (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖u k‖)) :
    torusFourierVelocity (fullFourierField id u) = u := by
  funext q i
  exact mFourierCoeff_fullFourierField_component u hu q i

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialCoefficientRecovery
