import Mettapedia.Analysis.IntegrableKernelPairing
import Mettapedia.Analysis.UnitTorusFourierTranslation

/-! # Fourier-series convolution by an integrable periodic kernel -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusIntegrableConvolution

open MeasureTheory UnitAddTorus UnitTorusFourierTranslation IntegrableKernelPairing
variable {d : Type*} [Fintype d]
local notation "Td" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_convolution (K : Td → ℂ) (hK : Integrable K) (f : C(Td, ℂ))
    (a : (d → ℤ) → ℂ) (ha : HasSum (fun k ↦ a k • mFourier k) f) (x : Td) :
    HasSum (fun k ↦ mFourierCoeff K k * mFourier k x * a k)
      (∫ h : Td, K h * f (x - h)) := by
  let shift : C(Td, Td) := ⟨fun h ↦ x - h, continuous_const.sub continuous_id⟩
  have hs := (pairingCLM volume K hK).hasSum
    ((ContinuousMap.compCLM (R := ℂ) ℂ shift).hasSum ha)
  apply hs.congr_fun
  intro k
  symm
  change (∫ h : Td, K h * (a k * mFourier k (x - h))) = _
  simp_rw [mFourier_sub]
  calc
    _ = ∫ h : Td, (mFourier k x * a k) * (mFourier (-k) h * K h) := by
      apply integral_congr_ae
      filter_upwards [] with h
      ring
    _ = _ := by rw [integral_const_mul]; change _ * mFourierCoeff K k = _; ring

end Mettapedia.Analysis.UnitTorusIntegrableConvolution
