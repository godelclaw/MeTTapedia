import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRegularizedMaterialRate
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Spatial averaging of the collision-safe finite-increment inequality

The actual unit-torus Haar integral cancels the translated energy
differences. Only the full rate and its envelope are integrated; no
measurability of the arbitrarily selected top eigenvector is assumed.
The pointwise discrete envelope and integrability of the full rate are
explicit hypotheses. Their physical limiting realization is separate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHaarDiffusionIncrement

open scoped RealInnerProductSpace
open MeasureTheory PancakeRegularizedMaterialRate PancakeSpectralFiniteDifference
open PancakeRegularizedDiffusion PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_regularizedEnergy (S : T3 → SymmetricStrain) (w : T3 → R3) (delta : ℝ)
    (hS : Continuous S) (hw : Continuous w) :
    Continuous (fun x ↦ regularizedEnergy (S x) delta (w x)) := by
  have hL := lipschitzWith_topEigenvalue.continuous.comp hS
  have hO := continuous_subtype_val.comp hS
  simp only [regularizedEnergy, regularizedGap, sub_apply, smul_apply, one_apply_eq_self]
  exact hw.inner (((hL.add continuous_const).smul hw).sub (hO.clm_apply hw))

def shiftEnergy (S : T3 → SymmetricStrain) (w : T3 → R3) (delta : ℝ) (h x : T3) : ℝ :=
  regularizedEnergy (S (x + h)) delta (w (x + h)) - regularizedEnergy (S x) delta (w x)

def shiftDissipation (w : T3 → R3) (h x : T3) : ℝ := ‖w (x + h) - w x‖ ^ 2

def shiftCost (S : T3 → SymmetricStrain) (w : T3 → R3) (h x : T3) : ℝ :=
  ‖(S (x + h)).1 - (S x).1‖ ^ 2 * ‖w x‖ ^ 2

def shiftRate (S : T3 → SymmetricStrain) (w : T3 → R3) (delta : ℝ) (h x : T3) : ℝ :=
  incrementRate (S x) (S (x + h)) delta (w x) (w (x + h) - w x)

theorem shiftRate_paid (S : T3 → SymmetricStrain) (w : T3 → R3) (delta : ℝ)
    (h x : T3) (hd : 0 < delta) :
    shiftRate S w delta h x + (delta / 2) * shiftDissipation w h x ≤
      shiftEnergy S w delta h x + (8 / delta) * shiftCost S w h x := by
  have hh := incrementRate_paid (S x) (S (x + h)) delta (w x) (w (x + h) - w x) hd
  have hc : w x + (w (x + h) - w x) = w (x + h) := by abel
  simpa only [hc, shiftRate, shiftEnergy, shiftCost, shiftDissipation, mul_assoc] using hh

theorem continuous_shiftEnergy (S : T3 → SymmetricStrain) (w : T3 → R3) (delta : ℝ)
    (h : T3) (hS : Continuous S) (hw : Continuous w) : Continuous (shiftEnergy S w delta h) :=
  ((continuous_regularizedEnergy S w delta hS hw).comp (continuous_id.add continuous_const)).sub
    (continuous_regularizedEnergy S w delta hS hw)

theorem continuous_shiftDissipation (w : T3 → R3) (h : T3) (hw : Continuous w) :
    Continuous (shiftDissipation w h) :=
  ((hw.comp (continuous_id.add continuous_const)).sub hw).norm.pow 2

theorem continuous_shiftCost (S : T3 → SymmetricStrain) (w : T3 → R3) (h : T3)
    (hS : Continuous S) (hw : Continuous w) : Continuous (shiftCost S w h) := by
  have hO := continuous_subtype_val.comp hS
  exact (((hO.comp (continuous_id.add continuous_const)).sub hO).norm.pow 2).mul (hw.norm.pow 2)

theorem integral_shiftEnergy_zero (S : T3 → SymmetricStrain) (w : T3 → R3) (delta : ℝ)
    (h : T3) (hS : Continuous S) (hw : Continuous w) :
    (∫ x : T3, shiftEnergy S w delta h x) = 0 := by
  have he := continuous_regularizedEnergy S w delta hS hw
  have hi : Integrable (fun x ↦ regularizedEnergy (S x) delta (w x)) :=
    he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x ↦ regularizedEnergy (S (x + h)) delta (w (x + h))) :=
    (he.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  unfold shiftEnergy
  rw [integral_sub hj hi,
    integral_add_right_eq_self (fun x ↦ regularizedEnergy (S x) delta (w x)) h, sub_self]

/-- Integrate a measurable full-rate envelope without integrating the
possibly nonmeasurable frame-dependent shiftRate separately. -/
theorem integral_rate_le_of_shift_envelope
    (S : T3 → SymmetricStrain) (w : T3 → R3) (delta c : ℝ) (h : T3)
    (F B : T3 → ℝ) (hd : 0 < delta) (hc : 0 ≤ c)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ c * shiftRate S w delta h x + B x) :
    (∫ x : T3, F x) + c * (delta / 2) * (∫ x : T3, shiftDissipation w h x) ≤
      c * (8 / delta) * (∫ x : T3, shiftCost S w h x) + ∫ x : T3, B x := by
  have hD : Integrable (shiftDissipation w h) :=
    (continuous_shiftDissipation w h hw).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hC : Integrable (shiftCost S w h) :=
    (continuous_shiftCost S w h hS hw).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hE : Integrable (shiftEnergy S w delta h) :=
    (continuous_shiftEnergy S w delta h hS hw).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hleft : Integrable (fun x ↦ F x + c * (delta / 2) * shiftDissipation w h x) :=
    hF.add (hD.const_mul _)
  have hright : Integrable (fun x ↦ c * shiftEnergy S w delta h x +
      c * (8 / delta) * shiftCost S w h x + B x) :=
    ((hE.const_mul _).add (hC.const_mul _)).add hB
  have hm := integral_mono_ae hleft hright (by
    filter_upwards [hpoint] with x hx
    have hp := mul_le_mul_of_nonneg_left (shiftRate_paid S w delta h x hd) hc
    linarith)
  rw [integral_add hF (hD.const_mul (c * (delta / 2))),
    integral_add (f := fun x ↦ c * shiftEnergy S w delta h x + c * (8 / delta) * shiftCost S w h x)
      (g := B) ((hE.const_mul c).add (hC.const_mul (c * (8 / delta)))) hB,
    integral_add (f := fun x ↦ c * shiftEnergy S w delta h x)
      (g := fun x ↦ c * (8 / delta) * shiftCost S w h x)
      (hE.const_mul c) (hC.const_mul (c * (8 / delta))), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_shiftEnergy_zero S w delta h hS hw] at hm
  simpa only [mul_zero, zero_add] using hm

/-- Paired translations give the central-difference spatial envelope.
The two frame-dependent rates are still not integrated separately. -/
theorem integral_rate_le_of_central_envelope
    (S : T3 → SymmetricStrain) (w : T3 → R3) (delta c : ℝ) (h : T3)
    (F B : T3 → ℝ) (hd : 0 < delta) (hc : 0 ≤ c)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3,
      F x ≤ c * (shiftRate S w delta h x + shiftRate S w delta (-h) x) + B x) :
    (∫ x : T3, F x) + c * (delta / 2) *
      (∫ x : T3, shiftDissipation w h x + shiftDissipation w (-h) x) ≤
      c * (8 / delta) * (∫ x : T3, shiftCost S w h x + shiftCost S w (-h) x) + ∫ x : T3, B x := by
  let D := fun x ↦ shiftDissipation w h x + shiftDissipation w (-h) x
  let C := fun x ↦ shiftCost S w h x + shiftCost S w (-h) x
  let E := fun x ↦ shiftEnergy S w delta h x + shiftEnergy S w delta (-h) x
  have hD : Integrable D := ((continuous_shiftDissipation w h hw).add
    (continuous_shiftDissipation w (-h) hw)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC : Integrable C := ((continuous_shiftCost S w h hS hw).add
    (continuous_shiftCost S w (-h) hS hw)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hEp : Integrable (shiftEnergy S w delta h) :=
    (continuous_shiftEnergy S w delta h hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hEm : Integrable (shiftEnergy S w delta (-h)) :=
    (continuous_shiftEnergy S w delta (-h) hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hE : Integrable E := hEp.add hEm
  have he0 : (∫ x : T3, E x) = 0 := by
    rw [integral_add hEp hEm, integral_shiftEnergy_zero S w delta h hS hw,
      integral_shiftEnergy_zero S w delta (-h) hS hw, zero_add]
  have hleft : Integrable (fun x ↦ F x + c * (delta / 2) * D x) := hF.add (hD.const_mul _)
  have hright : Integrable (fun x ↦ c * E x + c * (8 / delta) * C x + B x) :=
    ((hE.const_mul _).add (hC.const_mul _)).add hB
  have hm := integral_mono_ae hleft hright (by
    filter_upwards [hpoint] with x hx
    have hp := mul_le_mul_of_nonneg_left (shiftRate_paid S w delta h x hd) hc
    have hn := mul_le_mul_of_nonneg_left (shiftRate_paid S w delta (-h) x hd) hc
    dsimp only [D, C, E]
    linarith)
  rw [integral_add hF (hD.const_mul (c * (delta / 2))),
    integral_add (f := fun x ↦ c * E x + c * (8 / delta) * C x) (g := B)
      ((hE.const_mul c).add (hC.const_mul (c * (8 / delta)))) hB,
    integral_add (f := fun x ↦ c * E x) (g := fun x ↦ c * (8 / delta) * C x)
      (hE.const_mul c) (hC.const_mul (c * (8 / delta))),
    integral_const_mul, integral_const_mul, integral_const_mul, he0] at hm
  simpa only [mul_zero, zero_add] using hm

end Mettapedia.FluidDynamics.NavierStokes.PancakeHaarDiffusionIncrement
