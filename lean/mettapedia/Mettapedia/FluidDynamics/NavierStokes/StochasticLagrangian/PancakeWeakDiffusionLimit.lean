import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHaarDiffusionIncrement
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCentralDifferenceLimit

/-!
# A collision-safe spatial diffusion limit

Uniform approximation of the actual strain and vorticity second derivatives
passes the paid finite-increment inequality to the Haar integral. The
frame-dependent linear rate is never integrated in isolation: an integrable
full rate is bounded pointwise and only continuous envelopes are integrated.
The approximation and first-increment bounds are explicit hypotheses here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeakDiffusionLimit

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory PancakeRegularizedMaterialRate PancakeHaarDiffusionIncrement
open PancakeRegularizedDiffusion PancakeTopEigenvalueDerivative PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def centralDirection {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : T3 → E) (s : T3) (h : ℝ) (x : T3) : E :=
  (h ^ 2)⁻¹ • ((f (x + s) - f x) + (f (x + -s) - f x))

theorem linearRate_centralDirection (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta h : ℝ) (s x : T3) :
    linearRate (S x) delta (w x) (centralDirection (fun y ↦ (S y).1) s h x)
      (centralDirection w s h x) =
      (h ^ 2)⁻¹ * (shiftRate S w delta s x + shiftRate S w delta (-s) x) := by
  rw [centralDirection, centralDirection, linearRate_smul, linearRate_add]
  rfl

theorem continuous_gapApplied (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta : ℝ) (hS : Continuous S) (hw : Continuous w) :
    Continuous (fun x ↦ regularizedGap (S x) delta (w x)) := by
  have hL := lipschitzWith_topEigenvalue.continuous.comp hS
  have hO := continuous_subtype_val.comp hS
  simp only [regularizedGap, sub_apply, smul_apply, one_apply_eq_self]
  exact ((hL.add continuous_const).smul hw).sub (hO.clm_apply hw)

theorem shiftCost_le (S : T3 → SymmetricStrain) (w : T3 → R3)
    (L h : ℝ) (s x : T3) (hL : 0 ≤ L)
    (hinc : ‖(S (x + s)).1 - (S x).1‖ ≤ L * |h|) :
    shiftCost S w s x ≤ L ^ 2 * h ^ 2 * ‖w x‖ ^ 2 := by
  have hs : ‖(S (x + s)).1 - (S x).1‖ ^ 2 ≤ (L * |h|) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (abs_nonneg h))).mpr hinc
  simpa only [shiftCost, mul_pow, sq_abs] using mul_le_mul_of_nonneg_right hs (sq_nonneg ‖w x‖)

/-- One nonzero spatial increment, with explicit uniform consistency errors. -/
theorem integral_rate_le_at_increment
    (S : T3 → SymmetricStrain) (w : T3 → R3)
    (A : T3 → R3 →L[ℝ] R3) (b : T3 → R3)
    (F B : T3 → ℝ) (delta nu L h eS ew : ℝ) (s : T3)
    (hd : 0 < delta) (hnu : 0 ≤ nu) (hL : 0 ≤ L) (hh : h ≠ 0)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (S x) delta (w x) (A x) (b x) + B x)
    (hAp : ∀ x, ‖A x - centralDirection (fun y ↦ (S y).1) s h x‖ ≤ eS)
    (hbp : ∀ x, ‖b x - centralDirection w s h x‖ ≤ ew)
    (hplus : ∀ x, ‖(S (x + s)).1 - (S x).1‖ ≤ L * |h|)
    (hminus : ∀ x, ‖(S (x + -s)).1 - (S x).1‖ ≤ L * |h|) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * L ^ 2 * (∫ x : T3, ‖w x‖ ^ 2) +
      (∫ x : T3, B x) + 2 * nu * eS * (∫ x : T3, ‖w x‖ ^ 2) +
      2 * nu * ew * (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖) := by
  let W := fun x ↦ ‖w x‖ ^ 2
  let K := fun x ↦ ‖regularizedGap (S x) delta (w x)‖
  let B' := fun x ↦ B x + 2 * nu * eS * W x + 2 * nu * ew * K x
  have hW : Integrable W := (hw.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hK : Integrable K := (continuous_gapApplied S w delta hS hw).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hB' : Integrable B' := (hB.add (hW.const_mul _)).add (hK.const_mul _)
  have hc : 0 ≤ nu * (h ^ 2)⁻¹ := mul_nonneg hnu (inv_nonneg.mpr (sq_nonneg h))
  have hp : ∀ᵐ x : T3, F x ≤ (nu * (h ^ 2)⁻¹) *
      (shiftRate S w delta s x + shiftRate S w delta (-s) x) + B' x := by
    filter_upwards [hpoint] with x hx
    have he := linearRate_error (S x) delta (w x) (A x)
      (centralDirection (fun y ↦ (S y).1) s h x) (b x) (centralDirection w s h x)
    have h1 := mul_le_mul_of_nonneg_right (hAp x) (by positivity : 0 ≤ 2 * ‖w x‖ ^ 2)
    have h2 := mul_le_mul_of_nonneg_left (hbp x)
      (by positivity : 0 ≤ 2 * ‖regularizedGap (S x) delta (w x)‖)
    have he' : linearRate (S x) delta (w x) (A x) (b x) ≤
        (h ^ 2)⁻¹ * (shiftRate S w delta s x + shiftRate S w delta (-s) x) +
        2 * eS * W x + 2 * ew * K x := by
      rw [linearRate_centralDirection] at he
      dsimp only [W, K]
      nlinarith
    have hn := mul_le_mul_of_nonneg_left he' hnu
    dsimp only [B']
    nlinarith
  have hm := integral_rate_le_of_central_envelope S w delta (nu * (h ^ 2)⁻¹) s F B'
    hd hc hS hw hF hB' hp
  have hD : 0 ≤ ∫ x : T3, shiftDissipation w s x + shiftDissipation w (-s) x :=
    integral_nonneg (fun x ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hD' : 0 ≤ nu * (h ^ 2)⁻¹ * (delta / 2) *
      (∫ x : T3, shiftDissipation w s x + shiftDissipation w (-s) x) := by positivity
  have hC : Integrable (fun x ↦ shiftCost S w s x + shiftCost S w (-s) x) :=
    ((continuous_shiftCost S w s hS hw).add
      (continuous_shiftCost S w (-s) hS hw)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hcost := integral_mono hC (hW.const_mul (2 * L ^ 2 * h ^ 2)) (fun x ↦ by
    have h1 := shiftCost_le S w L h s x hL (hplus x)
    have h2 := shiftCost_le S w L h (-s) x hL (hminus x)
    dsimp only [W]
    linarith)
  rw [integral_const_mul] at hcost
  have hpaid := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg hc (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hd.le))
  have hcancel : nu * (h ^ 2)⁻¹ * (8 / delta) * (2 * L ^ 2 * h ^ 2 * (∫ x : T3, W x)) =
      (16 * nu / delta) * L ^ 2 * (∫ x : T3, W x) := by
    field_simp [hh]
    ring
  rw [hcancel] at hpaid
  have hBi : (∫ x : T3, B' x) = (∫ x : T3, B x) +
      2 * nu * eS * (∫ x : T3, W x) + 2 * nu * ew * (∫ x : T3, K x) := by
    dsimp only [B']
    rw [integral_add (f := fun x ↦ B x + 2 * nu * eS * W x)
      (g := fun x ↦ 2 * nu * ew * K x) (hB.add (hW.const_mul _)) (hK.const_mul _),
      integral_add (f := B) (g := fun x ↦ 2 * nu * eS * W x) hB (hW.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hBi] at hm
  dsimp only [W, K] at *
  linarith

/-- The spatial continuum limit of the paid inequality. No spatial
derivative of a selected eigenvector or second derivative of the largest
eigenvalue is used. The full rate and its nondiffusive envelope must be
integrable; the frame-dependent viscous response need not be. -/
theorem integral_rate_le_of_uniform_central_approx
    (S : T3 → SymmetricStrain) (w : T3 → R3)
    (A : T3 → R3 →L[ℝ] R3) (b : T3 → R3)
    (F B : T3 → ℝ) (delta nu L : ℝ) (shift : ℝ → T3) (eS ew : ℝ → ℝ)
    (hd : 0 < delta) (hnu : 0 ≤ nu) (hL : 0 ≤ L)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (S x) delta (w x) (A x) (b x) + B x)
    (hAp : ∀ h ≠ 0, ∀ x, ‖A x - centralDirection (fun y ↦ (S y).1) (shift h) h x‖ ≤ eS h)
    (hbp : ∀ h ≠ 0, ∀ x, ‖b x - centralDirection w (shift h) h x‖ ≤ ew h)
    (hplus : ∀ h ≠ 0, ∀ x, ‖(S (x + shift h)).1 - (S x).1‖ ≤ L * |h|)
    (hminus : ∀ h ≠ 0, ∀ x, ‖(S (x + -(shift h))).1 - (S x).1‖ ≤ L * |h|)
    (heS : Tendsto eS (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hew : Tendsto ew (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * L ^ 2 * (∫ x : T3, ‖w x‖ ^ 2) +
      ∫ x : T3, B x := by
  have ht := (((tendsto_const_nhds (x :=
    (16 * nu / delta) * L ^ 2 * (∫ x : T3, ‖w x‖ ^ 2) + ∫ x : T3, B x)).add
    ((heS.const_mul (2 * nu)).mul_const (∫ x : T3, ‖w x‖ ^ 2))).add
    ((hew.const_mul (2 * nu)).mul_const
      (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖)))
  have ht' : Tendsto (fun h ↦
      (16 * nu / delta) * L ^ 2 * (∫ x : T3, ‖w x‖ ^ 2) + (∫ x : T3, B x) +
      2 * nu * eS h * (∫ x : T3, ‖w x‖ ^ 2) +
      2 * nu * ew h * (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((16 * nu / delta) * L ^ 2 * (∫ x : T3, ‖w x‖ ^ 2) + ∫ x : T3, B x)) := by
    simpa only [mul_zero, zero_mul, add_zero] using ht
  apply ge_of_tendsto ht'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact integral_rate_le_at_increment S w A b F B delta nu L h (eS h) (ew h) (shift h)
    hd hnu hL hh hS hw hF hB hpoint (hAp h hh) (hbp h hh) (hplus h hh) (hminus h hh)

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeakDiffusionLimit
