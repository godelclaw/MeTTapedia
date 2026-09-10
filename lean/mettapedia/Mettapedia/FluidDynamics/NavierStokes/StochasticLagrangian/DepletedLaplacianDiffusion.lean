import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLaplacianDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionWeight

/-!
# Weak spatial diffusion paid by the capped alignment weight

The finite-increment cancellation survives the simultaneous spatial limit.
Only continuous scalar envelopes and an integrable full rate are integrated;
no selected eigenvector measurability or spectral gap is assumed.
The consistency errors still use full vorticity, but tend to zero before
the final estimate. Energy and weight regularizers are independent.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.DepletedLaplacianDiffusion

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory PancakeRegularizedMaterialRate PancakeHaarDiffusionIncrement
open PancakeWeakDiffusionLimit PancakeRegularizedDiffusion PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open PancakeLaplacianDiffusion (linearRate_sum)
open SpectralDiffusionWeight

def shiftCost (S : T3 → SymmetricStrain) (w : T3 → R3) (epsilon : ℝ) (s x : T3) : ℝ :=
  ‖(S (x + s)).1 - (S x).1‖ ^ 2 * weight (S x) (w x) epsilon

theorem shiftRate_paid (S : T3 → SymmetricStrain) (w : T3 → R3) (delta epsilon : ℝ)
    (s x : T3) (hd : 0 < delta) (heps : 0 < epsilon) :
    shiftRate S w delta s x + (delta / 2) * shiftDissipation w s x ≤
      shiftEnergy S w delta s x + (8 / delta) * shiftCost S w epsilon s x := by
  have h := incrementRate_paid_weight (S x) (S (x + s)) delta epsilon (w x) (w (x + s) - w x) hd heps
  have hv : w x + (w (x + s) - w x) = w (x + s) := by abel
  simpa only [hv, shiftRate, shiftEnergy, shiftCost, shiftDissipation, mul_assoc] using h

theorem continuous_shiftCost (S : T3 → SymmetricStrain) (w : T3 → R3) (epsilon : ℝ)
    (heps : 0 < epsilon) (s : T3) (hS : Continuous S) (hw : Continuous w) :
    Continuous (shiftCost S w epsilon s) := by
  have hO := continuous_subtype_val.comp hS
  exact (((hO.comp (continuous_id.add continuous_const)).sub hO).norm.pow 2).mul
    (continuous_weight S w epsilon heps hS hw)

theorem shiftCost_le (S : T3 → SymmetricStrain) (w : T3 → R3) (epsilon L h : ℝ)
    (s x : T3) (heps : 0 < epsilon) (_hL : 0 ≤ L)
    (hp : ‖(S (x + s)).1 - (S x).1‖ ≤ L * |h|) :
    shiftCost S w epsilon s x ≤ L ^ 2 * h ^ 2 * weight (S x) (w x) epsilon := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hh := mul_le_mul_of_nonneg_right hs (weight_nonneg (S x) (w x) epsilon heps)
  simpa only [shiftCost, mul_pow, sq_abs, mul_assoc] using hh

def centralUpper (S : T3 → SymmetricStrain) (w : T3 → R3) (delta epsilon h : ℝ) (s x : T3) : ℝ :=
  (h ^ 2)⁻¹ * (shiftEnergy S w delta s x + shiftEnergy S w delta (-s) x +
    (8 / delta) * (shiftCost S w epsilon s x + shiftCost S w epsilon (-s) x))

theorem linearRate_central_le_upper (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta epsilon h : ℝ) (s x : T3) (hd : 0 < delta) (heps : 0 < epsilon) :
    linearRate (S x) delta (w x) (centralDirection (fun y ↦ (S y).1) s h x)
      (centralDirection w s h x) ≤ centralUpper S w delta epsilon h s x := by
  rw [linearRate_centralDirection]
  apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg h))
  have hp := shiftRate_paid S w delta epsilon s x hd heps
  have hm := shiftRate_paid S w delta epsilon (-s) x hd heps
  have hpD : 0 ≤ (delta / 2) * shiftDissipation w s x := by unfold shiftDissipation; positivity
  have hmD : 0 ≤ (delta / 2) * shiftDissipation w (-s) x := by unfold shiftDissipation; positivity
  linarith

theorem continuous_centralUpper (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta epsilon h : ℝ) (s : T3) (heps : 0 < epsilon) (hS : Continuous S) (hw : Continuous w) :
    Continuous (centralUpper S w delta epsilon h s) :=
  (((continuous_shiftEnergy S w delta s hS hw).add
    (continuous_shiftEnergy S w delta (-s) hS hw)).add
    (((continuous_shiftCost S w epsilon heps s hS hw).add
      (continuous_shiftCost S w epsilon heps (-s) hS hw)).const_mul (8 / delta))).const_mul _

theorem integral_centralUpper_le (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta epsilon L h : ℝ) (s : T3) (hd : 0 < delta) (heps : 0 < epsilon) (hL : 0 ≤ L) (hh : h ≠ 0)
    (hS : Continuous S) (hw : Continuous w)
    (hp : ∀ x, ‖(S (x + s)).1 - (S x).1‖ ≤ L * |h|)
    (hm : ∀ x, ‖(S (x + -s)).1 - (S x).1‖ ≤ L * |h|) :
    (∫ x : T3, centralUpper S w delta epsilon h s x) ≤
      (16 / delta) * L ^ 2 * (∫ x : T3, weight (S x) (w x) epsilon) := by
  let E := fun x ↦ shiftEnergy S w delta s x + shiftEnergy S w delta (-s) x
  let C := fun x ↦ shiftCost S w epsilon s x + shiftCost S w epsilon (-s) x
  have hEp : Integrable (shiftEnergy S w delta s) :=
    (continuous_shiftEnergy S w delta s hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hEm : Integrable (shiftEnergy S w delta (-s)) :=
    (continuous_shiftEnergy S w delta (-s) hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hE : Integrable E := hEp.add hEm
  have hC : Integrable C := ((continuous_shiftCost S w epsilon heps s hS hw).add
    (continuous_shiftCost S w epsilon heps (-s) hS hw)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : Integrable (fun x ↦ weight (S x) (w x) epsilon) :=
    (continuous_weight S w epsilon heps hS hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hE0 : (∫ x : T3, E x) = 0 := by
    rw [integral_add hEp hEm, integral_shiftEnergy_zero S w delta s hS hw,
      integral_shiftEnergy_zero S w delta (-s) hS hw, zero_add]
  have hcost := integral_mono hC (hW.const_mul (2 * L ^ 2 * h ^ 2)) (fun x ↦ by
    have h1 := shiftCost_le S w epsilon L h s x heps hL (hp x)
    have h2 := shiftCost_le S w epsilon L h (-s) x heps hL (hm x)
    dsimp only [C]
    linarith)
  rw [integral_const_mul] at hcost
  change (∫ x : T3, (h ^ 2)⁻¹ * (E x + (8 / delta) * C x)) ≤ _
  rw [integral_const_mul, integral_add hE (hC.const_mul (8 / delta)),
    integral_const_mul, hE0, zero_add]
  calc
    _ ≤ (h ^ 2)⁻¹ * ((8 / delta) * (2 * L ^ 2 * h ^ 2 * (∫ x : T3, weight (S x) (w x) epsilon))) := by
      gcongr
    _ = _ := by field_simp [hh]; ring

/-- A joint finite-direction estimate. Only the single full rate is
assumed integrable, not its selected-frame coordinate decomposition. -/
theorem integral_joint_rate_le_at_increment {ι : Type*} (I : Finset ι)
    (S : T3 → SymmetricStrain) (w : T3 → R3)
    (A : ι → T3 → R3 →L[ℝ] R3) (b : ι → T3 → R3)
    (F B : T3 → ℝ) (delta epsilon nu h : ℝ) (L eS ew : ι → ℝ) (s : ι → T3)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu) (hL : ∀ i ∈ I, 0 ≤ L i) (hh : h ≠ 0)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (S x) delta (w x)
      (∑ i ∈ I, A i x) (∑ i ∈ I, b i x) + B x)
    (hAp : ∀ i ∈ I, ∀ x, ‖A i x - centralDirection (fun y ↦ (S y).1) (s i) h x‖ ≤ eS i)
    (hbp : ∀ i ∈ I, ∀ x, ‖b i x - centralDirection w (s i) h x‖ ≤ ew i)
    (hplus : ∀ i ∈ I, ∀ x, ‖(S (x + s i)).1 - (S x).1‖ ≤ L i * |h|)
    (hminus : ∀ i ∈ I, ∀ x, ‖(S (x + -(s i))).1 - (S x).1‖ ≤ L i * |h|) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * (∑ i ∈ I, L i ^ 2) * (∫ x : T3, weight (S x) (w x) epsilon) +
      (∫ x : T3, B x) + 2 * nu * (∑ i ∈ I, eS i) * (∫ x : T3, ‖w x‖ ^ 2) +
      2 * nu * (∑ i ∈ I, ew i) * (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖) := by
  let U := fun i ↦ centralUpper S w delta epsilon h (s i)
  let W := fun x ↦ ‖w x‖ ^ 2
  let K := fun x ↦ ‖regularizedGap (S x) delta (w x)‖
  let B' := fun x ↦ B x + 2 * nu * (∑ i ∈ I, eS i) * W x + 2 * nu * (∑ i ∈ I, ew i) * K x
  have hU : ∀ i, Integrable (U i) := fun i ↦
    (continuous_centralUpper S w delta epsilon h (s i) heps hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hUs : Integrable (fun x ↦ ∑ i ∈ I, U i x) :=
    (continuous_finsetSum I (fun i _ ↦ continuous_centralUpper S w delta epsilon h (s i) heps hS hw)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : Integrable W := (hw.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hK : Integrable K := (continuous_gapApplied S w delta hS hw).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hB' : Integrable B' := (hB.add (hW.const_mul _)).add (hK.const_mul _)
  have hp : ∀ᵐ x : T3, F x ≤ nu * (∑ i ∈ I, U i x) + B' x := by
    filter_upwards [hpoint] with x hx
    rw [linearRate_sum] at hx
    have hs := Finset.sum_le_sum (s := I) (fun i hi ↦ show linearRate (S x) delta (w x) (A i x) (b i x) ≤
        U i x + 2 * eS i * W x + 2 * ew i * K x by
      have he := linearRate_error (S x) delta (w x) (A i x)
        (centralDirection (fun y ↦ (S y).1) (s i) h x) (b i x) (centralDirection w (s i) h x)
      have hu := linearRate_central_le_upper S w delta epsilon h (s i) x hd heps
      have h1 := mul_le_mul_of_nonneg_right (hAp i hi x) (by positivity : 0 ≤ 2 * ‖w x‖ ^ 2)
      have h2 := mul_le_mul_of_nonneg_left (hbp i hi x)
        (by positivity : 0 ≤ 2 * ‖regularizedGap (S x) delta (w x)‖)
      dsimp only [U, W, K]
      nlinarith)
    have hs' : (∑ i ∈ I, linearRate (S x) delta (w x) (A i x) (b i x)) ≤
        (∑ i ∈ I, U i x) + 2 * (∑ i ∈ I, eS i) * W x + 2 * (∑ i ∈ I, ew i) * K x := by
      simpa only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] using hs
    have hn := mul_le_mul_of_nonneg_left hs' hnu
    dsimp only [B']
    nlinarith
  have hm := integral_mono_ae hF ((hUs.const_mul nu).add hB') hp
  change (∫ x : T3, F x) ≤ ∫ x : T3, nu * (∑ i ∈ I, U i x) + B' x at hm
  rw [integral_add (hUs.const_mul nu) hB', integral_const_mul,
    integral_finsetSum I (fun i _ ↦ hU i)] at hm
  have hc := Finset.sum_le_sum (s := I) (fun i hi ↦
    integral_centralUpper_le S w delta epsilon (L i) h (s i) hd heps (hL i hi) hh hS hw (hplus i hi) (hminus i hi))
  have hc' : (∑ i ∈ I, ∫ x : T3, U i x) ≤ (16 / delta) * (∑ i ∈ I, L i ^ 2) * (∫ x : T3, weight (S x) (w x) epsilon) := by
    simpa only [← Finset.sum_mul, ← Finset.mul_sum] using hc
  have hn := mul_le_mul_of_nonneg_left hc' hnu
  have hBi : (∫ x : T3, B' x) = (∫ x : T3, B x) +
      2 * nu * (∑ i ∈ I, eS i) * (∫ x : T3, W x) +
      2 * nu * (∑ i ∈ I, ew i) * (∫ x : T3, K x) := by
    dsimp only [B']
    rw [integral_add (f := fun x ↦ B x + 2 * nu * (∑ i ∈ I, eS i) * W x)
      (g := fun x ↦ 2 * nu * (∑ i ∈ I, ew i) * K x) (hB.add (hW.const_mul _)) (hK.const_mul _),
      integral_add (f := B) (g := fun x ↦ 2 * nu * (∑ i ∈ I, eS i) * W x) hB (hW.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hBi] at hm
  dsimp only [W, K] at *
  simp only [div_eq_mul_inv] at *
  nlinarith

/-- Simultaneous passage to all spatial directions preserves the
single full-rate integrability hypothesis. -/
theorem integral_joint_rate_le_of_uniform_approx {ι : Type*} (I : Finset ι)
    (S : T3 → SymmetricStrain) (w : T3 → R3)
    (A : ι → T3 → R3 →L[ℝ] R3) (b : ι → T3 → R3)
    (F B : T3 → ℝ) (delta epsilon nu : ℝ) (L : ι → ℝ) (shift : ι → ℝ → T3) (eS ew : ι → ℝ → ℝ)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu) (hL : ∀ i ∈ I, 0 ≤ L i)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (S x) delta (w x)
      (∑ i ∈ I, A i x) (∑ i ∈ I, b i x) + B x)
    (hAp : ∀ h ≠ 0, ∀ i ∈ I, ∀ x,
      ‖A i x - centralDirection (fun y ↦ (S y).1) (shift i h) h x‖ ≤ eS i h)
    (hbp : ∀ h ≠ 0, ∀ i ∈ I, ∀ x, ‖b i x - centralDirection w (shift i h) h x‖ ≤ ew i h)
    (hplus : ∀ h ≠ 0, ∀ i ∈ I, ∀ x, ‖(S (x + shift i h)).1 - (S x).1‖ ≤ L i * |h|)
    (hminus : ∀ h ≠ 0, ∀ i ∈ I, ∀ x, ‖(S (x + -(shift i h))).1 - (S x).1‖ ≤ L i * |h|)
    (heS : ∀ i ∈ I, Tendsto (eS i) (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hew : ∀ i ∈ I, Tendsto (ew i) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * (∑ i ∈ I, L i ^ 2) * (∫ x : T3, weight (S x) (w x) epsilon) +
      ∫ x : T3, B x := by
  have htS : Tendsto (fun h ↦ ∑ i ∈ I, eS i h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum I heS
  have htw : Tendsto (fun h ↦ ∑ i ∈ I, ew i h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum I hew
  have ht := (((tendsto_const_nhds (x :=
    (16 * nu / delta) * (∑ i ∈ I, L i ^ 2) * (∫ x : T3, weight (S x) (w x) epsilon) + ∫ x : T3, B x)).add
    ((htS.const_mul (2 * nu)).mul_const (∫ x : T3, ‖w x‖ ^ 2))).add
    ((htw.const_mul (2 * nu)).mul_const (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖)))
  have ht' : Tendsto (fun h ↦
      (16 * nu / delta) * (∑ i ∈ I, L i ^ 2) * (∫ x : T3, weight (S x) (w x) epsilon) + (∫ x : T3, B x) +
      2 * nu * (∑ i ∈ I, eS i h) * (∫ x : T3, ‖w x‖ ^ 2) +
      2 * nu * (∑ i ∈ I, ew i h) * (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((16 * nu / delta) * (∑ i ∈ I, L i ^ 2) * (∫ x : T3, weight (S x) (w x) epsilon) + ∫ x : T3, B x)) := by
    simpa only [mul_zero, zero_mul, add_zero] using ht
  apply ge_of_tendsto ht'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact integral_joint_rate_le_at_increment I S w A b F B delta epsilon nu h L (fun i ↦ eS i h)
    (fun i ↦ ew i h) (fun i ↦ shift i h) hd heps hnu hL hh hS hw hF hB hpoint
    (hAp h hh) (hbp h hh) (hplus h hh) (hminus h hh)

end Mettapedia.FluidDynamics.NavierStokes.DepletedLaplacianDiffusion
