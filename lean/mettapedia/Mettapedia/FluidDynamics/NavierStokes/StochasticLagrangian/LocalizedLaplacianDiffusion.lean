import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalizedDiffusionIncrement

/-!
# Collision-safe joint diffusion with local strain-gradient density

The spatial weak limit retains actual first-derivative norms under the
integral. Global Lipschitz constants are used for domination only.
Full-rate integrability is retained; coordinate rates are not integrated.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalizedLaplacianDiffusion

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory PancakeHaarDiffusionIncrement PancakeRegularizedMaterialRate
open PancakeWeakDiffusionLimit PancakeRegularizedDiffusion PancakeSpectralProjectorRegularity
open DepletedLaplacianDiffusion SpectralDiffusionWeight LocalizedDiffusionIncrement

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_joint_rate_le_centralUpper {ι : Type*} (I : Finset ι)
    (S : T3 → SymmetricStrain) (w : T3 → R3)
    (A : ι → T3 → R3 →L[ℝ] R3) (b : ι → T3 → R3)
    (F B : T3 → ℝ) (delta epsilon nu h : ℝ) (eS ew : ι → ℝ) (s : ι → T3)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (S x) delta (w x)
      (∑ i ∈ I, A i x) (∑ i ∈ I, b i x) + B x)
    (hAp : ∀ i ∈ I, ∀ x, ‖A i x - centralDirection (fun y ↦ (S y).1) (s i) h x‖ ≤ eS i)
    (hbp : ∀ i ∈ I, ∀ x, ‖b i x - centralDirection w (s i) h x‖ ≤ ew i) :
    (∫ x : T3, F x) ≤ nu * (∑ i ∈ I, ∫ x : T3, centralUpper S w delta epsilon h (s i) x) +
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
    rw [PancakeLaplacianDiffusion.linearRate_sum] at hx
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
  nlinarith

theorem tendsto_integral_centralUpper (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta epsilon L : ℝ) (shift : ℝ → T3) (G : T3 → R3 →L[ℝ] R3)
    (heps : 0 < epsilon) (hL : 0 ≤ L) (hS : Continuous S) (hw : Continuous w)
    (hzero : shift 0 = 0)
    (hG : ∀ x, HasDerivAt (fun h ↦ (S (x + shift h)).1) (G x) 0)
    (hGneg : ∀ x, HasDerivAt (fun h ↦ (S (x + -(shift h))).1) (-G x) 0)
    (hp : ∀ h ≠ 0, ∀ x, ‖(S (x + shift h)).1 - (S x).1‖ ≤ L * |h|)
    (hm : ∀ h ≠ 0, ∀ x, ‖(S (x + -(shift h))).1 - (S x).1‖ ≤ L * |h|) :
    Tendsto (fun h ↦ ∫ x : T3, centralUpper S w delta epsilon h (shift h) x) (𝓝[≠] (0 : ℝ))
      (𝓝 ((16 / delta) * ∫ x : T3, ‖G x‖ ^ 2 * weight (S x) (w x) epsilon)) := by
  have hplus := tendsto_integral_normalizedShiftCost S w epsilon L shift G heps hL hS hw hzero hG hp
  have hminus := tendsto_integral_normalizedShiftCost S w epsilon L (fun h ↦ -(shift h))
    (fun x ↦ -G x) heps hL hS hw (by simp only [hzero, neg_zero]) hGneg hm
  simp only [norm_neg] at hminus
  have h := (hplus.add hminus).const_mul (8 / delta)
  have he : (8 / delta) * ((∫ x : T3, ‖G x‖ ^ 2 * weight (S x) (w x) epsilon) +
      (∫ x : T3, ‖G x‖ ^ 2 * weight (S x) (w x) epsilon)) =
      (16 / delta) * ∫ x : T3, ‖G x‖ ^ 2 * weight (S x) (w x) epsilon := by ring
  rw [he] at h
  exact h.congr' (Eventually.of_forall (fun h ↦ (integral_centralUpper_eq S w delta epsilon h (shift h) heps hS hw).symm))

theorem integral_joint_rate_le_of_first_second_approx {ι : Type*} (I : Finset ι)
    (S : T3 → SymmetricStrain) (w : T3 → R3)
    (G A : ι → T3 → R3 →L[ℝ] R3) (b : ι → T3 → R3)
    (F B : T3 → ℝ) (delta epsilon nu : ℝ) (L : ι → ℝ) (shift : ι → ℝ → T3) (eS ew : ι → ℝ → ℝ)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu) (hL : ∀ i ∈ I, 0 ≤ L i)
    (hS : Continuous S) (hw : Continuous w) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (S x) delta (w x)
      (∑ i ∈ I, A i x) (∑ i ∈ I, b i x) + B x)
    (hzero : ∀ i ∈ I, shift i 0 = 0)
    (hG : ∀ i ∈ I, ∀ x, HasDerivAt (fun h ↦ (S (x + shift i h)).1) (G i x) 0)
    (hGneg : ∀ i ∈ I, ∀ x, HasDerivAt (fun h ↦ (S (x + -(shift i h))).1) (-G i x) 0)
    (hAp : ∀ h ≠ 0, ∀ i ∈ I, ∀ x,
      ‖A i x - centralDirection (fun y ↦ (S y).1) (shift i h) h x‖ ≤ eS i h)
    (hbp : ∀ h ≠ 0, ∀ i ∈ I, ∀ x, ‖b i x - centralDirection w (shift i h) h x‖ ≤ ew i h)
    (hplus : ∀ h ≠ 0, ∀ i ∈ I, ∀ x, ‖(S (x + shift i h)).1 - (S x).1‖ ≤ L i * |h|)
    (hminus : ∀ h ≠ 0, ∀ i ∈ I, ∀ x, ‖(S (x + -(shift i h))).1 - (S x).1‖ ≤ L i * |h|)
    (heS : ∀ i ∈ I, Tendsto (eS i) (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hew : ∀ i ∈ I, Tendsto (ew i) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) *
      (∑ i ∈ I, ∫ x : T3, ‖G i x‖ ^ 2 * weight (S x) (w x) epsilon) + ∫ x : T3, B x := by
  have htU := tendsto_finsetSum I (fun i hi ↦ tendsto_integral_centralUpper S w delta epsilon
    (L i) (shift i) (G i) heps (hL i hi) hS hw (hzero i hi) (hG i hi) (hGneg i hi)
    (fun h hh x ↦ hplus h hh i hi x) (fun h hh x ↦ hminus h hh i hi x))
  have htS : Tendsto (fun h ↦ ∑ i ∈ I, eS i h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum I heS
  have htw : Tendsto (fun h ↦ ∑ i ∈ I, ew i h) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum I hew
  have ht := (((htU.const_mul nu).add_const (∫ x : T3, B x)).add
    ((htS.const_mul (2 * nu)).mul_const (∫ x : T3, ‖w x‖ ^ 2))).add
    ((htw.const_mul (2 * nu)).mul_const (∫ x : T3, ‖regularizedGap (S x) delta (w x)‖))
  have he : nu * (∑ i ∈ I, (16 / delta) * (∫ x : T3, ‖G i x‖ ^ 2 * weight (S x) (w x) epsilon)) =
      (16 * nu / delta) * (∑ i ∈ I, ∫ x : T3, ‖G i x‖ ^ 2 * weight (S x) (w x) epsilon) := by
    rw [← Finset.mul_sum]
    ring
  simp only [mul_zero, zero_mul, add_zero, he] at ht
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact integral_joint_rate_le_centralUpper I S w A b F B delta epsilon nu h (fun i ↦ eS i h)
    (fun i ↦ ew i h) (fun i ↦ shift i h) hd heps hnu hS hw hF hB hpoint (hAp h hh) (hbp h hh)

end Mettapedia.FluidDynamics.NavierStokes.LocalizedLaplacianDiffusion
