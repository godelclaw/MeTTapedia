import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnisotropyDepletion

/-!
# Weight transport vanishes on the full top eigenspace

At a repeated largest eigenvalue, alignment with one chosen eigenline
is unnecessarily restrictive. Positivity of the actual spectral gap
operator implies that its quadratic derivative vanishes on its entire
kernel wherever the operator derivative exists. This gives an almost-
everywhere statement for physical strain-weight transport through collisions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeTopSpaceTransport

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeWeightVariationGradient PancakePhysicalWeightedTransport
open PancakePhysicalSpectralDefect PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeRegularizedDiffusion PancakeFourierTranslationCurve PancakeHaarTransportRate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem quadratic_rate_zero_on_kernel (K : ℝ → H →L[ℝ] H) (G : H →L[ℝ] H) (t : ℝ) (w : H)
    (hd : HasDerivAt K G t) (hpos : ∀ s, 0 ≤ ⟪w, K s w⟫) (hz : K t w = 0) :
    ⟪w, G w⟫ = 0 := by
  have hq := (hasDerivAt_const t w).inner ℝ (hd.clm_apply (hasDerivAt_const t w))
  simp only [inner_zero_left, map_zero, add_zero] at hq
  have hm : IsLocalMin (fun s ↦ ⟪w, K s w⟫) t := by
    apply Filter.Eventually.of_forall
    intro s
    change ⟪w, K t w⟫ ≤ ⟪w, K s w⟫
    rw [hz, inner_zero_right]
    exact hpos s
  exact hm.hasDerivAt_eq_zero hq

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ae_physicalGapGradient_zero_on_topSpace
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) :
    ∀ᵐ x : T3, ∀ w : R3, physicalGapWeight chi modes u 0 x w = 0 →
      ∀ j : Fin 3, ⟪w, physicalGapGradient chi modes u x j w⟫ = 0 := by
  filter_upwards [ae_hasDerivAt_physicalGapWeight chi modes u 0] with x hx
  intro w hw j
  apply quadratic_rate_zero_on_kernel _ _ 0 w (hx j)
  · intro s
    simpa only [zero_mul, physicalGapWeight] using regularizedGap_coercive
      (spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j s)) 0 w
  · simpa only [coordinateShift_zero, add_zero] using hw

theorem ae_physicalWeightVariation_zero_on_topSpace
    (chi beta : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, physicalGapWeight chi modes u 0 x (spatialVorticity modes u x) = 0 →
      physicalWeightVariation chi beta modes u delta x = 0 := by
  filter_upwards [ae_physicalWeightVariation_eq chi beta modes u delta,
    ae_physicalGapGradient_zero_on_topSpace chi modes u] with x hx hg hw
  rw [hx]
  simp only [hg _ hw, mul_zero, Finset.sum_const_zero]

end Mettapedia.FluidDynamics.NavierStokes.PancakeTopSpaceTransport
