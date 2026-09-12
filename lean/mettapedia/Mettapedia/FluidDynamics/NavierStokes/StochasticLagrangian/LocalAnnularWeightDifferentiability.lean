import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularMeanBalance

/-!
# Almost-everywhere material differentiability of the two-endpoint cutoff

The cutoff itself, not just its product with the signed source, has a locally
Lipschitz real spacetime lift. Rademacher differentiability gives the frozen
material-line derivative almost everywhere in space and time. Threshold and
equal-amplitude sets are not assumed null.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularWeightDifferentiability

open scoped Topology
open MeasureTheory Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity LocalLowDiffusionBudget
open Mettapedia.Analysis SignedCrossKernel UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalAnnularMeanBalance

local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "X6" => Fin 3 ⊕ Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def amplitudeWeight (L : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  1 - lowAmplitudeWeight L (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x))

def frozenWeight (L : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (x : T6) (h : ℝ) : ℝ :=
  amplitudeWeight L (u (t + h)) (x + materialShift (productVelocity (u t) x) h)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hSum hu in
theorem continuous_extendedWeight (L : ℝ) (hL : 0 < L) :
    Continuous (fun z : ℝ × T6 ↦ amplitudeWeight L
      (LocalSpaceTimeExtension.coefficients s a b hab z.1) z.2) := by
  let time : ℝ → Icc (0 : ℝ) T := fun t ↦
    ⟨Set.projIcc a b hab t, Ioo_subset_Icc_self (hI (Set.projIcc a b hab t).2)⟩
  have ht : Continuous time :=
    (continuous_subtype_val.comp (LipschitzWith.projIcc hab).continuous).subtype_mk _
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hx := hw.comp (f := fun z : ℝ × T6 ↦ (time z.1, leftPoint z.2))
    ((ht.comp continuous_fst).prodMk (continuous_leftPoint.comp continuous_snd))
  have hy := hw.comp (f := fun z : ℝ × T6 ↦ (time z.1, rightPoint z.2))
    ((ht.comp continuous_fst).prodMk (continuous_rightPoint.comp continuous_snd))
  exact (lipschitzWith_highAmplitudeWeight L hL).continuous.comp
    (f := fun z : ℝ × T6 ↦
      (fullVorticity (s.coefficients (time z.1)) (leftPoint z.2),
       fullVorticity (s.coefficients (time z.1)) (rightPoint z.2))) (hx.prodMk hy)

include hI hg hSum hu in
theorem locallyLipschitz_extendedWeight (L : ℝ) (hL : 0 < L) :
    LocallyLipschitz (fun z : ℝ × X6 ↦ amplitudeWeight L
      (LocalSpaceTimeExtension.coefficients s a b hab z.1) (torusPoint z.2)) := by
  let w : ℝ × X3 → R3 := fun z ↦ fullVorticity
    (LocalSpaceTimeExtension.coefficients s a b hab z.1) (torusPoint z.2)
  have hw : LocallyLipschitz w :=
    LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu
  have hx : LocallyLipschitz (fun z : ℝ × X6 ↦ fun i : Fin 3 ↦ z.2 (Sum.inl i)) :=
    lipschitzWith_restrict_left.locallyLipschitz.comp LipschitzWith.prod_snd.locallyLipschitz
  have hy : LocallyLipschitz (fun z : ℝ × X6 ↦ fun i : Fin 3 ↦ z.2 (Sum.inr i)) :=
    lipschitzWith_restrict_right.locallyLipschitz.comp LipschitzWith.prod_snd.locallyLipschitz
  have hwx := hw.comp (g := fun z : ℝ × X6 ↦ (z.1, fun i ↦ z.2 (Sum.inl i)))
    (LipschitzWith.prod_fst.locallyLipschitz.prodMk hx)
  have hwy := hw.comp (g := fun z : ℝ × X6 ↦ (z.1, fun i ↦ z.2 (Sum.inr i)))
    (LipschitzWith.prod_fst.locallyLipschitz.prodMk hy)
  exact (lipschitzWith_highAmplitudeWeight L hL).locallyLipschitz.comp
    (g := fun z : ℝ × X6 ↦
      (w (z.1, fun i ↦ z.2 (Sum.inl i)), w (z.1, fun i ↦ z.2 (Sum.inr i))))
    (hwx.prodMk hwy)

include hI hg hSum hu in
theorem ae_ae_differentiableAt_extendedFrozenWeight (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T6,
      DifferentiableAt ℝ (frozenWeight L (LocalSpaceTimeExtension.coefficients s a b hab) t x) 0 :=
  ae_ae_differentiableAt_materialLine
    (fun t ↦ amplitudeWeight L (LocalSpaceTimeExtension.coefficients s a b hab t))
    (fun t ↦ productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedWeight s a b hab hI g hSum hu L hL)
    (fun _ ↦ continuous_productVelocity _)
    (locallyLipschitz_extendedWeight s a b hab hI g hg hSum hu L hL)

theorem frozenWeight_extension_eq (L t : ℝ) (ht : t ∈ Ioo a b) (x : T6) :
    frozenWeight L (LocalSpaceTimeExtension.coefficients s a b hab) t x =ᶠ[𝓝 0]
      frozenWeight L s.coefficients t x := by
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  simp only [frozenWeight, LocalSpaceTimeExtension.coefficients_eq s a b hab (t + h) hh,
    LocalSpaceTimeExtension.coefficients_eq s a b hab t (Ioo_subset_Icc_self ht)]

include hab hI hg hSum hu in
theorem ae_ae_differentiableAt_frozenWeight (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → ∀ᵐ x : T6,
      DifferentiableAt ℝ (frozenWeight L s.coefficients t x) 0 := by
  filter_upwards [ae_ae_differentiableAt_extendedFrozenWeight s a b hab hI g hg hSum hu L hL]
    with t ht htab
  exact ht.mono (fun x hx ↦ hx.congr_of_eventuallyEq
    (frozenWeight_extension_eq s a b hab L t htab x).symm)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularWeightDifferentiability
