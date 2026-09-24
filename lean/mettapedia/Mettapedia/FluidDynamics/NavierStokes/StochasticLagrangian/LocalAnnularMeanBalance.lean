import Mettapedia.Analysis.UnitTorusProductTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourcePathIntegral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourceContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMeanAlignmentBalance

/-!
# Spatial material balance of the signed two-point annular source

Both endpoints are transported by the actual full velocity. Their product
velocity is incompressible, so the mean material derivative is exactly the
time derivative of the signed high-amplitude source. The cutoff interfaces
are retained by the locally Lipschitz weak chain rule.

The constant time extension is only a calculus device on a compact interior
interval. No global solution, cutoff-uniform estimate, or identification with
the expanded strain/diffusion rate is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance

open scoped Topology ContDiff
open MeasureTheory Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity LocalLowDiffusionBudget
open Mettapedia.Analysis SignedCrossKernel UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "X6" => Fin 3 ⊕ Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def density (n N : ℕ) (L : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * highAmplitudeStretch (2 * n) L
    (PeriodicRieszPolynomial.kernel N (leftPoint x - rightPoint x))
    (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x))

def productVelocity (u : FourierVelocity) : T6 → X6 :=
  pairVelocity (fun x j ↦ LocalMeanAlignmentBalance.velocity u x j)
    (fun x j ↦ LocalMeanAlignmentBalance.velocity u x j)

/-- An actual derivative along the two instantaneous full velocities. -/
def frozenMaterialRate (n N : ℕ) (L : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : T6 → ℝ :=
  scalarMaterialRate (fun τ ↦ density n N L (u τ)) (productVelocity (u t)) t

theorem continuous_productVelocity (u : FourierVelocity) : Continuous (productVelocity u) := by
  apply continuous_pairVelocity <;> apply continuous_pi <;> intro j <;>
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp
      (LocalMeanAlignmentBalance.continuous_velocity u)

theorem integral_density_eq (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T6, density n N L u x) =
      VorticityAnnularPolynomialSource.highAmplitudeSource (2 * n) L N u := by
  have hc := continuous_highAmplitudeStretch
    (fun x y : T3 ↦ PeriodicRieszPolynomial.kernel N (x - y))
    (fullVorticity u)
    ((PeriodicRieszPolynomial.continuous_kernel N).comp (continuous_fst.sub continuous_snd))
    (continuous_fullVorticity u hu) (2 * n) L hL
  simp only [density]
  rw [integral_const_mul, UnitTorusProductTransport.integral_pair
    (fun x y : T3 ↦ highAmplitudeStretch (2 * n) L (PeriodicRieszPolynomial.kernel N (x - y))
      (fullVorticity u x) (fullVorticity u y)) (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  rfl

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hSum hu in
theorem continuous_extendedDensity (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    Continuous (fun z : ℝ × T6 ↦ density n N L
      (LocalSpaceTimeExtension.coefficients s a b hab z.1) z.2) := by
  let time : ℝ → Icc (0 : ℝ) T := fun t ↦
    ⟨Set.projIcc a b hab t, Ioo_subset_Icc_self (hI (Set.projIcc a b hab t).2)⟩
  have ht : Continuous time :=
    (continuous_subtype_val.comp (LipschitzWith.projIcc hab).continuous).subtype_mk _
  have hd := LocalAnnularSourceContinuity.continuous_highAmplitudeDensity
    s g hSum hu (2 * n) N L hL
  have hp : Continuous (fun z : ℝ × T6 ↦ (time z.1, (leftPoint z.2, rightPoint z.2))) :=
    (ht.comp continuous_fst).prodMk
      ((continuous_leftPoint.comp continuous_snd).prodMk (continuous_rightPoint.comp continuous_snd))
  exact (hd.comp hp).const_mul (1 / 2 : ℝ)

include hI hg hSum hu in
theorem locallyLipschitz_extendedDensity (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    LocallyLipschitz (fun z : ℝ × X6 ↦ density n N L
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
  have hk : LocallyLipschitz (fun r : X3 ↦ PeriodicRieszPolynomial.kernel N (torusPoint r)) :=
    ((VorticityAnnularKernelTransport.contDiff_kernel_lift N).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz
  have hkernel : LocallyLipschitz (fun z : ℝ × X6 ↦
      PeriodicRieszPolynomial.kernel N
        (leftPoint (torusPoint z.2) - rightPoint (torusPoint z.2))) := by
    exact hk.comp (g := fun z : ℝ × X6 ↦
      (fun i ↦ z.2 (Sum.inl i)) - (fun i ↦ z.2 (Sum.inr i))) (hx.sub hy)
  exact (LocallyLipschitz.const (1 / 2 : ℝ)).mul_algebra
    (locallyLipschitz_highAmplitudeStretch_even n hL hkernel hwx hwy)

include hI hSum hu in
theorem locallyLipschitz_extendedProductVelocity (t : ℝ) (j : Fin 3 ⊕ Fin 3) :
    LocallyLipschitz (fun r : X6 ↦ productVelocity
      (LocalSpaceTimeExtension.coefficients s a b hab t) (torusPoint r) j) :=
  locallyLipschitz_pairVelocity _ _
    (LocalMeanAlignmentBalance.locallyLipschitz_extendedVelocity s a b hab hI g hSum hu t)
    (LocalMeanAlignmentBalance.locallyLipschitz_extendedVelocity s a b hab hI g hSum hu t) j

include hI hSum hu in
theorem divergence_extendedProductVelocity (t : ℝ) (x : T6) :
    coordinateDivergence (fun j y ↦ productVelocity
      (LocalSpaceTimeExtension.coefficients s a b hab t) y j) x = 0 := by
  rw [productVelocity, coordinateDivergence_pairVelocity]
  have hx := LocalMeanAlignmentBalance.divergence_extendedVelocity s a b hab hI g hSum hu t
    (leftPoint x)
  have hy := LocalMeanAlignmentBalance.divergence_extendedVelocity s a b hab hI g hSum hu t
    (rightPoint x)
  have he (v : Fin 3 → T3 → ℝ) (y : T3) : coordinateDivergence v y =
      PancakeWeakIncompressibleTransport.coordinateDivergence v y := rfl
  rw [he, he, hx, hy, add_zero]

include hI hg hSum hu in
theorem ae_hasDerivAt_extendedMean (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ,
      Integrable (frozenMaterialRate n N L (LocalSpaceTimeExtension.coefficients s a b hab) t) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6,
        density n N L (LocalSpaceTimeExtension.coefficients s a b hab τ) x)
        (∫ x : T6, frozenMaterialRate n N L
          (LocalSpaceTimeExtension.coefficients s a b hab) t x) t :=
  ae_hasDerivAt_mean_materialRate _ _
    (continuous_extendedDensity s a b hab hI g hSum hu n N L hL)
    (fun _ ↦ continuous_productVelocity _)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu n N L hL)
    (locallyLipschitz_extendedProductVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall
      (divergence_extendedProductVelocity s a b hab hI g hSum hu t))

/-- The calculus extension agrees with the original material rate inside the interval. -/
theorem frozenMaterialRate_extension_eq (n N : ℕ) (L t : ℝ)
    (ht : t ∈ Ioo a b) (x : T6) :
    frozenMaterialRate n N L (LocalSpaceTimeExtension.coefficients s a b hab) t x =
      frozenMaterialRate n N L s.coefficients t x := by
  unfold frozenMaterialRate scalarMaterialRate
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab t (Ioo_subset_Icc_self ht)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab (t + h) hh]

include hab hI hg hSum hu in
theorem absolutelyContinuousOnInterval_mean (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x : T6, density n N L (s.coefficients t) x) a b := by
  have hac := UnitTorusMaterialBalance.absolutelyContinuousOnInterval_mean
    (fun t ↦ density n N L (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu n N L hL)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu n N L hL) a b
  apply AbsolutelyContinuousComposition.congr hac
  intro t ht
  dsimp only
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab t (by simpa only [uIcc_of_le hab] using ht)]

include hab hI hg hSum hu in
theorem ae_hasDerivAt_mean (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b →
      Integrable (frozenMaterialRate n N L s.coefficients t) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6, density n N L (s.coefficients τ) x)
        (∫ x : T6, frozenMaterialRate n N L s.coefficients t x) t := by
  filter_upwards [ae_hasDerivAt_extendedMean s a b hab hI g hg hSum hu n N L hL]
    with t hd ht
  have he := funext (frozenMaterialRate_extension_eq s a b hab n N L t ht)
  rw [he] at hd
  refine ⟨hd.1, hd.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab τ hτ]

include hab hI hg hSum hu in
/-- Signed endpoint balance, with time integrability derived from the actual local fields. -/
theorem integral_frozenMaterialRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ ∫ x : T6, frozenMaterialRate n N L s.coefficients t x) volume a b ∧
      (∫ t in a..b, ∫ x : T6, frozenMaterialRate n N L s.coefficients t x) =
        VorticityAnnularPolynomialSource.highAmplitudeSource (2 * n) L N (s.coefficients b) -
          VorticityAnnularPolynomialSource.highAmplitudeSource (2 * n) L N (s.coefficients a) := by
  have h := UnitTorusMaterialBalance.intervalIntegral_materialRate_eq
    (fun t ↦ density n N L (LocalSpaceTimeExtension.coefficients s a b hab t))
    (fun t ↦ productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu n N L hL)
    (fun _ ↦ continuous_productVelocity _)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu n N L hL)
    (locallyLipschitz_extendedProductVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall
      (divergence_extendedProductVelocity s a b hab hI g hSum hu t)) a b
  have he : Set.EqOn
      (fun t ↦ ∫ x : T6, frozenMaterialRate n N L (LocalSpaceTimeExtension.coefficients s a b hab) t x)
      (fun t ↦ ∫ x : T6, frozenMaterialRate n N L s.coefficients t x) (uIoo a b) := by
    intro t ht
    exact integral_congr_ae (Filter.Eventually.of_forall
      (frozenMaterialRate_extension_eq s a b hab n N L t (by simpa only [uIoo_of_le hab] using ht)))
  have hm (t : ℝ) : (∫ x : T6, density n N L
      (LocalSpaceTimeExtension.coefficients s a b hab t) x) =
      VorticityAnnularPolynomialSource.highAmplitudeSource (2 * n) L N
        (LocalSpaceTimeExtension.coefficients s a b hab t) :=
    integral_density_eq n N L hL _
      (LocalSpaceTimeExtension.summable_moment s a b hab hI g hSum hu 1 (by omega) t)
  refine ⟨h.1.congr_uIoo he, (intervalIntegral.integral_congr_uIoo he).symm.trans ?_⟩
  have hresult := h.2
  rw [hm b, hm a] at hresult
  simpa only [frozenMaterialRate, LocalSpaceTimeExtension.coefficients_eq s a b hab b ⟨hab, le_rfl⟩,
    LocalSpaceTimeExtension.coefficients_eq s a b hab a ⟨le_rfl, hab⟩] using hresult

include hab hI hg hSum hu in
/-- Exact time-integrated signed source, without a pointwise absolute envelope. -/
theorem integral_source_eq_initial_add_weighted_rate (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun t ↦ (b - t) *
      ∫ x : T6, frozenMaterialRate n N L s.coefficients t x) volume a b ∧
      (∫ t in a..b, VorticityAnnularPolynomialSource.highAmplitudeSource
        (2 * n) L N (s.coefficients t)) =
        (b - a) * VorticityAnnularPolynomialSource.highAmplitudeSource
          (2 * n) L N (s.coefficients a) +
            ∫ t in a..b, (b - t) * ∫ x : T6, frozenMaterialRate n N L s.coefficients t x := by
  have h := AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (absolutelyContinuousOnInterval_mean s a b hab hI g hg hSum hu n N L hL)
    ((ae_hasDerivAt_mean s a b hab hI g hg hSum hu n N L hL).mono (fun t ht hmem ↦ (ht hmem).2))
  have hm (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x : T6, density n N L (s.coefficients t) x) =
        VorticityAnnularPolynomialSource.highAmplitudeSource (2 * n) L N (s.coefficients t) :=
    integral_density_eq n N L hL _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI ht)))))
  have hi : (∫ t in a..b, ∫ x : T6, density n N L (s.coefficients t) x) =
      ∫ t in a..b, VorticityAnnularPolynomialSource.highAmplitudeSource
        (2 * n) L N (s.coefficients t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hm t (by simpa only [uIcc_of_le hab] using ht)
  exact ⟨h.1, by simpa only [hi, hm a ⟨le_rfl, hab⟩] using h.2⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance
