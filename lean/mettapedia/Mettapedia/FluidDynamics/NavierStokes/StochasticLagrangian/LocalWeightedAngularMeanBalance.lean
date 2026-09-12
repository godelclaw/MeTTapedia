import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedAngularMeanRegularity

/-!
# Actual time-integrated evolution of the weighted angular mean

The nonsmooth scalar kernel is differentiated only where its material
derivative exists; local Lipschitz regularity proves this almost everywhere.
The endpoint rate is the actual vorticity equation. Incompressibility and
absolute continuity give exact signed identities on interior time intervals.
No cutoff-uniform or singular-time bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularMeanBalance

open scoped Topology
open MeasureTheory Set
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeCurlOutputTail
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget
open Mettapedia.Analysis WeightedCrossProduct UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalWeightedAngularMeanRegularity
open LocalWeightedAngularEvolution (pairEnergy materialPairRate symmetricAngularIntegral)
open LocalAnnularMeanBalance (productVelocity continuous_productVelocity
  locallyLipschitz_extendedProductVelocity divergence_extendedProductVelocity)
open LocalAnnularExplicitRate (tangentPath tangentPath_self hasDerivAt_tangentPath
  leftPoint_frozenShift rightPoint_frozenShift)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "X6" => Fin 3 ⊕ Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def kernelDensity (N : ℕ) (x : T6) : ℝ := kernelWeight N (leftPoint x - rightPoint x)

def frozenKernel (N : ℕ) (u : FourierVelocity) (x : T6) (h : ℝ) : ℝ :=
  kernelDensity N (x + materialShift (productVelocity u x) h)

def kernelRate (N : ℕ) (u : FourierVelocity) (x : T6) : ℝ := deriv (frozenKernel N u x) 0

theorem frozenKernel_eq_relativeShift (N : ℕ) (u : FourierVelocity) (x : T6) (h : ℝ) :
    frozenKernel N u x h = kernelWeight N (leftPoint x - rightPoint x +
      materialShift ((fun j ↦ LocalMeanAlignmentBalance.velocity u (leftPoint x) j) -
        (fun j ↦ LocalMeanAlignmentBalance.velocity u (rightPoint x) j)) h) := by
  unfold frozenKernel kernelDensity
  congr 1
  ext j
  simp only [leftPoint, rightPoint, Pi.add_apply, Pi.sub_apply, materialShift,
    productVelocity, pairVelocity, Sum.elim_inl, Sum.elim_inr, torusPoint, mul_sub,
    QuotientAddGroup.mk_sub]
  abel

def explicitRate (N : ℕ) (nu : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  kernelRate N u x * pairEnergy 2 u (leftPoint x) (rightPoint x) +
    kernelDensity N x * materialPairRate 2 u nu (leftPoint x) (rightPoint x)

def meanRate (N : ℕ) (nu : ℝ) (u : FourierVelocity) : ℝ := ∫ x : T6, explicitRate N nu u x

theorem continuous_kernelDensity (N : ℕ) : Continuous (kernelDensity N) :=
  (continuous_kernelWeight N).comp (continuous_leftPoint.sub continuous_rightPoint)

theorem locallyLipschitz_kernelDensity (N : ℕ) :
    LocallyLipschitz (fun z : ℝ × X6 ↦ kernelDensity N (torusPoint z.2)) := by
  have hx : LocallyLipschitz (fun z : ℝ × X6 ↦ fun i : Fin 3 ↦ z.2 (Sum.inl i)) :=
    lipschitzWith_restrict_left.locallyLipschitz.comp LipschitzWith.prod_snd.locallyLipschitz
  have hy : LocallyLipschitz (fun z : ℝ × X6 ↦ fun i : Fin 3 ↦ z.2 (Sum.inr i)) :=
    lipschitzWith_restrict_right.locallyLipschitz.comp LipschitzWith.prod_snd.locallyLipschitz
  exact (locallyLipschitz_kernelWeight_lift N).comp
    (g := fun z : ℝ × X6 ↦ (fun i ↦ z.2 (Sum.inl i)) - (fun i ↦ z.2 (Sum.inr i))) (hx.sub hy)

theorem ae_differentiableAt_frozenKernel (N : ℕ) (u : ℝ → FourierVelocity) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T6, DifferentiableAt ℝ (frozenKernel N (u t) x) 0 :=
  ae_ae_differentiableAt_materialLine (fun _ ↦ kernelDensity N) (fun t ↦ productVelocity (u t))
    ((continuous_kernelDensity N).comp continuous_snd) (fun _ ↦ continuous_productVelocity _)
    (locallyLipschitz_kernelDensity N)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu

theorem frozenMaterialRate_eq (N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : T6)
    (hK : DifferentiableAt ℝ (frozenKernel N (s.coefficients t) x) 0) :
    frozenMaterialRate N s.coefficients t x = explicitRate N nu (s.coefficients t) x := by
  obtain ⟨r, hr, _⟩ := torusPoint_bounded_rep (leftPoint x)
  obtain ⟨q, hq, _⟩ := torusPoint_bounded_rep (rightPoint x)
  let X := tangentPath s t r
  let Y := tangentPath s t q
  have hX : HasDerivAt X (liftedVelocity s t (X t)) t := hasDerivAt_tangentPath s t r
  have hY : HasDerivAt Y (liftedVelocity s t (Y t)) t := hasDerivAt_tangentPath s t q
  have hleft (h : ℝ) := leftPoint_frozenShift s t x r hr h
  have hright (h : ℝ) := rightPoint_frozenShift s t x q hq h
  have hp := LocalWeightedAngularEvolution.hasDerivAt_pairEnergy_path
    s g hg hSum hu a b hab hI X Y t ht hX hY 2
  have hp' := hp.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add t) (by simp)
  have htorus : PancakeFourierMaterialPaths.torusPoint = (torusPoint : X3 → T3) := rfl
  have hE : HasDerivAt (fun h ↦ pairEnergy 2 (s.coefficients (t + h))
      (leftPoint (x + materialShift (productVelocity (s.coefficients t) x) h))
      (rightPoint (x + materialShift (productVelocity (s.coefficients t) x) h)))
      (materialPairRate 2 (s.coefficients t) nu (leftPoint x) (rightPoint x)) 0 := by
    simpa only [htorus, Function.comp_def, id_eq, hleft, hright,
      X, Y, tangentPath_self, mul_one, hr, hq] using hp'
  have hd := hK.hasDerivAt.fun_mul hE
  have hs : materialShift (productVelocity (s.coefficients t) x) 0 = 0 := by
    ext j
    simp [materialShift, torusPoint]
  have hf : HasDerivAt (fun h ↦ density N (s.coefficients (t + h))
      (x + materialShift (productVelocity (s.coefficients t) x) h))
      (explicitRate N nu (s.coefficients t) x) 0 := by
    simpa only [density, frozenKernel, kernelDensity, kernelRate, explicitRate, hs, add_zero] using hd
  exact hf.deriv

theorem ae_hasDerivAt_mean (N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → Integrable (explicitRate N nu (s.coefficients t)) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6, density N (s.coefficients τ) x)
        (meanRate N nu (s.coefficients t)) t := by
  have h := ae_hasDerivAt_mean_materialRate
    (fun t ↦ density N (LocalSpaceTimeExtension.coefficients s a b hab t))
    (fun t ↦ productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu N)
    (fun _ ↦ continuous_productVelocity _)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu N)
    (locallyLipschitz_extendedProductVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall (divergence_extendedProductVelocity s a b hab hI g hSum hu t))
  filter_upwards [h, ae_differentiableAt_frozenKernel N s.coefficients] with t hd hK ht
  have he : frozenMaterialRate N (LocalSpaceTimeExtension.coefficients s a b hab) t =ᵐ[volume]
      explicitRate N nu (s.coefficients t) := by
    filter_upwards [hK] with x hx
    rw [frozenMaterialRate_extension_eq s a b hab N t ht x,
      frozenMaterialRate_eq s a b hab hI g hg hSum hu N t ht x hx]
  change Integrable (frozenMaterialRate N (LocalSpaceTimeExtension.coefficients s a b hab) t) ∧
    HasDerivAt _ (∫ x : T6, frozenMaterialRate N
      (LocalSpaceTimeExtension.coefficients s a b hab) t x) t at hd
  rw [integral_congr_ae he] at hd
  refine ⟨hd.1.congr he, hd.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab τ hτ]

theorem integral_angular_eq_initial_add_weighted_rate (N : ℕ) :
    IntervalIntegrable (fun t ↦ (b - t) * meanRate N nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, symmetricAngularIntegral N (s.coefficients t)) =
        (b - a) * symmetricAngularIntegral N (s.coefficients a) +
          ∫ t in a..b, (b - t) * meanRate N nu (s.coefficients t) := by
  have h := AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (absolutelyContinuousOnInterval_mean s a b hab hI g hg hSum hu N)
    ((ae_hasDerivAt_mean s a b hab hI g hg hSum hu N).mono (fun t ht hmem ↦ (ht hmem).2))
  have hm (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x : T6, density N (s.coefficients t) x) = symmetricAngularIntegral N (s.coefficients t) :=
    integral_density_eq N _ (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI ht)))))
  have hi : (∫ t in a..b, ∫ x : T6, density N (s.coefficients t) x) =
      ∫ t in a..b, symmetricAngularIntegral N (s.coefficients t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hm t (by simpa only [uIcc_of_le hab] using ht)
  exact ⟨h.1, by simpa only [hi, hm a ⟨le_rfl, hab⟩] using h.2⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularMeanBalance
