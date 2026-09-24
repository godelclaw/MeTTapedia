import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedAngularDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularExplicitRate
import Mettapedia.Analysis.UnitTorusPairIntegration

/-!
# Regularity of the actual weighted angular mean

The continuous finite Fourier representative has the same integral as the
constructed kernel. Its norm and the torus distance are only locally
Lipschitz; no differentiability at their singular sets is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularMeanRegularity

open scoped Topology ContDiff
open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget
open Mettapedia.Analysis WeightedCrossProduct UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalWeightedAngularEvolution (pairEnergy symmetricAngularIntegral)
open LocalAnnularMeanBalance (productVelocity)

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

def kernelWeight (N : ℕ) (h : T3) : ℝ := ‖h‖ * ‖PeriodicRieszPolynomial.kernel N h‖

theorem continuous_kernelWeight (N : ℕ) : Continuous (kernelWeight N) :=
  continuous_norm.mul (PeriodicRieszPolynomial.continuous_kernel N).norm

theorem locallyLipschitz_kernelWeight_lift (N : ℕ) :
    LocallyLipschitz (fun r : X3 ↦ kernelWeight N (torusPoint r)) := by
  have hK := ((VorticityAnnularKernelTransport.contDiff_kernel_lift N).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).locallyLipschitz
  exact ((lipschitzWith_one_norm.comp lipschitzWith_torusPoint).locallyLipschitz).mul_algebra
    (lipschitzWith_one_norm.locallyLipschitz.comp hK)

def density (N : ℕ) (u : FourierVelocity) (x : T6) : ℝ :=
  kernelWeight N (leftPoint x - rightPoint x) * pairEnergy 2 u (leftPoint x) (rightPoint x)

def frozenMaterialRate (N : ℕ) (u : ℝ → FourierVelocity) (t : ℝ) : T6 → ℝ :=
  scalarMaterialRate (fun τ ↦ density N (u τ)) (productVelocity (u t)) t

theorem integral_density_eq (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T6, density N u x) = symmetricAngularIntegral N u := by
  have hc : Continuous (fun p : T3 × T3 ↦ kernelWeight N (p.1 - p.2) * pairEnergy 2 u p.1 p.2) :=
    ((continuous_kernelWeight N).comp (continuous_fst.sub continuous_snd)).mul
      (LocalWeightedAngularEvolution.continuous_pairEnergy 2 u hu)
  rw [show (fun x : T6 ↦ density N u x) = (fun x ↦ kernelWeight N
    (leftPoint x - rightPoint x) * pairEnergy 2 u (leftPoint x) (rightPoint x)) from rfl,
    UnitTorusProductTransport.integral_pair (fun x y : T3 ↦ kernelWeight N (x - y) * pairEnergy 2 u x y)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    UnitTorusPairIntegration.integral_pair_eq_separation _ hc]
  simp only [sub_sub_cancel, kernelWeight, symmetricAngularIntegral]
  apply integral_congr_ae
  filter_upwards [PeriodicRieszPolynomial.kernel_ae_eq (d := 3) N] with h hh
  rw [hh]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hSum hu in
theorem continuous_extendedDensity (N : ℕ) :
    Continuous (fun z : ℝ × T6 ↦ density N
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
  have hp := (contDiff_energy 2).continuous.comp (hx.prodMk hy)
  exact ((continuous_kernelWeight N).comp
    ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))).mul hp

include hI hg hSum hu in
theorem locallyLipschitz_extendedDensity (N : ℕ) :
    LocallyLipschitz (fun z : ℝ × X6 ↦ density N
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
  have hkernel : LocallyLipschitz (fun z : ℝ × X6 ↦ kernelWeight N
      (leftPoint (torusPoint z.2) - rightPoint (torusPoint z.2))) :=
    (locallyLipschitz_kernelWeight_lift N).comp (g := fun z : ℝ × X6 ↦
      (fun i ↦ z.2 (Sum.inl i)) - (fun i ↦ z.2 (Sum.inr i))) (hx.sub hy)
  exact hkernel.mul_algebra (locallyLipschitz_energy 2 hwx hwy)

theorem frozenMaterialRate_extension_eq (N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : T6) :
    frozenMaterialRate N (LocalSpaceTimeExtension.coefficients s a b hab) t x =
      frozenMaterialRate N s.coefficients t x := by
  unfold frozenMaterialRate scalarMaterialRate
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab t (Ioo_subset_Icc_self ht)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab (t + h) hh]

include hab hI hg hSum hu in
theorem absolutelyContinuousOnInterval_mean (N : ℕ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x : T6, density N (s.coefficients t) x) a b := by
  have hac := UnitTorusMaterialBalance.absolutelyContinuousOnInterval_mean
    (fun t ↦ density N (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu N)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu N) a b
  apply AbsolutelyContinuousComposition.congr hac
  intro t ht
  dsimp only
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab t (by simpa only [uIcc_of_le hab] using ht)]

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularMeanRegularity
