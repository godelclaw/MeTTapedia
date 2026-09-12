import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSmoothSourceEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularMeanBalance

/-!
# Actual spacetime regularity for the retained two-point mean

The constant time extension is a local calculus device on a compact interior
interval. The product velocity is the existing actual incompressible velocity.
Neither a global extension nor a uniform nonlinear bound is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothMeanRegularity

open scoped Topology ContDiff
open MeasureTheory Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity LocalLowDiffusionBudget
open Mettapedia.Analysis SmoothAmplitudePairing UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
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

def density (n N : ℕ) (L : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * retainedStretch (2 * n) L
    (PeriodicRieszPolynomial.kernel N (leftPoint x - rightPoint x))
    (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x))

def frozenMaterialRate (n N : ℕ) (L : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : T6 → ℝ :=
  scalarMaterialRate (fun τ ↦ density n N L (u τ)) (productVelocity (u t)) t

theorem integral_density_eq (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T6, density n N L u x) = VorticitySmoothAmplitudeSource.retainedSource (2 * n) L N u := by
  have hc := VorticitySmoothAmplitudeSource.continuous_retainedDensity (2 * n) N L hL u hu
  simp only [density]
  rw [integral_const_mul, UnitTorusProductTransport.integral_pair
    (fun x y : T3 ↦ retainedStretch (2 * n) L (PeriodicRieszPolynomial.kernel N (x - y))
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
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hx := hw.comp (f := fun z : ℝ × T6 ↦ (time z.1, leftPoint z.2))
    ((ht.comp continuous_fst).prodMk (continuous_leftPoint.comp continuous_snd))
  have hy := hw.comp (f := fun z : ℝ × T6 ↦ (time z.1, rightPoint z.2))
    ((ht.comp continuous_fst).prodMk (continuous_rightPoint.comp continuous_snd))
  have hk : Continuous (fun z : ℝ × T6 ↦
      PeriodicRieszPolynomial.kernel N (leftPoint z.2 - rightPoint z.2)) :=
    (PeriodicRieszPolynomial.continuous_kernel N).comp
      ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))
  exact (continuous_retainedStretch (2 * n) L hL hk hx hy).const_mul (1 / 2 : ℝ)

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
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).locallyLipschitz
  have hkernel : LocallyLipschitz (fun z : ℝ × X6 ↦
      PeriodicRieszPolynomial.kernel N (leftPoint (torusPoint z.2) - rightPoint (torusPoint z.2))) :=
    hk.comp (g := fun z : ℝ × X6 ↦
      (fun i ↦ z.2 (Sum.inl i)) - (fun i ↦ z.2 (Sum.inr i))) (hx.sub hy)
  exact (LocallyLipschitz.const (1 / 2 : ℝ)).mul_algebra
    (locallyLipschitz_retainedStretch_even n L hL hkernel hwx hwy)

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

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothMeanRegularity
