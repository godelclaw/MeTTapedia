import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialPeriodicIntegral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularExplicitRate

/-!
# Regularity of the actual radial signed source on the product torus

The radial kernel and its local material derivative are the constructed
objects, including at coincident endpoints. Only the generic product velocity
and tangent-path calculus are reused from the annular development; no equality
between the kernel families is used. All regularity is local at fixed cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity

open scoped Topology ContDiff
open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget
open Mettapedia.Analysis SignedCrossKernel UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalAnnularMeanBalance (productVelocity)
open LocalAnnularExplicitRate (tangentPath tangentPath_self hasDerivAt_tangentPath
  leftPoint_frozenShift rightPoint_frozenShift)
open LocalRadialPeriodicEvolution

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

def density (n N : ℕ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * pairedStretch (2 * (n + 1))
    (PeriodicRadialRiesz.tensor N (leftPoint x - rightPoint x))
    (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x))

def frozenMaterialRate (n N : ℕ) (u : ℝ → FourierVelocity) (t : ℝ) : T6 → ℝ :=
  scalarMaterialRate (fun τ ↦ density n N (u τ)) (productVelocity (u t)) t

def explicitRate (n N : ℕ) (nu : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * fieldRate n N u nu (leftPoint x) (rightPoint x)

def meanRate (n N : ℕ) (nu : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T6, explicitRate n N nu u x

/-- The sum remains inside the spatial integral; all four signed image channels are retained. -/
theorem explicitRate_eq_imageSum (n N : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x : T6) :
    explicitRate n N nu u x = (1 / 2 : ℝ) *
      ∑' z : UnitTorusLattice.LatticeSubmodule (ι := Fin 3),
        LocalRadialImageEvolution.materialRate n N (z : R3) u nu
          (WithLp.ofLp (UnitTorusLattice.representative (leftPoint x)))
          (WithLp.ofLp (UnitTorusLattice.representative (rightPoint x))) := by
  have hs := hasSum_materialImageRates n N u nu hu hd
    (WithLp.ofLp (UnitTorusLattice.representative (leftPoint x)))
    (WithLp.ofLp (UnitTorusLattice.representative (rightPoint x)))
  simpa only [periodicRate_eq_fieldRate, LocalRadialPeriodicIntegral.torusPoint_representative,
    explicitRate] using (congrArg ((1 / 2 : ℝ) * ·) hs.tsum_eq).symm

theorem integral_density_eq (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T6, density n N u x) = VorticityRadialSource.source (2 * (n + 1)) N u := by
  have hc := continuous_pairedStretch
    (fun x y : T3 ↦ PeriodicRadialRiesz.tensor N (x - y)) (fullVorticity u)
    ((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd))
    (continuous_fullVorticity u hu) (2 * (n + 1))
  simp only [density]
  rw [integral_const_mul, UnitTorusProductTransport.integral_pair
    (fun x y : T3 ↦ pairedStretch (2 * (n + 1)) (PeriodicRadialRiesz.tensor N (x - y))
      (fullVorticity u x) (fullVorticity u y))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact (VorticityRadialPairing.source_eq_pairedSource _ N u hu).symm

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hSum hu in
theorem continuous_extendedDensity (n N : ℕ) :
    Continuous (fun z : ℝ × T6 ↦ density n N
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
      PeriodicRadialRiesz.tensor N (leftPoint z.2 - rightPoint z.2)) :=
    (PeriodicRadialRiesz.continuous_tensor N).comp
    ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))
  exact ((contDiff_pairedStretch_even (n + 1)).continuous.comp
    (hk.prodMk (hx.prodMk hy))).const_mul (1 / 2 : ℝ)

include hI hg hSum hu in
theorem locallyLipschitz_extendedDensity (n N : ℕ) :
    LocallyLipschitz (fun z : ℝ × X6 ↦ density n N
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
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hsep := L.lipschitz.locallyLipschitz.comp
    (g := fun z : ℝ × X6 ↦ (fun i ↦ z.2 (Sum.inl i)) - (fun i ↦ z.2 (Sum.inr i))) (hx.sub hy)
  have hk := (PeriodicRadialRiesz.contDiff_one_tensor_lift (d := 3) N).locallyLipschitz.comp hsep
  exact (LocallyLipschitz.const (1 / 2 : ℝ)).mul_algebra
    (locallyLipschitz_pairedStretch_even (n + 1) hk hwx hwy)

theorem frozenMaterialRate_extension_eq (n N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : T6) :
    frozenMaterialRate n N (LocalSpaceTimeExtension.coefficients s a b hab) t x =
      frozenMaterialRate n N s.coefficients t x := by
  unfold frozenMaterialRate scalarMaterialRate
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab t (Ioo_subset_Icc_self ht)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab (t + h) hh]

include hab hI hg hSum hu in
theorem frozenMaterialRate_eq (n N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : T6) :
    frozenMaterialRate n N s.coefficients t x = explicitRate n N nu (s.coefficients t) x := by
  obtain ⟨r, hr, _⟩ := torusPoint_bounded_rep (leftPoint x)
  obtain ⟨q, hq, _⟩ := torusPoint_bounded_rep (rightPoint x)
  have hp := hasDerivAt_periodicDensity_path s g hg hSum hu a b hab hI
    (tangentPath s t r) (tangentPath s t q) t ht
    (hasDerivAt_tangentPath s t r) (hasDerivAt_tangentPath s t q) n N
  have hp' := (hp.const_mul (1 / 2 : ℝ)).comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).const_add t) (by simp)
  have htorus : PancakeFourierMaterialPaths.torusPoint = (torusPoint : X3 → T3) := rfl
  have hf : HasDerivAt (fun h ↦ density n N (s.coefficients (t + h))
      (x + materialShift (productVelocity (s.coefficients t) x) h))
      (explicitRate n N nu (s.coefficients t) x) 0 := by
    simpa only [Function.comp_def, id_eq, density, periodicDensity,
      leftPoint_frozenShift s t x r hr, rightPoint_frozenShift s t x q hq,
      periodicRate_eq_fieldRate, tangentPath_self, htorus, hr, hq,
      add_zero, mul_one, explicitRate] using hp'
  exact hf.deriv

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity
