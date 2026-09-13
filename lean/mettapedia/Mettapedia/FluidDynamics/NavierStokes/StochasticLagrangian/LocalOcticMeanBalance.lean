import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularExplicitRate

/-!
# Time balance of the actual octic correlation

The product-torus incompressible transport cancels after integration. Local
regularity is obtained by clamping the solution's time parameter, not by
extending its existence interval. The complete signed rate is retained.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalOcticMeanBalance

open scoped Topology ContDiff
open MeasureTheory Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget
open Mettapedia.Analysis UnitTorusProductTransport UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalAnnularMeanBalance (productVelocity)
open LocalAnnularExplicitRate (tangentPath tangentPath_self hasDerivAt_tangentPath
  leftPoint_frozenShift rightPoint_frozenShift)
open LocalOcticCorrelation (pairDensity fieldRate periodicRate periodicRate_eq_fieldRate)
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

def density (N : ℕ) (u : FourierVelocity) (x : T6) : ℝ := pairDensity N u (leftPoint x) (rightPoint x)

def frozenMaterialRate (N : ℕ) (u : ℝ → FourierVelocity) (t : ℝ) : T6 → ℝ :=
  scalarMaterialRate (fun τ ↦ density N (u τ)) (productVelocity (u t)) t

def explicitRate (N : ℕ) (nu : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  fieldRate N u nu (leftPoint x) (rightPoint x)

def meanRate (N : ℕ) (nu : ℝ) (u : FourierVelocity) : ℝ := ∫ x : T6, explicitRate N nu u x

/-- Stretching and relative transport, minus both spatial diffusion curvatures. -/
def signedRate (N : ℕ) (nu : ℝ) (u : FourierVelocity) : ℝ :=
  meanRate N 0 u - nu *
    (LocalOcticDiffusion.pureContribution N u + LocalOcticCorrelation.mixedGradientContribution N u)

theorem explicitRate_split_viscosity (N : ℕ) (nu : ℝ) (u : FourierVelocity) (x : T6) :
    explicitRate N nu u x = explicitRate N 0 u x + nu *
      LocalOcticDiffusion.diffusionDensity (PeriodicRadialRiesz.tensor N) u (leftPoint x) (rightPoint x) := by
  simp only [explicitRate, fieldRate, LocalOcticDiffusion.diffusionDensity,
    OcticKernelCorrelation.materialRate_add_smul_endpoint, zero_smul, add_zero]

theorem meanRate_eq_signedRate (N : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hi : Integrable (explicitRate N nu u)) :
    meanRate N nu u = signedRate N nu u := by
  let d := LocalOcticDiffusion.diffusionDensity (PeriodicRadialRiesz.tensor N) u
  have hc : Continuous d.uncurry := LocalOcticDiffusion.continuous_diffusionDensity _
    (PeriodicRadialRiesz.continuous_tensor N) u hu
  have hd : Integrable (fun x : T6 ↦ d (leftPoint x) (rightPoint x)) :=
    (hc.comp (continuous_leftPoint.prodMk continuous_rightPoint)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : Integrable (explicitRate N 0 u) := by
    have he : explicitRate N 0 u = fun x ↦ explicitRate N nu u x - nu * d (leftPoint x) (rightPoint x) := by
      funext x
      dsimp only [d]
      linarith only [explicitRate_split_viscosity N nu u x]
    rw [he]
    exact hi.sub (hd.const_mul nu)
  unfold meanRate
  simp_rw [explicitRate_split_viscosity N nu u]
  rw [integral_add hz (hd.const_mul nu), integral_const_mul,
    UnitTorusProductTransport.integral_pair _
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change meanRate N 0 u + nu * LocalOcticDiffusion.diffusionContribution N u = _
  rw [LocalOcticDiffusion.diffusionContribution_eq N u hu]
  unfold signedRate
  ring

theorem integral_density_eq (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T6, density N u x) = LocalOcticCorrelation.correlation N u := by
  have hw := continuous_fullVorticity u hu
  have hc : Continuous (pairDensity N u).uncurry := OcticKernelCorrelation.continuous_density
    ((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd)
  change (∫ x : T6, pairDensity N u (leftPoint x) (rightPoint x)) = _
  rw [UnitTorusProductTransport.integral_pair _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    LocalOcticCorrelation.correlation_eq_pairIntegral N u hu]

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hSum hu in
theorem continuous_extendedDensity (N : ℕ) :
    Continuous (fun z : ℝ × T6 ↦ density N (LocalSpaceTimeExtension.coefficients s a b hab z.1) z.2) := by
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
  have hk : Continuous (fun z : ℝ × T6 ↦ PeriodicRadialRiesz.tensor N (leftPoint z.2 - rightPoint z.2)) :=
    (PeriodicRadialRiesz.continuous_tensor N).comp
    ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))
  exact OcticKernelCorrelation.continuous_density hk hx hy

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
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hsep := L.lipschitz.locallyLipschitz.comp
    (g := fun z : ℝ × X6 ↦ (fun i ↦ z.2 (Sum.inl i)) - (fun i ↦ z.2 (Sum.inr i))) (hx.sub hy)
  have hk := (PeriodicRadialRiesz.contDiff_one_tensor_lift (d := 3) N).locallyLipschitz.comp hsep
  exact OcticKernelCorrelation.locallyLipschitz_density hk hwx hwy

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
theorem frozenMaterialRate_eq (N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : T6) :
    frozenMaterialRate N s.coefficients t x = explicitRate N nu (s.coefficients t) x := by
  obtain ⟨r, hr, _⟩ := torusPoint_bounded_rep (leftPoint x)
  obtain ⟨q, hq, _⟩ := torusPoint_bounded_rep (rightPoint x)
  have hp := LocalOcticCorrelation.hasDerivAt_pairDensity_path s g hg hSum hu a b hab hI
    (tangentPath s t r) (tangentPath s t q) t ht
    (hasDerivAt_tangentPath s t r) (hasDerivAt_tangentPath s t q) N
  have hp' := hp.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add t) (by simp)
  have htorus : PancakeFourierMaterialPaths.torusPoint = (torusPoint : X3 → T3) := rfl
  have hf : HasDerivAt (fun h ↦ density N (s.coefficients (t + h))
      (x + materialShift (productVelocity (s.coefficients t) x) h))
      (explicitRate N nu (s.coefficients t) x) 0 := by
    simpa only [Function.comp_def, id_eq, density,
      leftPoint_frozenShift s t x r hr, rightPoint_frozenShift s t x q hq,
      periodicRate_eq_fieldRate, tangentPath_self, htorus, hr, hq,
      add_zero, mul_one, explicitRate] using hp'
  exact hf.deriv

include hab hI hg hSum hu

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

theorem ae_hasDerivAt_mean (N : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → Integrable (explicitRate N nu (s.coefficients t)) ∧
      HasDerivAt (fun τ ↦ ∫ x : T6, density N (s.coefficients τ) x) (meanRate N nu (s.coefficients t)) t := by
  have hd := ae_hasDerivAt_mean_materialRate
    (fun t ↦ density N (LocalSpaceTimeExtension.coefficients s a b hab t))
    (fun t ↦ productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t))
    (continuous_extendedDensity s a b hab hI g hSum hu N)
    (fun _ ↦ LocalAnnularMeanBalance.continuous_productVelocity _)
    (locallyLipschitz_extendedDensity s a b hab hI g hg hSum hu N)
    (LocalAnnularMeanBalance.locallyLipschitz_extendedProductVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall
      (LocalAnnularMeanBalance.divergence_extendedProductVelocity s a b hab hI g hSum hu t))
  filter_upwards [hd] with t ht hmem
  have he : scalarMaterialRate
      (fun τ ↦ density N (LocalSpaceTimeExtension.coefficients s a b hab τ))
      (productVelocity (LocalSpaceTimeExtension.coefficients s a b hab t)) t =
      explicitRate N nu (s.coefficients t) := by
    funext x
    exact (frozenMaterialRate_extension_eq s a b hab N t hmem x).trans
      (frozenMaterialRate_eq s a b hab hI g hg hSum hu N t hmem x)
  rw [he] at ht
  refine ⟨ht.1, ht.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [Icc_mem_nhds hmem.1 hmem.2] with τ hτ
  rw [LocalSpaceTimeExtension.coefficients_eq s a b hab τ hτ]

theorem integral_meanRate_eq (N : ℕ) :
    IntervalIntegrable (fun t ↦ meanRate N nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, meanRate N nu (s.coefficients t)) =
        LocalOcticCorrelation.correlation N (s.coefficients b) -
          LocalOcticCorrelation.correlation N (s.coefficients a) := by
  let f := fun t ↦ ∫ x : T6, density N (s.coefficients t) x
  have hac : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_mean s a b hab hI g hg hSum hu N
  have heq : deriv f =ᵐ[volume.restrict (uIoc a b)] (fun t ↦ meanRate N nu (s.coefficients t)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu N,
      (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t ht he hm
    have hm' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hm
    exact (ht (he.mpr hm')).2.deriv
  refine ⟨hac.intervalIntegrable_deriv.congr_ae heq, ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict heq, hac.integral_deriv_eq_sub]
  have hm (t : ℝ) (ht : t ∈ Icc a b) : f t = LocalOcticCorrelation.correlation N (s.coefficients t) :=
    integral_density_eq N _ (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI ht)))))
  rw [hm b ⟨hab, le_rfl⟩, hm a ⟨le_rfl, hab⟩]

/-- The complete signed evolution, with actual endpoint and relative transport. -/
theorem integral_signedRate_eq (N : ℕ) :
    IntervalIntegrable (fun t ↦ signedRate N nu (s.coefficients t)) volume a b ∧
      (∫ t in a..b, signedRate N nu (s.coefficients t)) =
        LocalOcticCorrelation.correlation N (s.coefficients b) -
          LocalOcticCorrelation.correlation N (s.coefficients a) := by
  obtain ⟨hi, he⟩ := integral_meanRate_eq s a b hab hI g hg hSum hu N
  have heq : (fun t ↦ meanRate N nu (s.coefficients t)) =ᵐ[volume.restrict (uIoc a b)]
      (fun t ↦ signedRate N nu (s.coefficients t)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [ae_hasDerivAt_mean s a b hab hI g hg hSum hu N,
      (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t ht he hm
    have hm' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hm
    exact meanRate_eq_signedRate N nu _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Ioo_subset_Icc_self (hI hm'))))
      (ht (he.mpr hm')).1
  exact ⟨hi.congr_ae heq, (intervalIntegral.integral_congr_ae_restrict heq).symm.trans he⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalOcticMeanBalance
