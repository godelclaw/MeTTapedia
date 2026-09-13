import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalNormalVorticity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.Analysis.LocallyLipschitzComposition
import Mettapedia.Analysis.AbsolutelyContinuousComposition

/-!
# Time comparison for actual normal vorticity

On compact interior intervals with nonzero image separation, absolute
continuity and forcing integrability are proved from the local solution.
Compression removes exponential strain growth from the scalar comparison.
The resulting forcing integral is not bounded uniformly in time, image,
or initial data here; its viscous part must still be treated in the signed
spatial balance.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity

open MeasureTheory
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeLocalMaterialTrajectories
open LocalLowDiffusionBudget LocalRadialImageEvolution
open Mettapedia.Analysis
open scoped RealInnerProductSpace
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y W : ℝ → X3) (hX : LocallyLipschitz X) (hY : LocallyLipschitz Y)
  (hW : LocallyLipschitz W) (z : R3)
  (hz : ∀ t ∈ Set.Icc a b, imageSeparation z (X t) (Y t) ≠ 0)

include hg hSum hu hab hI hX hY hW hz

set_option maxHeartbeats 600000 in
theorem absolutelyContinuousOnInterval_component_path :
    AbsolutelyContinuousOnInterval
      (fun τ ↦ component z (s.coefficients τ) (X τ) (Y τ) (torusPoint (W τ))) a b := by
  let p : ℝ → ℝ := fun t ↦ Set.projIcc a b hab t
  have hp : LocallyLipschitz p :=
    ((LipschitzWith.subtype_val (Set.Icc a b)).comp (LipschitzWith.projIcc hab)).locallyLipschitz
  let h : ℝ → R3 := fun t ↦ imageSeparation z (X (p t)) (Y (p t))
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : LocallyLipschitz h := (LocallyLipschitz.const z).add
    (L.lipschitz.locallyLipschitz.comp ((hX.comp hp).sub (hY.comp hp)))
  let w : ℝ → R3 := fun t ↦ fullVorticity (LocalSpaceTimeExtension.coefficients s a b hab t)
    (torusPoint (W (p t)))
  have hw : LocallyLipschitz w :=
    (LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu).comp
      (g := fun t : ℝ ↦ (t, W (p t)))
      (LocallyLipschitz.id.prodMk (hW.comp hp))
  have hi : LocallyLipschitz (fun t ↦ ⟪h t, w t⟫) :=
    (show ContDiff ℝ 1 (fun q : R3 × R3 ↦ ⟪q.1, q.2⟫) from
      contDiff_fst.inner ℝ contDiff_snd).locallyLipschitz.comp
        (g := fun t ↦ (h t, w t)) (hh.prodMk hw)
  have hn : LocallyLipschitz (fun t ↦ ‖h t‖) := lipschitzWith_one_norm.locallyLipschitz.comp hh
  have hc := hi.div_real hn (fun t ↦ norm_ne_zero_iff.mpr (hz (p t) (Set.projIcc a b hab t).2))
  apply AbsolutelyContinuousComposition.congr (AbsolutelyContinuousComposition.of_locallyLipschitz hc)
  intro t ht
  have hm : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using ht
  simp only [h, w, p, Set.projIcc_of_mem hab hm,
    LocalSpaceTimeExtension.coefficients_eq s a b hab t hm, component, NormalVorticityEnergy.component]

omit hg hW hz in
theorem continuousOn_strainQuotient_path
    (hne : ∀ t ∈ Set.Icc a b, imageSeparation z (X t) (Y t) ≠ 0) :
    ContinuousOn (fun t ↦ strainQuotient (s.coefficients t) (torusPoint (X t))
      (imageSeparation z (X t) (Y t))) (Set.Icc a b) := by
  have hp : Continuous (fun t : ℝ ↦ (Set.projIcc a b hab t : ℝ)) :=
    continuous_subtype_val.comp (LipschitzWith.projIcc hab).continuous
  have hS := LocalAlignmentContinuity.continuous_fullStrainOperator_parametric
    (LocalSpaceTimeExtension.coefficients s a b hab)
    (fun q i ↦ (s.continuous q i).comp hp) g hSum
    (fun t q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans
      (LocalSpaceTimeExtension.moment_bound s a b hab hI g hu t q))
  have hx : Continuous (fun t ↦ torusPoint (X t)) := by
    have hxc := hX.continuous
    unfold torusPoint
    fun_prop
  have hs := hS.comp (continuous_id.prodMk hx)
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : Continuous (fun t ↦ imageSeparation z (X t) (Y t)) :=
    continuous_const.add (L.continuous.comp (hX.continuous.sub hY.continuous))
  have hc := ((hh.inner (hs.clm_apply hh)).continuousOn).div
    (hh.norm.pow 2).continuousOn (fun t ht ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hne t ht)))
  apply hc.congr
  intro t ht
  simp only [strainQuotient, Pi.div_apply, Function.comp_apply, id_eq,
    LocalSpaceTimeExtension.coefficients_eq s a b hab t ht]

variable
  (hDX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s t (X t)) t)
  (hDY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (liftedVelocity s t (Y t)) t)
  (hDW : ∀ t ∈ Set.Ioo a b, HasDerivAt W (liftedVelocity s t (W t)) t)

include hDX hDY hDW

omit hX hY hW in
theorem ae_hasDerivAt_component_path :
    ∀ᵐ t, t ∈ Set.uIcc a b →
      HasDerivAt (fun τ ↦ component z (s.coefficients τ) (X τ) (Y τ) (torusPoint (W τ)))
        (strainQuotient (s.coefficients t) (torusPoint (X t)) (imageSeparation z (X t) (Y t)) *
          component z (s.coefficients t) (X t) (Y t) (torusPoint (W t)) +
          forcing z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t))) t := by
  filter_upwards [Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b)] with t he ht
  have hm : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using ht
  have hi : t ∈ Set.Ioo a b := he.mpr hm
  exact hasDerivAt_component_path s g hg hSum hu a b hab hI X Y W t hi
    (hDX t hi) (hDY t hi) (hDW t hi) z (hz t hm)

theorem intervalIntegrable_forcing_path :
    IntervalIntegrable
      (fun t ↦ forcing z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t))) volume a b := by
  have hc := absolutelyContinuousOnInterval_component_path s g hg hSum hu a b hab hI X Y W hX hY hW z hz
  have hs := continuousOn_strainQuotient_path s g hSum hu a b hab hI X Y hX hY z hz
  have hprod : IntervalIntegrable (fun t ↦
      strainQuotient (s.coefficients t) (torusPoint (X t)) (imageSeparation z (X t) (Y t)) *
        component z (s.coefficients t) (X t) (Y t) (torusPoint (W t))) volume a b :=
    (hs.mul (by simpa only [Set.uIcc_of_le hab] using hc.continuousOn)).intervalIntegrable_of_Icc hab
  apply (hc.intervalIntegrable_deriv.sub hprod).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  filter_upwards [ae_hasDerivAt_component_path s g hg hSum hu a b hab hI X Y W z hz hDX hDY hDW]
    with t hd ht
  rw [(hd (Set.uIoc_subset_uIcc ht)).deriv]
  ring

/-- The right-hand side is an actual forcing integral, not a global budget. -/
theorem abs_component_le_initial_add_integral
    (hσ : ∀ t ∈ Set.Icc a b,
      strainQuotient (s.coefficients t) (torusPoint (X t)) (imageSeparation z (X t) (Y t)) ≤ 0) :
    |component z (s.coefficients b) (X b) (Y b) (torusPoint (W b))| ≤
      |component z (s.coefficients a) (X a) (Y a) (torusPoint (W a))| +
        ∫ t in a..b, |forcing z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t))| := by
  apply NormalVorticityEnergy.abs_le_initial_add_integral hab
    (absolutelyContinuousOnInterval_component_path s g hg hSum hu a b hab hI X Y W hX hY hW z hz)
    (intervalIntegrable_forcing_path s g hg hSum hu a b hab hI X Y W hX hY hW z hz hDX hDY hDW)
    (ae_hasDerivAt_component_path s g hg hSum hu a b hab hI X Y W z hz hDX hDY hDW)
  simpa only [Set.uIcc_of_le hab] using hσ

end Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity
