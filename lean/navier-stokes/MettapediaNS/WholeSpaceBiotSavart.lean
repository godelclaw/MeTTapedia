import EulerBlowup.Ring3D.Lit3.PotentialTheory3
import MettapediaNS.WholeSpaceBKM
import MettapediaNS.QuadraticSingularIntegral

/-!
# Whole-space Biot–Savart reconstruction using upstream potential theory

The velocity is the actual curl of the Newtonian vector potential constructed
by Alpöge–Buckmaster. The proved potential theory is supplied explicitly;
none of its analytic laws is an assumption in the results below. Coordinate
adapters identify its divergence and curl with the OpenAI and pancake APIs.

This module does not assert a Navier–Stokes evolution, an arbitrary-data
time budget, or a principal-value representation of the strain.
-/

noncomputable section

open MeasureTheory EulerSmoothLimit EulerVectorCalculus EulerMeanCutoffCurl
open scoped ContDiff

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart

open EulerBlowup Ring3D SpatialBKMIntegrand

/-- The upstream coordinate derivatives use the same standard axes. -/
theorem pd3_eq_partialDerivative (f : Space → ℝ) (i : Fin 3) (x : Space) :
    pd3 i f x = partialDerivative f i x := rfl

theorem curl3_eq_vectorCurl (u : Space → Space) (x : Space) :
    curl3 u x = vectorCurl u x := by
  ext i
  fin_cases i <;> simp [curl3, vectorCurl, curl_apply, pd3, partialDerivative, e3]

theorem div3_eq_divergence {u : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) : div3 u x = divergence u x := by
  rw [divergence_eq_coordinate_sum]
  simp only [div3, pd3, e3, fderiv_coordinate u x hu]

/-- A semantic name for the imported construction, not a second velocity. -/
abbrev velocity (vort : Space → Space) : Space → Space := biotSavart3 vort

theorem contDiff_velocity {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) : ContDiff ℝ ∞ (velocity vort) :=
  (biotSavart3_contDiff Lit3.potential_theory_R3 vort hvort hc).2

theorem memLp_velocity {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) : MemLp (velocity vort) 2 volume :=
  biotSavart3_memLp Lit3.potential_theory_R3 vort hvort hc

theorem divergence_velocity_eq_zero {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) (x : Space) :
    divergence (velocity vort) x = 0 := by
  have hdiv (y : Space) : div3 vort y = 0 :=
    (div3_eq_divergence (hvort.differentiable (by simp) y)).trans (hd y)
  rw [← div3_eq_divergence ((contDiff_velocity hvort hc).differentiable (by simp) x)]
  exact (biotSavart3_div_curl Lit3.potential_theory_R3 vort hvort hc hdiv).1 x

theorem vectorCurl_velocity_eq {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) (x : Space) :
    vectorCurl (velocity vort) x = vort x := by
  have hdiv (y : Space) : div3 vort y = 0 :=
    (div3_eq_divergence (hvort.differentiable (by simp) y)).trans (hd y)
  rw [← curl3_eq_vectorCurl]
  exact (biotSavart3_div_curl Lit3.potential_theory_R3 vort hvort hc hdiv).2 x

/-- Curl recovery in the existing pancake route's coordinate interface. -/
theorem curlField_velocity_eq {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) (x : Space) :
    curlField (velocity vort) x = vort x := by
  rw [WholeSpaceBKM.curlField_eq_vectorCurl
    ((contDiff_velocity hvort hc).differentiable (by simp) x)]
  exact vectorCurl_velocity_eq hvort hc hd x

/-- The Hessian of the constructed potential, represented by the integrable
first-derivative kernel acting on a derivative of the source. No principal-
value identity is assumed in making this transfer. -/
theorem newtonianHessian_eq_integral {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (i j : Fin 3) (x : Space) :
    pd3 i (pd3 j (newton3 f)) x =
      ∫ y : Space, gradG3 (x - y) i * pd3 j f y := by
  have hfun : pd3 j (newton3 f) = newton3 (pd3 j f) := by
    funext y
    simpa only [iterPartial3] using (Lit3.newton3_smooth f hf hc).2 [j] y
  rw [hfun]
  exact Lit3.newton3_kernel_deriv (pd3 j f)
    (Lit3.newton3_poisson_aux_pdSmooth f hf j)
    (Lit3.newton3_poisson_aux_pdSupp f hc j) i x

theorem vecPot_apply (vort : Space → Space) (j : Fin 3) (x : Space) :
    vecPot vort x j = -newton3 (fun y ↦ vort y j) x := by
  simp [vecPot, e3, Pi.single_apply]

theorem velocity_apply (vort : Space → Space) (j : Fin 3) (x : Space) :
    velocity vort x j = -pd3 (j + 1) (newton3 (fun y ↦ vort y (j + 2))) x +
      pd3 (j + 2) (newton3 (fun y ↦ vort y (j + 1))) x := by
  change curl3 (vecPot vort) x j = _
  rw [curl3_eq_vectorCurl]
  simp only [vectorCurl, curl_apply, vecPot_apply, partialDerivative, pd3,
    fderiv_fun_neg, neg_apply, e3]
  abel

/-- An actual velocity-gradient entry. The remaining source derivative is
visible; removing it requires a justified singular-integral representation. -/
theorem velocity_partial_eq_integrals {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (i j : Fin 3) (x : Space) :
    pd3 i (fun y ↦ velocity vort y j) x =
      -(∫ y : Space, gradG3 (x - y) i * pd3 (j + 1) (fun z ↦ vort z (j + 2)) y) +
        ∫ y : Space, gradG3 (x - y) i * pd3 (j + 2) (fun z ↦ vort z (j + 1)) y := by
  have hs (k : Fin 3) : ContDiff ℝ ∞ (fun y ↦ vort y k) := contDiff_euclidean.mp hvort k
  have hcs (k : Fin 3) : HasCompactSupport (fun y ↦ vort y k) :=
    hc.comp_left (g := fun z : Space ↦ z k) rfl
  have hn (k : Fin 3) := (Lit3.newton3_smooth _ (hs k) (hcs k)).1
  have hp (k l : Fin 3) : Differentiable ℝ (pd3 l (newton3 (fun y ↦ vort y k))) :=
    (Lit3.newton3_poisson_aux_pdSmooth _ (hn k) l).differentiable (by simp)
  simp_rw [velocity_apply]
  change (fderiv ℝ (fun y ↦
    -pd3 (j + 1) (newton3 (fun z ↦ vort z (j + 2))) y +
      pd3 (j + 2) (newton3 (fun z ↦ vort z (j + 1))) y) x) (e3 i) = _
  rw [((hp (j + 2) (j + 1) x).hasFDerivAt.fun_neg.fun_add
    (hp (j + 1) (j + 2) x).hasFDerivAt).fderiv]
  simp only [add_apply, neg_apply]
  change -pd3 i (pd3 (j + 1) (newton3 (fun y ↦ vort y (j + 2)))) x +
      pd3 i (pd3 (j + 2) (newton3 (fun y ↦ vort y (j + 1)))) x = _
  rw [newtonianHessian_eq_integral (hs _) (hcs _),
    newtonianHessian_eq_integral (hs _) (hcs _)]

/-- The derivative of the imported Newtonian gradient away from its pole.
The derivative of the norm power is supplied by mathlib. -/
theorem partial_gradG3 (i j : Fin 3) {x : Space} (hx : x ≠ 0) :
    pd3 j (fun y ↦ gradG3 y i) x = (4 * Real.pi)⁻¹ *
      ((if i = j then 1 else 0) / ‖x‖ ^ 3 - 3 * x i * x j / ‖x‖ ^ 5) := by
  have hn : HasFDerivAt (fun y : Space ↦ ‖y‖ ^ 3)
      ((3 * ‖x‖) • innerSL ℝ x) x := by
    simpa only [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one, Real.rpow_ofNat]
      using (hasFDerivAt_norm_rpow x (p := 3) (by norm_num))
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hs := ((hasDerivAt_inv (pow_ne_zero 3 hxnorm)).comp_hasFDerivAt x hn).const_mul
    ((4 * Real.pi)⁻¹)
  have hcoord : HasFDerivAt (fun y : Space ↦ y i)
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt
  have hd := hs.fun_mul hcoord
  simp only [Function.comp_def] at hd
  change fderiv ℝ (fun y : Space ↦ ((4 * Real.pi)⁻¹ * (‖y‖ ^ 3)⁻¹) * y i) x
    (e3 j) = _
  rw [hd.fderiv]
  simp [e3, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  split_ifs <;> field_simp <;> ring

/-- Off-diagonal derivatives are exactly the quadratic kernel components
already covered by the imported singular-integral bounds. -/
theorem partial_gradG3_eq_coordinateProduct (i j : Fin 3) (hij : i ≠ j)
    {x : Space} (hx : x ≠ 0) :
    (pd3 j (fun y ↦ gradG3 y i) x : ℂ) =
      (-(3 / (4 * Real.pi) : ℝ) : ℂ) * NS.Lit.CZ.homKer
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j) x := by
  rw [partial_gradG3 i j hx,
    Mettapedia.Analysis.QuadraticSingularIntegral.homKer_coordinateProduct, ite_eq_right hij]
  push_cast
  ring

theorem partial_gradG3_sub_eq_coordinateSquareDifference (i j : Fin 3)
    {x : Space} (hx : x ≠ 0) :
    (pd3 i (fun y ↦ gradG3 y i) x - pd3 j (fun y ↦ gradG3 y j) x : ℂ) =
      (-(3 / (4 * Real.pi) : ℝ) : ℂ) * NS.Lit.CZ.homKer
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j) x := by
  rw [partial_gradG3 i i hx, partial_gradG3 j j hx,
    Mettapedia.Analysis.QuadraticSingularIntegral.homKer_coordinateSquareDifference]
  simp only [ite_true]
  push_cast
  ring

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart
