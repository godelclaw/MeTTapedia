import Mettapedia.Analysis.AngularCurlEvolution
import Mettapedia.Analysis.CrossProductEvolution
import Mathlib.Tactic.Module

/-!
# Explicit value and jet gradients of angular curl energy

The first variation is kept signed and linear in both input rates. Its
jet gradient permits periodic integration by parts without dividing by
amplitude or introducing derivatives of an incoming source into a norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open WeightedCurlCancellation EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def amplitudeGradientRate (a : R3) (D : Fin 3 → R3) (v : R3) (E : Fin 3 → R3) : R3 :=
  WithLp.toLp 2 (fun j ↦ ⟪v, D j⟫ + ⟪a, E j⟫)

theorem angularCurlRate_eq (a : R3) (D : Fin 3 → R3) (v : R3) (E : Fin 3 → R3) :
    angularCurlRate a D v E = (2 * ⟪a, v⟫) • curlJet D + ‖a‖ ^ 2 • curlJet E -
      cross (amplitudeGradientRate a D v E) a - cross (amplitudeGradient a D) v := by
  ext i
  fin_cases i <;> simp [angularCurlRate, angularJetRate, curlJet, amplitudeGradientRate,
    amplitudeGradient, cross, cross_apply, Matrix.cons_val_two] <;> ring

/-- The adjoint of the curl contraction on first jets. -/
def curlJetAdjoint (b : R3) (j : Fin 3) : R3 :=
  ![WithLp.toLp 2 ![0, b 2, -b 1], WithLp.toLp 2 ![-b 2, 0, b 0],
    WithLp.toLp 2 ![b 1, -b 0, 0]] j

theorem inner_curlJet_eq (b : R3) (E : Fin 3 → R3) :
    ⟪b, curlJet E⟫ = ∑ j : Fin 3, ⟪curlJetAdjoint b j, E j⟫ := by
  simp [curlJet, curlJetAdjoint, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

def valueGradient (a : R3) (D : Fin 3 → R3) : R3 :=
  (2 * ‖angularCurl a D‖ ^ 2 + 4 * ‖a‖ ^ 2 * ⟪angularCurl a D, curlJet D⟫) • a -
    (2 * ‖a‖ ^ 2) • (∑ j : Fin 3, cross a (angularCurl a D) j • D j) -
    (2 * ‖a‖ ^ 2) • cross (angularCurl a D) (amplitudeGradient a D)

def jetGradient (a : R3) (D : Fin 3 → R3) (j : Fin 3) : R3 :=
  (2 * ‖a‖ ^ 4) • curlJetAdjoint (angularCurl a D) j -
    (2 * ‖a‖ ^ 2 * cross a (angularCurl a D) j) • a

theorem angularCurlDensityRate_eq_pairing (a : R3) (D : Fin 3 → R3) (v : R3) (E : Fin 3 → R3) :
    angularCurlDensityRate a D v E = ⟪valueGradient a D, v⟫ +
      ∑ j : Fin 3, ⟪jetGradient a D j, E j⟫ := by
  have hg : ⟪angularCurl a D, cross (amplitudeGradientRate a D v E) a⟫ =
      ∑ j : Fin 3, cross a (angularCurl a D) j * (⟪v, D j⟫ + ⟪a, E j⟫) := by
    rw [inner_cross_cycle]
    simp [amplitudeGradientRate, PiLp.inner_apply, Fin.sum_univ_three]
  have hh : ⟪angularCurl a D, cross (amplitudeGradient a D) v⟫ =
      ⟪cross (angularCurl a D) (amplitudeGradient a D), v⟫ := by
    rw [inner_cross_cycle, inner_cross_cycle]
    exact real_inner_comm _ _
  simp only [angularCurlDensityRate, angularCurlRate_eq, inner_sub_right, inner_add_right,
    real_inner_smul_right, hg, hh, inner_curlJet_eq, valueGradient, jetGradient,
    inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_comm (D _) v,
    Fin.sum_univ_three]
  ring

def jetGradientRate (a : R3) (D : Fin 3 → R3) (v : R3) (E : Fin 3 → R3) (j : Fin 3) : R3 :=
  (8 * ‖a‖ ^ 2 * ⟪a, v⟫) • curlJetAdjoint (angularCurl a D) j +
    (2 * ‖a‖ ^ 4) • curlJetAdjoint (angularCurlRate a D v E) j -
    (4 * ⟪a, v⟫ * cross a (angularCurl a D) j +
      2 * ‖a‖ ^ 2 * (cross v (angularCurl a D) + cross a (angularCurlRate a D v E)) j) • a -
    (2 * ‖a‖ ^ 2 * cross a (angularCurl a D) j) • v

/-- Euler's identity retains the contribution of the outer amplitude weight. -/
theorem gradient_pairing_self (a : R3) (D : Fin 3 → R3) :
    ⟪valueGradient a D, a⟫ + ∑ j : Fin 3, ⟪jetGradient a D j, D j⟫ =
      8 * angularCurlDensity a D := by
  rw [← angularCurlDensityRate_eq_pairing]
  simpa only [one_smul, mul_one] using angularCurlDensityRate_proportional a D 1

theorem hasDerivAt_curlJetAdjoint {b : ℝ → R3} {db : R3} {t : ℝ}
    (hb : HasDerivAt b db t) (j : Fin 3) :
    HasDerivAt (fun τ ↦ curlJetAdjoint (b τ) j) (curlJetAdjoint db j) t := by
  have hc (i : Fin 3) := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hb
  have hf : HasDerivAt (fun τ ↦ WithLp.ofLp (curlJetAdjoint (b τ) j))
      (WithLp.ofLp (curlJetAdjoint db j)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases j <;> fin_cases i <;>
      first | exact hc _ | exact (hc _).neg | exact hasDerivAt_const t 0
  let L := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv
  exact L.hasFDerivAt.comp_hasDerivAt t hf

theorem hasDerivAt_jetGradient {a : ℝ → R3} {D : ℝ → Fin 3 → R3}
    {v : R3} {E : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a v t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (E j) t) (j : Fin 3) :
    HasDerivAt (fun τ ↦ jetGradient (a τ) (D τ) j) (jetGradientRate (a t) (D t) v E j) t := by
  have hH := hasDerivAt_angularCurl ha hD
  have hcross := (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_cross ha hH)
  change HasDerivAt (fun τ ↦ cross (a τ) (angularCurl (a τ) (D τ)) j)
    ((cross v (angularCurl (a t) (D t)) + cross (a t) (angularCurlRate (a t) (D t) v E)) j) t at hcross
  have h := (((ha.norm_sq.fun_pow 2).const_mul 2).smul (hasDerivAt_curlJetAdjoint hH j)).sub
    (((ha.norm_sq.const_mul 2).mul hcross).smul ha)
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat, pow_one] at h
  apply h.congr_deriv
  simp only [jetGradientRate, Pi.mul_apply]
  module

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_curlJetAdjoint (b : X → R3) (hb : Continuous b) (j : Fin 3) :
    Continuous (fun x ↦ curlJetAdjoint (b x) j) := by
  fin_cases j <;> unfold curlJetAdjoint <;> fun_prop

theorem continuous_amplitudeGradient (a : X → R3) (D : Fin 3 → X → R3)
    (ha : Continuous a) (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ amplitudeGradient (a x) (fun j ↦ D j x)) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
    (continuous_pi (fun j ↦ ha.inner (hD j)))

theorem continuous_valueGradient (a : X → R3) (D : Fin 3 → X → R3)
    (ha : Continuous a) (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ valueGradient (a x) (fun j ↦ D j x)) := by
  have hH := continuous_angularCurl a D ha hD
  have hg := continuous_amplitudeGradient a D ha hD
  have hb : Continuous (fun x ↦ curlJet (fun j ↦ D j x)) := by unfold curlJet; fun_prop
  have hr := contDiff_cross.continuous.comp (ha.prodMk hH)
  have hh := contDiff_cross.continuous.comp (hH.prodMk hg)
  have hs : Continuous (fun x ↦ ∑ j : Fin 3, cross (a x) (angularCurl (a x) (fun j ↦ D j x)) j • D j x) :=
    continuous_finsetSum _ (fun j _ ↦ ((PiLp.continuous_apply 2 _ j).comp hr).smul (hD j))
  exact (((((hH.norm.pow 2).const_mul 2).add (((ha.norm.pow 2).const_mul 4).mul (hH.inner hb))).smul ha).sub
    (((ha.norm.pow 2).const_mul 2).smul hs)).sub (((ha.norm.pow 2).const_mul 2).smul hh)

theorem continuous_jetGradient (a : X → R3) (D : Fin 3 → X → R3)
    (ha : Continuous a) (hD : ∀ j, Continuous (D j)) (j : Fin 3) :
    Continuous (fun x ↦ jetGradient (a x) (fun k ↦ D k x) j) := by
  have hH := continuous_angularCurl a D ha hD
  have hr := contDiff_cross.continuous.comp (ha.prodMk hH)
  exact ((((ha.norm.pow 4).const_mul 2).smul (continuous_curlJetAdjoint _ hH j)).sub
    ((((ha.norm.pow 2).const_mul 2).mul ((PiLp.continuous_apply 2 _ j).comp hr)).smul ha))

theorem continuous_jetGradientRate (a v : X → R3) (D E : Fin 3 → X → R3)
    (ha : Continuous a) (hv : Continuous v) (hD : ∀ j, Continuous (D j))
    (hE : ∀ j, Continuous (E j)) (j : Fin 3) :
    Continuous (fun x ↦ jetGradientRate (a x) (fun k ↦ D k x) (v x) (fun k ↦ E k x) j) := by
  have hH := continuous_angularCurl a D ha hD
  have hdH := continuous_angularCurlRate a v D E ha hv hD hE
  have hJ := continuous_curlJetAdjoint _ hH j
  have hdJ := continuous_curlJetAdjoint _ hdH j
  have hr := (PiLp.continuous_apply 2 _ j).comp (contDiff_cross.continuous.comp (ha.prodMk hH))
  have hdr := (PiLp.continuous_apply 2 _ j).comp
    ((contDiff_cross.continuous.comp (hv.prodMk hH)).add (contDiff_cross.continuous.comp (ha.prodMk hdH)))
  exact ((((((ha.norm.pow 2).const_mul 8).mul (ha.inner hv)).smul hJ).add
    (((ha.norm.pow 4).const_mul 2).smul hdJ)).sub
      (((((ha.inner hv).const_mul 4).mul hr).add (((ha.norm.pow 2).const_mul 2).mul hdr)).smul ha)).sub
        ((((ha.norm.pow 2).const_mul 2).mul hr).smul hv)

end Continuity

end Mettapedia.Analysis.AngularCurlDecomposition
