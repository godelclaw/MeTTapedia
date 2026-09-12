import Mettapedia.Analysis.SignedCrossKernel
import Mettapedia.Analysis.ODE.QuadraticFormBound
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Material derivative of the high-amplitude weight on a strict branch

The smaller endpoint determines the derivative above threshold. The
equal-norm interface and threshold crossing are not silently differentiated.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open Filter
open scoped Topology RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem hasDerivAt_highAmplitudeWeight_of_left_lt {a b : ℝ → R3} {v : R3} {t L : ℝ}
    (ha : HasDerivAt a v t) (hb : ContinuousAt b t) (hL : 0 < L)
    (hLa : L < ‖a t‖) (hab : ‖a t‖ < ‖b t‖) :
    HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ))
      (L * ⟪a t, v⟫ / ‖a t‖ ^ 3) t := by
  have hpos : 0 < ‖a t‖ := hL.trans hLa
  have ha0 : a t ≠ 0 := norm_pos_iff.mp hpos
  have hn : HasDerivAt (fun τ ↦ ‖a τ‖) (⟪a t, v⟫ / ‖a t‖) t :=
    (ODE.hasDerivWithinAt_norm_of_ne_zero (s := Set.univ) ha.hasDerivWithinAt ha0).hasDerivAt Filter.univ_mem
  have hd := ((hasDerivAt_const t L).div hn hpos.ne').const_sub 1
  have he1 : ∀ᶠ τ in 𝓝 t, L < ‖a τ‖ := ha.continuousAt.norm.eventually (eventually_gt_nhds hLa)
  have he2 : ∀ᶠ τ in 𝓝 t, ‖a τ‖ - ‖b τ‖ < 0 :=
    (ha.continuousAt.norm.sub hb.norm).eventually (eventually_lt_nhds (sub_neg.mpr hab))
  have he : (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) =ᶠ[𝓝 t]
      (fun τ ↦ 1 - L / ‖a τ‖) := by
    filter_upwards [he1, he2] with τ h1 h2
    simp only [lowAmplitudeWeight, min_eq_left (sub_neg.mp h2).le, max_eq_right h1.le]
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  field_simp [hpos.ne']
  ring

theorem hasDerivAt_highAmplitudeWeight_of_right_lt {a b : ℝ → R3} {v : R3} {t L : ℝ}
    (ha : ContinuousAt a t) (hb : HasDerivAt b v t) (hL : 0 < L)
    (hLb : L < ‖b t‖) (hba : ‖b t‖ < ‖a t‖) :
    HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ))
      (L * ⟪b t, v⟫ / ‖b t‖ ^ 3) t := by
  simpa only [lowAmplitudeWeight, min_comm] using
    hasDerivAt_highAmplitudeWeight_of_left_lt hb ha hL hLb hba

end Mettapedia.Analysis.SignedCrossKernel
