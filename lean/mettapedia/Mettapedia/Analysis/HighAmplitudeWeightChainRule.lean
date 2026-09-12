import Mettapedia.Analysis.HighAmplitudeWeightEvolution
import Mettapedia.Analysis.HighAmplitudeWeightRegularity
import Mettapedia.Analysis.DerivativeContact

/-!
# The amplitude-cutoff chain rule at ties and threshold contacts

At a differentiable tie the cutoff touches either smooth endpoint branch,
so their derivatives agree. At a differentiable threshold contact its
derivative vanishes. Absolute continuity supplies differentiability almost
everywhere without requiring either interface set to be null.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def highAmplitudeWeightRate (L : ℝ) (a b v w : R3) : ℝ :=
  if L < min ‖a‖ ‖b‖ then
    if ‖a‖ ≤ ‖b‖ then L * ⟪a, v⟫ / ‖a‖ ^ 3 else L * ⟪b, w⟫ / ‖b‖ ^ 3
  else 0

theorem hasDerivAt_highAmplitudeWeight_of_left_le {a b : ℝ → R3} {v : R3} {t L : ℝ}
    (ha : HasDerivAt a v t) (hL : 0 < L) (hLa : L < ‖a t‖) (hab : ‖a t‖ ≤ ‖b t‖)
    (hd : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t) :
    HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ))
      (L * ⟪a t, v⟫ / ‖a t‖ ^ 3) t := by
  have hpos : 0 < ‖a t‖ := hL.trans hLa
  have hn : HasDerivAt (fun τ ↦ ‖a τ‖) (⟪a t, v⟫ / ‖a t‖) t :=
    (ODE.hasDerivWithinAt_norm_of_ne_zero (s := Set.univ) ha.hasDerivWithinAt
      (norm_pos_iff.mp hpos)).hasDerivAt Filter.univ_mem
  have hb := ((hasDerivAt_const t L).div hn hpos.ne').const_sub 1
  have he : 1 - lowAmplitudeWeight L (a t) (b t) = 1 - L / ‖a t‖ := by
    simp only [lowAmplitudeWeight, min_eq_left hab, max_eq_right hLa.le]
  have hle : ∀ᶠ τ in 𝓝 t, 1 - lowAmplitudeWeight L (a τ) (b τ) ≤ 1 - L / ‖a τ‖ := by
    filter_upwards [ha.continuousAt.norm.eventually (eventually_gt_nhds hLa)] with τ hτ
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left hL.le
      (hL.trans_le (le_max_left _ _))
      (max_le hτ.le (min_le_left _ _))
  have hr := DerivativeContact.eq_of_eventually_le_of_eq hd.hasDerivAt hb hle he
  apply hd.hasDerivAt.congr_deriv
  rw [hr]
  field_simp [hpos.ne']
  ring

theorem hasDerivAt_highAmplitudeWeight_of_min_le {a b : ℝ → R3} {t L : ℝ}
    (hL : 0 < L) (hmin : min ‖a t‖ ‖b t‖ ≤ L)
    (hd : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t) :
    HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) 0 t := by
  have hm : IsLocalMin (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t := by
    apply Eventually.of_forall
    intro τ
    have he : 1 - lowAmplitudeWeight L (a t) (b t) = 0 := by
      simp only [lowAmplitudeWeight, max_eq_left hmin, div_self hL.ne', sub_self]
    dsimp only
    rw [he]
    exact sub_nonneg.mpr (lowAmplitudeWeight_le_one L hL _ _)
  exact hd.hasDerivAt.congr_deriv (hm.hasDerivAt_eq_zero hd.hasDerivAt)

theorem hasDerivAt_highAmplitudeWeight_of_differentiable {a b : ℝ → R3} {v w : R3} {t L : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) (hL : 0 < L)
    (hd : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t) :
    HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ))
      (highAmplitudeWeightRate L (a t) (b t) v w) t := by
  unfold highAmplitudeWeightRate
  split_ifs with hmin hab
  · exact hasDerivAt_highAmplitudeWeight_of_left_le ha hL
      (hmin.trans_le (min_le_left _ _)) hab hd
  · simpa only [lowAmplitudeWeight, min_comm] using
      hasDerivAt_highAmplitudeWeight_of_left_le hb hL
        (hmin.trans_le (min_le_right _ _)) (le_of_not_ge hab)
        (by simpa only [lowAmplitudeWeight, min_comm] using hd)
  · exact hasDerivAt_highAmplitudeWeight_of_min_le hL (le_of_not_gt hmin) hd

theorem ae_hasDerivAt_highAmplitudeWeight {a b v w : ℝ → R3} {s t L : ℝ}
    (hL : 0 < L)
    (hac : AbsolutelyContinuousOnInterval (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) s t)
    (ha : ∀ᵐ τ, τ ∈ Set.uIcc s t → HasDerivAt a (v τ) τ)
    (hb : ∀ᵐ τ, τ ∈ Set.uIcc s t → HasDerivAt b (w τ) τ) :
    ∀ᵐ τ, τ ∈ Set.uIcc s t → HasDerivAt (fun r ↦ 1 - lowAmplitudeWeight L (a r) (b r))
      (highAmplitudeWeightRate L (a τ) (b τ) (v τ) (w τ)) τ := by
  filter_upwards [hac.ae_differentiableAt, ha, hb] with τ hτ hda hdb hmem
  exact hasDerivAt_highAmplitudeWeight_of_differentiable (hda hmem) (hdb hmem) hL (hτ hmem)

theorem highAmplitudeWeightRate_swap_of_differentiable {a b : ℝ → R3} {v w : R3} {t L : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) (hL : 0 < L)
    (hd : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t) :
    highAmplitudeWeightRate L (a t) (b t) v w = highAmplitudeWeightRate L (b t) (a t) w v := by
  have hs : HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ))
      (highAmplitudeWeightRate L (b t) (a t) w v) t := by
    simpa only [lowAmplitudeWeight, min_comm] using
      hasDerivAt_highAmplitudeWeight_of_differentiable hb ha hL
        (by simpa only [lowAmplitudeWeight, min_comm] using hd)
  exact (hasDerivAt_highAmplitudeWeight_of_differentiable ha hb hL hd).unique hs

theorem endpointWeightRates_eq_of_tie {a b : ℝ → R3} {v w : R3} {t L : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) (hL : 0 < L)
    (hLa : L < ‖a t‖) (heq : ‖a t‖ = ‖b t‖)
    (hd : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ)) t) :
    L * ⟪a t, v⟫ / ‖a t‖ ^ 3 = L * ⟪b t, w⟫ / ‖b t‖ ^ 3 := by
  have hs : HasDerivAt (fun τ ↦ 1 - lowAmplitudeWeight L (a τ) (b τ))
      (L * ⟪b t, w⟫ / ‖b t‖ ^ 3) t := by
    simpa only [lowAmplitudeWeight, min_comm] using
      hasDerivAt_highAmplitudeWeight_of_left_le hb hL (heq ▸ hLa) heq.ge
        (by simpa only [lowAmplitudeWeight, min_comm] using hd)
  exact (hasDerivAt_highAmplitudeWeight_of_left_le ha hL hLa heq.le hd).unique hs

end Mettapedia.Analysis.SignedCrossKernel
