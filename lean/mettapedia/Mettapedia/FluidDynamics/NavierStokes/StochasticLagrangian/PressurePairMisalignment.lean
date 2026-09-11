import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CoherentPressurePair

/-!
# A frequency-uniform pressure-pair bound by vorticity misalignment

The divergence-free case turns the coherent pair's longitudinal frequency
ratios into transverse vorticity errors. The general estimate also retains
normalized divergence defects, which need not vanish after localization.
Both include zero and nearly cancelling frequencies without an output cone.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment

open scoped RealInnerProductSpace
open Mettapedia.Analysis.EuclideanCrossProduct
open PancakeAnisotropyDepletion PressureTiltSymbol CoherentPressurePair

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem abs_tracePair_le (k p w v : E3) : |tracePair k p w v| ≤ ‖w‖ * ‖v‖ := by
  by_cases hk : k = 0
  · simp [hk, tracePair, mul_nonneg (norm_nonneg w) (norm_nonneg v)]
  by_cases hp : p = 0
  · simp [hp, tracePair, mul_nonneg (norm_nonneg w) (norm_nonneg v)]
  have hkn := norm_pos_iff.mpr hk
  have hpn := norm_pos_iff.mpr hp
  have h1 : |⟪p, cross k w⟫| ≤ ‖p‖ * ‖k‖ * ‖w‖ := by
    have h := (abs_real_inner_le_norm p (cross k w)).trans
      (mul_le_mul_of_nonneg_left (norm_cross_le k w) (norm_nonneg p))
    simpa only [mul_assoc] using h
  have h2 : |⟪k, cross p v⟫| ≤ ‖k‖ * ‖p‖ * ‖v‖ := by
    have h := (abs_real_inner_le_norm k (cross p v)).trans
      (mul_le_mul_of_nonneg_left (norm_cross_le p v) (norm_nonneg k))
    simpa only [mul_assoc] using h
  rw [tracePair, abs_div, abs_mul,
    abs_of_nonneg (mul_nonneg (sq_nonneg ‖k‖) (sq_nonneg ‖p‖))]
  calc
    _ ≤ ((‖p‖ * ‖k‖ * ‖w‖) * (‖k‖ * ‖p‖ * ‖v‖)) / (‖k‖ ^ 2 * ‖p‖ ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem norm_tiltPair_le (e k p w v : E3) (he : ‖e‖ = 1) :
    ‖tiltPair e k p w v‖ ≤ ‖w‖ * ‖v‖ := by
  rw [tiltPair, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul (abs_tracePair_le k p w v) (norm_tiltSymbol_le_one e (k + p) he)
    (norm_nonneg _) (mul_nonneg (norm_nonneg w) (norm_nonneg v))
  simpa only [mul_one] using h

theorem tiltPair_add_left (e k p w z v : E3) :
    tiltPair e k p (w + z) v = tiltPair e k p w v + tiltPair e k p z v := by
  simp only [tiltPair, tracePair, cross_add_right, inner_add_right, add_mul, add_div, add_smul]

theorem tiltPair_add_right (e k p w v z : E3) :
    tiltPair e k p w (v + z) = tiltPair e k p w v + tiltPair e k p w z := by
  simp only [tiltPair, tracePair, cross_add_right, inner_add_right, mul_add, add_div, add_smul]

theorem tiltPair_smul_left (r : ℝ) (e k p w v : E3) :
    tiltPair e k p (r • w) v = r • tiltPair e k p w v := by
  simp only [tiltPair, tracePair, cross_smul_right, real_inner_smul_right, smul_smul]
  congr 1
  ring

theorem tiltPair_smul_right (r : ℝ) (e k p w v : E3) :
    tiltPair e k p w (r • v) = r • tiltPair e k p w v := by
  simp only [tiltPair, tracePair, cross_smul_right, real_inner_smul_right, smul_smul]
  congr 1
  ring

theorem longitudinal_mul_amplitude_le_add_divergence (e k w : E3) :
    |⟪k, e⟫| / ‖k‖ * |⟪e, w⟫| ≤ ‖lineRemainder e w‖ + |⟪k, w⟫| / ‖k‖ := by
  by_cases hk : k = 0
  · simp only [hk, inner_zero_left, abs_zero, norm_zero, zero_div, zero_mul, add_zero]
    exact norm_nonneg _
  have hkn := norm_pos_iff.mpr hk
  have h : |⟪e, w⟫| * |⟪k, e⟫| ≤ |⟪k, w⟫| + ‖k‖ * ‖lineRemainder e w‖ := by
    calc
      _ = |⟪k, w⟫ - ⟪k, lineRemainder e w⟫| := by
        rw [lineRemainder, inner_sub_right, real_inner_smul_right, sub_sub_cancel, abs_mul]
      _ ≤ |⟪k, w⟫| + |⟪k, lineRemainder e w⟫| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ⟪k, w⟫ 0 ⟪k, lineRemainder e w⟫
      _ ≤ _ := add_le_add le_rfl (abs_real_inner_le_norm k (lineRemainder e w))
  apply (le_of_mul_le_mul_left (a := ‖k‖) ?_ hkn)
  calc
    _ = |⟪e, w⟫| * |⟪k, e⟫| := by field_simp
    _ ≤ |⟪k, w⟫| + ‖k‖ * ‖lineRemainder e w‖ := h
    _ = _ := by field_simp; ring

theorem longitudinal_mul_amplitude_le (e k w : E3) (hw : ⟪k, w⟫ = 0) :
    |⟪k, e⟫| / ‖k‖ * |⟪e, w⟫| ≤ ‖lineRemainder e w‖ := by
  simpa only [hw, abs_zero, zero_div, add_zero] using longitudinal_mul_amplitude_le_add_divergence e k w

theorem tiltPair_decomposition (e k p w v : E3) :
    tiltPair e k p w v =
      (⟪e, w⟫ * ⟪e, v⟫) • tiltPair e k p e e +
        ⟪e, w⟫ • tiltPair e k p e (lineRemainder e v) +
        tiltPair e k p (lineRemainder e w) v := by
  have hw : w = ⟪e, w⟫ • e + lineRemainder e w := by unfold lineRemainder; abel
  have hv : v = ⟪e, v⟫ • e + lineRemainder e v := by unfold lineRemainder; abel
  have hleft : tiltPair e k p w v =
      ⟪e, w⟫ • tiltPair e k p e v + tiltPair e k p (lineRemainder e w) v := by
    calc
      _ = tiltPair e k p (⟪e, w⟫ • e + lineRemainder e w) v := congrArg (fun z ↦ tiltPair e k p z v) hw
      _ = _ := by rw [tiltPair_add_left, tiltPair_smul_left]
  have hright : tiltPair e k p e v =
      ⟪e, v⟫ • tiltPair e k p e e + tiltPair e k p e (lineRemainder e v) := by
    calc
      _ = tiltPair e k p e (⟪e, v⟫ • e + lineRemainder e v) := congrArg (tiltPair e k p e) hv
      _ = _ := by rw [tiltPair_add_right, tiltPair_smul_right]
  rw [hleft, hright, smul_add, smul_smul]

/-- Localized amplitudes need not be divergence-free. The two normalized
divergence defects are retained as separate boundary costs. -/
theorem norm_tiltPair_le_misalignment_add_divergence (e k p w v : E3) (he : ‖e‖ = 1) :
    ‖tiltPair e k p w v‖ ≤
      2 * (‖lineRemainder e w‖ * ‖v‖ + ‖w‖ * ‖lineRemainder e v‖) +
        |⟪k, w⟫| / ‖k‖ * ‖v‖ + ‖w‖ * (|⟪p, v⟫| / ‖p‖) := by
  have ha : |⟪e, w⟫| ≤ ‖w‖ := by simpa only [he, one_mul] using abs_real_inner_le_norm e w
  have hb : |⟪e, v⟫| ≤ ‖v‖ := by simpa only [he, one_mul] using abs_real_inner_le_norm e v
  have hka := longitudinal_mul_amplitude_le_add_divergence e k w
  have hpb := longitudinal_mul_amplitude_le_add_divergence e p v
  have hcoh := mul_le_mul_of_nonneg_left (norm_tiltPair_coherent_le e k p he)
    (mul_nonneg (abs_nonneg ⟪e, w⟫) (abs_nonneg ⟪e, v⟫))
  have hA := mul_le_mul_of_nonneg_right hka (abs_nonneg ⟪e, v⟫)
  have hB := mul_le_mul_of_nonneg_right hpb (abs_nonneg ⟪e, w⟫)
  have hAv := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ‖lineRemainder e w‖ + |⟪k, w⟫| / ‖k‖ by positivity)
  have hBw := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ ‖lineRemainder e v‖ + |⟪p, v⟫| / ‖p‖ by positivity)
  have hfirst : ‖(⟪e, w⟫ * ⟪e, v⟫) • tiltPair e k p e e‖ ≤
      (‖lineRemainder e w‖ + |⟪k, w⟫| / ‖k‖) * ‖v‖ +
        ‖w‖ * (‖lineRemainder e v‖ + |⟪p, v⟫| / ‖p‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    nlinarith only [hcoh, hA, hB, hAv, hBw]
  have hsecond : ‖⟪e, w⟫ • tiltPair e k p e (lineRemainder e v)‖ ≤
      ‖w‖ * ‖lineRemainder e v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have h := norm_tiltPair_le e k p e (lineRemainder e v) he
    rw [he, one_mul] at h
    exact mul_le_mul ha h (norm_nonneg _) (norm_nonneg w)
  have hthird := norm_tiltPair_le e k p (lineRemainder e w) v he
  rw [tiltPair_decomposition]
  have hnorm := (norm_add_le
    ((⟪e, w⟫ * ⟪e, v⟫) • tiltPair e k p e e + ⟪e, w⟫ • tiltPair e k p e (lineRemainder e v))
    (tiltPair e k p (lineRemainder e w) v)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith only [hnorm, hfirst, hsecond, hthird]

/-- Arbitrary real divergence-free vorticity pairs. The gain is actual
direction misalignment, not a small wavevector-cone assumption. -/
theorem norm_tiltPair_le_misalignment (e k p w v : E3) (he : ‖e‖ = 1)
    (hw : ⟪k, w⟫ = 0) (hv : ⟪p, v⟫ = 0) :
    ‖tiltPair e k p w v‖ ≤
      2 * (‖lineRemainder e w‖ * ‖v‖ + ‖w‖ * ‖lineRemainder e v‖) := by
  simpa only [hw, hv, abs_zero, zero_div, zero_mul, mul_zero, add_zero] using
    norm_tiltPair_le_misalignment_add_divergence e k p w v he

end Mettapedia.FluidDynamics.NavierStokes.PressurePairMisalignment
