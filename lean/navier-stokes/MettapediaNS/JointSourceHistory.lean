import MettapediaNS.JointPressureCotangent
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Causal source transfer in the original joint metric

The complete pressure-parent source is Hess p-B^T B. Its work can be
estimated by the evolving joint metric's source norm, without replacing
it by separate pressure and parent norms or an inverse-viscosity charge.
The time comparison below retains all covariant diffusion. A compatible
interval uses the square increment of the accumulated source amplitude;
it does not receive a fresh initial allowance at a seam.

These are finite metric and scalar physical-time theorems. Continuous
stochastic construction and weak spatial integration are separate. The
source history and a physical curl-direction comparison still require a
finite bound from the full original fluid datum. No such bound or global
regularity is a hypothesis hidden in a history structure here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointSourceHistory

open Set MeasureTheory JointReceiverTensor JointTensorSymmetry TransportedFrameMetric
open scoped Matrix BigOperators

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Pair3" => Fin 3 × Fin 3
local notation "Mat9" => Matrix Pair3 Pair3 ℝ

theorem metric_pair_square_le (Q : Mat9) (hQ : Q.PosSemidef)
    (v w : Pair3 → ℝ) : pair Q v w ^ 2 ≤ pair Q v v * pair Q w w := by
  have hs : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.1
  have hn (r : ℝ) :
      0 ≤ pair Q v v * (r * r) + (-2 * pair Q v w) * r + pair Q w w := by
    have h := hQ.dotProduct_mulVec_nonneg (r • v - w)
    change 0 ≤ pair Q (r • v - w) (r • v - w) at h
    simp only [pair, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
    rw [show w ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (Q *ᵥ w) from pair_symm Q hs w v] at h
    unfold pair
    nlinarith only [h]
  have hd := discrim_le_zero hn
  unfold discrim at hd
  nlinarith only [hd]

theorem metric_pair_le_roots (Q : Mat9) (hQ : Q.PosSemidef)
    (v w : Pair3 → ℝ) :
    pair Q v w ≤ Real.sqrt (pair Q v v) * Real.sqrt (pair Q w w) := by
  have h := metric_pair_square_le Q hQ v w
  have hv : 0 ≤ pair Q v v := hQ.dotProduct_mulVec_nonneg v
  have hw : 0 ≤ pair Q w w := hQ.dotProduct_mulVec_nonneg w
  have hp := mul_nonneg (Real.sqrt_nonneg (pair Q v v)) (Real.sqrt_nonneg (pair Q w w))
  have he : (Real.sqrt (pair Q v v) * Real.sqrt (pair Q w w)) ^ 2 =
      pair Q v v * pair Q w w := by
    rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hw]
  nlinarith only [h, hp, he]

/-- The source norm retains the complete joint source, including its
pressure-parent cross term. No spatial derivative is removed. -/
theorem tensor_source_production_le (ν : ℝ) (Q : Mat9) (hQ : Q.PosSemidef)
    (B Y S : Mat3) (K : Fin 3 → Mat9)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (dY : Fin 3 → Mat3) :
    production ν Q B Y 0 S K dY + 2 * ν * diffusionCost Q Y K dY ≤
      2 * Real.sqrt (normalizedSquare Q Y) * Real.sqrt (normalizedSquare Q S) := by
  rw [production_eq ν Q (Matrix.isHermitian_iff_isSymm.mp hQ.1) B Y 0 S K hK]
  simp only [sourceWork, retainedSource, mul_zero, sub_zero]
  have h := metric_pair_le_roots Q hQ (flatten Y) (flatten S)
  unfold normalizedSquare
  nlinarith only [h]

theorem defect_source_square (Q : Mat9) (hQ : Q.IsSymm) (B P : Mat3) :
    normalizedSquare Q (gradientDefectSource B P) =
      normalizedSquare Q P + normalizedSquare Q (B.transpose * B) -
        2 * pair Q (flatten P) (flatten (B.transpose * B)) := by
  change pair Q (flatten P - flatten (B.transpose * B))
    (flatten P - flatten (B.transpose * B)) = _
  rw [pair_sub_self Q hQ]
  unfold normalizedSquare
  ring

/-- The actual compatibility source from the canonical gradient-rate
bridge is used, rather than an independent control or omitted pressure. -/
theorem defect_source_production_le (ν : ℝ) (Q : Mat9) (hQ : Q.PosSemidef)
    (B A P : Mat3) (K : Fin 3 → Mat9)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (dE : Fin 3 → Mat3) :
    production ν Q B (gradientDefect A B) 0 (gradientDefectSource B P) K dE +
        2 * ν * diffusionCost Q (gradientDefect A B) K dE ≤
      2 * Real.sqrt (normalizedSquare Q (gradientDefect A B)) *
        Real.sqrt (normalizedSquare Q (gradientDefectSource B P)) :=
  tensor_source_production_le ν Q hQ B _ _ K hK dE

section Time

variable {s t : ℝ} (hst : s ≤ t) (q q' B b d : ℝ → ℝ)
    (hq : ∀ r ∈ Icc s t, 0 ≤ q r)
    (hb : ∀ r ∈ Icc s t, 0 ≤ b r)
    (hd : ∀ r ∈ Icc s t, 0 ≤ d r)
    (hqd : ∀ r ∈ Icc s t, HasDerivWithinAt q (q' r) (Icc s t) r)
    (hBd : ∀ r ∈ Icc s t, HasDerivWithinAt B (b r) (Icc s t) r)
    (hwork : ∀ r ∈ Icc s t, q' r + d r ≤ 2 * Real.sqrt (q r) * b r)

include hst hq hb hd hqd hBd hwork

/-- The regularized square-root comparison is valid even when the
initial or intermediate energy vanishes. It retains the seam energy. -/
theorem root_history_le (r : ℝ) (hr : r ∈ Icc s t) :
    Real.sqrt (q r) ≤ Real.sqrt (q s) + B r - B s := by
  have hqc : ContinuousOn q (Icc s t) := fun x hx ↦ (hqd x hx).continuousWithinAt
  have hBc : ContinuousOn B (Icc s t) := fun x hx ↦ (hBd x hx).continuousWithinAt
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos (x : ℝ) (hx : x ∈ Icc s t) : 0 < q x + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (hq x hx) (sq_pos_of_pos hε)
  let g : ℝ → ℝ := fun x ↦ Real.sqrt (q x + ε ^ 2) - B x
  have hg : ContinuousOn g (Icc s t) :=
    (Real.continuous_sqrt.comp_continuousOn (hqc.add continuousOn_const)).sub hBc
  have hg' (x : ℝ) (hx : x ∈ interior (Icc s t)) :
      HasDerivWithinAt g (q' x / (2 * Real.sqrt (q x + ε ^ 2)) - b x)
        (interior (Icc s t)) x := by
    have hi := interior_subset hx
    exact (((hqd x hi).add_const (ε ^ 2)).sqrt (hpos x hi).ne').sub
      (hBd x hi) |>.mono interior_subset
  have hn (x : ℝ) (hx : x ∈ interior (Icc s t)) :
      q' x / (2 * Real.sqrt (q x + ε ^ 2)) - b x ≤ 0 := by
    have hi := interior_subset hx
    have hsqrt := Real.sqrt_le_sqrt (show q x ≤ q x + ε ^ 2 by nlinarith only [sq_nonneg ε])
    have hm := mul_le_mul_of_nonneg_right hsqrt (hb x hi)
    have hw := hwork x hi
    have hp : 0 < 2 * Real.sqrt (q x + ε ^ 2) :=
      mul_pos (by norm_num) (Real.sqrt_pos.2 (hpos x hi))
    apply sub_nonpos.mpr
    apply (div_le_iff₀ hp).2
    nlinarith only [hm, hw, hd x hi]
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) hg hg' hn
  have he := hm (show s ∈ Icc s t from ⟨le_rfl, hst⟩) hr hr.1
  change Real.sqrt (q r + ε ^ 2) - B r ≤ Real.sqrt (q s + ε ^ 2) - B s at he
  have hs := Real.sqrt_le_sqrt (show q r ≤ q r + ε ^ 2 by nlinarith only [sq_nonneg ε])
  have hbnd : Real.sqrt (q s + ε ^ 2) ≤ Real.sqrt (q s) + ε := by
    apply Real.sqrt_le_iff.2
    refine ⟨add_nonneg (Real.sqrt_nonneg _) hε.le, ?_⟩
    have hs0 := Real.sq_sqrt (hq s ⟨le_rfl, hst⟩)
    nlinarith only [hs0, mul_nonneg (Real.sqrt_nonneg (q s)) hε.le]
  linarith only [he, hs, hbnd]

/-- The completed energy minus the original running square is antitone.
Z is the literal cumulative diffusion primitive, not an assumed reserve. -/
theorem completed_history_antitone (Z : ℝ → ℝ)
    (hZd : ∀ r ∈ Icc s t, HasDerivWithinAt Z (d r) (Icc s t) r) :
    AntitoneOn (fun r ↦ q r + Z r - (Real.sqrt (q s) + B r - B s) ^ 2) (Icc s t) := by
  have hqc : ContinuousOn q (Icc s t) := fun x hx ↦ (hqd x hx).continuousWithinAt
  have hBc : ContinuousOn B (Icc s t) := fun x hx ↦ (hBd x hx).continuousWithinAt
  have hZc : ContinuousOn Z (Icc s t) := fun x hx ↦ (hZd x hx).continuousWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
    ((hqc.add hZc).sub ((continuousOn_const.add hBc).sub continuousOn_const |>.pow 2))
    (f' := fun x ↦ q' x + d x -
      2 * (Real.sqrt (q s) + B x - B s) * b x)
  · intro x hx
    have hi := interior_subset hx
    have hh := (((hBd x hi).const_add (Real.sqrt (q s))).sub_const (B s)).pow 2
    convert! ((hqd x hi).add (hZd x hi)).sub hh |>.mono interior_subset using 1
    simp
  · intro x hx
    have hi := interior_subset hx
    have hn := root_history_le hst q q' B b d hq hb hd hqd hBd hwork x hi
    have hm := mul_le_mul_of_nonneg_right hn (hb x hi)
    have hw := hwork x hi
    linarith only [hm, hw]

/-- Every interval uses the same accumulated amplitude, retaining the
interaction with all earlier source history. -/
theorem compatible_interval_cost (Z : ℝ → ℝ)
    (hZd : ∀ r ∈ Icc s t, HasDerivWithinAt Z (d r) (Icc s t) r)
    (r v : ℝ) (hr : r ∈ Icc s t) (hv : v ∈ Icc s t) (hrv : r ≤ v) :
    q v - q r + Z v - Z r ≤
      (Real.sqrt (q s) + B v - B s) ^ 2 -
        (Real.sqrt (q s) + B r - B s) ^ 2 := by
  have h := completed_history_antitone hst q q' B b d hq hb hd hqd hBd hwork Z hZd hr hv hrv
  linarith only [h]

theorem completed_prefix_bound (Z : ℝ → ℝ)
    (hZd : ∀ r ∈ Icc s t, HasDerivWithinAt Z (d r) (Icc s t) r)
    (r : ℝ) (hr : r ∈ Icc s t) :
    q r + Z r - Z s ≤ (Real.sqrt (q s) + B r - B s) ^ 2 := by
  have h := compatible_interval_cost hst q q' B b d hq hb hd hqd hBd hwork Z hZd
    s r ⟨le_rfl, hst⟩ hr hr.1
  have he : (Real.sqrt (q s) + B s - B s) ^ 2 = q s := by
    rw [add_sub_cancel_right, Real.sq_sqrt (hq s ⟨le_rfl, hst⟩)]
  rw [he] at h
  linarith only [h]

end Time

/-- Continuous source and diffusion densities give the literal physical
integrals. Bounding the source integral from original fluid data is still
required; it is not supplied by this comparison theorem. -/
theorem integrated_source_history {T : ℝ} (hT : 0 ≤ T)
    (q q' b d : ℝ → ℝ) (hzero : q 0 = 0)
    (hq : ∀ r ∈ Icc 0 T, 0 ≤ q r)
    (hb : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hd : ∀ r ∈ Icc 0 T, 0 ≤ d r)
    (hqd : ∀ r ∈ Icc 0 T, HasDerivWithinAt q (q' r) (Icc 0 T) r)
    (hbc : Continuous b) (hdc : Continuous d)
    (hwork : ∀ r ∈ Icc 0 T, q' r + d r ≤ 2 * Real.sqrt (q r) * b r) :
    q T + (∫ r in (0 : ℝ)..T, d r) ≤ (∫ r in (0 : ℝ)..T, b r) ^ 2 := by
  let B : ℝ → ℝ := fun x ↦ ∫ r in (0 : ℝ)..x, b r
  let Z : ℝ → ℝ := fun x ↦ ∫ r in (0 : ℝ)..x, d r
  have hBd (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt B (b r) (Icc 0 T) r :=
    (intervalIntegral.integral_hasDerivAt_right (hbc.intervalIntegrable 0 r)
      hbc.aestronglyMeasurable.stronglyMeasurableAtFilter hbc.continuousAt).hasDerivWithinAt
  have hZd (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt Z (d r) (Icc 0 T) r :=
    (intervalIntegral.integral_hasDerivAt_right (hdc.intervalIntegrable 0 r)
      hdc.aestronglyMeasurable.stronglyMeasurableAtFilter hdc.continuousAt).hasDerivWithinAt
  have h := completed_prefix_bound hT q q' B b d hq hb hd hqd hBd hwork Z hZd T ⟨hT, le_rfl⟩
  simpa only [B, Z, intervalIntegral.integral_same, hzero, Real.sqrt_zero,
    zero_add, sub_zero] using h

def remainingReserve (cap running : ℝ) : ℝ := cap ^ 2 - running ^ 2

/-- A datum-fixed cap must be proved for the original running amplitude.
Without that cap this expression need not remain nonnegative. -/
theorem remainingReserve_nonneg (cap running : ℝ) (hr : 0 ≤ running)
    (hc : running ≤ cap) : 0 ≤ remainingReserve cap running := by
  unfold remainingReserve
  have hn : 0 ≤ cap := hr.trans hc
  nlinarith only [hr, hc, hn]

theorem reserve_payment (cap x y cost : ℝ) (hc : cost ≤ y ^ 2 - x ^ 2) :
    cost ≤ remainingReserve cap x - remainingReserve cap y := by
  unfold remainingReserve
  linarith only [hc]

/-- The previous accumulated amplitude creates a genuine cross cost.
Replacing the interval by a fresh source square forgets that history. -/
theorem square_increment (old fresh : ℝ) :
    (old + fresh) ^ 2 - old ^ 2 = 2 * old * fresh + fresh ^ 2 := by ring

theorem fresh_square_strictly_underpays (old fresh : ℝ)
    (ho : 0 < old) (hf : 0 < fresh) :
    fresh ^ 2 < (old + fresh) ^ 2 - old ^ 2 := by
  rw [square_increment]
  have hp := mul_pos ho hf
  nlinarith only [hp]

end Mettapedia.FluidDynamics.NavierStokes.JointSourceHistory
