import MettapediaNS.JointReceiverTensor

/-!
# Physical curl in the retained joint area metric

The original-gradient packet has a paid inverse-joint-metric norm.
Its curl only requires the forward area moment in its actual direction,
rather than coercivity in every direction of the two-index moment.
The finite same-law conversion below retains that geometric cost.

For the unforced triangular mixing class the forward frames have a
datum-fixed entry budget. The finite triangular bound is certified here;
the stochastic/PDE construction and the physical-time class estimate
remain analytic. No arbitrary-history budget is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointCurlGeometry

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanSolenoidal WholeSpaceBetchov CovectorParentHistory
  JointReceiverTensor
open scoped Matrix BigOperators Kronecker

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Vec3" => Fin 3 → ℝ
local notation "Pair3" => Fin 3 × Fin 3
local notation "Mat9" => Matrix Pair3 Pair3 ℝ

def tensorCurl (A : Mat3) : Vec3 :=
  fun i ↦ A (i + 2) (i + 1) - A (i + 1) (i + 2)

theorem curl_pair (A : Mat3) (z : Vec3) :
    z ⬝ᵥ tensorCurl A = flatten (skewMatrix z) ⬝ᵥ flatten A := by
  simp [tensorCurl, flatten, skewMatrix, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_three]
  change z 0 * (A 2 1 - A 1 2) + z 1 * (A 0 2 - A 2 0) +
    z 2 * (A 1 0 - A 0 1) = _
  ring

private theorem metric_square_le (C : Mat9) (hC : C.PosSemidef)
    (a r : Pair3 → ℝ) :
    (TransportedFrameMetric.pair C a r) ^ 2 ≤
      TransportedFrameMetric.pair C r r * TransportedFrameMetric.pair C a a := by
  have hsym : C.IsSymm := Matrix.isHermitian_iff_isSymm.mp hC.1
  have hs (t : ℝ) : 0 ≤ TransportedFrameMetric.pair C a a -
      2 * t * TransportedFrameMetric.pair C a r +
        t ^ 2 * TransportedFrameMetric.pair C r r := by
    have hn := hC.dotProduct_mulVec_nonneg (a - t • r)
    have he : TransportedFrameMetric.pair C (a - t • r) (a - t • r) =
        TransportedFrameMetric.pair C a a - 2 * t * TransportedFrameMetric.pair C a r +
          t ^ 2 * TransportedFrameMetric.pair C r r := by
      simp only [TransportedFrameMetric.pair, Matrix.mulVec_sub, Matrix.mulVec_smul,
        sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [show r ⬝ᵥ (C *ᵥ a) = a ⬝ᵥ (C *ᵥ r) from
        TransportedFrameMetric.pair_symm C hsym r a]
      ring
    rwa [← he]
  have hd := discrim_le_zero (a := TransportedFrameMetric.pair C r r)
    (b := -2 * TransportedFrameMetric.pair C a r)
    (c := TransportedFrameMetric.pair C a a) (fun t ↦ by
      nlinarith only [hs t])
  simp only [discrim] at hd
  nlinarith only [hd]

variable {σ : Type*} [Fintype σ]

/-- Only the forward area cost in the chosen curl direction is retained. -/
theorem directional_curl_square_le (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (A : Mat3) (z : Vec3) :
    (z ⬝ᵥ tensorCurl A) ^ 2 ≤
      2 * normalizedSquare (jointMoment S)⁻¹ A *
        TransportedFrameMetric.pair S.forwardMoment z z := by
  let C := jointMoment S
  let a := C⁻¹ *ᵥ flatten A
  let r := flatten (skewMatrix z)
  have hC : C.PosDef := jointMoment_posDef S
  have hi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hC.isUnit.map Matrix.detMonoidHom)
  have ha : C *ᵥ a = flatten A := by
    change C *ᵥ (C⁻¹ *ᵥ flatten A) = _
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  have hsym : C.IsSymm := Matrix.isHermitian_iff_isSymm.mp hC.1
  have hp : TransportedFrameMetric.pair C a r = z ⬝ᵥ tensorCurl A := by
    rw [TransportedFrameMetric.pair_symm C hsym a r, TransportedFrameMetric.pair,
      ha, curl_pair]
  have hq : TransportedFrameMetric.pair C a a = normalizedSquare C⁻¹ A := by
    rw [TransportedFrameMetric.pair, ha, dotProduct_comm]
    rfl
  have he := metric_square_le C hC.posSemidef a r
  rw [hp, hq] at he
  have hr := joint_skew_area S hdet z
  change TransportedFrameMetric.pair C r r = _ at hr
  rw [hr] at he
  change _ ≤ 2 * normalizedSquare C⁻¹ A * _
  nlinarith only [he]

theorem actual_curl_square_le (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (x : Space) (A : Mat3)
    (hcurvature : (gradientMatrix m x - A).IsSymm) (z : Vec3) :
    (z ⬝ᵥ (fun i ↦ (vorticityField u).field x i)) ^ 2 ≤
      2 * normalizedSquare (jointMoment S)⁻¹ A *
        TransportedFrameMetric.pair S.forwardMoment z z := by
  rw [original_tensor_curl u m hγ x A hcurvature]
  exact directional_curl_square_le S hdet A z

/-- A bound only in the actual curl direction suffices for conversion.
No such bound is supplied for arbitrary evolving NS histories. -/
theorem curl_le_of_direction_budget (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (A : Mat3) (κ : ℝ) (hκ : 0 ≤ κ)
    (hgeom : TransportedFrameMetric.pair S.forwardMoment (tensorCurl A) (tensorCurl A) ≤
      κ * (tensorCurl A ⬝ᵥ tensorCurl A)) :
    tensorCurl A ⬝ᵥ tensorCurl A ≤ 2 * κ * normalizedSquare (jointMoment S)⁻¹ A := by
  have hd := directional_curl_square_le S hdet A (tensorCurl A)
  have hq := normalizedSquare_nonneg (jointMoment S)⁻¹
    (jointMoment_posDef S).inv.posSemidef A
  have hw : 0 ≤ tensorCurl A ⬝ᵥ tensorCurl A :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hh := mul_le_mul_of_nonneg_left hgeom
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hq)
  by_cases hz : tensorCurl A ⬝ᵥ tensorCurl A = 0
  · rw [hz]
    positivity
  · have hp : 0 < tensorCurl A ⬝ᵥ tensorCurl A := lt_of_le_of_ne hw (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      _ ≤ 2 * normalizedSquare (jointMoment S)⁻¹ A *
          TransportedFrameMetric.pair S.forwardMoment (tensorCurl A) (tensorCurl A) := by
        simpa only [pow_two] using hd
      _ ≤ 2 * normalizedSquare (jointMoment S)⁻¹ A *
          (κ * (tensorCurl A ⬝ᵥ tensorCurl A)) := hh
      _ = _ := by ring

/-- Frames that preserve the actual curl covector need no other
geometric payment. Planar flows share such a normal direction. -/
theorem invariant_curl_le (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (A : Mat3)
    (hfixed : ∀ s, (S.inverseFrame s).transpose *ᵥ tensorCurl A = tensorCurl A) :
    tensorCurl A ⬝ᵥ tensorCurl A ≤ 2 * normalizedSquare (jointMoment S)⁻¹ A := by
  have hg : TransportedFrameMetric.pair S.forwardMoment (tensorCurl A) (tensorCurl A) ≤
      1 * (tensorCurl A ⬝ᵥ tensorCurl A) := by
    unfold TransportedFrameMetric.pair
    rw [← S.receiverCost_eq_forward]
    simp only [CovectorJointParent.JointSamples.receiverCost, hfixed,
      ← Finset.sum_mul, S.weight_sum, one_mul]
    exact le_rfl
  simpa only [mul_one] using curl_le_of_direction_budget S hdet A 1 (by norm_num) hg

def frameSquare (J : Mat3) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, J i j ^ 2

theorem transpose_frame_square_le (J : Mat3) (z : Vec3) :
    (J.transpose *ᵥ z) ⬝ᵥ (J.transpose *ᵥ z) ≤ frameSquare J * (z ⬝ᵥ z) := by
  have hb (j : Fin 3) : (∑ i : Fin 3, J i j * z i) ^ 2 ≤
      (∑ i : Fin 3, J i j ^ 2) * ∑ i : Fin 3, z i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ J i j) z
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦ hb j)
  simp only [← Finset.sum_mul] at hs
  rw [Finset.sum_comm] at hs
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, ← pow_two,
    frameSquare] using hs

theorem receiver_le_of_frame_budget (S : CovectorJointParent.JointSamples σ)
    (κ : ℝ) (hframe : ∀ s, frameSquare (S.inverseFrame s) ≤ κ) (z : Vec3) :
    TransportedFrameMetric.pair S.forwardMoment z z ≤ κ * (z ⬝ᵥ z) := by
  unfold TransportedFrameMetric.pair
  rw [← S.receiverCost_eq_forward]
  have hz : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have he (s : σ) : ((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ
      ((S.inverseFrame s).transpose *ᵥ z) ≤ κ * (z ⬝ᵥ z) :=
    (transpose_frame_square_le _ z).trans (mul_le_mul_of_nonneg_right (hframe s) hz)
  unfold CovectorJointParent.JointSamples.receiverCost
  calc
    _ ≤ ∑ s, S.weight s * (κ * (z ⬝ᵥ z)) :=
      Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (he s) (S.weight_nonneg s)
    _ = κ * (z ⬝ᵥ z) := by rw [← Finset.sum_mul, S.weight_sum, one_mul]

def triangularFrame (b c d : ℝ) : Mat3 := !![1, b, 0; 0, 1, 0; c, d, 1]

theorem triangularFrame_det (b c d : ℝ) : (triangularFrame b c d).det = 1 := by
  simp [triangularFrame, Matrix.det_fin_three]

theorem triangularFrame_square (b c d : ℝ) :
    frameSquare (triangularFrame b c d) = 3 + b ^ 2 + c ^ 2 + d ^ 2 := by
  simp [frameSquare, triangularFrame, Fin.sum_univ_three]
  ring

def triangularBudget (r s : ℝ) : ℝ := 3 + r ^ 2 + s ^ 2 + (r * s) ^ 2

theorem triangularBudget_nonneg (r s : ℝ) : 0 ≤ triangularBudget r s := by
  unfold triangularBudget
  positivity

theorem triangular_frame_le (b c d r s : ℝ) (_hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hb : |b| ≤ r) (hc : |c| ≤ s) (hd : |d| ≤ r * s) :
    frameSquare (triangularFrame b c d) ≤ triangularBudget r s := by
  have hb2 : b ^ 2 ≤ r ^ 2 := by nlinarith only [sq_abs b, hb, abs_nonneg b, _hr]
  have hc2 : c ^ 2 ≤ s ^ 2 := by nlinarith only [sq_abs c, hc, abs_nonneg c, _hs]
  have hd2 : d ^ 2 ≤ (r * s) ^ 2 := by
    nlinarith only [sq_abs d, hd, abs_nonneg d, mul_nonneg _hr _hs]
  rw [triangularFrame_square, triangularBudget]
  linarith only [hb2, hc2, hd2]

/-- The original path entry budget gives a uniform curl conversion for
the triangular class, once its stochastic construction is identified. -/
theorem triangular_curl_le (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ j, (S.frame j).det = 1) (A : Mat3)
    (b c d : σ → ℝ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hJ : ∀ j, S.inverseFrame j = triangularFrame (b j) (c j) (d j))
    (hb : ∀ j, |b j| ≤ r) (hc : ∀ j, |c j| ≤ s) (hd : ∀ j, |d j| ≤ r * s) :
    tensorCurl A ⬝ᵥ tensorCurl A ≤
      2 * triangularBudget r s * normalizedSquare (jointMoment S)⁻¹ A := by
  apply curl_le_of_direction_budget S hdet A _ (triangularBudget_nonneg r s)
  apply receiver_le_of_frame_budget S
  intro j
  rw [hJ j]
  exact triangular_frame_le _ _ _ r s hr hs (hb j) (hc j) (hd j)

end Mettapedia.FluidDynamics.NavierStokes.JointCurlGeometry
