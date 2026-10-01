import MettapediaNS.JointCurlGeometry
import MettapediaNS.JointCoframePressure
import Mathlib.Tactic.NoncommRing

/-!
# Symmetric and curl channels of the original joint tensor

The two copies of each frame are identical. Their joint moment and its
inverse preserve symmetric and skew tensors. The normalized quadratic
energy splits exactly; its skew part is half the inverse-forward-moment
vorticity energy. No symmetric/skew cross payment is hidden in this norm.

The physical gradient-compatibility defect A-grad u is a different
quantity. Its supplied original-tensor rate and literal canonical NS
gradient rate retain Hess p-B^T B. The finite identities below do not
bound that source over arbitrary histories. Continuous stochastic and
physical-time identification remain separate analytic obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointTensorSymmetry

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanSolenoidal WholeSpaceBetchov CovectorParentHistory
  JointReceiverTensor JointCurlGeometry
open scoped Matrix BigOperators Kronecker

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Vec3" => Fin 3 → ℝ
local notation "Pair3" => Fin 3 × Fin 3
local notation "Mat9" => Matrix Pair3 Pair3 ℝ

def transposeVector (v : Pair3 → ℝ) : Pair3 → ℝ := fun ij ↦ v (ij.2, ij.1)

def symmetricPart (A : Mat3) : Mat3 := (1 / 2 : ℝ) • (A + A.transpose)

def skewPart (A : Mat3) : Mat3 := (1 / 2 : ℝ) • (A - A.transpose)

theorem tensor_decomposition (A : Mat3) : A = symmetricPart A + skewPart A := by
  ext i j
  simp [symmetricPart, skewPart]
  ring

private theorem flatten_add (A B : Mat3) : flatten (A + B) = flatten A + flatten B := rfl

private theorem transpose_dot (v w : Pair3 → ℝ) :
    transposeVector v ⬝ᵥ w = v ⬝ᵥ transposeVector w := by
  simp [transposeVector, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

private theorem symmetric_fixed (A : Mat3) :
    transposeVector (flatten (symmetricPart A)) = flatten (symmetricPart A) := by
  ext ij
  simp [transposeVector, flatten, symmetricPart]
  ring

private theorem skew_negated (A : Mat3) :
    transposeVector (flatten (skewPart A)) = -flatten (skewPart A) := by
  ext ij
  simp [transposeVector, flatten, skewPart]
  ring

private theorem kronecker_transpose (G : Mat3) (v : Pair3 → ℝ) :
    (G ⊗ₖ G) *ᵥ transposeVector v = transposeVector ((G ⊗ₖ G) *ᵥ v) := by
  ext ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [transposeVector, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

variable {σ : Type*} [Fintype σ]

theorem jointMoment_transpose (S : CovectorJointParent.JointSamples σ) (v : Pair3 → ℝ) :
    jointMoment S *ᵥ transposeVector v = transposeVector (jointMoment S *ᵥ v) := by
  rw [jointMoment_eq_jointGram]
  ext ij
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, transposeVector]
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg (fun z ↦ S.weight s * z)
    (congrFun (kronecker_transpose ((S.frame s).transpose * S.frame s) v) ij)

theorem jointInverse_transpose (S : CovectorJointParent.JointSamples σ) (v : Pair3 → ℝ) :
    (jointMoment S)⁻¹ *ᵥ transposeVector v =
      transposeVector ((jointMoment S)⁻¹ *ᵥ v) := by
  have hu := (jointMoment_posDef S).isUnit.map Matrix.detMonoidHom
  have hi : jointMoment S * (jointMoment S)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hj : (jointMoment S)⁻¹ * jointMoment S = 1 := Matrix.nonsing_inv_mul _ hu
  have he : jointMoment S *ᵥ ((jointMoment S)⁻¹ *ᵥ transposeVector v) =
      jointMoment S *ᵥ transposeVector ((jointMoment S)⁻¹ *ᵥ v) := by
    rw [jointMoment_transpose, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  have hf := congrArg (fun z ↦ (jointMoment S)⁻¹ *ᵥ z) he
  simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hj, Matrix.one_mul,
    Matrix.one_mulVec] using hf

/-- The retained inverse metric has no pairing between the two channels. -/
theorem inverse_channel_orthogonal (S : CovectorJointParent.JointSamples σ)
    (v w : Pair3 → ℝ) (hv : transposeVector v = v) (hw : transposeVector w = -w) :
    TransportedFrameMetric.pair (jointMoment S)⁻¹ v w = 0 := by
  have he := transpose_dot v ((jointMoment S)⁻¹ *ᵥ w)
  rw [hv, ← jointInverse_transpose, hw, Matrix.mulVec_neg, dotProduct_neg] at he
  unfold TransportedFrameMetric.pair
  linarith only [he]

theorem symmetric_skew_orthogonal (S : CovectorJointParent.JointSamples σ) (A B : Mat3) :
    TransportedFrameMetric.pair (jointMoment S)⁻¹ (flatten (symmetricPart A))
      (flatten (skewPart B)) = 0 :=
  inverse_channel_orthogonal S _ _ (symmetric_fixed A) (skew_negated B)

theorem normalized_tensor_split (S : CovectorJointParent.JointSamples σ) (A : Mat3) :
    normalizedSquare (jointMoment S)⁻¹ A =
      normalizedSquare (jointMoment S)⁻¹ (symmetricPart A) +
        normalizedSquare (jointMoment S)⁻¹ (skewPart A) := by
  have hs : ((jointMoment S)⁻¹).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (jointMoment_posDef S).inv.1
  have hcross := symmetric_skew_orthogonal S A A
  have hreverse := TransportedFrameMetric.pair_symm (jointMoment S)⁻¹ hs
    (flatten (skewPart A)) (flatten (symmetricPart A))
  rw [hcross] at hreverse
  conv_lhs => rw [tensor_decomposition A]
  simp only [normalizedSquare, flatten_add, TransportedFrameMetric.pair,
    Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  unfold TransportedFrameMetric.pair at hcross hreverse
  rw [hcross, hreverse]
  ring

private theorem kronecker_skew (G : Mat3) (hG : G.IsSymm) (z : Vec3) :
    (G ⊗ₖ G) *ᵥ flatten (skewMatrix z) = flatten (skewMatrix (G.adjugate *ᵥ z)) := by
  have h01 : G 1 0 = G 0 1 := hG.apply 0 1
  have h02 : G 2 0 = G 0 2 := hG.apply 0 2
  have h12 : G 2 1 = G 1 2 := hG.apply 1 2
  ext ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [flatten, skewMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.adjugate_fin_three,
      h01, h02, h12] <;> ring

theorem jointMoment_skew (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (z : Vec3) :
    jointMoment S *ᵥ flatten (skewMatrix z) =
      flatten (skewMatrix (S.forwardMoment *ᵥ z)) := by
  rw [jointMoment_eq_jointGram, CovectorReceiverGeometry.forwardMoment_eq_sample_area S hdet]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
  simp_rw [kronecker_skew _ (Matrix.isSymm_transpose_mul_self _) z]
  ext ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [flatten, skewMatrix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_neg_distrib]

private theorem skew_flatten_ne_zero (z : Vec3) (hz : z ≠ 0) :
    flatten (skewMatrix z) ≠ 0 := by
  intro he
  apply hz
  ext i
  fin_cases i
  · simpa [flatten, skewMatrix] using congrFun he (2, 1)
  · simpa [flatten, skewMatrix] using congrFun he (0, 2)
  · simpa [flatten, skewMatrix] using congrFun he (1, 0)

theorem forwardMoment_posDef (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) : S.forwardMoment.PosDef := by
  have hpsd : S.forwardMoment.PosSemidef := by
    unfold CovectorJointParent.JointSamples.forwardMoment
    apply Matrix.posSemidef_sum
    intro s _
    have h := Matrix.posSemidef_self_mul_conjTranspose (S.inverseFrame s)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h.smul (S.weight_nonneg s)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1
  intro z hz
  have hpos := (jointMoment_posDef S).dotProduct_mulVec_pos (skew_flatten_ne_zero z hz)
  change 0 < TransportedFrameMetric.pair (jointMoment S)
    (flatten (skewMatrix z)) (flatten (skewMatrix z)) at hpos
  rw [joint_skew_area S hdet z] at hpos
  unfold TransportedFrameMetric.pair at hpos
  simp only [star_trivial]
  linarith only [hpos]

theorem jointInverse_skew (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (z : Vec3) :
    (jointMoment S)⁻¹ *ᵥ flatten (skewMatrix z) =
      flatten (skewMatrix ((S.forwardMoment)⁻¹ *ᵥ z)) := by
  have hM : S.forwardMoment * (S.forwardMoment)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((forwardMoment_posDef S hdet).isUnit.map Matrix.detMonoidHom)
  have hC : (jointMoment S)⁻¹ * jointMoment S = 1 :=
    Matrix.nonsing_inv_mul _ ((jointMoment_posDef S).isUnit.map Matrix.detMonoidHom)
  have he : jointMoment S *ᵥ flatten (skewMatrix ((S.forwardMoment)⁻¹ *ᵥ z)) =
      flatten (skewMatrix z) := by
    rw [jointMoment_skew S hdet, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  have hf := congrArg (fun v ↦ (jointMoment S)⁻¹ *ᵥ v) he
  rw [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] at hf
  exact hf.symm

private theorem skew_dot (v w : Vec3) :
    flatten (skewMatrix v) ⬝ᵥ flatten (skewMatrix w) = 2 * (v ⬝ᵥ w) := by
  simp [flatten, skewMatrix, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem normalized_skew_square (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (z : Vec3) :
    normalizedSquare (jointMoment S)⁻¹ (skewMatrix z) =
      2 * TransportedFrameMetric.pair (S.forwardMoment)⁻¹ z z := by
  rw [normalizedSquare, TransportedFrameMetric.pair, jointInverse_skew S hdet, skew_dot]
  rfl

theorem normalized_curl_channel (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (A : Mat3) :
    normalizedSquare (jointMoment S)⁻¹ (skewPart A) =
      (1 / 2 : ℝ) * TransportedFrameMetric.pair (S.forwardMoment)⁻¹
        (tensorCurl A) (tensorCurl A) := by
  have he : skewPart A = (1 / 2 : ℝ) • skewMatrix (tensorCurl A) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewPart, skewMatrix, tensorCurl]
  have hf (Y : Mat3) : flatten ((1 / 2 : ℝ) • Y) = (1 / 2 : ℝ) • flatten Y := rfl
  rw [he, normalizedSquare, hf]
  simp only [TransportedFrameMetric.pair, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  change (1 / 2 : ℝ) * ((1 / 2 : ℝ) * normalizedSquare (jointMoment S)⁻¹
    (skewMatrix (tensorCurl A))) = _
  rw [normalized_skew_square S hdet]
  unfold TransportedFrameMetric.pair
  ring

/-- A joint quadratic norm supplies no extra cross channel beyond the
nonnegative transported symmetric norm and inverse-area curl norm. -/
theorem normalized_original_split (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (A : Mat3) :
    normalizedSquare (jointMoment S)⁻¹ A =
      normalizedSquare (jointMoment S)⁻¹ (symmetricPart A) +
        (1 / 2 : ℝ) * TransportedFrameMetric.pair (S.forwardMoment)⁻¹
          (tensorCurl A) (tensorCurl A) := by
  rw [normalized_tensor_split, normalized_curl_channel S hdet]

/-- A spatial moment derivative that preserves transpose gives a
channel-preserving connection. Its physical construction is explicit. -/
theorem jointConnection_transpose (S : CovectorJointParent.JointSamples σ)
    (dC : Mat9) (hdC : ∀ v, dC *ᵥ transposeVector v = transposeVector (dC *ᵥ v))
    (v : Pair3 → ℝ) :
    (dC * (jointMoment S)⁻¹) *ᵥ transposeVector v =
      transposeVector ((dC * (jointMoment S)⁻¹) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, jointInverse_transpose, hdC, Matrix.mulVec_mulVec]

private theorem pair_channel_split (S : CovectorJointParent.JointSamples σ)
    (v w : Pair3 → ℝ) (hv : transposeVector v = v) (hw : transposeVector w = -w) :
    TransportedFrameMetric.pair (jointMoment S)⁻¹ (v + w) (v + w) =
      TransportedFrameMetric.pair (jointMoment S)⁻¹ v v +
        TransportedFrameMetric.pair (jointMoment S)⁻¹ w w := by
  have hs : ((jointMoment S)⁻¹).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (jointMoment_posDef S).inv.1
  have hc := inverse_channel_orthogonal S v w hv hw
  have hr := TransportedFrameMetric.pair_symm (jointMoment S)⁻¹ hs w v
  rw [hc] at hr
  unfold TransportedFrameMetric.pair at hc hr ⊢
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [hc, hr]
  ring

private theorem transpose_sub (v w : Pair3 → ℝ) :
    transposeVector (v - w) = transposeVector v - transposeVector w := rfl

/-- The full spatial diffusion separates only when the retained
connections preserve transpose; no connection or derivative is dropped. -/
theorem diffusion_channel_split (S : CovectorJointParent.JointSamples σ)
    (A : Mat3) (K : Fin 3 → Mat9) (dA : Fin 3 → Mat3)
    (hT : ∀ k v, K k *ᵥ transposeVector v = transposeVector (K k *ᵥ v)) :
    diffusionCost (jointMoment S)⁻¹ A K dA =
      diffusionCost (jointMoment S)⁻¹ (symmetricPart A) K (fun k ↦ symmetricPart (dA k)) +
        diffusionCost (jointMoment S)⁻¹ (skewPart A) K (fun k ↦ skewPart (dA k)) := by
  unfold diffusionCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  let v := flatten (symmetricPart (dA k)) - K k *ᵥ flatten (symmetricPart A)
  let w := flatten (skewPart (dA k)) - K k *ᵥ flatten (skewPart A)
  have hv : transposeVector v = v := by
    dsimp only [v]
    rw [transpose_sub, symmetric_fixed, ← hT k, symmetric_fixed]
  have hw : transposeVector w = -w := by
    dsimp only [w]
    rw [transpose_sub, skew_negated, ← hT k, skew_negated, Matrix.mulVec_neg]
    simp only [sub_eq_add_neg, neg_add, neg_neg]
  have he : flatten (dA k) - K k *ᵥ flatten A = v + w := by
    conv_lhs => rw [tensor_decomposition (dA k), tensor_decomposition A]
    simp only [flatten_add, Matrix.mulVec_add]
    dsimp only [v, w]
    abel
  rw [he]
  exact pair_channel_split S v w hv hw

/-- Supplied source-free production retains the complete diffusion
and has no transfer term between the symmetric and skew norms. -/
theorem original_production_split (ν : ℝ) (S : CovectorJointParent.JointSamples σ)
    (B A : Mat3) (K : Fin 3 → Mat9)
    (hK : ∀ k, (jointMoment S)⁻¹ * K k = (K k).transpose * (jointMoment S)⁻¹)
    (dA : Fin 3 → Mat3)
    (hT : ∀ k v, K k *ᵥ transposeVector v = transposeVector (K k *ᵥ v)) :
    production ν (jointMoment S)⁻¹ B A 0 0 K dA =
      production ν (jointMoment S)⁻¹ B (symmetricPart A) 0 0 K
        (fun k ↦ symmetricPart (dA k)) +
      production ν (jointMoment S)⁻¹ B (skewPart A) 0 0 K
        (fun k ↦ skewPart (dA k)) := by
  have hs : ((jointMoment S)⁻¹).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (jointMoment_posDef S).inv.1
  simp only [original_tensor_production ν _ hs B _ K hK]
  rw [diffusion_channel_split S A K dA hT]
  ring

/-- The split uses literal physical curl after the existing projection
and symmetric-curvature identification, not an independent curl variable. -/
theorem actual_original_split (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (x : Space) (A : Mat3)
    (hcurvature : (gradientMatrix m x - A).IsSymm) :
    normalizedSquare (jointMoment S)⁻¹ A =
      normalizedSquare (jointMoment S)⁻¹ (symmetricPart A) +
        (1 / 2 : ℝ) * TransportedFrameMetric.pair (S.forwardMoment)⁻¹
          (fun i ↦ (vorticityField u).field x i)
          (fun i ↦ (vorticityField u).field x i) := by
  have hc : (fun i ↦ (vorticityField u).field x i) = tensorCurl A :=
    original_tensor_curl u m hγ x A hcurvature
  rw [normalized_original_split S hdet, hc]

def gradientDefect (A B : Mat3) : Mat3 := A - B

def gradientDefectSource (B P : Mat3) : Mat3 := P - B.transpose * B

theorem gradient_defect_symmetric (A B : Mat3) (hc : tensorCurl A = tensorCurl B) :
    (gradientDefect A B).IsSymm := by
  have h0 : A 2 1 - A 1 2 = B 2 1 - B 1 2 := congrFun hc 0
  have h1 : A 0 2 - A 2 0 = B 0 2 - B 2 0 := congrFun hc 1
  have h2 : A 1 0 - A 0 1 = B 1 0 - B 0 1 := congrFun hc 2
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change A 1 0 - B 1 0 = A 0 1 - B 0 1
    linarith only [h2]
  · change A 2 0 - B 2 0 = A 0 2 - B 0 2
    linarith only [h1]
  · change A 0 1 - B 0 1 = A 1 0 - B 1 0
    linarith only [h2]
  · rfl
  · change A 2 1 - B 2 1 = A 1 2 - B 1 2
    linarith only [h0]
  · change A 0 2 - B 0 2 = A 2 0 - B 2 0
    linarith only [h1]
  · change A 1 2 - B 1 2 = A 2 1 - B 2 1
    linarith only [h0]
  · rfl

theorem actual_gradient_defect_symmetric (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (x : Space) (A : Mat3)
    (hcurvature : (gradientMatrix m x - A).IsSymm) :
    (gradientDefect A (gradientMatrix u x)).IsSymm := by
  apply gradient_defect_symmetric
  exact (original_tensor_curl u m hγ x A hcurvature).symm

theorem gradient_defect_rate (B A P : Mat3) :
    tensorRate B A 0 0 - (-B * B - P) =
      -B.transpose * gradientDefect A B - gradientDefect A B * B +
        gradientDefectSource B P := by
  unfold tensorRate retainedSource gradientDefect gradientDefectSource
  noncomm_ring

/-- A pressure Hessian has a symmetric source but need not have a
nonpositive source. The actual history must pay its signed work. -/
theorem gradient_defect_source_symmetric (B P : Mat3) (hP : P.IsSymm) :
    (gradientDefectSource B P).IsSymm := by
  unfold gradientDefectSource
  exact hP.sub (Matrix.isSymm_transpose_mul_self B)

/-- This supplied identity exposes the remaining signed pressure and
quadratic source together with the complete metric diffusion. -/
theorem gradient_defect_production (ν : ℝ) (Q : Mat9) (hQ : Q.IsSymm)
    (B A P : Mat3) (K : Fin 3 → Mat9)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (dE : Fin 3 → Mat3) :
    production ν Q B (gradientDefect A B) 0 (gradientDefectSource B P) K dE =
      2 * TransportedFrameMetric.pair Q (flatten (gradientDefect A B))
        (flatten (gradientDefectSource B P)) -
          2 * ν * diffusionCost Q (gradientDefect A B) K dE := by
  rw [production_eq ν Q hQ B _ 0 _ K hK]
  simp only [sourceWork, retainedSource, mul_zero, sub_zero]

/-- The current gradient rate is the literal canonical unforced NS RHS.
Identifying the original packet's supplied rate over time is separate. -/
theorem actual_gradient_defect_rate (ν : ℝ) (u : SmoothL2Field Space)
    (x : Space) (A : Mat3) :
    tensorRate (gradientMatrix u x) A 0 0 - JointCoframePressure.actualGradientRate ν u x =
      -(gradientMatrix u x).transpose * gradientDefect A (gradientMatrix u x) -
        gradientDefect A (gradientMatrix u x) * gradientMatrix u x +
          gradientDefectSource (gradientMatrix u x) (gradientMatrix (pressureField u) x) := by
  have hp : materialGradientRate ν u u x = -(gradientMatrix u x * gradientMatrix u x) := by
    rw [passive_gradient_rate]
    ext i j
    rfl
  rw [JointCoframePressure.actual_gradient_rate, hp]
  simpa only [neg_mul] using gradient_defect_rate (gradientMatrix u x) A
    (gradientMatrix (pressureField u) x)

end Mettapedia.FluidDynamics.NavierStokes.JointTensorSymmetry
