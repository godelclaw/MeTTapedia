import MettapediaNS.CovectorReceiverGeometry
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Joint stochastic frames for receiver and original-gradient tensors

The completed defect Y=R-grad H has two covariant indices. Its drift is
-B^T Y-YB, with the full retained source S-B^T grad H. Lifting both
indices on each original frame gives a joint Gram moment; its skew
channel is precisely the original forward area moment. Independent
averaging of the two frame copies does not preserve this moment.

The same lift transports the original datum's gradient tensor, with a
finite original-label Gram bound. A symmetric flow-curvature tensor
drops out of actual curl reconstruction; the source-free tensor packet
has complete normalized diffusion paid by its original gradient energy.

The existing transported-frame metric identity cancels both index
strains with complete diffusion on this lift. The continuous joint
moment construction, inverse differentiation, physical-time comparison,
source history allowance and uniform critical conversion remain analytic/open. In particular an
unforced fluid still has the internal source certified below.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointReceiverTensor

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal WholeSpaceViscousEnergy WholeSpaceBetchov
  EulerVectorCalculus WholeSpacePressureDiffusion CovectorParentHistory CovectorFluidBridge
open scoped Matrix BigOperators Kronecker

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Pair3" => Fin 3 × Fin 3
local notation "Mat9" => Matrix Pair3 Pair3 ℝ

def flatten (Y : Mat3) : Pair3 → ℝ := fun ij ↦ Y ij.1 ij.2

def twoIndexDrift (B : Mat3) : Mat9 :=
  (-B.transpose) ⊗ₖ (1 : Mat3) + (1 : Mat3) ⊗ₖ (-B.transpose)

def retainedSource (B BH S : Mat3) : Mat3 := S - B.transpose * BH

def tensorRate (B Y BH S : Mat3) : Mat3 :=
  -B.transpose * Y - Y * B + retainedSource B BH S

theorem tensor_rate (B Y BH S : Mat3) :
    flatten (tensorRate B Y BH S) =
      twoIndexDrift B *ᵥ flatten Y + flatten (retainedSource B BH S) := by
  ext ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [flatten, tensorRate, twoIndexDrift, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

/-- The actual completed receiver's supplied rate has this same tensor
drift and its original passive-parent source. -/
theorem completed_receiver_rate (B R BH P S : Mat3) :
    flatten (CovectorReceiverGeometry.completedDefectRate B R BH P S) =
      twoIndexDrift B *ᵥ flatten (R - BH) + flatten (retainedSource B BH S) := by
  rw [show CovectorReceiverGeometry.completedDefectRate B R BH P S =
      tensorRate B (R - BH) BH S by
    rw [CovectorReceiverGeometry.completed_defect_rate]
    unfold tensorRate retainedSource
    abel]
  exact tensor_rate B (R - BH) BH S

variable {σ : Type*} [Fintype σ]

def jointFrame (S : CovectorJointParent.JointSamples σ) (s : σ) : Mat9 :=
  S.frame s ⊗ₖ S.frame s

/-- Both index copies use the same sample. This is a fourth frame
moment, not a tensor product of separately averaged second moments. -/
def jointMoment (S : CovectorJointParent.JointSamples σ) : Mat9 :=
  ∑ s, S.weight s • ((jointFrame S s).transpose * jointFrame S s)

theorem jointMoment_eq_jointGram (S : CovectorJointParent.JointSamples σ) :
    jointMoment S = ∑ s, S.weight s •
      (((S.frame s).transpose * S.frame s) ⊗ₖ
        ((S.frame s).transpose * S.frame s)) := by
  unfold jointMoment jointFrame
  apply Finset.sum_congr rfl
  intro s _
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul]

theorem jointMoment_nonneg (S : CovectorJointParent.JointSamples σ) :
    (jointMoment S).PosSemidef := by
  unfold jointMoment
  apply Matrix.posSemidef_sum
  intro s _
  have hg : ((jointFrame S s).transpose * jointFrame S s).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (jointFrame S s)
  exact hg.smul (S.weight_nonneg s)

theorem jointFrame_left_inverse (S : CovectorJointParent.JointSamples σ) (s : σ) :
    (S.inverseFrame s ⊗ₖ S.inverseFrame s) * jointFrame S s = 1 := by
  rw [jointFrame, ← Matrix.mul_kronecker_mul, S.inverse_frame]
  simp

/-- Positivity follows from the normalized law and its invertible
original frames; it does not provide a uniform coercivity constant. -/
theorem jointMoment_posDef (S : CovectorJointParent.JointSamples σ) :
    (jointMoment S).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (jointMoment_nonneg S).1
  intro v hv
  have hsome : ∃ s, 0 < S.weight s := by
    have hw : 0 < ∑ s, S.weight s := by rw [S.weight_sum]; norm_num
    obtain ⟨s, _, hs⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun s _ ↦ S.weight_nonneg s)).mp hw
    exact ⟨s, hs⟩
  have hinj (s : σ) : Function.Injective (jointFrame S s).mulVec := by
    intro x y h
    have he := congrArg (fun z ↦ (S.inverseFrame s ⊗ₖ S.inverseFrame s) *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, jointFrame_left_inverse, Matrix.one_mulVec] using he
  have hg (s : σ) : ((jointFrame S s).transpose * jointFrame S s).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self (jointFrame S s) (hinj s)
  simp only [jointMoment, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (S.weight_nonneg s)
      ((hg s).posSemidef.dotProduct_mulVec_nonneg v)
  · obtain ⟨s, hs⟩ := hsome
    exact ⟨s, Finset.mem_univ s, mul_pos hs ((hg s).dotProduct_mulVec_pos hv)⟩

def skewMatrix (v : Fin 3 → ℝ) : Mat3 :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

/-- The skew channel of a two-index Gram is the three-dimensional
area Gram, with the factor two from the two skew entries. -/
theorem skew_gram_area (G : Mat3) (hG : G.IsSymm) (v : Fin 3 → ℝ) :
    TransportedFrameMetric.pair (G ⊗ₖ G) (flatten (skewMatrix v))
      (flatten (skewMatrix v)) = 2 * TransportedFrameMetric.pair G.adjugate v v := by
  simp [TransportedFrameMetric.pair, flatten, skewMatrix, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.adjugate_fin_three]
  simp only [hG.apply 0 1, hG.apply 0 2, hG.apply 1 2]
  ring

theorem joint_skew_area (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (v : Fin 3 → ℝ) :
    TransportedFrameMetric.pair (jointMoment S) (flatten (skewMatrix v))
      (flatten (skewMatrix v)) = 2 * TransportedFrameMetric.pair S.forwardMoment v v := by
  rw [jointMoment_eq_jointGram, CovectorReceiverGeometry.forwardMoment_eq_sample_area S hdet]
  simp only [TransportedFrameMetric.pair_matrix_sum, TransportedFrameMetric.pair_matrix_smul]
  simp_rw [skew_gram_area _ (Matrix.isSymm_transpose_mul_self _) v]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

def normalizedSquare (Q : Mat9) (Y : Mat3) : ℝ :=
  TransportedFrameMetric.pair Q (flatten Y) (flatten Y)

theorem normalizedSquare_nonneg (Q : Mat9) (hQ : Q.PosSemidef) (Y : Mat3) :
    0 ≤ normalizedSquare Q Y := hQ.dotProduct_mulVec_nonneg (flatten Y)

def diffusionCost (Q : Mat9) (Y : Mat3) (K : Fin 3 → Mat9)
    (dY : Fin 3 → Mat3) : ℝ :=
  ∑ k, TransportedFrameMetric.pair Q (flatten (dY k) - K k *ᵥ flatten Y)
    (flatten (dY k) - K k *ᵥ flatten Y)

theorem diffusionCost_nonneg (Q : Mat9) (hQ : Q.PosSemidef) (Y : Mat3)
    (K : Fin 3 → Mat9) (dY : Fin 3 → Mat3) : 0 ≤ diffusionCost Q Y K dY :=
  Finset.sum_nonneg fun k _ ↦
    hQ.dotProduct_mulVec_nonneg (flatten (dY k) - K k *ᵥ flatten Y)

def sourceWork (Q : Mat9) (B Y BH S : Mat3) : ℝ :=
  TransportedFrameMetric.pair Q (flatten Y) (flatten (retainedSource B BH S))

/-- The input metric is the inverse joint frame moment in the physical
application. Its full time rate and spatial connection remain explicit. -/
def production (ν : ℝ) (Q : Mat9) (B Y BH S : Mat3) (K : Fin 3 → Mat9)
    (dY : Fin 3 → Mat3) : ℝ :=
  TransportedFrameMetric.production ν Q (flatten Y) (flatten (tensorRate B Y BH S))
    (TransportedFrameMetric.rate ν Q (twoIndexDrift B) K)
    (fun k ↦ flatten (dY k)) (fun k ↦ TransportedFrameMetric.gradient Q (K k))

theorem production_eq (ν : ℝ) (Q : Mat9) (hQ : Q.IsSymm) (B Y BH S : Mat3)
    (K : Fin 3 → Mat9) (hK : ∀ k, Q * K k = (K k).transpose * Q)
    (dY : Fin 3 → Mat3) :
    production ν Q B Y BH S K dY =
      2 * sourceWork Q B Y BH S - 2 * ν * diffusionCost Q Y K dY := by
  rw [production, tensor_rate, TransportedFrameMetric.production_eq ν Q
    (twoIndexDrift B) hQ K hK]
  rfl

theorem production_le_source (ν : ℝ) (hν : 0 ≤ ν) (Q : Mat9) (hQ : Q.PosSemidef)
    (B Y BH S : Mat3) (K : Fin 3 → Mat9)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (dY : Fin 3 → Mat3) :
    production ν Q B Y BH S K dY ≤ 2 * sourceWork Q B Y BH S := by
  rw [production_eq ν Q (Matrix.isHermitian_iff_isSymm.mp hQ.1) B Y BH S K hK]
  have hc := diffusionCost_nonneg Q hQ Y K dY
  nlinarith only [mul_nonneg hν hc]

/-- V is the original label gradient in the physical construction.
Each label and both coframe copies remain on the same sample. -/
def transportedOriginalTensor (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) : Mat3 :=
  ∑ s, S.weight s • ((S.frame s).transpose * V s * S.frame s)

def originalTensorCovector (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) : Pair3 → ℝ :=
  ∑ s, S.weight s • ((jointFrame S s).transpose *ᵥ flatten (V s))

private theorem flatten_sample (F V : Mat3) :
    flatten (F.transpose * V * F) = (F ⊗ₖ F).transpose *ᵥ flatten V := by
  ext ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [flatten, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

theorem original_tensor_matches (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) :
    flatten (transportedOriginalTensor S V) = originalTensorCovector S V := by
  ext ij
  simp only [transportedOriginalTensor, originalTensorCovector,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flatten,
    Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro s _
  have hs := congrFun (flatten_sample (S.frame s) (V s)) ij
  exact congrArg (fun z ↦ S.weight s * z) hs

def originalTensorEnergy (S : CovectorJointParent.JointSamples σ) (V : σ → Mat3) : ℝ :=
  ∑ s, S.weight s * (flatten (V s) ⬝ᵥ flatten (V s))

def originalTensorVariance (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) (a : Pair3 → ℝ) : ℝ :=
  ∑ s, S.weight s * ((flatten (V s) - jointFrame S s *ᵥ a) ⬝ᵥ
    (flatten (V s) - jointFrame S s *ᵥ a))

theorem originalTensorVariance_nonneg (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) (a : Pair3 → ℝ) : 0 ≤ originalTensorVariance S V a := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (S.weight_nonneg s)
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

private theorem transpose_pair (F : Mat9) (a v : Pair3 → ℝ) :
    a ⬝ᵥ (F.transpose *ᵥ v) = (F *ᵥ a) ⬝ᵥ v := by
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem square_sub (v w : Pair3 → ℝ) :
    (v - w) ⬝ᵥ (v - w) = v ⬝ᵥ v - 2 * (w ⬝ᵥ v) + w ⬝ᵥ w := by
  simp only [sub_dotProduct, dotProduct_sub]
  rw [dotProduct_comm v w]
  ring

theorem originalTensorVariance_expansion (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) (a : Pair3 → ℝ) :
    originalTensorVariance S V a = originalTensorEnergy S V -
      2 * (a ⬝ᵥ originalTensorCovector S V) + a ⬝ᵥ (jointMoment S *ᵥ a) := by
  have he (s : σ) :
      S.weight s * ((flatten (V s) - jointFrame S s *ᵥ a) ⬝ᵥ
        (flatten (V s) - jointFrame S s *ᵥ a)) =
      S.weight s * (flatten (V s) ⬝ᵥ flatten (V s)) -
        2 * (S.weight s * (a ⬝ᵥ ((jointFrame S s).transpose *ᵥ flatten (V s)))) +
        S.weight s * (a ⬝ᵥ (((jointFrame S s).transpose * jointFrame S s) *ᵥ a)) := by
    rw [← Matrix.mulVec_mulVec, transpose_pair, transpose_pair, square_sub]
    ring
  simp only [originalTensorVariance, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, originalTensorEnergy, originalTensorCovector, jointMoment,
    Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem originalTensorVariance_deficit (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) (a : Pair3 → ℝ)
    (ha : jointMoment S *ᵥ a = originalTensorCovector S V) :
    originalTensorVariance S V a = originalTensorEnergy S V -
      a ⬝ᵥ originalTensorCovector S V := by
  rw [originalTensorVariance_expansion, ha]
  ring

theorem original_tensor_energy_le (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) (a : Pair3 → ℝ)
    (ha : jointMoment S *ᵥ a = originalTensorCovector S V) :
    a ⬝ᵥ originalTensorCovector S V ≤ originalTensorEnergy S V := by
  have hv := originalTensorVariance_nonneg S V a
  rw [originalTensorVariance_deficit S V a ha] at hv
  linarith only [hv]

/-- The finite original-label bound uses the actual inverse joint
moment, whose existence follows from the same original sample law. -/
theorem original_tensor_normalized_le (S : CovectorJointParent.JointSamples σ)
    (V : σ → Mat3) :
    normalizedSquare (jointMoment S)⁻¹ (transportedOriginalTensor S V) ≤
      originalTensorEnergy S V := by
  have hi : jointMoment S * (jointMoment S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _
      ((jointMoment_posDef S).isUnit.map Matrix.detMonoidHom)
  have ha : jointMoment S *ᵥ ((jointMoment S)⁻¹ *ᵥ originalTensorCovector S V) =
      originalTensorCovector S V := by
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  have hb := original_tensor_energy_le S V _ ha
  rw [normalizedSquare, original_tensor_matches, TransportedFrameMetric.pair]
  rw [dotProduct_comm]
  exact hb

/-- This is the source-free transported original-gradient packet.
The completed receiver Y has its separate, generally nonzero source. -/
theorem original_tensor_production (ν : ℝ) (Q : Mat9) (hQ : Q.IsSymm)
    (B A : Mat3) (K : Fin 3 → Mat9)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (dA : Fin 3 → Mat3) :
    production ν Q B A 0 0 K dA = -2 * ν * diffusionCost Q A K dA := by
  rw [production_eq ν Q hQ B A 0 0 K hK]
  have hz : flatten (0 : Mat3) = 0 := rfl
  simp only [sourceWork, retainedSource, mul_zero, sub_zero, hz,
    TransportedFrameMetric.pair, Matrix.mulVec_zero, dotProduct_zero,
    mul_zero, zero_sub, neg_mul]

/-- The symmetric flow-curvature correction contributes no physical
curl. Its symmetry is an explicit construction/identification obligation. -/
theorem original_tensor_curl (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (x : Space) (A : Mat3)
    (hcurvature : (gradientMatrix m x - A).IsSymm) :
    (fun i ↦ (vorticityField u).field x i) =
      fun i ↦ A (i + 2) (i + 1) - A (i + 1) (i + 2) := by
  rw [← actual_curl_reconstruction u m hγ x]
  ext i
  have hc := hcurvature.apply (i + 1) (i + 2)
  change gradMatrix m x (i + 2) (i + 1) - A (i + 2) (i + 1) =
    gradMatrix m x (i + 1) (i + 2) - A (i + 1) (i + 2) at hc
  change gradMatrix m x (i + 2) (i + 1) - gradMatrix m x (i + 1) (i + 2) = _
  linarith only [hc]

private theorem skew_square_le (A : Mat3) :
    (∑ i : Fin 3, (A (i + 2) (i + 1) - A (i + 1) (i + 2)) ^ 2) ≤
      2 * ∑ i : Fin 3, ∑ j : Fin 3, A i j ^ 2 := by
  simp only [Fin.sum_univ_three]
  change (A 2 1 - A 1 2) ^ 2 + (A 0 2 - A 2 0) ^ 2 + (A 1 0 - A 0 1) ^ 2 ≤ _
  nlinarith only [sq_nonneg (A 2 1 + A 1 2), sq_nonneg (A 0 2 + A 2 0),
    sq_nonneg (A 1 0 + A 0 1), sq_nonneg (A 0 0), sq_nonneg (A 1 1), sq_nonneg (A 2 2)]

/-- Physical metric coercivity is exposed rather than assumed to be
uniform over arbitrary evolving stochastic frames. -/
theorem original_tensor_curl_conversion (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (x : Space) (A : Mat3)
    (hcurvature : (gradientMatrix m x - A).IsSymm) (Q : Mat9) (b : ℝ) (hb : 0 ≤ b)
    (hcoercive : b * (∑ i : Fin 3, ∑ j : Fin 3, A i j ^ 2) ≤ normalizedSquare Q A) :
    b * (∑ i : Fin 3, ((vorticityField u).field x i) ^ 2) ≤ 2 * normalizedSquare Q A := by
  have hc := original_tensor_curl u m hγ x A hcurvature
  have hs := mul_le_mul_of_nonneg_left (skew_square_le A) hb
  simp_rw [show ∀ i : Fin 3, (vorticityField u).field x i =
      A (i + 2) (i + 1) - A (i + 1) (i + 2) from fun i ↦ congrFun hc i]
  nlinarith only [hs, hcoercive]

end Mettapedia.FluidDynamics.NavierStokes.JointReceiverTensor
