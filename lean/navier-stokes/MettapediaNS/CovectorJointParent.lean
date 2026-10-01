import MettapediaNS.CovectorFluidBridge
import MettapediaNS.SelectedPressureCotangent
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# A joint stochastic parent and its variance payment

The forward-transported original parent has the literal incompressible
Lie-transport RHS. In a joint finite law, averaging the inverse frame and
the original parent separately need not give this parent. Retaining both
gives an exact mismatch bounded by their normalized variance against every
receiver, with the forward-frame receiver cost explicit.

The finite samples below share each inverse frame and terminal datum.
They are not a constructed stochastic NS flow. The continuous stochastic
realization, physical-time variance identity and a continuation-strength
bound on the geometric receiver remain analytic/open obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CovectorJointParent

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanSolenoidal EulerVectorCalculus
  WholeSpaceViscousEnergy WholeSpaceBetchov WholeSpaceViscousFlow
  CovectorParentHistory
open scoped Matrix BigOperators Laplacian

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Vec3" => Fin 3 → ℝ

/-- The same actual drift transports the original forward parent.
No independently selected velocity or external force enters this RHS. -/
def parentRhs (ν : ℝ) (u g : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldSub (scaleField ν (laplacianField g))
    (SelectedPressureCotangent.velocityBracket u g)

theorem parentRhs_field (ν : ℝ) (u g : SmoothL2Field Space) (x : Space) :
    (parentRhs ν u g).field x = ν • Δ g.field x -
      fderiv ℝ g.field x (u.field x) + fderiv ℝ u.field x (g.field x) := by
  simp only [parentRhs, fieldSub_field, scaleField_field, laplacianField_field,
    SelectedPressureCotangent.velocityBracket, advectionField_field]
  abel

theorem parentRhs_solenoidal (ν : ℝ) (u g : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hg : g.toLp ∈ solenoidalSpace) :
    (parentRhs ν u g).toLp ∈ solenoidalSpace := by
  rw [parentRhs, toLp_fieldSub, scaleField_toLp]
  exact solenoidalSpace.sub_mem
    (solenoidalSpace.smul_mem ν (WholeSpaceViscousEnergy.laplacianField_mem_solenoidal g hg))
    (SelectedPressureCotangent.velocityBracket_solenoidal u g hu hg)

def materialParentRate (ν : ℝ) (u g : SmoothL2Field Space) (x : Space) : Vec3 :=
  fun i ↦ ((parentRhs ν u g).field x + fderiv ℝ g.field x (u.field x) -
    ν • Δ g.field x) i

theorem material_parent_rate (ν : ℝ) (u g : SmoothL2Field Space) (x : Space) :
    materialParentRate ν u g x = gradientMatrix u x *ᵥ (fun i ↦ g.field x i) := by
  ext i
  change _ = ∑ k : Fin 3, gradMatrix u x i k * g.field x k
  rw [materialParentRate, parentRhs_field]
  have he := WholeSpaceTimeSmooth.advectionField_field_sum g u x
  rw [advectionField_field] at he
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [he]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, gradMatrix, mul_comm]
  ring

variable {σ : Type*} [Fintype σ]

/-- A joint normalized finite law. Every sample retains its own inverse
frame and original terminal datum; they are not separately recombined. -/
structure JointSamples (σ : Type*) [Fintype σ] where
  weight : σ → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : ∑ s, weight s = 1
  frame : σ → Mat3
  inverseFrame : σ → Mat3
  inverse_frame : ∀ s, inverseFrame s * frame s = 1
  terminal : σ → Vec3

namespace JointSamples

def covector (S : JointSamples σ) : Vec3 :=
  ∑ s, S.weight s • ((S.frame s).transpose *ᵥ S.terminal s)

def coframeMoment (S : JointSamples σ) : Mat3 :=
  ∑ s, S.weight s • ((S.frame s).transpose * S.frame s)

def forwardMoment (S : JointSamples σ) : Mat3 :=
  ∑ s, S.weight s • (S.inverseFrame s * (S.inverseFrame s).transpose)

def parent (S : JointSamples σ) : Vec3 :=
  ∑ s, S.weight s • (S.inverseFrame s *ᵥ S.terminal s)

def terminalEnergy (S : JointSamples σ) : ℝ :=
  ∑ s, S.weight s * (S.terminal s ⬝ᵥ S.terminal s)

def variance (S : JointSamples σ) (a : Vec3) : ℝ :=
  ∑ s, S.weight s * ((S.terminal s - S.frame s *ᵥ a) ⬝ᵥ
    (S.terminal s - S.frame s *ᵥ a))

def receiverCost (S : JointSamples σ) (z : Vec3) : ℝ :=
  ∑ s, S.weight s * (((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ
    ((S.inverseFrame s).transpose *ᵥ z))

private theorem square_nonneg (v : Vec3) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)

private theorem transpose_pair (F : Mat3) (a v : Vec3) :
    a ⬝ᵥ (F.transpose *ᵥ v) = (F *ᵥ a) ⬝ᵥ v := by
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem square_sub_smul (e v : Vec3) (t : ℝ) :
    (e - t • v) ⬝ᵥ (e - t • v) =
      e ⬝ᵥ e - 2 * t * (v ⬝ᵥ e) + t ^ 2 * (v ⬝ᵥ v) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm e v]
  ring

theorem variance_nonneg (S : JointSamples σ) (a : Vec3) : 0 ≤ S.variance a := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (S.weight_nonneg s) (square_nonneg _)

theorem receiverCost_nonneg (S : JointSamples σ) (z : Vec3) : 0 ≤ S.receiverCost z := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (S.weight_nonneg s) (square_nonneg _)

theorem receiverCost_eq_forward (S : JointSamples σ) (z : Vec3) :
    S.receiverCost z = z ⬝ᵥ (S.forwardMoment *ᵥ z) := by
  simp only [receiverCost, forwardMoment, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Matrix.mulVec_mulVec]
  rw [show z ⬝ᵥ (S.inverseFrame s *ᵥ ((S.inverseFrame s).transpose *ᵥ z)) =
    ((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ ((S.inverseFrame s).transpose *ᵥ z) by
      simpa only [Matrix.transpose_transpose] using
        transpose_pair (S.inverseFrame s).transpose z ((S.inverseFrame s).transpose *ᵥ z)]

theorem variance_expansion (S : JointSamples σ) (a : Vec3) :
    S.variance a = S.terminalEnergy - 2 * (a ⬝ᵥ S.covector) +
      a ⬝ᵥ (S.coframeMoment *ᵥ a) := by
  have he (s : σ) : S.weight s * ((S.terminal s - S.frame s *ᵥ a) ⬝ᵥ
      (S.terminal s - S.frame s *ᵥ a)) =
      S.weight s * (S.terminal s ⬝ᵥ S.terminal s) -
        2 * (S.weight s * (a ⬝ᵥ ((S.frame s).transpose *ᵥ S.terminal s))) +
        S.weight s * (a ⬝ᵥ (((S.frame s).transpose * S.frame s) *ᵥ a)) := by
    rw [← Matrix.mulVec_mulVec, transpose_pair, transpose_pair]
    have hs := square_sub_smul (S.terminal s) (S.frame s *ᵥ a) 1
    simp only [one_smul, one_mul, one_pow, mul_one] at hs
    linear_combination S.weight s * hs
  simp only [variance, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, terminalEnergy, covector, coframeMoment, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The normal equation identifies the same canonical normalized parent;
the residual cannot be reset without changing that joint history. -/
theorem variance_eq_deficit (S : JointSamples σ) (a : Vec3)
    (ha : S.coframeMoment *ᵥ a = S.covector) :
    S.variance a = S.terminalEnergy - a ⬝ᵥ S.covector := by
  rw [variance_expansion, ha]
  ring

theorem normalized_energy_le (S : JointSamples σ) (a : Vec3)
    (ha : S.coframeMoment *ᵥ a = S.covector) :
    a ⬝ᵥ S.covector ≤ S.terminalEnergy := by
  have h := S.variance_nonneg a
  rw [variance_eq_deficit S a ha] at h
  linarith

theorem normalized_energy_nonneg (S : JointSamples σ) (a : Vec3)
    (ha : S.coframeMoment *ᵥ a = S.covector) :
    0 ≤ a ⬝ᵥ S.covector := by
  rw [← ha]
  simp only [coframeMoment, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_nonneg
  intro s _
  rw [← Matrix.mulVec_mulVec, transpose_pair]
  exact mul_nonneg (S.weight_nonneg s) (square_nonneg _)

theorem variance_le_terminalEnergy (S : JointSamples σ) (a : Vec3)
    (ha : S.coframeMoment *ᵥ a = S.covector) :
    S.variance a ≤ S.terminalEnergy := by
  rw [variance_eq_deficit S a ha]
  have h := S.normalized_energy_nonneg a ha
  linarith only [h]

theorem parent_mismatch (S : JointSamples σ) (a : Vec3) :
    S.parent - a = ∑ s, S.weight s • (S.inverseFrame s *ᵥ
      (S.terminal s - S.frame s *ᵥ a)) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    S.inverse_frame, Matrix.one_mulVec, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, S.weight_sum, one_smul, parent]

/-- Every receiver keeps a concrete forward-frame cost. Positive
variance payment alone does not erase this receiver or its geometry. -/
theorem receiver_completion (S : JointSamples σ) (a z : Vec3) (t : ℝ) :
    0 ≤ S.variance a - 2 * t * (z ⬝ᵥ (S.parent - a)) + t ^ 2 * S.receiverCost z := by
  have hp : 0 ≤ ∑ s, S.weight s *
      ((S.terminal s - S.frame s *ᵥ a - t • ((S.inverseFrame s).transpose *ᵥ z)) ⬝ᵥ
       (S.terminal s - S.frame s *ᵥ a - t • ((S.inverseFrame s).transpose *ᵥ z))) :=
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (S.weight_nonneg s) (square_nonneg _)
  have hc : z ⬝ᵥ (S.parent - a) = ∑ s, S.weight s *
      (((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ (S.terminal s - S.frame s *ᵥ a)) := by
    rw [parent_mismatch]
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [show z ⬝ᵥ (S.inverseFrame s *ᵥ (S.terminal s - S.frame s *ᵥ a)) =
      ((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ (S.terminal s - S.frame s *ᵥ a) by
        simpa only [Matrix.transpose_transpose] using
          transpose_pair (S.inverseFrame s).transpose z (S.terminal s - S.frame s *ᵥ a)]
  have he (s : σ) : S.weight s *
      ((S.terminal s - S.frame s *ᵥ a - t • ((S.inverseFrame s).transpose *ᵥ z)) ⬝ᵥ
       (S.terminal s - S.frame s *ᵥ a - t • ((S.inverseFrame s).transpose *ᵥ z))) =
      S.weight s * ((S.terminal s - S.frame s *ᵥ a) ⬝ᵥ (S.terminal s - S.frame s *ᵥ a)) -
        (2 * t) * (S.weight s * (((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ
          (S.terminal s - S.frame s *ᵥ a))) +
        t ^ 2 * (S.weight s * (((S.inverseFrame s).transpose *ᵥ z) ⬝ᵥ
          ((S.inverseFrame s).transpose *ᵥ z))) := by
    rw [square_sub_smul]
    ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hp
  simpa only [variance, receiverCost, hc] using hp

theorem receiver_square_le (S : JointSamples σ) (a z : Vec3) :
    (z ⬝ᵥ (S.parent - a)) ^ 2 ≤ S.receiverCost z * S.variance a := by
  have hd := discrim_le_zero (a := S.receiverCost z)
    (b := -2 * (z ⬝ᵥ (S.parent - a))) (c := S.variance a) (fun t ↦ by
      have hp := S.receiver_completion a z t
      calc
        0 ≤ S.variance a - 2 * t * (z ⬝ᵥ (S.parent - a)) +
            t ^ 2 * S.receiverCost z := hp
        _ = S.receiverCost z * (t * t) +
            (-2 * (z ⬝ᵥ (S.parent - a))) * t + S.variance a := by ring)
  simp only [discrim] at hd
  nlinarith only [hd]

theorem receiver_work_le (S : JointSamples σ) (a z : Vec3) :
    2 * (z ⬝ᵥ (S.parent - a)) ≤ S.variance a + S.receiverCost z := by
  have h := S.receiver_completion a z 1
  norm_num only [one_mul, one_pow] at h
  linarith only [h]

theorem receiver_work_neg_le (S : JointSamples σ) (a z : Vec3) :
    -2 * (z ⬝ᵥ (S.parent - a)) ≤ S.variance a + S.receiverCost z := by
  have h := S.receiver_completion a z (-1)
  norm_num only [neg_one_sq, one_mul, mul_neg_one] at h
  linarith only [h]

/-- The receiver of the `N (partial_j B) a` source when the
covariant gradient is tested in its inverse-frame metric. -/
def sourceReceiver (dB : Fin 3 → Mat3) (r : Fin 3 → Vec3) : Vec3 :=
  ∑ j, (dB j).transpose *ᵥ r j

def parentSourceWork (dB : Fin 3 → Mat3) (r : Fin 3 → Vec3) (a : Vec3) : ℝ :=
  ∑ j, r j ⬝ᵥ (dB j *ᵥ a)

theorem parent_source_mismatch (S : JointSamples σ) (a : Vec3)
    (dB : Fin 3 → Mat3) (r : Fin 3 → Vec3) :
    sourceReceiver dB r ⬝ᵥ (S.parent - a) =
      parentSourceWork dB r S.parent - parentSourceWork dB r a := by
  have he (j : Fin 3) : ((dB j).transpose *ᵥ r j) ⬝ᵥ (S.parent - a) =
      r j ⬝ᵥ (dB j *ᵥ S.parent) - r j ⬝ᵥ (dB j *ᵥ a) := by
    rw [dotProduct_comm, transpose_pair, Matrix.mulVec_sub, sub_dotProduct,
      dotProduct_comm (dB j *ᵥ S.parent), dotProduct_comm (dB j *ᵥ a)]
  simp only [sourceReceiver, sum_dotProduct, he, Finset.sum_sub_distrib, parentSourceWork]

/-- One joint variance pays the entire parent mismatch. The combined
geometric receiver cost and the retained parent's work both remain. -/
theorem parent_source_transfer (S : JointSamples σ) (a : Vec3)
    (dB : Fin 3 → Mat3) (r : Fin 3 → Vec3) :
    2 * parentSourceWork dB r a ≤ 2 * parentSourceWork dB r S.parent +
      S.variance a + S.receiverCost (sourceReceiver dB r) := by
  have h := S.receiver_work_neg_le a (sourceReceiver dB r)
  rw [parent_source_mismatch] at h
  linarith only [h]

end JointSamples

end Mettapedia.FluidDynamics.NavierStokes.CovectorJointParent
