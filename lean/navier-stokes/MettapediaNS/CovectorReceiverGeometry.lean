import MettapediaNS.CovectorJointParent
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The actual geometric receiver and its retained moment defect

The covariant-gradient source uses the full Hessian of the actual
velocity. Its physical-gradient part is a gradient, hence has zero work
against an incompressible parent. The remaining receiver retains the
actual gradient defect; it is not set to zero or independently selected.

The finite cofactor rate exposes a signed area-moment defect between the
forward moment and the adjugate of the averaged coframe. The parabolic
chain rule, joint stochastic realization, short-prefix obstruction and
arbitrary-history payment remain analytic/separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CovectorReceiverGeometry

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVectorCalculus WholeSpaceBetchov WholeSpaceViscousEnergy
  CovectorParentHistory CovectorFluidBridge
open scoped Matrix BigOperators

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Vec3" => Fin 3 → ℝ

/-- The source uses actual velocity Hessians and the retained gradient
columns. In the physical application r_j=partial_j m-K_j m. -/
def fullReceiver (u : SmoothL2Field Space) (r : Fin 3 → SmoothL2Field Space) :
    SmoothL2Field Space :=
  sumField Finset.univ fun j ↦ transposeStretch (u.directionalField (axis j)) (r j)

def baselineReceiver (u : SmoothL2Field Space) : SmoothL2Field Space :=
  fullReceiver u fun j ↦ u.directionalField (axis j)

def receiverDefect (u : SmoothL2Field Space) (r : Fin 3 → SmoothL2Field Space) :
    SmoothL2Field Space :=
  fullReceiver u fun j ↦ fieldSub (r j) (u.directionalField (axis j))

theorem full_receiver_matches (u : SmoothL2Field Space)
    (r : Fin 3 → SmoothL2Field Space) (x : Space) :
    (fun i ↦ (fullReceiver u r).field x i) =
      CovectorJointParent.JointSamples.sourceReceiver
        (fun j ↦ gradientMatrix (u.directionalField (axis j)) x)
        (fun j i ↦ (r j).field x i) := by
  ext i
  change _ = ∑ j : Fin 3, ∑ k : Fin 3,
    gradMatrix (u.directionalField (axis j)) x k i * (r j).field x k
  simp only [fullReceiver, sumField_field, transposeStretch_coordinate,
    WithLp.ofLp_sum, Finset.sum_apply]

theorem receiver_decomposition (u : SmoothL2Field Space)
    (r : Fin 3 → SmoothL2Field Space) :
    fullReceiver u r = addField (baselineReceiver u) (receiverDefect u r) := by
  apply field_ext
  funext x
  ext i
  simp only [fullReceiver, baselineReceiver, receiverDefect, sumField_field,
    transposeStretch_coordinate, fieldSub_field, WithLp.ofLp_sub, Pi.sub_apply,
    WithLp.ofLp_sum, Finset.sum_apply, mul_sub, Finset.sum_sub_distrib,
    addField_field, WithLp.ofLp_add, Pi.add_apply]
  abel

theorem baselineReceiver_gradient (u : SmoothL2Field Space) :
    (baselineReceiver u).toLp ∈ gradientSpace := by
  rw [baselineReceiver, fullReceiver, toLp_sumField]
  exact gradientSpace.sum_mem fun j _ ↦
    transposeStretch_self_gradient (u.directionalField (axis j))

/-- This cancellation holds at every time with the current actual
velocity; it does not assert that the evolving defect vanishes. -/
theorem projected_receiver_defect (u : SmoothL2Field Space)
    (r : Fin 3 → SmoothL2Field Space) :
    solenoidalField (fullReceiver u r) = solenoidalField (receiverDefect u r) := by
  apply smoothField_eq_of_toLp_eq
  rw [receiver_decomposition, solenoidalField_toLp, toLp_addField, map_add,
    (solenoidalProjection_eq_zero_iff _).mpr (baselineReceiver_gradient u),
    zero_add, solenoidalField_toLp]

theorem receiver_parent_work (u g : SmoothL2Field Space)
    (r : Fin 3 → SmoothL2Field Space) (hg : g.toLp ∈ solenoidalSpace) :
    ⟪(fullReceiver u r).toLp, g.toLp⟫_ℝ =
      ⟪(receiverDefect u r).toLp, g.toLp⟫_ℝ := by
  have hz := hg _ (baselineReceiver_gradient u)
  rw [receiver_decomposition, toLp_addField, inner_add_left, hz, zero_add]

theorem integral_receiver_parent_work (u g : SmoothL2Field Space)
    (r : Fin 3 → SmoothL2Field Space) (hg : g.toLp ∈ solenoidalSpace) :
    (∫ x, ⟪(fullReceiver u r).field x, g.field x⟫_ℝ) =
      ∫ x, ⟪(receiverDefect u r).field x, g.field x⟫_ℝ := by
  have hf : (∫ x, ⟪(fullReceiver u r).field x, g.field x⟫_ℝ) =
      ⟪(fullReceiver u r).toLp, g.toLp⟫_ℝ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(fullReceiver u r).toLp_ae, g.toLp_ae] with x hx hgx
    rw [hx, hgx]
  have hd : (∫ x, ⟪(receiverDefect u r).field x, g.field x⟫_ℝ) =
      ⟪(receiverDefect u r).toLp, g.toLp⟫_ℝ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(receiverDefect u r).toLp_ae, g.toLp_ae] with x hx hgx
    rw [hx, hgx]
  rw [hf, hd, receiver_parent_work u g r hg]

/-- The polarization of the quadratic three-dimensional
adjugate. Its interpretation as the actual parabolic chain rule is separate. -/
def adjugateRate (N H : Mat3) : Mat3 :=
  (N + H).adjugate - N.adjugate - H.adjugate

set_option maxHeartbeats 800000 in
theorem adjugate_strain_rate (N B : Mat3) :
    adjugateRate N (-B.transpose * N - N * B) =
      B * N.adjugate + N.adjugate * B.transpose -
        (2 * B.trace) • N.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugateRate, Matrix.adjugate_fin_three, Matrix.add_apply,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.transpose_apply,
      Matrix.vecMul, dotProduct, smul_eq_mul, Matrix.trace, Fin.sum_univ_three,
      Matrix.of_apply] <;> ring

def areaMomentDefect (M N : Mat3) : Mat3 := M - N.adjugate

def areaDefectRate (ν : ℝ) (B M N : Mat3) (dN : Fin 3 → Mat3) : Mat3 :=
  B * M + M * B.transpose -
    (adjugateRate N (-B.transpose * N - N * B) -
      (2 * ν) • ∑ k, (dN k).adjugate)

/-- The determinant-one flow identifies M as the averaged adjugate
of each sample Gram matrix, not the adjugate of the average N. -/
theorem area_defect_rate (ν : ℝ) (B M N : Mat3) (dN : Fin 3 → Mat3)
    (hB : B.trace = 0) :
    areaDefectRate ν B M N dN =
      B * areaMomentDefect M N + areaMomentDefect M N * B.transpose +
        (2 * ν) • ∑ k, (dN k).adjugate := by
  rw [areaDefectRate, adjugate_strain_rate, hB]
  simp only [mul_zero, zero_smul, sub_zero, areaMomentDefect, mul_sub, sub_mul]
  abel

/-- The covariance receiver retains the actual original impulse.
No independently selected pressure correction is introduced. -/
def completedGradientDefect (m H : SmoothL2Field Space)
    (K : Fin 3 → Mat3) (x : Space) : Mat3 :=
  Matrix.of (fun i j ↦ covariantDerivative m K x j i) - gradientMatrix H x

theorem actual_defect_reconstruction (u m H : SmoothL2Field Space)
    (K : Fin 3 → Mat3) (x : Space) :
    Matrix.of (fun i j ↦ covariantDerivative m K x j i) - gradientMatrix u x =
      gradientMatrix (PressureImpulseHistory.impulse u H) x +
        completedGradientDefect m H K x := by
  ext i j
  change covariantDerivative m K x j i - gradMatrix u x i j =
    gradMatrix (PressureImpulseHistory.impulse u H) x i j +
      (covariantDerivative m K x j i - gradMatrix H x i j)
  rw [RetainedParentCompletion.impulse_gradient_entry]
  ring

variable {σ : Type*} [Fintype σ]

theorem inverseFrame_eq_adjugate (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) (s : σ) :
    S.inverseFrame s = (S.frame s).adjugate := by
  calc
    S.inverseFrame s = S.inverseFrame s * 1 := (mul_one _).symm
    _ = S.inverseFrame s * (S.frame s * (S.frame s).adjugate) := by
      rw [Matrix.mul_adjugate, hdet s, one_smul]
    _ = (S.inverseFrame s * S.frame s) * (S.frame s).adjugate :=
      (mul_assoc _ _ _).symm
    _ = (S.frame s).adjugate := by rw [S.inverse_frame, one_mul]

/-- Volume preservation identifies the moment of the actual sample
area matrix. It does not commute adjugation with expectation. -/
theorem forwardMoment_eq_sample_area (S : CovectorJointParent.JointSamples σ)
    (hdet : ∀ s, (S.frame s).det = 1) :
    S.forwardMoment =
      ∑ s, S.weight s • ((S.frame s).transpose * S.frame s).adjugate := by
  unfold CovectorJointParent.JointSamples.forwardMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [inverseFrame_eq_adjugate S hdet, Matrix.adjugate_mul_distrib,
    ← Matrix.adjugate_transpose]

/-- The supplied full covariant source S must retain its actual
Hessian/connection terms when this algebra is applied to a flow. -/
def completedDefectRate (B R BH P S : Mat3) : Mat3 :=
  ((-B.transpose * R - R * B + S) - (-B * B - P)) -
    (P - (BH - B) * B)

theorem completed_defect_rate (B R BH P S : Mat3) :
    completedDefectRate B R BH P S =
      -B.transpose * (R - BH) - (R - BH) * B - B.transpose * BH + S := by
  unfold completedDefectRate
  noncomm_ring

end Mettapedia.FluidDynamics.NavierStokes.CovectorReceiverGeometry
