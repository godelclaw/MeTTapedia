import MettapediaNS.RetainedParentCompletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TransportedFrameMetric

/-!
# Covector geometry for actual retained parent gradients

Differentiating the literal passive RHS gives `D grad H = -(grad H)(grad u)`.
Rows therefore transport as covectors, with deformation `-(grad u)ᵀ`.
The pressure impulse retains the actual canonical Hessian as its source.
The existing inverse-frame cancellation applies to these literal rows and
their spatial derivatives, with all metric derivatives retained.

Construction of the inverse-flow coframe, its inverse differentiation and
the time/weak comparison are analytic obligations. The nonpositive passive
production does not pay weighted impulse-pressure work or provide uniform
conversion to ordinary vorticity. No nonlinear renewal bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CovectorParentHistory

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanClassical EulerMeanSolenoidal WholeSpaceViscousEnergy WholeSpaceBetchov
  WholeSpacePressureDiffusion MiddleEigenvalueAlgebra PressureImpulseHistory RetainedParentCompletion
open scoped Matrix BigOperators

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The literal whole-space gradient, viewed as a `3 × 3` matrix. -/
abbrev gradientMatrix (H : SmoothL2Field Space) (x : Space) : Mat3 := gradMatrix H x

-- Compose the gradients by their literal dot-product entries.
private def matrixProduct (V B : Mat3) : Mat3 := fun i j ↦ ∑ k, V i k * B k j

private theorem grad_add (A B : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradientMatrix (addField A B) x i j = gradientMatrix A x i j + gradientMatrix B x i j := by
  have hd : (addField A B).directionalField (axis j) =
      addField (A.directionalField (axis j)) (B.directionalField (axis j)) :=
    wordField_add A B (fun _ : Fin 1 ↦ j)
  simp only [gradientMatrix, gradMatrix, hd, addField_field, WithLp.ofLp_add, Pi.add_apply]

private theorem grad_neg (A : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradientMatrix (fieldNeg A) x i j = -gradientMatrix A x i j := by
  have hd : (fieldNeg A).directionalField (axis j) =
      fieldNeg (A.directionalField (axis j)) := wordField_neg A (fun _ : Fin 1 ↦ j)
  change ((fieldNeg A).directionalField (axis j)).field x i = _
  rw [hd]
  rfl

private theorem grad_scale (c : ℝ) (A : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradientMatrix (scaleField c A) x i j = c * gradientMatrix A x i j := by
  simp only [gradientMatrix, gradMatrix, directionalField_field, scaleField_fderiv,
    smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

/-- The actual gradient of the passive RHS, with transport and viscosity
removed using their literal smooth fields. -/
def materialGradientRate (ν : ℝ) (u H : SmoothL2Field Space) (x : Space) : Mat3 :=
  fun i j ↦ gradientMatrix (passiveRhs ν u H) x i j +
    (advectionField u (H.directionalField (axis j))).field x i -
    ν * (laplacianField (H.directionalField (axis j))).field x i

theorem passive_gradient_rate (ν : ℝ) (u H : SmoothL2Field Space) (x : Space) :
    materialGradientRate ν u H x = -(matrixProduct (gradientMatrix H x) (gradientMatrix u x)) := by
  ext i j
  have hl : gradientMatrix (laplacianField H) x i j =
      (laplacianField (H.directionalField (axis j))).field x i := by
    change ((laplacianField H).directionalField (axis j)).field x i = _
    rw [show (laplacianField H).directionalField (axis j) =
      laplacianField (H.directionalField (axis j)) from
      wordField_laplacianField H (fun _ : Fin 1 ↦ j)]
  have ha : gradientMatrix (advectionField u H) x i j =
      (advectionField u (H.directionalField (axis j))).field x i +
        (matrixProduct (gradientMatrix H x) (gradientMatrix u x)) i j := by
    change ((advectionField u H).directionalField (axis j)).field x i = _
    rw [advection_directional, addField_field]
    simp only [WithLp.ofLp_add, Pi.add_apply, WholeSpaceTimeSmooth.advectionField_field_sum,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, matrixProduct, gradientMatrix, gradMatrix, mul_comm]
  simp only [materialGradientRate, passiveRhs, grad_add, grad_neg, grad_scale,
    ha, hl, Matrix.neg_apply]
  ring

/-- The original pressure impulse retains the literal canonical pressure
field, rather than an independently supplied force. -/
def impulseGradientRate (ν : ℝ) (u H : SmoothL2Field Space) (x : Space) : Mat3 :=
  fun i j ↦ gradientMatrix (addField (passiveRhs ν u (impulse u H)) (pressureField u)) x i j +
    (advectionField u ((impulse u H).directionalField (axis j))).field x i -
    ν * (laplacianField ((impulse u H).directionalField (axis j))).field x i

theorem impulse_gradient_rate (ν : ℝ) (u H : SmoothL2Field Space) (x : Space) :
    impulseGradientRate ν u H x =
      -(matrixProduct (gradientMatrix (impulse u H) x) (gradientMatrix u x)) +
        gradientMatrix (pressureField u) x := by
  ext i j
  have h := congrFun (congrFun (passive_gradient_rate ν u (impulse u H) x) i) j
  simp only [materialGradientRate, Matrix.neg_apply] at h
  simp only [impulseGradientRate, grad_add, Matrix.add_apply, Matrix.neg_apply]
  linarith only [h]

private theorem row_rate (B V : Mat3) (i : Fin 3) :
    (-(B.transpose)) *ᵥ V i = (-(matrixProduct V B)) i := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.transpose_apply,
    matrixProduct, mul_neg, Finset.sum_neg_distrib, mul_comm]

def metricSquare (H : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.pair Q (gradientMatrix H x i) (gradientMatrix H x i)

def metricCost (H : SmoothL2Field Space) (Q : Mat3) (K : Fin 3 → Mat3)
    (x : Space) : ℝ :=
  ∑ i : Fin 3, ∑ k : Fin 3, TransportedFrameMetric.pair Q
    (gradientMatrix (H.directionalField (axis k)) x i - K k *ᵥ gradientMatrix H x i)
    (gradientMatrix (H.directionalField (axis k)) x i - K k *ᵥ gradientMatrix H x i)

def passiveMetricProduction (ν : ℝ) (u H : SmoothL2Field Space) (Q : Mat3)
    (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.production ν Q (gradientMatrix H x i)
    (materialGradientRate ν u H x i)
    (TransportedFrameMetric.rate ν Q (-(gradientMatrix u x).transpose) K)
    (fun k ↦ gradientMatrix (H.directionalField (axis k)) x i)
    (fun k ↦ TransportedFrameMetric.gradient Q (K k))

def impulseMetricProduction (ν : ℝ) (u H : SmoothL2Field Space) (Q : Mat3)
    (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.production ν Q (gradientMatrix (impulse u H) x i)
    (impulseGradientRate ν u H x i)
    (TransportedFrameMetric.rate ν Q (-(gradientMatrix u x).transpose) K)
    (fun k ↦ gradientMatrix ((impulse u H).directionalField (axis k)) x i)
    (fun k ↦ TransportedFrameMetric.gradient Q (K k))

def pressureWork (u H : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.pair Q (gradientMatrix (impulse u H) x i)
    (gradientMatrix (pressureField u) x i)

theorem passive_metric_production (ν : ℝ) (u H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.IsSymm) (K : Fin 3 → Mat3)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (x : Space) :
    passiveMetricProduction ν u H Q K x = -2 * ν * metricCost H Q K x := by
  unfold passiveMetricProduction
  rw [passive_gradient_rate]
  simp_rw [← row_rate]
  have he (i : Fin 3) := TransportedFrameMetric.production_eq ν Q
    (-(gradientMatrix u x).transpose) hQ K hK (gradientMatrix H x i) 0
    (fun k ↦ gradientMatrix (H.directionalField (axis k)) x i)
  simp only [add_zero, TransportedFrameMetric.pair, Matrix.mulVec_zero,
    dotProduct_zero, mul_zero, zero_sub] at he
  simp_rw [he]
  simp only [metricCost, TransportedFrameMetric.pair, Finset.sum_neg_distrib,
    ← Finset.mul_sum, neg_mul]

theorem impulse_metric_production (ν : ℝ) (u H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.IsSymm) (K : Fin 3 → Mat3)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (x : Space) :
    impulseMetricProduction ν u H Q K x = 2 * pressureWork u H Q x -
      2 * ν * metricCost (impulse u H) Q K x := by
  unfold impulseMetricProduction
  have hr (i : Fin 3) : impulseGradientRate ν u H x i =
      (-(gradientMatrix u x).transpose) *ᵥ gradientMatrix (impulse u H) x i +
        gradientMatrix (pressureField u) x i := by
    ext j
    rw [impulse_gradient_rate]
    change (-(matrixProduct (gradientMatrix (impulse u H) x) (gradientMatrix u x))) i j +
        gradientMatrix (pressureField u) x i j = _
    rw [row_rate]
    rfl
  simp_rw [hr, TransportedFrameMetric.production_eq ν Q
    (-(gradientMatrix u x).transpose) hQ K hK]
  simp only [pressureWork, metricCost, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem metricSquare_nonneg (H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (x : Space) : 0 ≤ metricSquare H Q x :=
  Finset.sum_nonneg fun i _ ↦ hQ.dotProduct_mulVec_nonneg (gradientMatrix H x i)

theorem metricCost_nonneg (H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (K : Fin 3 → Mat3) (x : Space) :
    0 ≤ metricCost H Q K x :=
  Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦
    hQ.dotProduct_mulVec_nonneg
      (gradientMatrix (H.directionalField (axis k)) x i - K k *ᵥ gradientMatrix H x i)

theorem passive_metric_nonpos (ν : ℝ) (hν : 0 ≤ ν) (u H : SmoothL2Field Space)
    (Q : Mat3) (hQ : Q.PosSemidef) (K : Fin 3 → Mat3)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (x : Space) :
    passiveMetricProduction ν u H Q K x ≤ 0 := by
  rw [passive_metric_production ν u H Q (Matrix.isHermitian_iff_isSymm.mp hQ.1) K hK]
  simpa only [neg_mul] using neg_nonpos.mpr
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν)
      (metricCost_nonneg H Q hQ K x))

theorem metricSquare_initial_identity (H : SmoothL2Field Space) (x : Space) :
    metricSquare H (1 : Mat3) x = normSq (gradientMatrix H x) := by
  simp only [metricSquare, TransportedFrameMetric.pair, Matrix.one_mulVec,
    dotProduct, normSq, pow_two]

/-- The ordinary fluid vorticity is still the target. A conversion bound
is an explicit input, not a conclusion of metric dissipation. -/
theorem actual_vorticity_le (u H : SmoothL2Field Space) (Q : Mat3) (x : Space)
    (κ : ℝ) (hH : normSq (gradientMatrix H x) ≤ κ * metricSquare H Q x)
    (hI : normSq (gradientMatrix (impulse u H) x) ≤ κ * metricSquare (impulse u H) Q x) :
    vortSq (gradientMatrix u x) ≤
      4 * κ * (metricSquare H Q x + metricSquare (impulse u H) Q x) := by
  have hv := RetainedParentCompletion.vorticity_normSq_le (gradientMatrix u x)
  have hb := actual_gradient_square_le u H x
  simp only [retainedGradientSquare] at hb
  nlinarith only [hv, hb, hH, hI]

end Mettapedia.FluidDynamics.NavierStokes.CovectorParentHistory
