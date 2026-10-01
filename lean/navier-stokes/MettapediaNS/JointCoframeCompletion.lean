import MettapediaNS.JointCoframePressure

/-!
# A nonnegative completion of the actual pressure endpoint

For the retained impulse gradient A and actual fluid gradient B, the
completion Z=B+Aᵀ cancels the canonical pressure Hessian. Its remaining
source is AᵀB-BᵀAᵀ, supplied by the same original parents. This module
certifies literal rates and the full supplied-coframe production.
The source has no asserted favorable sign or original-data history bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointCoframeCompletion

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev WholeSpaceViscousEnergy WholeSpaceBetchov
  WholeSpacePressureDiffusion PressureImpulseHistory RetainedParentCompletion
  CovectorParentHistory JointCoframePressure
open scoped Matrix BigOperators

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

private def product (V B : Mat3) : Mat3 := fun i j ↦ ∑ k, V i k * B k j

def completedGradient (u H : SmoothL2Field Space) (x : Space) : Mat3 :=
  gradientMatrix u x + (gradientMatrix (impulse u H) x).transpose

def completedSource (u H : SmoothL2Field Space) (x : Space) : Mat3 :=
  product (gradientMatrix (impulse u H) x).transpose (gradientMatrix u x) -
    product (gradientMatrix u x).transpose (gradientMatrix (impulse u H) x).transpose

def completedGradientRate (ν : ℝ) (u H : SmoothL2Field Space) (x : Space) : Mat3 :=
  actualGradientRate ν u x + (impulseGradientRate ν u H x).transpose

/-- The actual canonical pressure Hessian cancels. The impulse source
retains its complete deformation by the same actual gradient. -/
theorem completed_gradient_rate (ν : ℝ) (u H : SmoothL2Field Space) (x : Space) :
    completedGradientRate ν u H x =
      -(product (completedGradient u H x) (gradientMatrix u x)) + completedSource u H x := by
  ext i j
  have hu := congrFun (congrFun (passive_gradient_rate ν u u x) i) j
  have hI := congrFun (congrFun (impulse_gradient_rate ν u H x) j) i
  change materialGradientRate ν u u x i j = -(∑ k, gradientMatrix u x i k *
    gradientMatrix u x k j) at hu
  change impulseGradientRate ν u H x j i = -(∑ k, gradientMatrix (impulse u H) x j k *
    gradientMatrix u x k i) + gradientMatrix (pressureField u) x j i at hI
  have hP := gradMatrix_symmetric (pressureField u) (pressureField_mem_gradient u) x j i
  change gradientMatrix (pressureField u) x j i = gradientMatrix (pressureField u) x i j at hP
  simp only [completedGradientRate, actual_gradient_rate, Matrix.add_apply,
    Matrix.sub_apply, Matrix.transpose_apply, hu, hI, hP, product,
    completedGradient, completedSource, Matrix.neg_apply, add_mul,
    Finset.sum_add_distrib]
  ring_nf
  simp only [mul_comm]

def completedSquare (u H : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.pair Q (completedGradient u H x i)
    (completedGradient u H x i)

theorem completedSquare_nonneg (u H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (x : Space) : 0 ≤ completedSquare u H Q x :=
  Finset.sum_nonneg fun i _ ↦ hQ.dotProduct_mulVec_nonneg (completedGradient u H x i)

def completedCost (u H : SmoothL2Field Space) (Q : Mat3)
    (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, ∑ k : Fin 3, TransportedFrameMetric.pair Q
    (completedGradient (u.directionalField (axis k)) (H.directionalField (axis k)) x i -
      K k *ᵥ completedGradient u H x i)
    (completedGradient (u.directionalField (axis k)) (H.directionalField (axis k)) x i -
      K k *ᵥ completedGradient u H x i)

theorem completedCost_nonneg (u H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (K : Fin 3 → Mat3) (x : Space) :
    0 ≤ completedCost u H Q K x :=
  Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦
    hQ.dotProduct_mulVec_nonneg
      (completedGradient (u.directionalField (axis k)) (H.directionalField (axis k)) x i -
        K k *ᵥ completedGradient u H x i)

def completedWork (u H : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.pair Q (completedGradient u H x i)
    (completedSource u H x i)

def completedProduction (ν : ℝ) (u H : SmoothL2Field Space) (Q : Mat3)
    (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.production ν Q (completedGradient u H x i)
    (completedGradientRate ν u H x i)
    (TransportedFrameMetric.rate ν Q (-(gradientMatrix u x).transpose) K)
    (fun k ↦ completedGradient (u.directionalField (axis k)) (H.directionalField (axis k)) x i)
    (fun k ↦ TransportedFrameMetric.gradient Q (K k))

private theorem row_rate (B V : Mat3) (i : Fin 3) :
    (-(B.transpose)) *ᵥ V i = (-(product V B)) i := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.transpose_apply,
    product, mul_neg, Finset.sum_neg_distrib, mul_comm]

theorem completed_production (ν : ℝ) (u H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.IsSymm) (K : Fin 3 → Mat3)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (x : Space) :
    completedProduction ν u H Q K x = 2 * completedWork u H Q x -
      2 * ν * completedCost u H Q K x := by
  have hr (i : Fin 3) : completedGradientRate ν u H x i =
      (-(gradientMatrix u x).transpose) *ᵥ completedGradient u H x i +
        completedSource u H x i := by
    rw [completed_gradient_rate, row_rate]
    rfl
  simp only [completedProduction, hr, TransportedFrameMetric.production_eq ν Q
    (-(gradientMatrix u x).transpose) hQ K hK, completedWork, completedCost,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The actual antisymmetric gradient is reconstructed jointly; no
metric coercivity for this ordinary physical observable is asserted. -/
theorem actual_skew_reconstruction (u H : SmoothL2Field Space) (x : Space) :
    (2 : ℝ) • (gradientMatrix u x - (gradientMatrix u x).transpose) =
      (gradientMatrix H x - (gradientMatrix H x).transpose) +
        (completedGradient u H x - (completedGradient u H x).transpose) := by
  ext i j
  change 2 * (gradMatrix u x i j - gradMatrix u x j i) =
    (gradMatrix H x i j - gradMatrix H x j i) +
      ((gradMatrix u x i j + gradMatrix (impulse u H) x j i) -
        (gradMatrix u x j i + gradMatrix (impulse u H) x i j))
  rw [impulse_gradient_entry, impulse_gradient_entry]
  ring

end Mettapedia.FluidDynamics.NavierStokes.JointCoframeCompletion
