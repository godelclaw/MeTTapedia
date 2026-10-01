import MettapediaNS.CovectorParentHistory
import MettapediaNS.ForcedCandidatePancake

/-!
# Actual fluid reconstruction from a transported velocity covector

For `u = P m`, where P is the actual Helmholtz projection, the full
covector equation `D m = -(grad u)ᵀ m` projects to the unforced NS
equation and retains the actual curl. This is the deterministic
reconstruction in the Constantin--Iyer representation (math/0511067,
Theorem 2.2 and equation 4.5). Its stochastic construction and a uniform
bound on the curl of the evolving covector remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CovectorFluidBridge

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical EulerVectorCalculus WholeSpaceViscousEnergy WholeSpaceBetchov
  WholeSpacePressureDiffusion WholeSpaceViscousFlow CovectorParentHistory EulerMeanPressure

open scoped Matrix BigOperators Laplacian

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

def transposeStretch (u m : SmoothL2Field Space) : SmoothL2Field Space :=
  sumField Finset.univ (fun k : Fin 3 ↦
    scalarProduct (coord m k) (ForcedCandidatePancake.gradientField (coord u k)))

theorem transposeStretch_coordinate (u m : SmoothL2Field Space) (x : Space) (i : Fin 3) :
    (transposeStretch u m).field x i = ∑ k : Fin 3, gradMatrix u x k i * m.field x k := by
  simp only [transposeStretch, sumField_field, scalarProduct_field,
    ForcedCandidatePancake.gradientField_field, gradient_coordinate, coord_field,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [show partialDerivative (coord u k).field i x = gradMatrix u x k i by
    change ((coord u k).directionalField (axis i)).field x = _
    rw [coord_directional_field]
    rfl]
  ring

def pairingPotential (u m : SmoothL2Field Space) : SmoothL2Field ℝ :=
  sumField Finset.univ (fun k : Fin 3 ↦ scalarProduct (coord u k) (coord m k))

theorem pairing_gradient (u m : SmoothL2Field Space) :
    ForcedCandidatePancake.gradientField (pairingPotential u m) =
      addField (transposeStretch u m) (transposeStretch m u) := by
  apply field_ext
  funext x
  ext i
  rw [ForcedCandidatePancake.gradientField_field, gradient_coordinate]
  change ((pairingPotential u m).directionalField (axis i)).field x = _
  rw [show (pairingPotential u m).directionalField (axis i) =
    sumField Finset.univ (fun k : Fin 3 ↦
      (scalarProduct (coord u k) (coord m k)).directionalField (axis i)) from
        wordField_sum Finset.univ _ (fun _ : Fin 1 ↦ i)]
  simp only [sumField_field, scalarProduct_directional, addField_field,
    scalarProduct_field, smul_eq_mul, coord_directional_field, coord_field,
    WithLp.ofLp_add, Pi.add_apply, transposeStretch_coordinate, gradMatrix,
    Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ ↦ a + b)
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [mul_comm]

theorem gradient_lie_transport (u γ : SmoothL2Field Space)
    (hγ : γ.toLp ∈ gradientSpace) :
    addField (advectionField u γ) (transposeStretch u γ) =
      ForcedCandidatePancake.gradientField (pairingPotential u γ) := by
  rw [pairing_gradient]
  apply field_ext
  funext x
  ext i
  simp only [addField_field, WithLp.ofLp_add, Pi.add_apply,
    WholeSpaceTimeSmooth.advectionField_field_sum, WithLp.ofLp_sum,
    Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    transposeStretch_coordinate]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show (γ.directionalField (axis k)).field x i = gradMatrix γ x i k from rfl,
    gradMatrix_symmetric γ hγ x i k]
  ring

theorem transposeStretch_self_gradient (u : SmoothL2Field Space) :
    (transposeStretch u u).toLp ∈ gradientSpace := by
  have he : transposeStretch u u =
      scaleField (1 / 2 : ℝ) (ForcedCandidatePancake.gradientField (pairingPotential u u)) := by
    rw [pairing_gradient]
    apply field_ext
    funext x
    simp only [scaleField_field, addField_field]
    module
  rw [he, scaleField_toLp]
  exact gradientSpace.smul_mem _ (ForcedCandidatePancake.gradientField_mem _)

def covectorRhs (ν : ℝ) (u m : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldSub (PressureImpulseHistory.passiveRhs ν u m) (transposeStretch u m)

theorem covectorRhs_field (ν : ℝ) (u m : SmoothL2Field Space) (x : Space) :
    (covectorRhs ν u m).field x =
      -fderiv ℝ m.field x (u.field x) + ν • Δ m.field x -
        (transposeStretch u m).field x := by
  simp only [covectorRhs, fieldSub_field, PressureImpulseHistory.passiveRhs,
    addField_field, fieldNeg_field, scaleField_field,
    advectionField_field, laplacianField_field]

private theorem transposeStretch_sub (u m n : SmoothL2Field Space) :
    transposeStretch u (fieldSub m n) =
      fieldSub (transposeStretch u m) (transposeStretch u n) := by
  apply field_ext
  funext x
  ext i
  simp only [transposeStretch_coordinate, fieldSub_field, WithLp.ofLp_sub,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem directional_sub (A B : SmoothL2Field Space) (v : Space) :
    (fieldSub A B).directionalField v =
      fieldSub (A.directionalField v) (B.directionalField v) := by
  apply field_ext
  funext x
  have he : (fieldSub A B).field = A.field - B.field := funext (fieldSub_field A B)
  simp only [directionalField_field, fieldSub_field]
  rw [he, fderiv_sub (A.smooth.differentiable (by simp) x)
    (B.smooth.differentiable (by simp) x)]
  rfl

private theorem laplacian_sub (A B : SmoothL2Field Space) :
    laplacianField (fieldSub A B) = fieldSub (laplacianField A) (laplacianField B) := by
  apply field_ext
  funext x
  simp only [laplacianField, directional_sub, sumField_field, fieldSub_field,
    Finset.sum_sub_distrib]

private theorem advection_sub (u A B : SmoothL2Field Space) :
    advectionField u (fieldSub A B) =
      fieldSub (advectionField u A) (advectionField u B) := by
  apply field_ext
  funext x
  have he : (fieldSub A B).field = A.field - B.field := funext (fieldSub_field A B)
  simp only [advectionField_field, fieldSub_field]
  rw [he, fderiv_sub (A.smooth.differentiable (by simp) x)
    (B.smooth.differentiable (by simp) x)]
  rfl

theorem covectorRhs_sub (ν : ℝ) (u m n : SmoothL2Field Space) :
    covectorRhs ν u (fieldSub m n) =
      fieldSub (covectorRhs ν u m) (covectorRhs ν u n) := by
  apply smoothField_eq_of_toLp_eq
  simp only [covectorRhs, toLp_fieldSub, transposeStretch_sub,
    PressureImpulseHistory.passiveRhs_toLp, advection_sub, laplacian_sub,
    toLp_fieldSub, smul_sub]
  abel

theorem gradient_covectorRhs (ν : ℝ) (u γ : SmoothL2Field Space)
    (hγ : γ.toLp ∈ gradientSpace) : (covectorRhs ν u γ).toLp ∈ gradientSpace := by
  have hl : (laplacianField γ).toLp ∈ gradientSpace := by
    rw [toLp_laplacianField]
    exact Submodule.sum_mem _ fun i _ ↦ word_gradient γ hγ (doubleWord i)
  have he : (covectorRhs ν u γ).toLp =
      ν • (laplacianField γ).toLp -
        (ForcedCandidatePancake.gradientField (pairingPotential u γ)).toLp := by
    rw [← gradient_lie_transport u γ hγ]
    simp only [covectorRhs, toLp_fieldSub, PressureImpulseHistory.passiveRhs_toLp,
      toLp_addField]
    abel
  rw [he]
  exact gradientSpace.sub_mem (gradientSpace.smul_mem ν hl)
    (ForcedCandidatePancake.gradientField_mem _)

theorem projected_covectorRhs_self (ν : ℝ) (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) :
    (solenoidalField (covectorRhs ν u u)).toLp = (nsProjectedRhs ν u).toLp := by
  have hs := (solenoidalProjection_eq_zero_iff _).mpr (transposeStretch_self_gradient u)
  have hl : solenoidalProjection (laplacianField u).toLp = (laplacianField u).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr
      (WholeSpaceViscousEnergy.laplacianField_mem_solenoidal u hu)
  simp only [solenoidalField_toLp, covectorRhs, toLp_fieldSub,
    PressureImpulseHistory.passiveRhs_toLp, map_sub, map_add, map_neg, map_smul,
    hs, sub_zero, hl, nsProjectedRhs_toLp, projectedRhs, toLp_fieldNeg,
    solenoidalField_toLp]

/-- A retained smooth gradient difference is enough for exact nonlinear
reconstruction. No estimate of an unknown future solution is assumed. -/
theorem projected_covectorRhs (ν : ℝ) (u m : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hγ : (fieldSub m u).toLp ∈ gradientSpace) :
    (solenoidalField (covectorRhs ν u m)).toLp = (nsProjectedRhs ν u).toLp := by
  have hz := (solenoidalProjection_eq_zero_iff _).mpr
    (gradient_covectorRhs ν u (fieldSub m u) hγ)
  rw [covectorRhs_sub, toLp_fieldSub, map_sub] at hz
  rw [solenoidalField_toLp]
  have he := projected_covectorRhs_self ν u hu
  rw [solenoidalField_toLp] at he
  exact (sub_eq_zero.mp hz).trans he

/-- The actual projection defines the drift; the hidden gradient is not
an independent force or independently selected velocity. -/
theorem nonlinear_pushdown (ν : ℝ) (m : SmoothL2Field Space) :
    solenoidalField (covectorRhs ν (solenoidalField m) m) =
      nsProjectedRhs ν (solenoidalField m) := by
  apply smoothField_eq_of_toLp_eq
  apply projected_covectorRhs
  · rw [solenoidalField_toLp]
    exact solenoidalProjection_mem m.toLp
  · rw [toLp_fieldSub, solenoidalField_toLp]
    exact sub_solenoidalProjection_mem_gradient m.toLp

theorem actual_curl_reconstruction (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (x : Space) :
    (vorticityField m).field x = (vorticityField u).field x := by
  ext i
  change gradMatrix m x (i + 2) (i + 1) - gradMatrix m x (i + 1) (i + 2) =
    gradMatrix u x (i + 2) (i + 1) - gradMatrix u x (i + 1) (i + 2)
  have hs := gradMatrix_symmetric (fieldSub m u) hγ x (i + 2) (i + 1)
  change gradMatrix (PressureImpulseHistory.impulse u m) x (i + 2) (i + 1) =
    gradMatrix (PressureImpulseHistory.impulse u m) x (i + 1) (i + 2) at hs
  rw [RetainedParentCompletion.impulse_gradient_entry,
    RetainedParentCompletion.impulse_gradient_entry] at hs
  linarith only [hs]

def materialCovectorRate (ν : ℝ) (u m : SmoothL2Field Space) (x : Space) : Fin 3 → ℝ :=
  fun i ↦ ((covectorRhs ν u m).field x + fderiv ℝ m.field x (u.field x) -
    ν • Δ m.field x) i

theorem material_covector_rate (ν : ℝ) (u m : SmoothL2Field Space) (x : Space) :
    materialCovectorRate ν u m x =
      (-(gradientMatrix u x).transpose) *ᵥ (fun i ↦ m.field x i) := by
  ext i
  change _ = ∑ k : Fin 3, -(gradMatrix u x k i) * m.field x k
  simp only [materialCovectorRate, covectorRhs_field, WithLp.ofLp_add,
    WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply, WithLp.ofLp_neg, Pi.neg_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, transposeStretch_coordinate,
    neg_mul, Finset.sum_neg_distrib]
  ring

def metricSquare (m : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  TransportedFrameMetric.pair Q (fun i ↦ m.field x i) (fun i ↦ m.field x i)

theorem metricSquare_nonneg (m : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (x : Space) : 0 ≤ metricSquare m Q x :=
  hQ.dotProduct_mulVec_nonneg (fun i ↦ m.field x i)

theorem metricSquare_initial_identity (m : SmoothL2Field Space) (x : Space) :
    metricSquare m (1 : Mat3) x = ∑ i : Fin 3, (m.field x i) ^ 2 := by
  simp only [metricSquare, TransportedFrameMetric.pair, Matrix.one_mulVec,
    dotProduct, pow_two]

def covariantDerivative (m : SmoothL2Field Space) (K : Fin 3 → Mat3)
    (x : Space) (j : Fin 3) : Fin 3 → ℝ :=
  (fun i ↦ (m.directionalField (axis j)).field x i) - K j *ᵥ (fun i ↦ m.field x i)

def connectionCurl (m : SmoothL2Field Space) (K : Fin 3 → Mat3) (x : Space) : Fin 3 → ℝ :=
  fun i ↦ (K (i + 1) *ᵥ (fun k ↦ m.field x k)) (i + 2) -
    (K (i + 2) *ᵥ (fun k ↦ m.field x k)) (i + 1)

def covariantCurl (m : SmoothL2Field Space) (K : Fin 3 → Mat3) (x : Space) : Fin 3 → ℝ :=
  fun i ↦ covariantDerivative m K x (i + 1) (i + 2) -
    covariantDerivative m K x (i + 2) (i + 1)

/-- Ordinary physical curl retains the spatial variation of the same
moving coframe. No payment for that connection is assumed. -/
theorem actual_vorticity_split (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (K : Fin 3 → Mat3) (x : Space) :
    (fun i ↦ (vorticityField u).field x i) =
      covariantCurl m K x + connectionCurl m K x := by
  rw [← actual_curl_reconstruction u m hγ x]
  ext i
  change gradMatrix m x (i + 2) (i + 1) - gradMatrix m x (i + 1) (i + 2) = _
  simp only [covariantCurl, connectionCurl, covariantDerivative, Pi.add_apply,
    Pi.sub_apply, gradMatrix]
  ring

def metricCost (m : SmoothL2Field Space) (Q : Mat3) (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  ∑ j : Fin 3, TransportedFrameMetric.pair Q
    (covariantDerivative m K x j) (covariantDerivative m K x j)

theorem metricCost_nonneg (m : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (K : Fin 3 → Mat3) (x : Space) : 0 ≤ metricCost m Q K x :=
  Finset.sum_nonneg fun j _ ↦ hQ.dotProduct_mulVec_nonneg (covariantDerivative m K x j)

def metricProduction (ν : ℝ) (u m : SmoothL2Field Space) (Q : Mat3)
    (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  TransportedFrameMetric.production ν Q (fun i ↦ m.field x i)
    (materialCovectorRate ν u m x)
    (TransportedFrameMetric.rate ν Q (-(gradientMatrix u x).transpose) K)
    (fun j i ↦ (m.directionalField (axis j)).field x i)
    (fun j ↦ TransportedFrameMetric.gradient Q (K j))

theorem metric_production (ν : ℝ) (u m : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.IsSymm) (K : Fin 3 → Mat3)
    (hK : ∀ j, Q * K j = (K j).transpose * Q) (x : Space) :
    metricProduction ν u m Q K x = -2 * ν * metricCost m Q K x := by
  rw [metricProduction, material_covector_rate]
  have he := TransportedFrameMetric.production_eq ν Q (-(gradientMatrix u x).transpose)
    hQ K hK (fun i ↦ m.field x i) 0
    (fun j i ↦ (m.directionalField (axis j)).field x i)
  simpa only [add_zero, TransportedFrameMetric.pair, Matrix.mulVec_zero,
    dotProduct_zero, mul_zero, zero_sub, metricCost, covariantDerivative, neg_mul] using he

theorem metric_nonpos (ν : ℝ) (hν : 0 ≤ ν) (u m : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.PosSemidef) (K : Fin 3 → Mat3)
    (hK : ∀ j, Q * K j = (K j).transpose * Q) (x : Space) :
    metricProduction ν u m Q K x ≤ 0 := by
  have hs : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.1
  rw [metric_production ν u m Q hs K hK x]
  have hc := metricCost_nonneg m Q hQ K x
  nlinarith only [mul_nonneg hν hc]

private theorem skew_square_le (R : Mat3) :
    (∑ i : Fin 3, (R (i + 1) (i + 2) - R (i + 2) (i + 1)) ^ 2) ≤
      2 * ∑ j : Fin 3, ∑ i : Fin 3, R j i ^ 2 := by
  simp only [Fin.sum_univ_three]
  change (R 1 2 - R 2 1) ^ 2 + (R 2 0 - R 0 2) ^ 2 + (R 0 1 - R 1 0) ^ 2 ≤ _
  nlinarith only [sq_nonneg (R 1 2 + R 2 1), sq_nonneg (R 2 0 + R 0 2),
    sq_nonneg (R 0 1 + R 1 0), sq_nonneg (R 0 0), sq_nonneg (R 1 1),
    sq_nonneg (R 2 2)]

/-- This conversion exposes both remaining inputs: physical coercivity
of the supplied metric and the curl of its connection. It is not a
time-integrated regularity estimate. -/
theorem actual_vorticity_conversion (u m : SmoothL2Field Space)
    (hγ : (fieldSub m u).toLp ∈ gradientSpace) (Q : Mat3) (K : Fin 3 → Mat3)
    (x : Space) (b : ℝ) (hb : 0 ≤ b)
    (hcoercive : ∀ j : Fin 3,
      b * (∑ i : Fin 3, covariantDerivative m K x j i ^ 2) ≤
        TransportedFrameMetric.pair Q (covariantDerivative m K x j)
          (covariantDerivative m K x j)) :
    b * (∑ i : Fin 3, ((vorticityField u).field x i) ^ 2) ≤
      4 * metricCost m Q K x +
        2 * b * (∑ i : Fin 3, connectionCurl m K x i ^ 2) := by
  have hs := skew_square_le (fun j i ↦ covariantDerivative m K x j i)
  change (∑ i : Fin 3, covariantCurl m K x i ^ 2) ≤
    2 * ∑ j : Fin 3, ∑ i : Fin 3, covariantDerivative m K x j i ^ 2 at hs
  have hp : (∑ i : Fin 3, ((vorticityField u).field x i) ^ 2) ≤
      2 * (∑ i : Fin 3, covariantCurl m K x i ^ 2) +
        2 * (∑ i : Fin 3, connectionCurl m K x i ^ 2) := by
    have he (i : Fin 3) : (vorticityField u).field x i =
        covariantCurl m K x i + connectionCurl m K x i :=
      congrFun (actual_vorticity_split u m hγ K x) i
    simp_rw [he]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    change (covariantCurl m K x i + connectionCurl m K x i) ^ 2 ≤ _
    nlinarith only [sq_nonneg (covariantCurl m K x i - connectionCurl m K x i)]
  have hc : b * (∑ j : Fin 3, ∑ i : Fin 3, covariantDerivative m K x j i ^ 2) ≤
      metricCost m Q K x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ hcoercive j
  have hs' := mul_le_mul_of_nonneg_left hs hb
  have hp' := mul_le_mul_of_nonneg_left hp hb
  nlinarith only [hc, hs', hp']

end Mettapedia.FluidDynamics.NavierStokes.CovectorFluidBridge
