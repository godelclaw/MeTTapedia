import MettapediaNS.CovectorParentHistory

/-!
# Joint parent geometry and the actual coframe pressure commutator

Reconstructing the original gradient retains the cross moment of both
parents. Its literal canonical NS rate has negative covariant diffusion
and signed pressure work. Solenoidality and pressure-Hessian symmetry
cancel every spatially constant metric, including anisotropic ones.
A smooth matrix correction leaves precisely its spatial commutator.

These are actual spatial-field identities and supplied-metric generator
identities. Construction of the evolving stochastic coframe, integration
in physical time, payment of its signed commutator and conversion to an
ordinary continuation criterion remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointCoframePressure

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanClassical EulerMeanSolenoidal WholeSpaceViscousEnergy
  WholeSpaceBetchov WholeSpacePressureDiffusion PressureImpulseHistory RetainedParentCompletion
  CovectorParentHistory
open scoped Matrix BigOperators

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

def parentCross (u H : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.pair Q (gradientMatrix H x i)
    (gradientMatrix (impulse u H) x i)

/-- The signed cross moment reconstructs the actual fluid gradient. -/
theorem actual_square_reconstruction (u H : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.IsSymm) (x : Space) :
    metricSquare u Q x = metricSquare H Q x + metricSquare (impulse u H) Q x -
      2 * parentCross u H Q x := by
  have hr (i : Fin 3) : gradientMatrix u x i =
      gradientMatrix H x i - gradientMatrix (impulse u H) x i := by
    ext j
    simp only [Pi.sub_apply, gradientMatrix, impulse_gradient_entry]
    ring
  simp only [metricSquare, hr, TransportedFrameMetric.pair_sub_self Q hQ,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, parentCross]
  ring

def actualGradientRate (ν : ℝ) (u : SmoothL2Field Space) (x : Space) : Mat3 :=
  fun i j ↦ gradientMatrix (projectedNavierStokesRhs ν u) x i j +
    (advectionField u (u.directionalField (axis j))).field x i -
    ν * (laplacianField (u.directionalField (axis j))).field x i

theorem actual_gradient_rate (ν : ℝ) (u : SmoothL2Field Space) (x : Space) :
    actualGradientRate ν u x = materialGradientRate ν u u x -
      gradientMatrix (pressureField u) x := by
  have he : projectedNavierStokesRhs ν u =
      fieldSub (passiveRhs ν u u) (pressureField u) := by
    apply field_ext
    funext y
    simp only [projectedNavierStokesRhs, navierStokesRhs, eulerRhs, passiveRhs,
      addField_field, fieldNeg_field, scaleField_field, fieldSub_field]
    module
  ext i j
  have hg : gradientMatrix (projectedNavierStokesRhs ν u) x i j =
      gradientMatrix (passiveRhs ν u u) x i j -
        gradientMatrix (pressureField u) x i j := by
    rw [he]
    have hf : (fieldSub (passiveRhs ν u u) (pressureField u)).field =
        (passiveRhs ν u u).field - (pressureField u).field :=
      funext (fieldSub_field _ _)
    simp only [gradientMatrix, gradMatrix, directionalField_field]
    rw [hf, fderiv_sub ((passiveRhs ν u u).smooth.differentiable (by simp) x)
      ((pressureField u).smooth.differentiable (by simp) x)]
    rfl
  simp only [actualGradientRate, materialGradientRate, Matrix.sub_apply, hg]
  ring

def actualPressureWork (u : SmoothL2Field Space) (Q : Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.pair Q (gradientMatrix u x i)
    (gradientMatrix (pressureField u) x i)

theorem actual_pressure_reconstruction (u H : SmoothL2Field Space) (Q : Mat3) (x : Space) :
    actualPressureWork u Q x =
      (∑ i : Fin 3, TransportedFrameMetric.pair Q (gradientMatrix H x i)
        (gradientMatrix (pressureField u) x i)) - pressureWork u H Q x := by
  have hr (i : Fin 3) : gradientMatrix u x i =
      gradientMatrix H x i - gradientMatrix (impulse u H) x i := by
    ext j
    simp only [Pi.sub_apply, gradientMatrix, impulse_gradient_entry]
    ring
  simp only [actualPressureWork, hr, pressureWork, TransportedFrameMetric.pair,
    sub_dotProduct, Finset.sum_sub_distrib]

/-- Conversion in the actual gradient direction is still an explicit
physical input. Joint reconstruction avoids separate parent conversions. -/
theorem actual_vorticity_conversion (u : SmoothL2Field Space) (Q : Mat3) (x : Space)
    (κ : ℝ) (h : MiddleEigenvalueAlgebra.normSq (gradientMatrix u x) ≤ κ * metricSquare u Q x) :
    MiddleEigenvalueAlgebra.vortSq (gradientMatrix u x) ≤ 2 * κ * metricSquare u Q x := by
  have hv := vorticity_normSq_le (gradientMatrix u x)
  linarith only [hv, h]

def actualMetricProduction (ν : ℝ) (u : SmoothL2Field Space) (Q : Mat3)
    (K : Fin 3 → Mat3) (x : Space) : ℝ :=
  ∑ i : Fin 3, TransportedFrameMetric.production ν Q (gradientMatrix u x i)
    (actualGradientRate ν u x i)
    (TransportedFrameMetric.rate ν Q (-(gradientMatrix u x).transpose) K)
    (fun k ↦ gradientMatrix (u.directionalField (axis k)) x i)
    (fun k ↦ TransportedFrameMetric.gradient Q (K k))

/-- No new pressure-force square is introduced when the parents are
recombined before estimating their production. -/
theorem actual_metric_production (ν : ℝ) (u : SmoothL2Field Space) (Q : Mat3)
    (hQ : Q.IsSymm) (K : Fin 3 → Mat3)
    (hK : ∀ k, Q * K k = (K k).transpose * Q) (x : Space) :
    actualMetricProduction ν u Q K x = -2 * actualPressureWork u Q x -
      2 * ν * metricCost u Q K x := by
  have hp := passive_metric_production ν u u Q hQ K hK x
  have he : actualMetricProduction ν u Q K x =
      passiveMetricProduction ν u u Q K x - 2 * actualPressureWork u Q x := by
    have hr (i : Fin 3) : actualGradientRate ν u x i =
        materialGradientRate ν u u x i - gradientMatrix (pressureField u) x i := by
      rw [actual_gradient_rate]
      rfl
    simp only [actualMetricProduction, hr,
      passiveMetricProduction, actualPressureWork, TransportedFrameMetric.production,
      TransportedFrameMetric.pair, Matrix.mulVec_sub, dotProduct_sub,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, ← Finset.mul_sum]
    ring
  rw [he, hp]
  ring

private theorem product_integrable (X Y : SmoothL2Field ℝ) :
    Integrable (fun x ↦ X.field x * Y.field x) := by
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using field_inner_integrable X Y

private theorem triple_integrable (X Y Z : SmoothL2Field ℝ) :
    Integrable (fun x ↦ X.field x * Y.field x * Z.field x) := by
  simpa only [RCLike.inner_apply, conj_trivial, scalarProduct_field, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using field_inner_integrable (scalarProduct X Y) Z

private theorem column_trace (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace)
    (x : Space) (k : Fin 3) :
    (∑ i : Fin 3, ((coord (u.directionalField (axis k)) i).directionalField
      (axis i)).field x) = 0 := by
  simpa only [coord_directional_field, hessTensor, Fin.sum_univ_three] using
    hessTensor_trace u hu x k

private theorem constant_column (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace)
    (k j : Fin 3) :
    (∫ x, ∑ i : Fin 3, gradMatrix u x i k * gradMatrix (pressureField u) x j i) = 0 := by
  let Y := coord (pressureField u) j
  let X := fun i ↦ coord (u.directionalField (axis k)) i
  have hi (i : Fin 3) := product_integrable (X i) (Y.directionalField (axis i))
  have hd (i : Fin 3) := product_integrable ((X i).directionalField (axis i)) Y
  have he (i : Fin 3) := field_directional_inner (X i) Y (axis i)
  simp only [field_inner, RCLike.inner_apply, conj_trivial] at he
  have hsum := congrArg (fun a : Fin 3 → ℝ ↦ ∑ i, a i) (funext he)
  simp only [Finset.sum_neg_distrib] at hsum
  have hz : (∫ x, ∑ i : Fin 3, Y.field x * ((X i).directionalField (axis i)).field x) = 0 := by
    have hf : (fun x ↦ ∑ i : Fin 3, Y.field x * ((X i).directionalField (axis i)).field x) =
        fun _ ↦ (0 : ℝ) := by
      funext x
      rw [← Finset.mul_sum, show (∑ i, ((X i).directionalField (axis i)).field x) = 0 from
        column_trace u hu x k, mul_zero]
    rw [hf, integral_zero]
  rw [integral_finsetSum _ fun i _ ↦ (hd i).congr
    (Filter.Eventually.of_forall fun x ↦ by ring)] at hz
  have hw : (∫ x, ∑ i : Fin 3, gradMatrix u x i k * gradMatrix (pressureField u) x j i) =
      ∑ i : Fin 3, ∫ x, (Y.directionalField (axis i)).field x * (X i).field x := by
    have heq : (fun x ↦ ∑ i : Fin 3, gradMatrix u x i k *
        gradMatrix (pressureField u) x j i) =
        fun x ↦ ∑ i : Fin 3, (X i).field x * (Y.directionalField (axis i)).field x := by
      simp only [X, Y, coord_field, coord_directional_field, gradMatrix]
    rw [heq, integral_finsetSum _ fun i _ ↦ hi i]
    simp only [mul_comm]
  rw [hw]
  linarith only [hsum, hz]

private theorem weighted_column (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace)
    (w : SmoothL2Field ℝ) (k j : Fin 3) :
    (∫ x, ∑ i : Fin 3, w.field x * gradMatrix u x i k *
      gradMatrix (pressureField u) x j i) =
      -(∫ x, ∑ i : Fin 3, (w.directionalField (axis i)).field x *
        gradMatrix u x i k * (pressureField u).field x j) := by
  let Y := coord (pressureField u) j
  let X := fun i ↦ coord (u.directionalField (axis k)) i
  have hi (i : Fin 3) := triple_integrable w (X i) (Y.directionalField (axis i))
  have hd (i : Fin 3) := triple_integrable (w.directionalField (axis i)) (X i) Y
  have ht (i : Fin 3) := triple_integrable w ((X i).directionalField (axis i)) Y
  have he (i : Fin 3) := field_directional_inner (scalarProduct w (X i)) Y (axis i)
  simp only [field_inner, RCLike.inner_apply, conj_trivial, scalarProduct_directional,
    addField_field, scalarProduct_field, smul_eq_mul] at he
  have he' (i : Fin 3) :
      (∫ x, w.field x * (X i).field x * (Y.directionalField (axis i)).field x) =
      -(∫ x, (w.directionalField (axis i)).field x * (X i).field x * Y.field x) -
        ∫ x, w.field x * ((X i).directionalField (axis i)).field x * Y.field x := by
    have hentry := he i
    have hf : (fun x ↦ Y.field x *
        ((w.directionalField (axis i)).field x * (X i).field x +
          w.field x * ((X i).directionalField (axis i)).field x)) =
        fun x ↦ (w.directionalField (axis i)).field x * (X i).field x * Y.field x +
          w.field x * ((X i).directionalField (axis i)).field x * Y.field x := by
      funext x; ring
    rw [hf, integral_add (hd i) (ht i)] at hentry
    have hp : (fun x ↦ (Y.directionalField (axis i)).field x *
        (w.field x * (X i).field x)) =
        fun x ↦ w.field x * (X i).field x * (Y.directionalField (axis i)).field x := by
      funext x; ring
    rw [hp] at hentry
    linarith only [hentry]
  have hz : (∫ x, ∑ i : Fin 3,
      w.field x * ((X i).directionalField (axis i)).field x * Y.field x) = 0 := by
    have hf : (fun x ↦ ∑ i : Fin 3,
        w.field x * ((X i).directionalField (axis i)).field x * Y.field x) =
        fun _ ↦ (0 : ℝ) := by
      funext x
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      rw [show (∑ i, ((X i).directionalField (axis i)).field x) = 0 from
        column_trace u hu x k, mul_zero, zero_mul]
    rw [hf, integral_zero]
  simp only [X, Y, coord_field, coord_directional_field] at hi hd ht he' hz ⊢
  simp only [gradMatrix]
  rw [integral_finsetSum _ fun i _ ↦ hi i,
    integral_finsetSum _ fun i _ ↦ hd i]
  simp_rw [he']
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [integral_finsetSum _ fun i _ ↦ ht i] at hz
  rw [hz, sub_zero]

/-- A constant matrix plus a smooth L² correction. No positivity or
symmetry is required for the spatial pressure cancellation. -/
def spatialMetric (Q₀ : Mat3) (w : Fin 3 → Fin 3 → SmoothL2Field ℝ) (x : Space) : Mat3 :=
  fun k j ↦ Q₀ k j + (w k j).field x

def pressureCommutator (u : SmoothL2Field Space)
    (w : Fin 3 → Fin 3 → SmoothL2Field ℝ) (x : Space) : ℝ :=
  ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3,
    ((w k j).directionalField (axis i)).field x * gradMatrix u x i k *
      (pressureField u).field x j

private theorem pressure_entries (u : SmoothL2Field Space) (Q : Mat3) (x : Space) :
    actualPressureWork u Q x = ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3,
      Q k j * gradMatrix u x i k * gradMatrix (pressureField u) x j i := by
  simp only [actualPressureWork, TransportedFrameMetric.pair, Matrix.mulVec,
    dotProduct, gradientMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [gradMatrix_symmetric _ (pressureField_mem_gradient u) x i j]
  ring

theorem actualPressureWork_integrable (u : SmoothL2Field Space) (Q₀ : Mat3)
    (w : Fin 3 → Fin 3 → SmoothL2Field ℝ) :
    Integrable (fun x ↦ actualPressureWork u (spatialMetric Q₀ w x) x) := by
  simp_rw [pressure_entries]
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro i _
  have hc := (product_integrable (coord (u.directionalField (axis k)) i)
    (coord ((pressureField u).directionalField (axis i)) j)).const_mul (Q₀ k j)
  have hw := triple_integrable (w k j) (coord (u.directionalField (axis k)) i)
    (coord ((pressureField u).directionalField (axis i)) j)
  convert hc.add hw using 1
  funext x
  simp only [Pi.add_apply, spatialMetric, coord_field, gradMatrix]
  ring

theorem pressureCommutator_integrable (u : SmoothL2Field Space)
    (w : Fin 3 → Fin 3 → SmoothL2Field ℝ) : Integrable (pressureCommutator u w) := by
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro i _
  exact triple_integrable ((w k j).directionalField (axis i))
    (coord (u.directionalField (axis k)) i) (coord (pressureField u) j)

/-- Solenoidality removes the gradient derivative; canonical Hessian
symmetry permits integration against the pressure gradient itself. -/
theorem integral_actual_pressure_commutator (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (Q₀ : Mat3)
    (w : Fin 3 → Fin 3 → SmoothL2Field ℝ) :
    (∫ x, actualPressureWork u (spatialMetric Q₀ w x) x) =
      -(∫ x, pressureCommutator u w x) := by
  let c := fun (k j i : Fin 3) (x : Space) ↦
    Q₀ k j * gradMatrix u x i k * gradMatrix (pressureField u) x j i
  let e := fun (k j i : Fin 3) (x : Space) ↦
    (w k j).field x * gradMatrix u x i k * gradMatrix (pressureField u) x j i
  let d := fun (k j i : Fin 3) (x : Space) ↦
    ((w k j).directionalField (axis i)).field x * gradMatrix u x i k *
      (pressureField u).field x j
  have hi (k j i : Fin 3) : Integrable (c k j i) := by
    simpa only [c, coord_field, gradMatrix, mul_assoc] using (product_integrable
      (coord (u.directionalField (axis k)) i)
      (coord ((pressureField u).directionalField (axis i)) j)).const_mul (Q₀ k j)
  have hw (k j i : Fin 3) : Integrable (e k j i) := triple_integrable (w k j)
    (coord (u.directionalField (axis k)) i)
    (coord ((pressureField u).directionalField (axis i)) j)
  have hd (k j i : Fin 3) : Integrable (d k j i) :=
    triple_integrable ((w k j).directionalField (axis i))
      (coord (u.directionalField (axis k)) i) (coord (pressureField u) j)
  have hc (k j : Fin 3) : (∫ x, ∑ i : Fin 3, c k j i x) = 0 := by
    simp only [c, mul_assoc, ← Finset.mul_sum, integral_const_mul,
      constant_column u hu k j, mul_zero]
  have hs (k j : Fin 3) :
      (∫ x, ∑ i : Fin 3, (c k j i x + e k j i x)) =
        -(∫ x, ∑ i : Fin 3, d k j i x) := by
    simp only [Finset.sum_add_distrib]
    rw [integral_add
      (integrable_finsetSum _ fun i _ ↦ hi k j i)
      (integrable_finsetSum _ fun i _ ↦ hw k j i), hc, zero_add]
    exact weighted_column u hu (w k j) k j
  have he : (fun x ↦ actualPressureWork u (spatialMetric Q₀ w x) x) =
      fun x ↦ ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, (c k j i x + e k j i x) := by
    funext x
    rw [pressure_entries]
    simp only [spatialMetric, c, e, add_mul]
  have hce (k j i : Fin 3) : Integrable (fun x ↦ c k j i x + e k j i x) := by
    convert (hi k j i).add (hw k j i) using 1
    all_goals rfl
  rw [he, integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun i _ ↦ hce k j i]
  have he' : (fun x ↦ pressureCommutator u w x) =
      fun x ↦ ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, d k j i x := rfl
  rw [he', integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun i _ ↦ hd k j i, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun i _ ↦
    hce k j i,
    integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun i _ ↦ hd k j i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ hs k j

/-- All constant metrics cancel, including anisotropic ones. -/
theorem integral_constant_pressure_eq_zero (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (Q : Mat3) :
    (∫ x, actualPressureWork u Q x) = 0 := by
  have hi (k j i : Fin 3) : Integrable
      (fun x ↦ Q k j * gradMatrix u x i k * gradMatrix (pressureField u) x j i) := by
    simpa only [coord_field, gradMatrix, mul_assoc] using (product_integrable
      (coord (u.directionalField (axis k)) i)
      (coord ((pressureField u).directionalField (axis i)) j)).const_mul (Q k j)
  simp_rw [pressure_entries]
  rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun i _ ↦ hi k j i]
  have he (k j : Fin 3) : (∫ x, ∑ i : Fin 3,
      Q k j * gradMatrix u x i k * gradMatrix (pressureField u) x j i) = 0 := by
    simp only [mul_assoc, ← Finset.mul_sum, integral_const_mul,
      constant_column u hu k j, mul_zero]
  have hs (k : Fin 3) : (∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
      Q k j * gradMatrix u x i k * gradMatrix (pressureField u) x j i) = 0 := by
    rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun i _ ↦ hi k j i]
    simp_rw [he]
    exact Finset.sum_const_zero
  simp_rw [hs]
  exact Finset.sum_const_zero

end Mettapedia.FluidDynamics.NavierStokes.JointCoframePressure
