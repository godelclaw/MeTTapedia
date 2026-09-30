import MettapediaNS.WholeSpaceBetchov
import MettapediaNS.WholeSpacePressure

/-!
# Integrated diffusion of the constructed pressure Hessian

The pressure is the actual Helmholtz pressure of a smooth solenoidal
whole-space velocity. Integration by parts identifies the squared Hessian
with the squared Poisson source, and its spatial derivatives with the
derivatives of that source. The resulting estimates supply a concrete
pressure term in the joint geometry/pressure diffusion comparison.

These are spatial identities at any smooth solution prefix. They do not
bound nonlinear production or the continuation budget over arbitrary
histories. In particular an unweighted integral cannot be substituted for
the diffusion restricted by the soft excess weight.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureDiffusion

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical EulerMeanPressure WholeSpaceViscousEnergy WholeSpaceBetchov
  MiddleEigenvalueAlgebra WholeSpaceOrderEnergy

/-- The actual divergence, represented as a smooth scalar L² field. -/
def traceField (A : SmoothL2Field Space) : SmoothL2Field ℝ :=
  sumField Finset.univ (fun i : Fin 3 ↦ coord (A.directionalField (axis i)) i)

theorem traceField_field (A : SmoothL2Field Space) (x : Space) :
    (traceField A).field x = ∑ i : Fin 3, gradMatrix A x i i := rfl

theorem traceField_eq_divergence (A : SmoothL2Field Space) (x : Space) :
    (traceField A).field x = divergence A.field x := by
  rw [divergence_eq_coordinate_sum, traceField_field]
  rfl

private theorem coord_second_comm (A : SmoothL2Field Space) (i j k : Fin 3) :
    ((coord A i).directionalField (axis j)).directionalField (axis k) =
      ((coord A i).directionalField (axis k)).directionalField (axis j) := by
  apply field_ext
  funext x
  exact EulerVectorCalculus.partialDerivative_comm (coord A i).field
    ((coord A i).smooth.of_le (by simp)) j k x

private theorem cross_integral (A : SmoothL2Field Space) (i j : Fin 3) :
    (∫ x, gradMatrix A x i j * gradMatrix A x j i) =
      ∫ x, gradMatrix A x i i * gradMatrix A x j j := by
  have h₁ := field_directional_inner (coord A i)
    ((coord A j).directionalField (axis i)) (axis j)
  have h₂ := field_directional_inner (coord A i)
    ((coord A j).directionalField (axis j)) (axis i)
  rw [coord_second_comm A j i j] at h₁
  have h := h₁.trans h₂.symm
  simp only [field_inner, RCLike.inner_apply, conj_trivial, coord_directional_field] at h
  simpa only [gradMatrix, mul_comm] using h

private theorem grad_product_integrable (A : SmoothL2Field Space) (i j k l : Fin 3) :
    Integrable (fun x ↦ gradMatrix A x i j * gradMatrix A x k l) := by
  have h := field_inner_integrable (coord (A.directionalField (axis j)) i)
    (coord (A.directionalField (axis l)) k)
  simpa only [RCLike.inner_apply, conj_trivial, coord_field, gradMatrix, mul_comm] using h

/-- Two integrations by parts exchange the crossed derivatives. No
solenoidal hypothesis is needed in this spatial identity. -/
theorem integral_trSq_eq_divergence_sq (A : SmoothL2Field Space) :
    (∫ x, trSq (gradMatrix A x)) = ∫ x, ((traceField A).field x) ^ 2 := by
  have hi (i j : Fin 3) := grad_product_integrable A i j j i
  have hd (i j : Fin 3) := grad_product_integrable A i i j j
  have hc : (∫ x, trSq (gradMatrix A x)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, gradMatrix A x i j * gradMatrix A x j i := by
    simp only [trSq]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ fun j _ ↦ hi i j]
  have hc' : (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x, gradMatrix A x i j * gradMatrix A x j i) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, gradMatrix A x i i * gradMatrix A x j j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact cross_integral A i j
  have hd' : (∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
      gradMatrix A x i i * gradMatrix A x j j) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, gradMatrix A x i i * gradMatrix A x j j := by
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hd i j]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ fun j _ ↦ hd i j]
  rw [hc, hc', ← hd']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [traceField_field, Fin.sum_univ_three]
    ring

theorem gradMatrix_symmetric (A : SmoothL2Field Space) (hA : A.toLp ∈ gradientSpace)
    (x : Space) (i j : Fin 3) : gradMatrix A x i j = gradMatrix A x j i :=
  gradientSpace_classical_curl_zero A.toLp hA A.field A.toLp_ae A.smooth x j i

/-- The gradient-field identity applies even if the scalar potential
itself is not in L². It applies to the constructed pressure gradient. -/
theorem integral_normSq_eq_divergence_sq (A : SmoothL2Field Space)
    (hA : A.toLp ∈ gradientSpace) :
    (∫ x, normSq (gradMatrix A x)) = ∫ x, ((traceField A).field x) ^ 2 := by
  have he (x : Space) : normSq (gradMatrix A x) = trSq (gradMatrix A x) := by
    simp only [normSq, trSq, pow_two]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [gradMatrix_symmetric A hA x j i]
  simp_rw [he]
  exact integral_trSq_eq_divergence_sq A

/-- The Poisson source as a smooth scalar field; its value is `tr((∇u)²)`. -/
def sourceField (u : SmoothL2Field Space) : SmoothL2Field ℝ :=
  sumField Finset.univ (fun i : Fin 3 ↦ sumField Finset.univ (fun j : Fin 3 ↦
    scalarProduct (coord (u.directionalField (axis j)) i)
      (coord (u.directionalField (axis i)) j)))

theorem sourceField_field (u : SmoothL2Field Space) (x : Space) :
    (sourceField u).field x = trSq (gradMatrix u x) := by
  simp only [sourceField, sumField_field, scalarProduct_field, smul_eq_mul,
    coord_field, trSq, gradMatrix]

theorem traceField_advection (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (x : Space) :
    (traceField (advectionField u u)).field x = trSq (gradMatrix u x) := by
  have h₀ := hessTensor_trace u hu x 0
  have h₁ := hessTensor_trace u hu x 1
  have h₂ := hessTensor_trace u hu x 2
  have e₁₀ (k : Fin 3) := hessTensor_symm u x 1 0 k
  have e₂₀ (k : Fin 3) := hessTensor_symm u x 2 0 k
  have e₂₁ (k : Fin 3) := hessTensor_symm u x 2 1 k
  simp only [traceField, sumField_field, coord_field]
  simp_rw [← coord_directional_field, coord_advection_directional_field]
  simp only [Fin.sum_univ_three, trSq, e₁₀, e₂₀, e₂₁] at *
  linear_combination u.field x 0 * h₀ + u.field x 1 * h₁ + u.field x 2 * h₂

/-- Canonical pressure satisfies the actual Poisson source identity.
No externally supplied pressure or evolution estimate is assumed. -/
theorem traceField_pressureField (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) :
    traceField (pressureField u) = fieldNeg (sourceField u) := by
  apply field_ext
  funext x
  let A := advectionField u u
  let V := solenoidalField A
  have hV : V.toLp ∈ solenoidalSpace := by
    rw [solenoidalField_toLp]
    exact solenoidalProjection_mem A.toLp
  have hd (i j : Fin 3) : gradMatrix (pressureField u) x i j =
      gradMatrix V x i j - gradMatrix A x i j := by
    have he : (pressureField u).field = V.field - A.field := by
      funext y
      exact fieldSub_field V A y
    change (fderiv ℝ (pressureField u).field x (axis j)) i = _
    rw [he, fderiv_sub (V.smooth.differentiable (by simp) x)
      (A.smooth.differentiable (by simp) x)]
    rfl
  have hz : (traceField V).field x = 0 := by
    rw [traceField_field, Fin.sum_univ_three]
    exact gradMatrix_trace V hV x
  rw [traceField_field, fieldNeg_field, sourceField_field]
  simp only [hd, Finset.sum_sub_distrib]
  change (traceField V).field x - (traceField A).field x = _
  rw [hz, traceField_advection u hu x]
  ring

/-- Exact L² identity for the actual pressure Hessian. -/
theorem integral_pressure_hessian_sq (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) :
    (∫ x, normSq (gradMatrix (pressureField u) x)) =
      ∫ x, (trSq (gradMatrix u x)) ^ 2 := by
  rw [integral_normSq_eq_divergence_sq _ (pressureField_mem_gradient u),
    traceField_pressureField u hu]
  simp only [fieldNeg_field, sourceField_field, neg_sq]

private theorem sumField_directional {ι : Type*} (s : Finset ι)
    (A : ι → SmoothL2Field ℝ) (k : Fin 3) :
    (sumField s A).directionalField (axis k) =
      sumField s (fun i ↦ (A i).directionalField (axis k)) :=
  wordField_sum s A (fun _ : Fin 1 ↦ k)

private theorem fieldNeg_directional (A : SmoothL2Field ℝ) (k : Fin 3) :
    (fieldNeg A).directionalField (axis k) = fieldNeg (A.directionalField (axis k)) :=
  wordField_map (-(ContinuousLinearMap.id ℝ ℝ)) A (fun _ : Fin 1 ↦ k)

theorem traceField_directional (A : SmoothL2Field Space) (k : Fin 3) :
    traceField (A.directionalField (axis k)) = (traceField A).directionalField (axis k) := by
  apply field_ext
  funext x
  simp only [traceField, sumField_directional, sumField_field]
  apply Finset.sum_congr rfl
  intro i _
  rw [coord_directional_field, directionalField_comm]
  rfl

/-- Derivative of the actual Poisson source, retaining all crossed entries. -/
theorem sourceField_directional_field (u : SmoothL2Field Space) (k : Fin 3) (x : Space) :
    ((sourceField u).directionalField (axis k)).field x =
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        gradMatrix u x j i * gradMatrix (u.directionalField (axis k)) x i j := by
  have hd (i j : Fin 3) :
      ((coord (u.directionalField (axis j)) i).directionalField (axis k)).field x =
        gradMatrix (u.directionalField (axis k)) x i j := by
    rw [coord_directional_field, directionalField_comm]
    rfl
  simp only [sourceField, sumField_directional, sumField_field, scalarProduct_directional,
    addField_field, scalarProduct_field, smul_eq_mul, hd, coord_grad_field,
    Fin.sum_univ_three]
  ring

/-- Exact spatial derivative identity for the constructed pressure Hessian. -/
theorem integral_pressure_hessian_directional_sq (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (k : Fin 3) :
    (∫ x, normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) =
      ∫ x, (((sourceField u).directionalField (axis k)).field x) ^ 2 := by
  have hg : ((pressureField u).directionalField (axis k)).toLp ∈ gradientSpace := by
    rw [d_eq_word]
    exact word_gradient _ (pressureField_mem_gradient u) _
  rw [integral_normSq_eq_divergence_sq _ hg, traceField_directional,
    traceField_pressureField u hu, fieldNeg_directional]
  simp only [fieldNeg_field, neg_sq]

/-- Squared Frobenius norm of the velocity gradient as a scalar L² field. -/
def gradientNormField (u : SmoothL2Field Space) : SmoothL2Field ℝ :=
  sumField Finset.univ (fun i : Fin 3 ↦ sumField Finset.univ (fun j : Fin 3 ↦
    scalarProduct (coord (u.directionalField (axis j)) i)
      (coord (u.directionalField (axis j)) i)))

theorem gradientNormField_field (u : SmoothL2Field Space) (x : Space) :
    (gradientNormField u).field x = normSq (gradMatrix u x) := by
  simp only [gradientNormField, sumField_field, scalarProduct_field, smul_eq_mul,
    coord_field, normSq, gradMatrix, pow_two]

theorem normSq_product_integrable (u v : SmoothL2Field Space) :
    Integrable (fun x ↦ normSq (gradMatrix u x) * normSq (gradMatrix v x)) := by
  have h := field_inner_integrable (gradientNormField u) (gradientNormField v)
  simpa only [RCLike.inner_apply, conj_trivial, gradientNormField_field, mul_comm] using h

theorem trSq_sq_le_normSq_sq (A : GradMatrix) : (trSq A) ^ 2 ≤ (normSq A) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p ↦ A p.1 p.2) (fun p ↦ A p.2 p.1)
  simp only [Fintype.sum_prod_type] at h
  have he : (∑ i : Fin 3, ∑ j : Fin 3, A j i ^ 2) = ∑ i : Fin 3, ∑ j : Fin 3, A i j ^ 2 := by
    rw [Finset.sum_comm]
  rw [he] at h
  simpa only [trSq, normSq, pow_two] using h

theorem source_directional_sq_le (u : SmoothL2Field Space) (k : Fin 3) (x : Space) :
    (((sourceField u).directionalField (axis k)).field x) ^ 2 ≤
      4 * normSq (gradMatrix u x) * normSq (gradMatrix (u.directionalField (axis k)) x) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p ↦ gradMatrix u x p.2 p.1)
    (fun p ↦ gradMatrix (u.directionalField (axis k)) x p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  have he : (∑ i : Fin 3, ∑ j : Fin 3, gradMatrix u x j i ^ 2) =
      normSq (gradMatrix u x) := by
    rw [Finset.sum_comm]
    rfl
  rw [he] at h
  rw [sourceField_directional_field]
  dsimp [normSq] at *
  nlinarith only [h]

/-- The actual pressure square is bounded by a local velocity quartic. -/
theorem integral_pressure_hessian_sq_le (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) :
    (∫ x, normSq (gradMatrix (pressureField u) x)) ≤
      ∫ x, (normSq (gradMatrix u x)) ^ 2 := by
  rw [integral_pressure_hessian_sq u hu]
  have hi := field_inner_integrable (sourceField u) (sourceField u)
  have hj := normSq_product_integrable u u
  simp only [RCLike.inner_apply, conj_trivial, sourceField_field, ← pow_two] at hi hj
  exact integral_mono hi hj (fun x ↦ trSq_sq_le_normSq_sq _)

/-- This derivative cost is one of the terms in the joint convex diffusion,
with no future-solution supremum or pressure estimate as a hypothesis. -/
theorem integral_pressure_hessian_directional_sq_le (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (k : Fin 3) :
    (∫ x, normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) ≤
      4 * ∫ x, normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x) := by
  rw [integral_pressure_hessian_directional_sq u hu k, ← integral_const_mul]
  have hi := field_inner_integrable ((sourceField u).directionalField (axis k))
    ((sourceField u).directionalField (axis k))
  simp only [RCLike.inner_apply, conj_trivial, ← pow_two] at hi
  exact integral_mono hi ((normSq_product_integrable u _).const_mul 4)
    (fun x ↦ by simpa only [mul_assoc] using source_directional_sq_le u k x)

private theorem fieldSub_directional (A B : SmoothL2Field Space) (k : Fin 3) :
    (fieldSub A B).directionalField (axis k) =
      fieldSub (A.directionalField (axis k)) (B.directionalField (axis k)) := by
  change wordField (fieldSub A B) (fun _ : Fin 1 ↦ k) =
    fieldSub (wordField A (fun _ : Fin 1 ↦ k)) (wordField B (fun _ : Fin 1 ↦ k))
  simp only [fieldSub, wordField_add, fieldNeg, wordField_map]

private theorem gradMatrix_sub (A B : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (fieldSub A B) x i j = gradMatrix A x i j - gradMatrix B x i j := by
  have he : (fieldSub A B).field = A.field - B.field := funext (fieldSub_field A B)
  change (fderiv ℝ (fieldSub A B).field x (axis j)) i = _
  rw [he, fderiv_sub (A.smooth.differentiable (by simp) x)
    (B.smooth.differentiable (by simp) x)]
  rfl

/-- A weighted square retains the sharp coefficient needed for the
pressure-source bound and the completed Hessian's two diffusion costs. -/
theorem normSq_gradMatrix_sub_le (A B : SmoothL2Field Space) (x : Space) :
    normSq (gradMatrix (fieldSub A B) x) ≤
      (33 / 5 : ℝ) * normSq (gradMatrix A x) +
        (33 / 28 : ℝ) * normSq (gradMatrix B x) := by
  simp only [normSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [gradMatrix_sub]
  nlinarith only [sq_nonneg (28 * gradMatrix A x i j + 5 * gradMatrix B x i j)]

/-- The memory-pressure difference is tied to actual fluid pressure.
`observed` may be the gradient of the pressure observer of `u⊗u+C`;
the construction of that memory is a separate PDE obligation. -/
theorem integral_memory_pressure_directional_sq_le (u observed : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (k : Fin 3) :
    (∫ x, normSq (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
      (33 / 5 : ℝ) * (∫ x, normSq (gradMatrix (observed.directionalField (axis k)) x)) +
        (33 / 7 : ℝ) * ∫ x, normSq (gradMatrix u x) *
          normSq (gradMatrix (u.directionalField (axis k)) x) := by
  rw [fieldSub_directional]
  have hm := integral_mono (normSq_integrable _)
    (((normSq_integrable (observed.directionalField (axis k))).const_mul (33 / 5)).add
      ((normSq_integrable ((pressureField u).directionalField (axis k))).const_mul (33 / 28)))
    (normSq_gradMatrix_sub_le (observed.directionalField (axis k))
      ((pressureField u).directionalField (axis k)))
  simp only [Pi.add_apply] at hm
  rw [integral_add
      ((normSq_integrable (observed.directionalField (axis k))).const_mul (33 / 5))
      ((normSq_integrable ((pressureField u).directionalField (axis k))).const_mul (33 / 28)),
    integral_const_mul, integral_const_mul] at hm
  have hp := integral_pressure_hessian_directional_sq_le u hu k
  linarith

/-- The completed diffusion pays the derivative of memory pressure with
coefficient `33/56 < 1`. Its physical Hessian lower bound is explicit.
The integral is unweighted; this does not pay an excess-selected norm. -/
theorem memory_pressure_directional_paid (u observed : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (k : Fin 3) (ν : ℝ) (hν : 0 ≤ ν)
    (D : Space → ℝ) (hD : Integrable D)
    (hlower : ∀ x, 8 * ν * normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x) +
      (56 / 5 : ℝ) * ν * normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D x) :
    ν * (∫ x, normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
        (33 / 56 : ℝ) * ∫ x, D x := by
  have hlow := integral_mono
    (((normSq_product_integrable u _).const_mul (8 * ν)).add
      ((normSq_integrable (observed.directionalField (axis k))).const_mul ((56 / 5) * ν)))
    hD (fun x ↦ by simpa only [mul_assoc, Pi.add_apply] using hlower x)
  simp only [Pi.add_apply] at hlow
  rw [integral_add ((normSq_product_integrable u _).const_mul (8 * ν))
      ((normSq_integrable (observed.directionalField (axis k))).const_mul ((56 / 5) * ν)),
    integral_const_mul, integral_const_mul] at hlow
  have hm := mul_le_mul_of_nonneg_left
    (integral_memory_pressure_directional_sq_le u observed hu k) hν
  nlinarith only [hlow, hm]

/-- The complete spatial gradient of memory pressure has the same strict
payment coefficient after summing the three actual coordinate derivatives. -/
theorem memory_pressure_gradient_paid (u observed : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (ν : ℝ) (hν : 0 ≤ ν)
    (D : Fin 3 → Space → ℝ) (hD : ∀ k, Integrable (D k))
    (hlower : ∀ k x, 8 * ν * normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x) +
      (56 / 5 : ℝ) * ν * normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D k x) :
    ν * (∫ x, ∑ k : Fin 3, normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
        (33 / 56 : ℝ) * ∫ x, ∑ k : Fin 3, D k x := by
  rw [integral_finsetSum _ fun k _ ↦ normSq_integrable _,
    integral_finsetSum _ fun k _ ↦ hD k]
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦
    memory_pressure_directional_paid u observed hu k ν hν (D k) (hD k) (hlower k)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureDiffusion
