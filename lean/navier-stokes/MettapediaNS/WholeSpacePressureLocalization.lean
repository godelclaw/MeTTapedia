import MettapediaNS.WholeSpacePressureDiffusion

/-!
# The signed localization defect of actual pressure diffusion

A varying weight introduces a pressure flux into the integrated Hessian
identity. The pressure below is constructed from the full solenoidal fluid.
The last theorem retains that signed flux in the memory-pressure payment;
it does not assume that the unweighted estimate remains true after selection.

Weights here are smooth scalar fields with all jets in L². Applying these
identities to the continuous soft-excess weight requires a weak limit.
The evolving memory and the completed physical Hessian bound remain separate
obligations, as does payment of the flux over arbitrary solution histories.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureLocalization

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical EulerMeanPressure WholeSpaceViscousEnergy WholeSpaceBetchov
  MiddleEigenvalueAlgebra WholeSpaceOrderEnergy WholeSpacePressureDiffusion

private theorem triple_integrable (X Y Z : SmoothL2Field ℝ) :
    Integrable (fun x ↦ X.field x * Y.field x * Z.field x) := by
  have h := field_inner_integrable (scalarProduct X Y) Z
  simpa only [RCLike.inner_apply, conj_trivial, scalarProduct_field, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using h

private theorem weighted_grad_integrable (w : SmoothL2Field ℝ) (A : SmoothL2Field Space) :
    Integrable (fun x ↦ w.field x * normSq (gradMatrix A x)) := by
  have h := field_inner_integrable w (gradientNormField A)
  simpa only [RCLike.inner_apply, conj_trivial, gradientNormField_field, mul_comm] using h

private theorem weighted_div_integrable (w : SmoothL2Field ℝ) (A : SmoothL2Field Space) :
    Integrable (fun x ↦ w.field x * ((traceField A).field x) ^ 2) := by
  have h := field_inner_integrable w (scalarProduct (traceField A) (traceField A))
  simpa only [RCLike.inner_apply, conj_trivial, scalarProduct_field, smul_eq_mul,
    pow_two, mul_comm] using h

private theorem coord_second_comm (A : SmoothL2Field Space) (i j k : Fin 3) :
    ((coord A i).directionalField (axis j)).directionalField (axis k) =
      ((coord A i).directionalField (axis k)).directionalField (axis j) := by
  apply field_ext
  funext x
  exact EulerVectorCalculus.partialDerivative_comm (coord A i).field
    ((coord A i).smooth.of_le (by simp)) j k x

private theorem weighted_cross_integral (w : SmoothL2Field ℝ)
    (A : SmoothL2Field Space) (i j : Fin 3) :
    (∫ x, w.field x * gradMatrix A x i j * gradMatrix A x j i) =
      (∫ x, w.field x * gradMatrix A x i i * gradMatrix A x j j) +
      (∫ x, (w.directionalField (axis i)).field x * A.field x i * gradMatrix A x j j) -
      ∫ x, (w.directionalField (axis j)).field x * A.field x i * gradMatrix A x j i := by
  have h₁ := field_directional_inner (scalarProduct w (coord A i))
    ((coord A j).directionalField (axis i)) (axis j)
  have h₂ := field_directional_inner (scalarProduct w (coord A i))
    ((coord A j).directionalField (axis j)) (axis i)
  rw [coord_second_comm A j i j] at h₁
  have h := h₁.trans h₂.symm
  simp only [field_inner, scalarProduct_directional, addField_field,
    scalarProduct_field, smul_eq_mul, RCLike.inner_apply, conj_trivial,
    coord_field, coord_directional_field] at h
  have h₃ := triple_integrable w (coord (A.directionalField (axis j)) i)
    (coord (A.directionalField (axis i)) j)
  have h₄ := triple_integrable w (coord (A.directionalField (axis i)) i)
    (coord (A.directionalField (axis j)) j)
  have h₅ := triple_integrable (w.directionalField (axis i)) (coord A i)
    (coord (A.directionalField (axis j)) j)
  have h₆ := triple_integrable (w.directionalField (axis j)) (coord A i)
    (coord (A.directionalField (axis i)) j)
  simp only [coord_field] at h₃ h₄ h₅ h₆
  have e₁ : (fun x ↦ (A.directionalField (axis i)).field x j *
      ((w.directionalField (axis j)).field x * A.field x i +
        w.field x * (A.directionalField (axis j)).field x i)) =
      fun x ↦ (w.directionalField (axis j)).field x * A.field x i *
        (A.directionalField (axis i)).field x j +
        w.field x * (A.directionalField (axis j)).field x i *
          (A.directionalField (axis i)).field x j := by funext x; ring
  have e₂ : (fun x ↦ (A.directionalField (axis j)).field x j *
      ((w.directionalField (axis i)).field x * A.field x i +
        w.field x * (A.directionalField (axis i)).field x i)) =
      fun x ↦ (w.directionalField (axis i)).field x * A.field x i *
        (A.directionalField (axis j)).field x j +
        w.field x * (A.directionalField (axis i)).field x i *
          (A.directionalField (axis j)).field x j := by funext x; ring
  rw [e₁, e₂, integral_add h₆ h₃, integral_add h₅ h₄] at h
  change (∫ x, w.field x * (A.directionalField (axis j)).field x i *
      (A.directionalField (axis i)).field x j) = _
  simp only [gradMatrix]
  linarith

/-- The signed boundary work from a varying spatial weight. For a gradient
field, its flux is `(div A) A-(grad A) A`. -/
def fluxWork (w : SmoothL2Field ℝ) (A : SmoothL2Field Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ((w.directionalField (axis i)).field x * A.field x i * gradMatrix A x j j -
      (w.directionalField (axis j)).field x * A.field x i * gradMatrix A x j i)

theorem fluxWork_integrable (w : SmoothL2Field ℝ) (A : SmoothL2Field Space) :
    Integrable (fluxWork w A) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (triple_integrable (w.directionalField (axis i)) (coord A i)
    (coord (A.directionalField (axis j)) j)).sub
      (triple_integrable (w.directionalField (axis j)) (coord A i)
        (coord (A.directionalField (axis i)) j))

/-- The weighted crossed-derivative identity retains the localization flux.
There is no divergence-free or gradient hypothesis in this identity. -/
theorem integral_weighted_trSq (w : SmoothL2Field ℝ) (A : SmoothL2Field Space) :
    (∫ x, w.field x * trSq (gradMatrix A x)) =
      (∫ x, w.field x * ((traceField A).field x) ^ 2) + ∫ x, fluxWork w A x := by
  have hi (i j : Fin 3) : Integrable
      (fun x ↦ w.field x * gradMatrix A x i j * gradMatrix A x j i) :=
    triple_integrable w (coord (A.directionalField (axis j)) i)
      (coord (A.directionalField (axis i)) j)
  have hd (i j : Fin 3) : Integrable
      (fun x ↦ w.field x * gradMatrix A x i i * gradMatrix A x j j) :=
    triple_integrable w (coord (A.directionalField (axis i)) i)
      (coord (A.directionalField (axis j)) j)
  have hp (i j : Fin 3) : Integrable (fun x ↦
      (w.directionalField (axis i)).field x * A.field x i * gradMatrix A x j j) :=
    triple_integrable (w.directionalField (axis i)) (coord A i)
      (coord (A.directionalField (axis j)) j)
  have hn (i j : Fin 3) : Integrable (fun x ↦
      (w.directionalField (axis j)).field x * A.field x i * gradMatrix A x j i) :=
    triple_integrable (w.directionalField (axis j)) (coord A i)
      (coord (A.directionalField (axis i)) j)
  have hf (i j : Fin 3) : Integrable (fun x ↦
      (w.directionalField (axis i)).field x * A.field x i * gradMatrix A x j j -
        (w.directionalField (axis j)).field x * A.field x i * gradMatrix A x j i) :=
    (hp i j).sub (hn i j)
  have ht : (∫ x, w.field x * trSq (gradMatrix A x)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, w.field x * gradMatrix A x i j * gradMatrix A x j i := by
    simp only [trSq, Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ fun j _ ↦ hi i j]
  have he (x : Space) : w.field x * ((traceField A).field x) ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, w.field x * gradMatrix A x i i * gradMatrix A x j j := by
    simp only [traceField_field, Fin.sum_univ_three]
    ring
  simp_rw [he]
  rw [ht, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hd i j]
  simp only [fluxWork]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hf i j]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ ↦ hd i j,
    integral_finsetSum _ fun j _ ↦ hf i j]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sub (hp i j) (hn i j), weighted_cross_integral]
  ring

/-- This identity needs only a genuine gradient field, not an L² scalar
potential. In particular it applies to the actual pressure gradient. -/
theorem integral_weighted_normSq (w : SmoothL2Field ℝ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ gradientSpace) :
    (∫ x, w.field x * normSq (gradMatrix A x)) =
      (∫ x, w.field x * ((traceField A).field x) ^ 2) + ∫ x, fluxWork w A x := by
  have he (x : Space) : normSq (gradMatrix A x) = trSq (gradMatrix A x) := by
    simp only [normSq, trSq, pow_two]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [gradMatrix_symmetric A hA x j i]
  simp_rw [he]
  exact integral_weighted_trSq w A

private theorem sumField_directional {ι : Type*} (s : Finset ι)
    (A : ι → SmoothL2Field ℝ) (k : Fin 3) :
    (sumField s A).directionalField (axis k) =
      sumField s (fun i ↦ (A i).directionalField (axis k)) :=
  wordField_sum s A (fun _ : Fin 1 ↦ k)

/-- Derivative of the squared Hessian norm as a literal smooth field. -/
theorem gradientNormField_directional_field (A : SmoothL2Field Space) (k : Fin 3)
    (x : Space) :
    ((gradientNormField A).directionalField (axis k)).field x =
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        gradMatrix A x i j * gradMatrix (A.directionalField (axis k)) x i j := by
  have hd (i j : Fin 3) :
      ((coord (A.directionalField (axis j)) i).directionalField (axis k)).field x =
        gradMatrix (A.directionalField (axis k)) x i j := by
    rw [coord_directional_field, directionalField_comm]
    rfl
  simp only [gradientNormField, sumField_directional, sumField_field,
    scalarProduct_directional, addField_field, scalarProduct_field, smul_eq_mul,
    hd, coord_grad_field, Fin.sum_univ_three]
  ring

/-- For `P=Hess p`, this is `P grad(Delta p)-(1/2)grad|P|²`.
The potential itself need not be an L² field. -/
def pressureFlux (u : SmoothL2Field Space) (x : Space) (j : Fin 3) : ℝ :=
  (∑ k : Fin 3, gradMatrix (pressureField u) x j k *
    ((traceField (pressureField u)).directionalField (axis k)).field x) -
      (1 / 2 : ℝ) * ((gradientNormField (pressureField u)).directionalField (axis j)).field x

/-- The coordinate localization work equals the signed physical pressure
flux. All pressure derivatives come from the canonical full-fluid field. -/
theorem directional_fluxWork_sum_eq (u : SmoothL2Field Space) (w : SmoothL2Field ℝ)
    (x : Space) :
    (∑ k : Fin 3, fluxWork w ((pressureField u).directionalField (axis k)) x) =
      ∑ j : Fin 3, (w.directionalField (axis j)).field x * pressureFlux u x j := by
  let A := pressureField u
  have hg (k : Fin 3) : (A.directionalField (axis k)).toLp ∈ gradientSpace := by
    rw [d_eq_word]
    exact word_gradient _ (pressureField_mem_gradient u) _
  have hs (k i j : Fin 3) : gradMatrix (A.directionalField (axis k)) x j i =
      gradMatrix (A.directionalField (axis j)) x i k := by
    rw [gradMatrix_symmetric _ (hg k) x j i]
    change (((A.directionalField (axis k)).directionalField (axis j)).field x) i = _
    rw [directionalField_comm]
    rfl
  have ht (k j : Fin 3) :
      (∑ i : Fin 3, (A.directionalField (axis k)).field x i *
        gradMatrix (A.directionalField (axis k)) x j i) =
      ∑ i : Fin 3, gradMatrix A x i k * gradMatrix (A.directionalField (axis j)) x i k := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hs k i j]
    rfl
  have hf (k : Fin 3) : fluxWork w (A.directionalField (axis k)) x =
      ∑ j : Fin 3, (w.directionalField (axis j)).field x *
        (gradMatrix A x j k * ((traceField A).directionalField (axis k)).field x -
          ∑ i : Fin 3, gradMatrix A x i k *
            gradMatrix (A.directionalField (axis j)) x i k) := by
    rw [← traceField_directional]
    simp_rw [← ht]
    simp only [fluxWork, traceField_field, gradMatrix, Fin.sum_univ_three]
    ring
  change (∑ k : Fin 3, fluxWork w (A.directionalField (axis k)) x) = _
  simp_rw [hf]
  change _ = ∑ j : Fin 3, (w.directionalField (axis j)).field x *
    ((∑ k : Fin 3, gradMatrix A x j k *
      ((traceField A).directionalField (axis k)).field x) -
      (1 / 2 : ℝ) * ((gradientNormField A).directionalField (axis j)).field x)
  simp only [gradientNormField_directional_field, Fin.sum_univ_three]
  ring

/-- Each coordinate derivative of the constructed pressure retains its
actual Poisson source and the signed localization work. -/
theorem integral_weighted_pressure_directional (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (w : SmoothL2Field ℝ) (k : Fin 3) :
    (∫ x, w.field x * normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) =
      (∫ x, w.field x * (((sourceField u).directionalField (axis k)).field x) ^ 2) +
        ∫ x, fluxWork w ((pressureField u).directionalField (axis k)) x := by
  have hg : ((pressureField u).directionalField (axis k)).toLp ∈ gradientSpace := by
    rw [d_eq_word]
    exact word_gradient _ (pressureField_mem_gradient u) _
  rw [integral_weighted_normSq _ _ hg, traceField_directional,
    traceField_pressureField u hu]
  have hn : (fieldNeg (sourceField u)).directionalField (axis k) =
      fieldNeg ((sourceField u).directionalField (axis k)) :=
    wordField_map (-(ContinuousLinearMap.id ℝ ℝ)) (sourceField u) (fun _ : Fin 1 ↦ k)
  rw [hn]
  simp only [fieldNeg_field, neg_sq]

/-- The spatial source bound pays the weighted local part; the remaining
term is the actual signed pressure flux rather than an assumed estimate. -/
theorem integral_weighted_pressure_directional_le (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (w : SmoothL2Field ℝ) (hw : ∀ x, 0 ≤ w.field x)
    (k : Fin 3) :
    (∫ x, w.field x * normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) ≤
      4 * (∫ x, w.field x * normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x)) +
        ∫ x, fluxWork w ((pressureField u).directionalField (axis k)) x := by
  rw [integral_weighted_pressure_directional u hu w k]
  have hi : Integrable (fun x ↦ w.field x *
      (((sourceField u).directionalField (axis k)).field x) ^ 2) := by
    convert! triple_integrable w ((sourceField u).directionalField (axis k))
      ((sourceField u).directionalField (axis k)) using 1
    funext x
    ring
  have hj := triple_integrable w (gradientNormField u)
    (gradientNormField (u.directionalField (axis k)))
  simp only [gradientNormField_field] at hj
  have h := integral_mono hi (hj.const_mul 4) (fun x ↦ by
    have hs := mul_le_mul_of_nonneg_left (source_directional_sq_le u k x) (hw x)
    simpa only [mul_assoc, mul_left_comm] using hs)
  rw [integral_const_mul] at h
  linarith

private theorem fieldSub_directional (A B : SmoothL2Field Space) (k : Fin 3) :
    (fieldSub A B).directionalField (axis k) =
      fieldSub (A.directionalField (axis k)) (B.directionalField (axis k)) := by
  change wordField (fieldSub A B) (fun _ : Fin 1 ↦ k) =
    fieldSub (wordField A (fun _ : Fin 1 ↦ k)) (wordField B (fun _ : Fin 1 ↦ k))
  simp only [fieldSub, wordField_add, fieldNeg, wordField_map]

/-- The selected memory-pressure norm is paid up to the actual signed
pressure flux. The observed gradient's construction from memory is separate. -/
theorem integral_weighted_memory_directional_le (u observed : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (w : SmoothL2Field ℝ) (hw : ∀ x, 0 ≤ w.field x)
    (k : Fin 3) :
    (∫ x, w.field x * normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
      (33 / 5 : ℝ) * (∫ x, w.field x *
        normSq (gradMatrix (observed.directionalField (axis k)) x)) +
      (33 / 7 : ℝ) * (∫ x, w.field x * normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x)) +
      (33 / 28 : ℝ) * ∫ x, fluxWork w ((pressureField u).directionalField (axis k)) x := by
  rw [fieldSub_directional]
  have hm := integral_mono (weighted_grad_integrable w _)
    (((weighted_grad_integrable w (observed.directionalField (axis k))).const_mul (33 / 5)).add
      ((weighted_grad_integrable w ((pressureField u).directionalField (axis k))).const_mul (33 / 28)))
    (fun x ↦ by
      have h := mul_le_mul_of_nonneg_left
        (normSq_gradMatrix_sub_le (observed.directionalField (axis k))
          ((pressureField u).directionalField (axis k)) x) (hw x)
      simpa only [Pi.add_apply, mul_add, mul_assoc, mul_left_comm] using h)
  simp only [Pi.add_apply] at hm
  rw [integral_add
      ((weighted_grad_integrable w (observed.directionalField (axis k))).const_mul (33 / 5))
      ((weighted_grad_integrable w ((pressureField u).directionalField (axis k))).const_mul (33 / 28)),
    integral_const_mul, integral_const_mul] at hm
  have hp := integral_weighted_pressure_directional_le u hu w hw k
  linarith

/-- The same strict coefficient as in the unweighted estimate is retained,
with the signed localization work exposed rather than discarded. -/
theorem memory_pressure_directional_paid_with_flux (u observed : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (w : SmoothL2Field ℝ) (hw : ∀ x, 0 ≤ w.field x)
    (k : Fin 3) (ν : ℝ) (hν : 0 ≤ ν) (D : Space → ℝ)
    (hD : Integrable (fun x ↦ w.field x * D x))
    (hlower : ∀ x, 8 * ν * normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x) +
      (56 / 5 : ℝ) * ν * normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D x) :
    ν * (∫ x, w.field x * normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
      (33 / 56 : ℝ) * (∫ x, w.field x * D x) +
        (33 / 28 : ℝ) * ν * ∫ x, fluxWork w ((pressureField u).directionalField (axis k)) x := by
  have hi := triple_integrable w (gradientNormField u)
    (gradientNormField (u.directionalField (axis k)))
  simp only [gradientNormField_field] at hi
  have hlow := integral_mono
    ((hi.const_mul (8 * ν)).add
      ((weighted_grad_integrable w (observed.directionalField (axis k))).const_mul ((56 / 5) * ν)))
    hD (fun x ↦ by
      have h := mul_le_mul_of_nonneg_left (hlower x) (hw x)
      simpa only [Pi.add_apply, mul_add, mul_assoc, mul_left_comm] using h)
  simp only [Pi.add_apply] at hlow
  rw [integral_add (hi.const_mul (8 * ν))
      ((weighted_grad_integrable w (observed.directionalField (axis k))).const_mul ((56 / 5) * ν)),
    integral_const_mul, integral_const_mul] at hlow
  have hm := mul_le_mul_of_nonneg_left
    (integral_weighted_memory_directional_le u observed hu w hw k) hν
  nlinarith only [hlow, hm]

/-- Full selected spatial payment, retaining every coordinate derivative
of canonical pressure and its signed weight flux. -/
theorem memory_pressure_gradient_paid_with_flux (u observed : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (w : SmoothL2Field ℝ) (hw : ∀ x, 0 ≤ w.field x)
    (ν : ℝ) (hν : 0 ≤ ν) (D : Fin 3 → Space → ℝ)
    (hD : ∀ k, Integrable (fun x ↦ w.field x * D k x))
    (hlower : ∀ k x, 8 * ν * normSq (gradMatrix u x) *
        normSq (gradMatrix (u.directionalField (axis k)) x) +
      (56 / 5 : ℝ) * ν * normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D k x) :
    ν * (∫ x, w.field x * ∑ k : Fin 3, normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
      (33 / 56 : ℝ) * (∫ x, w.field x * ∑ k : Fin 3, D k x) +
        (33 / 28 : ℝ) * ν * ∫ x, ∑ k : Fin 3,
          fluxWork w ((pressureField u).directionalField (axis k)) x := by
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun k _ ↦ weighted_grad_integrable w _,
    integral_finsetSum _ fun k _ ↦ hD k,
    integral_finsetSum _ fun k _ ↦ fluxWork_integrable w _]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ ↦
    memory_pressure_directional_paid_with_flux u observed hu w hw k ν hν (D k) (hD k) (hlower k)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureLocalization
