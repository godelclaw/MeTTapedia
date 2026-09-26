import MettapediaNS.WholeSpaceEnstrophyContinuation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MiddleEigenvalueAlgebra

/-!
# Betchov's identity on `ℝ³`

Let `u` be a smooth solenoidal field on `ℝ³` with all derivatives in `L²`, with gradient
`A a b = ∂_b u_a`. The square and cube traces of `A` are divergences:

```text
tr(A²) = div((u·∇)u),   tr(A³) = div(F),   F_i = (u·∇)u_k ∂_k u_i - u_i tr(A²)/2.
```

Each flux is a sum of products of two smooth `L²` fields, so the upstream integration by
parts gives `∫ tr(A²) = 0` and `∫ tr(A³) = 0` (`integral_trSq_eq_zero`,
`integral_trCube_eq_zero`). The pointwise identities are those of `MiddleEigenvalueAlgebra`,
already used on the torus.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBetchov

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal EulerMeanClassical
  WholeSpaceViscousEnergy WholeSpaceOrderEnergy MiddleEigenvalueAlgebra

/-! ## Coordinates and derivatives -/

/-- A coordinate of a field. -/
def coord (A : SmoothL2Field Space) (a : Fin 3) : SmoothL2Field ℝ :=
  mapField (EuclideanSpace.proj a) A

theorem coord_field (A : SmoothL2Field Space) (a : Fin 3) (x : Space) :
    (coord A a).field x = A.field x a := rfl

theorem coord_directional_field (A : SmoothL2Field Space) (a : Fin 3) (v x : Space) :
    ((coord A a).directionalField v).field x = (A.directionalField v).field x a := by
  rw [coord, coordinate_directional_field, directionalField_field]

/-- The velocity gradient `A a b = ∂_b u_a`. -/
def gradMatrix (u : SmoothL2Field Space) (x : Space) : GradMatrix :=
  fun a b ↦ (u.directionalField (axis b)).field x a

/-- The second derivatives `D i j k = ∂_i ∂_j u_k`. -/
def hessTensor (u : SmoothL2Field Space) (x : Space) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun i j k ↦ ((u.directionalField (axis j)).directionalField (axis i)).field x k

theorem hessTensor_symm (u : SmoothL2Field Space) (x : Space) (i j k : Fin 3) :
    hessTensor u x i j k = hessTensor u x j i k := by
  simp only [hessTensor]
  rw [directionalField_comm]

theorem gradMatrix_trace (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) (x : Space) :
    gradMatrix u x 0 0 + gradMatrix u x 1 1 + gradMatrix u x 2 2 = 0 := by
  have h := solenoidal_representative_divergence _ hA _ u.smooth u.toLp_ae x
  rw [divergence_eq_coordinate_sum, Fin.sum_univ_three] at h
  simpa only [gradMatrix, directionalField_field, axis] using h

theorem hessTensor_trace (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) (x : Space)
    (k : Fin 3) : hessTensor u x 0 k 0 + hessTensor u x 1 k 1 + hessTensor u x 2 k 2 = 0 := by
  have hs : (u.directionalField (axis k)).toLp ∈ solenoidalSpace := by
    rw [d_eq_word]
    exact word_solenoidal u hA _
  have h := solenoidal_representative_divergence _ hs _ (u.directionalField (axis k)).smooth
    (u.directionalField (axis k)).toLp_ae x
  rw [divergence_eq_coordinate_sum, Fin.sum_univ_three] at h
  simpa only [hessTensor, directionalField_field, axis] using h

/-! ## Divergences of products integrate to zero -/

theorem pair_integrable (X Y : SmoothL2Field ℝ) (v : Space) :
    Integrable (fun x ↦ (X.directionalField v).field x * Y.field x +
      X.field x * (Y.directionalField v).field x) := by
  have h1 := field_inner_integrable (X.directionalField v) Y
  have h2 := field_inner_integrable X (Y.directionalField v)
  simp only [RCLike.inner_apply, conj_trivial] at h1 h2
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply]
  ring

/-- **The integral of the derivative of a product vanishes.** -/
theorem integral_pair_directional (X Y : SmoothL2Field ℝ) (v : Space) :
    ∫ x, ((X.directionalField v).field x * Y.field x +
      X.field x * (Y.directionalField v).field x) = 0 := by
  have h := field_directional_ibp X Y v
  have h1 := field_inner_integrable (X.directionalField v) Y
  have h2 := field_inner_integrable X (Y.directionalField v)
  simp only [RCLike.inner_apply, conj_trivial] at h h1 h2
  have h' : ∫ x, Y.field x * (X.directionalField v).field x =
      -∫ x, (Y.directionalField v).field x * X.field x := by
    simpa only [directionalField_field] using h
  have e : (fun x ↦ (X.directionalField v).field x * Y.field x +
      X.field x * (Y.directionalField v).field x) =
      fun x ↦ Y.field x * (X.directionalField v).field x +
        (Y.directionalField v).field x * X.field x := by
    funext x
    ring
  rw [e, integral_add h1 h2, h']
  ring

/-! ## The square trace -/

theorem trSq_eq_pairs (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) (x : Space) :
    trSq (gradMatrix u x) = ∑ k : Fin 3, ∑ j : Fin 3,
      (((coord u j).directionalField (axis k)).field x *
          (coord (u.directionalField (axis j)) k).field x +
        (coord u j).field x *
          ((coord (u.directionalField (axis j)) k).directionalField (axis k)).field x) := by
  rw [← sqFluxDiv_eq (fun j ↦ u.field x j) (gradMatrix u x) (hessTensor u x)
    (hessTensor_trace u hA x)]
  simp only [sqFluxDiv, coord_directional_field, coord_field, gradMatrix, hessTensor]

/-- **`∫ tr(A²) = 0`.** -/
theorem integral_trSq_eq_zero (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) :
    ∫ x, trSq (gradMatrix u x) = 0 := by
  simp only [trSq_eq_pairs u hA]
  rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun j _ ↦ pair_integrable _ _ _]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ pair_integrable _ _ _]
  exact Finset.sum_eq_zero fun j _ ↦ integral_pair_directional _ _ _

/-! ## The cube trace -/

theorem coord_advection_field (u : SmoothL2Field Space) (k : Fin 3) (x : Space) :
    (coord (advectionField u u) k).field x = ∑ j : Fin 3, u.field x j * gradMatrix u x k j := by
  rw [coord_field, advectionField_field_sum]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    gradMatrix]

theorem coord_advection_directional_field (u : SmoothL2Field Space) (i k : Fin 3) (x : Space) :
    ((coord (advectionField u u) k).directionalField (axis i)).field x =
      ∑ j : Fin 3, u.field x j * hessTensor u x j i k +
        ∑ j : Fin 3, gradMatrix u x j i * gradMatrix u x k j := by
  rw [coord_directional_field, advection_directional, addField_field, advectionField_field_sum,
    advectionField_field_sum]
  simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, gradMatrix, hessTensor]

theorem coord_grad_field (u : SmoothL2Field Space) (a b : Fin 3) (x : Space) :
    (coord (u.directionalField (axis b)) a).field x = gradMatrix u x a b := rfl

theorem coord_grad_directional_field (u : SmoothL2Field Space) (a b i : Fin 3) (x : Space) :
    ((coord (u.directionalField (axis b)) a).directionalField (axis i)).field x =
      hessTensor u x i b a := by
  rw [coord_directional_field]
  rfl

theorem product_field (u : SmoothL2Field Space) (i a b : Fin 3) (x : Space) :
    (scalarProduct (coord u i) (coord (u.directionalField (axis b)) a)).field x =
      u.field x i * gradMatrix u x a b := by
  rw [scalarProduct_field, smul_eq_mul, coord_field, coord_grad_field]

theorem product_directional_field (u : SmoothL2Field Space) (i a b : Fin 3) (x : Space) :
    ((scalarProduct (coord u i) (coord (u.directionalField (axis b)) a)).directionalField
      (axis i)).field x =
      gradMatrix u x i i * gradMatrix u x a b + u.field x i * hessTensor u x i b a := by
  rw [scalarProduct_directional, addField_field, scalarProduct_field, scalarProduct_field,
    smul_eq_mul, smul_eq_mul, coord_directional_field, coord_grad_directional_field,
    coord_field, coord_field]
  rfl

/-- Sums of derivatives of products integrate to zero. -/
theorem integral_sum_pairs {ι : Type*} (s : Finset ι) (X Y : ι → SmoothL2Field ℝ)
    (v : ι → Space) :
    ∫ x, ∑ i ∈ s, (((X i).directionalField (v i)).field x * (Y i).field x +
      (X i).field x * ((Y i).directionalField (v i)).field x) = 0 := by
  rw [integral_finsetSum _ fun i _ ↦ pair_integrable _ _ _]
  exact Finset.sum_eq_zero fun i _ ↦ integral_pair_directional _ _ _

theorem sum_pairs_integrable {ι : Type*} (s : Finset ι) (X Y : ι → SmoothL2Field ℝ)
    (v : ι → Space) :
    Integrable (fun x ↦ ∑ i ∈ s, (((X i).directionalField (v i)).field x * (Y i).field x +
      (X i).field x * ((Y i).directionalField (v i)).field x)) :=
  integrable_finsetSum _ fun i _ ↦ pair_integrable _ _ _

/-- The first part of the cube flux divergence in the direction `i`. -/
def cubeAdvectionPairs (u : SmoothL2Field Space) (i : Fin 3) (x : Space) : ℝ :=
  ∑ k : Fin 3, (((coord (advectionField u u) k).directionalField (axis i)).field x *
      (coord (u.directionalField (axis k)) i).field x +
    (coord (advectionField u u) k).field x *
      ((coord (u.directionalField (axis k)) i).directionalField (axis i)).field x)

/-- The second part of the cube flux divergence in the direction `i`. -/
def cubeTracePairs (u : SmoothL2Field Space) (i : Fin 3) (x : Space) : ℝ :=
  ∑ p : Fin 3 × Fin 3,
    (((scalarProduct (coord u i) (coord (u.directionalField (axis p.2)) p.1)).directionalField
        (axis i)).field x * (coord (u.directionalField (axis p.1)) p.2).field x +
      (scalarProduct (coord u i) (coord (u.directionalField (axis p.2)) p.1)).field x *
        ((coord (u.directionalField (axis p.1)) p.2).directionalField (axis i)).field x)

theorem integral_cubeAdvectionPairs (u : SmoothL2Field Space) (i : Fin 3) :
    ∫ x, cubeAdvectionPairs u i x = 0 :=
  integral_sum_pairs Finset.univ (fun k ↦ coord (advectionField u u) k)
    (fun k ↦ coord (u.directionalField (axis k)) i) (fun _ ↦ axis i)

theorem integral_cubeTracePairs (u : SmoothL2Field Space) (i : Fin 3) :
    ∫ x, cubeTracePairs u i x = 0 :=
  integral_sum_pairs Finset.univ
    (fun p : Fin 3 × Fin 3 ↦ scalarProduct (coord u i) (coord (u.directionalField (axis p.2)) p.1))
    (fun p ↦ coord (u.directionalField (axis p.1)) p.2) (fun _ ↦ axis i)

theorem cubeAdvectionPairs_integrable (u : SmoothL2Field Space) (i : Fin 3) :
    Integrable (cubeAdvectionPairs u i) :=
  sum_pairs_integrable Finset.univ (fun k ↦ coord (advectionField u u) k)
    (fun k ↦ coord (u.directionalField (axis k)) i) (fun _ ↦ axis i)

theorem cubeTracePairs_integrable (u : SmoothL2Field Space) (i : Fin 3) :
    Integrable (cubeTracePairs u i) :=
  sum_pairs_integrable Finset.univ
    (fun p : Fin 3 × Fin 3 ↦ scalarProduct (coord u i) (coord (u.directionalField (axis p.2)) p.1))
    (fun p ↦ coord (u.directionalField (axis p.1)) p.2) (fun _ ↦ axis i)

theorem trCube_eq_pairs (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) (x : Space) :
    trCube (gradMatrix u x) =
      ∑ i : Fin 3, (cubeAdvectionPairs u i x - (1 / 2 : ℝ) * cubeTracePairs u i x) := by
  have e10 (k : Fin 3) := hessTensor_symm u x 1 0 k
  have e20 (k : Fin 3) := hessTensor_symm u x 2 0 k
  have e21 (k : Fin 3) := hessTensor_symm u x 2 1 k
  rw [← cubeFluxDiv_eq (fun j ↦ u.field x j) (gradMatrix u x) (hessTensor u x)
    (gradMatrix_trace u hA x) (hessTensor_trace u hA x) (hessTensor_symm u x)]
  simp only [cubeAdvectionPairs, cubeTracePairs, Fintype.sum_prod_type,
    coord_advection_directional_field, coord_advection_field, coord_grad_field,
    coord_grad_directional_field, product_directional_field, product_field,
    cubeFluxDiv, trSq, Fin.sum_univ_three, e10, e20, e21]
  ring

/-- **Betchov: `∫ tr(A³) = 0`.** -/
theorem integral_trCube_eq_zero (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) :
    ∫ x, trCube (gradMatrix u x) = 0 := by
  have hi (i : Fin 3) : Integrable
      (fun x ↦ cubeAdvectionPairs u i x - (1 / 2 : ℝ) * cubeTracePairs u i x) :=
    (cubeAdvectionPairs_integrable u i).sub ((cubeTracePairs_integrable u i).const_mul _)
  simp only [trCube_eq_pairs u hA]
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integral_sub (cubeAdvectionPairs_integrable u i)
      ((cubeTracePairs_integrable u i).const_mul _), integral_const_mul,
    integral_cubeAdvectionPairs, integral_cubeTracePairs]
  ring

/-! ## Enstrophy production and the middle eigenvalue -/

open scoped RealInnerProductSpace

/-- The pointwise enstrophy production `Σᵢ ⟪(∂ᵢu·∇)u, ∂ᵢu⟫ = Σ A_ji A_kj A_ki`. -/
def cubicSelf (A : GradMatrix) : ℝ :=
  ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, A j i * A k j * A k i

theorem cubicSelf_eq (A : GradMatrix) (htr : A 0 0 + A 1 1 + A 2 2 = 0) :
    cubicSelf A = trCube (symm A) - stretch A / 4 := by
  simp only [cubicSelf, trCube, MiddleEigenvalueAlgebra.symm_apply, stretch, vort,
    Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (1 / 4 : ℝ) * ((A 2 1 - A 1 2) ^ 2 + (A 0 2 - A 2 0) ^ 2 +
    (A 1 0 - A 0 1) ^ 2) * htr

theorem normSq_symm_eq (A : GradMatrix) : normSq (symm A) = (normSq A + trSq A) / 2 := by
  simp only [normSq, MiddleEigenvalueAlgebra.symm_apply, trSq, Fin.sum_univ_three]
  ring

theorem normSq_gradMatrix_eq (u : SmoothL2Field Space) (x : Space) :
    normSq (gradMatrix u x) = ∑ i : Fin 3,
      ⟪(u.directionalField (axis i)).field x, (u.directionalField (axis i)).field x⟫_ℝ := by
  simp only [inner_eq_sum, normSq, gradMatrix, sq]
  exact Finset.sum_comm

theorem inner_advection_directional (u : SmoothL2Field Space) (i : Fin 3) (x : Space) :
    ⟪(advectionField (u.directionalField (axis i)) u).field x,
        (u.directionalField (axis i)).field x⟫_ℝ =
      ∑ k : Fin 3, ∑ j : Fin 3, gradMatrix u x j i * gradMatrix u x k j * gradMatrix u x k i := by
  rw [advectionField_field_sum, sum_inner]
  simp only [real_inner_smul_left, inner_eq_sum, gradMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

theorem inner_commutator_one (u : SmoothL2Field Space) (i : Fin 3) :
    ⟪(transportCommutator u u (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i)).toLp,
        (wordField u (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i)).toLp⟫_ℝ =
      ∫ x, ∑ k : Fin 3, ∑ j : Fin 3,
        gradMatrix u x j i * gradMatrix u x k j * gradMatrix u x k i := by
  rw [transportCommutator_one, wordField_snoc, wordField_zero, field_inner]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ inner_advection_directional u i x)

theorem sum_words_one (f : (Fin 1 → Fin 3) → ℝ) :
    ∑ w : Fin 1 → Fin 3, f w = ∑ i : Fin 3, f (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) :=
  (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)).symm _ _ fun i ↦ by congr 1).symm

theorem cubicTerm_integrable (u : SmoothL2Field Space) (i : Fin 3) :
    Integrable (fun x ↦ ∑ k : Fin 3, ∑ j : Fin 3,
      gradMatrix u x j i * gradMatrix u x k j * gradMatrix u x k i) := by
  refine (field_inner_integrable (advectionField (u.directionalField (axis i)) u)
    (u.directionalField (axis i))).congr (Filter.Eventually.of_forall fun x ↦ ?_)
  exact inner_advection_directional u i x

theorem cubicSelf_integrable (u : SmoothL2Field Space) :
    Integrable (fun x ↦ cubicSelf (gradMatrix u x)) :=
  integrable_finsetSum _ fun i _ ↦ cubicTerm_integrable u i

/-- **The order-one production is the integrated cubic self-interaction.** -/
theorem orderProduction_one_eq (ν : ℝ) (u P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hA : u.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    orderProduction 1 u (navierStokesRhs ν u P) =
      -2 * (∫ x, cubicSelf (gradMatrix u x)) - 2 * ν * orderEnergy 2 u := by
  rw [orderProduction_navierStokesRhs 1 ν u P hdiv hA hP, sum_words_one]
  simp only [inner_commutator_one]
  rw [← integral_finsetSum _ fun i _ ↦ cubicTerm_integrable u i]
  simp only [cubicSelf]

theorem orderEnergy_one_eq (u : SmoothL2Field Space) :
    orderEnergy 1 u = ∫ x, normSq (gradMatrix u x) := by
  have hi (i : Fin 3) := field_inner_integrable (u.directionalField (axis i))
    (u.directionalField (axis i))
  rw [orderEnergy, sum_words_one]
  simp only [wordField_snoc, wordField_zero, ← real_inner_self_eq_norm_sq, field_inner]
  rw [← integral_finsetSum _ fun i _ ↦ hi i]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (normSq_gradMatrix_eq u x).symm)

theorem normSq_integrable (u : SmoothL2Field Space) :
    Integrable (fun x ↦ normSq (gradMatrix u x)) := by
  exact (integrable_finsetSum Finset.univ fun i _ ↦ field_inner_integrable
    (u.directionalField (axis i)) (u.directionalField (axis i))).congr
    (Filter.Eventually.of_forall fun x ↦ (normSq_gradMatrix_eq u x).symm)

theorem trSq_integrable (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) :
    Integrable (fun x ↦ trSq (gradMatrix u x)) := by
  have h := integrable_finsetSum Finset.univ fun k _ ↦ sum_pairs_integrable Finset.univ
    (fun j ↦ coord u j) (fun j ↦ coord (u.directionalField (axis j)) k) (fun _ ↦ axis k)
  exact h.congr (Filter.Eventually.of_forall fun x ↦ (trSq_eq_pairs u hA x).symm)

theorem trCube_integrable (u : SmoothL2Field Space) (hA : u.toLp ∈ solenoidalSpace) :
    Integrable (fun x ↦ trCube (gradMatrix u x)) := by
  have h := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦
    (cubeAdvectionPairs_integrable u i).sub ((cubeTracePairs_integrable u i).const_mul (1 / 2 : ℝ))
  exact h.congr (Filter.Eventually.of_forall fun x ↦ (trCube_eq_pairs u hA x).symm)

/-- **Enstrophy production is controlled by the positive middle eigenvalue.** If the middle
eigenvalue of the strain is at most `K ≥ 0` everywhere, then the order-one production is at
most `2 K E₁`. -/
theorem orderProduction_one_le {ν : ℝ} (hν : 0 ≤ ν) (u P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hA : u.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, PancakeSpectralProjectorRegularity.SymmetricStrain.secondEigenvalue
      (toStrain (symm (gradMatrix u x)) (symm_symm _)) ≤ K) :
    orderProduction 1 u (navierStokesRhs ν u P) ≤ 2 * K * orderEnergy 1 u := by
  have htr (x : Space) := gradMatrix_trace u hA x
  have hC := cubicSelf_integrable u
  have hT := trCube_integrable u hA
  have hN := normSq_integrable u
  have hQ := trSq_integrable u hA
  have hS : Integrable (fun x ↦ stretch (gradMatrix u x)) := by
    refine (hT.sub hC).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, cubicSelf_eq _ (htr x), trCube_eq _ (htr x)]
    ring
  have hTS : Integrable (fun x ↦ trCube (symm (gradMatrix u x))) := by
    refine (hC.add (hS.div_const 4)).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, cubicSelf_eq _ (htr x)]
    ring
  have h0 := integral_trCube_eq_zero u hA
  have hstretch : ∫ x, stretch (gradMatrix u x) = -∫ x, cubicSelf (gradMatrix u x) := by
    have e : (fun x ↦ stretch (gradMatrix u x)) =
        fun x ↦ trCube (gradMatrix u x) - cubicSelf (gradMatrix u x) := by
      funext x
      rw [cubicSelf_eq _ (htr x), trCube_eq _ (htr x)]
      ring
    rw [e, integral_sub hT hC, h0, zero_sub]
  have hsymm : ∫ x, trCube (symm (gradMatrix u x)) =
      3 / 4 * ∫ x, cubicSelf (gradMatrix u x) := by
    have e : (fun x ↦ trCube (symm (gradMatrix u x))) =
        fun x ↦ cubicSelf (gradMatrix u x) + stretch (gradMatrix u x) / 4 := by
      funext x
      rw [cubicSelf_eq _ (htr x)]
      ring
    rw [e, integral_add hC (hS.div_const 4), integral_div, hstretch]
    ring
  have hpt (x : Space) : -(4 / 3) * trCube (symm (gradMatrix u x)) ≤
      2 * K * normSq (symm (gradMatrix u x)) := by
    have h := neg_trCube_le (symm (gradMatrix u x)) (symm_symm _)
      (by rw [symm_trace]; exact htr x)
    have hn : 0 ≤ normSq (symm (gradMatrix u x)) :=
      Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hm : max (PancakeSpectralProjectorRegularity.SymmetricStrain.secondEigenvalue
        (toStrain (symm (gradMatrix u x)) (symm_symm _))) 0 ≤ K := max_le (hK x) hK0
    nlinarith
  have hNS : Integrable (fun x ↦ normSq (symm (gradMatrix u x))) := by
    refine ((hN.add hQ).div_const 2).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, normSq_symm_eq]
  have hint := integral_mono (hTS.const_mul (-(4 / 3))) (hNS.const_mul (2 * K)) hpt
  rw [integral_const_mul, integral_const_mul, hsymm] at hint
  have hnorm : ∫ x, normSq (symm (gradMatrix u x)) = orderEnergy 1 u / 2 := by
    have e : (fun x ↦ normSq (symm (gradMatrix u x))) =
        fun x ↦ (normSq (gradMatrix u x) + trSq (gradMatrix u x)) / 2 := by
      funext x
      exact normSq_symm_eq _
    rw [e, integral_div, integral_add hN hQ, integral_trSq_eq_zero u hA, add_zero,
      orderEnergy_one_eq]
  rw [hnorm] at hint
  have key : -∫ x, cubicSelf (gradMatrix u x) ≤ K * orderEnergy 1 u := by linarith
  rw [orderProduction_one_eq ν u P hdiv hA hP]
  have hE2 := mul_nonneg hν (orderEnergy_nonneg 2 u)
  linarith

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBetchov

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanSolenoidal EulerVolterraConvolution EulerContinuousTimeIntegral
  WholeSpaceViscousEnergy WholeSpaceOrderEnergy MiddleEigenvalueAlgebra WholeSpaceBetchov
open PancakeSpectralProjectorRegularity.SymmetricStrain

theorem realIntegral_le_of_nonneg (T : ℝ) (hT : 0 ≤ T) (K : C(Icc (0 : ℝ) T, ℝ))
    (hK : ∀ t, 0 ≤ K t) {t S : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) :
    realIntegral T hT K t ≤ realIntegral T hT K S := by
  have hc := extendPath_continuous T hT K
  simp only [realIntegral]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 t)
    (hc.intervalIntegrable t S)]
  have h : 0 ≤ ∫ s in t..S, extendPath T hT K s :=
    intervalIntegral.integral_nonneg (μ := volume) htS fun s _ ↦
      (show 0 ≤ extendPath T hT K s from hK _)
  linarith

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- **Grönwall from the middle eigenvalue.** If a continuous `K ≥ 0` bounds the middle strain
eigenvalue at every point, the gradient energy grows at most like `exp (2 ∫ K)`. -/
theorem orderEnergy_one_le_of_middle (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    (K : C(Icc (0 : ℝ) T, ℝ)) (hK0 : ∀ t, 0 ≤ K t)
    (hK : ∀ t x, secondEigenvalue
      (toStrain (symm (gradMatrix (U.velocity t) x)) (symm_symm _)) ≤ K t)
    (t : Icc (0 : ℝ) T) :
    orderEnergy 1 (U.velocity t) ≤
      orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩) * Real.exp (2 * realIntegral T hT K t) := by
  have h := variable_linear_stability T hT (extendPath T hT (U.orderEnergyPath 1))
    (fun r ↦ orderProduction 1 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    2 K ((U.orderEnergyPath 1).continuous.comp continuous_projIcc).continuousOn
    (fun r hr ↦ by
      have h := U.orderEnergy_hasDerivWithinAt 1 ⟨r, hr.1, hr.2.le⟩
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h)
    (fun r _ ↦ by
      have h := orderProduction_one_le hν (U.velocity (projIcc 0 T hT r))
        (U.pressureForce (projIcc 0 T hT r)) (U.velocity_divergence _) (U.solenoidal _)
        (U.gradient _) (hK0 _) (hK _)
      rw [← U.derivative_eq_navierStokesRhs] at h
      simpa only [extendPath, orderEnergyPath, ContinuousMap.coe_mk] using h) t
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), orderEnergyPath,
    ContinuousMap.coe_mk] using h

end NSEvolution

/-- **Integrable sheet-forming strain gives global evolutions.** If on every finite horizon the
middle strain eigenvalue of every evolution from the datum has a nonnegative continuous
majorant with uniformly bounded time integral, the datum has evolutions on every interval. -/
theorem hasNSEvolution_of_middle_bound {ν : ℝ} (hν : 0 < ν)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    (hbound : ∀ H, ∃ G, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
      U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∃ K : C(Icc (0 : ℝ) S, ℝ), (∀ t, 0 ≤ K t) ∧
        (∀ t x, secondEigenvalue
          (toStrain (symm (gradMatrix (U.velocity t) x)) (symm_symm _)) ≤ K t) ∧
        realIntegral S hS.le K S ≤ G) :
    ∀ T, 0 < T → HasNSEvolution ν A T := by
  refine hasNSEvolution_of_orderOne_bound hν A hA fun H ↦ ?_
  obtain ⟨G, hG⟩ := hbound H
  refine ⟨orderEnergy 1 A * Real.exp (2 * G), fun S hS hSH U hU t ↦ ?_⟩
  obtain ⟨K, hK0, hK, hKG⟩ := hG S hS hSH U hU
  have h := U.orderEnergy_one_le_of_middle hν.le K hK0 hK t
  rw [hU] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (orderEnergy_nonneg 1 A))
  have := realIntegral_le_of_nonneg S hS.le K hK0 t.2.1 t.2.2
  linarith

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOfficial

open Set EulerSmoothLimit EulerLpTranslation EulerMeanSolenoidal EulerContinuousTimeIntegral
  WholeSpaceViscousFlow MiddleEigenvalueAlgebra WholeSpaceBetchov
open PancakeSpectralProjectorRegularity.SymmetricStrain
open Mettapedia.FluidDynamics.NavierStokes.OfficialWholeSpaceProblem

/-- **Sheet-forming strain criterion for the official statement (A).** If, for every viscosity,
every smooth solenoidal datum and every finite horizon, the positive middle strain eigenvalue
of the smooth evolutions has a continuous majorant with bounded time integral, the official
whole-space statement holds. -/
theorem wholeSpaceStatementA_of_middle_bound
    (hbound : ∀ ν : ℝ, 0 < ν → ∀ A : SmoothL2Field Space, A.toLp ∈ solenoidalSpace →
      ∀ H, ∃ G, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
        U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∃ K : C(Icc (0 : ℝ) S, ℝ), (∀ t, 0 ≤ K t) ∧
          (∀ t x, secondEigenvalue
            (toStrain (symm (gradMatrix (U.velocity t) x)) (symm_symm _)) ≤ K t) ∧
          realIntegral S hS.le K S ≤ G) :
    WholeSpaceStatementA :=
  wholeSpaceStatementA_of_global fun ν hν A hA ↦
    hasNSEvolution_of_middle_bound hν A hA (hbound ν hν A hA)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOfficial
