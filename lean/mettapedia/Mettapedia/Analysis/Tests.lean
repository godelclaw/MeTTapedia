import Mettapedia.Analysis.ODE.QuadraticFormBound
import Mettapedia.Analysis.ODE.AbsolutelyContinuousComparison
import Mettapedia.Analysis.ODE.VariableGronwall
import Mettapedia.Analysis.LogarithmicScaleBound
import Mettapedia.Analysis.SimpleImplicitRoot
import Mettapedia.Analysis.OperatorQuadraticForm
import Mettapedia.Analysis.IdempotentDerivatives
import Mettapedia.Analysis.SpectralRelationDerivatives
import Mettapedia.Analysis.KernelCrossTerm
import Mettapedia.Analysis.OrthogonalProjectionParabolic
import Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion
import Mettapedia.Analysis.SecondDerivative
import Mettapedia.Analysis.PositiveOperatorKernelCurvature
import Mettapedia.Analysis.RankOneCommutator
import Mettapedia.Analysis.OrthonormalOperatorBound
import Mettapedia.Analysis.FiniteMultiplierLocalization
import Mettapedia.Analysis.LocallyLipschitz
import Mettapedia.Analysis.LocallyLipschitzDifferentiability
import Mettapedia.Analysis.FiniteCoefficientEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Regression examples for the analysis estimates. -/

open Set MeasureTheory Mettapedia.Analysis Mettapedia.Analysis.ODE
open scoped ContDiff RealInnerProductSpace

-- Equal vectors attain the finite linear-combination bound.
example : ‖∑ _j : Fin 3, (1 : ℝ) • (2 : ℝ)‖ ^ 2 =
    (∑ _j : Fin 3, ‖(1 : ℝ)‖ ^ 2) * (∑ _j : Fin 3, ‖(2 : ℝ)‖ ^ 2) := by
  norm_num

-- Three identical terms attain the three-term coefficient-energy factor.
example : FiniteMultiplierLocalization.scalarEnergy ({0} : Finset ℕ)
    (fun _ ↦ (1 : ℂ) + 1 + 1) =
      3 * (FiniteMultiplierLocalization.scalarEnergy ({0} : Finset ℕ) (fun _ ↦ (1 : ℂ)) +
        FiniteMultiplierLocalization.scalarEnergy ({0} : Finset ℕ) (fun _ ↦ (1 : ℂ)) +
        FiniteMultiplierLocalization.scalarEnergy ({0} : Finset ℕ) (fun _ ↦ (1 : ℂ))) := by
  norm_num [FiniteMultiplierLocalization.scalarEnergy]

#print axioms Finset.norm_sum_smul_sq_le
#print axioms Finset.norm_sum_sq_le_card_mul_sum_norm_sq
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.scalarEnergy_nonneg
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.scalarEnergy_add_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.scalarEnergy_sum_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.scalarEnergy_const_mul
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.scalarEnergy_add_add_le

-- A corner in the scalar factor is compatible with local Lipschitz regularity.
example : LocallyLipschitz (fun x : ℝ ↦ ‖x‖ • (x, x ^ 2)) := by
  have hg : ContDiff ℝ 1 (fun x : ℝ ↦ (x, x ^ 2)) := by fun_prop
  exact lipschitzWith_one_norm.locallyLipschitz.smul_real hg.locallyLipschitz

-- Rademacher applies to vector-valued maps without a globally smooth choice.
example : ∀ᵐ x : ℝ, DifferentiableAt ℝ (fun x : ℝ ↦ (‖x‖, x)) x := by
  have hf : LocallyLipschitz (fun x : ℝ ↦ (‖x‖, x)) :=
    lipschitzWith_one_norm.locallyLipschitz.prodMk LipschitzWith.id.locallyLipschitz
  exact hf.ae_differentiableAt volume

example : StronglyMeasurable (fun x : ℝ ↦ deriv (fun t : ℝ ↦ (x * t, t ^ 2)) 0) := by
  apply Continuous.stronglyMeasurable_deriv_const
  fun_prop

#print axioms LocallyLipschitz.smul_real
#print axioms LocallyLipschitz.ae_differentiableAt
#print axioms Continuous.stronglyMeasurable_deriv_const

-- Coincident output modes interfere; they must be collected before squaring.
example : FiniteMultiplierLocalization.scalarConvolution ({0, 1} : Finset ℤ)
    {0, 1} (fun _ ↦ (1 : ℝ)) (fun _ ↦ 1) 1 = 2 := by
  unfold FiniteMultiplierLocalization.scalarConvolution
  rw [Finset.sum_filter, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- A single frequency shift already creates a nonzero commutator.
example : FiniteMultiplierLocalization.commutatorCoefficient ({1} : Finset ℤ)
    {1} (fun _ ↦ (1 : ℝ)) (fun _ ↦ 1) (fun k ↦ (k : ℝ)) 2 = -1 := by
  norm_num [FiniteMultiplierLocalization.commutatorCoefficient, Finset.sum_filter,
    Finset.sum_product]

example : FiniteMultiplierLocalization.vectorConvolution ({1} : Finset ℤ)
    {1} (fun _ ↦ (1 : ℝ)) (fun k ↦ (k : ℝ)) 2 = 1 ∧
    FiniteMultiplierLocalization.scalarConvolution ({1} : Finset ℤ)
      {1} (fun _ ↦ (1 : ℝ)) (fun _ ↦ 1) 2 * 2 = 2 := by
  unfold FiniteMultiplierLocalization.vectorConvolution FiniteMultiplierLocalization.scalarConvolution
  simp only [Finset.sum_filter, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- Constant spatial cutoffs have no multiplier commutator, including at zero.
example {G E : Type*} [AddCommGroup G] [DecidableEq G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Finset G)
    (c b : G → ℝ) (m : G → E) (q : G) :
    FiniteMultiplierLocalization.commutatorCoefficient {0} K c b m q = 0 := by
  classical
  unfold FiniteMultiplierLocalization.commutatorCoefficient
  apply Finset.sum_eq_zero
  intro pk hpk
  have hp : pk.1 = 0 := Finset.mem_singleton.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).1
  simp [hp]

#print axioms Mettapedia.Analysis.FiniteConvolutionEnergy.sum_fiber_weight_le
#print axioms Mettapedia.Analysis.FiniteConvolutionEnergy.sum_norm_sq_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.vectorConvolution_multiplier_eq
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.commutator_energy_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.localized_multiplier_energy_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.localized_multiplier_energy_le_of_variation
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.localized_multiplier_energy_le_with_tail

-- Rank-one projection attains the orthonormal-basis energy bound.
example :
    let b := EuclideanSpace.basisFun (Fin 2) ℝ
    let R := InnerProductSpace.rankOne ℝ (b 0) (b 0)
    ‖R‖ ^ 2 = ∑ j, ‖R (b j)‖ ^ 2 := by
  dsimp only
  simp [InnerProductSpace.norm_rankOne, InnerProductSpace.rankOne_apply,
    Fin.sum_univ_two, EuclideanSpace.inner_single_right]

#print axioms ContinuousLinearMap.norm_apply_sq_le_sum_orthonormalBasis
#print axioms ContinuousLinearMap.norm_sq_le_sum_orthonormalBasis

-- A rank-one operator can annihilate the leading direction while its
-- commutator still rotates the transverse plane. This is operator algebra,
-- not an assertion about a pressure produced by a PDE solution.
example :
    let e := (EuclideanSpace.basisFun (Fin 3) ℝ) 0
    let f := (EuclideanSpace.basisFun (Fin 3) ℝ) 1
    let g := (EuclideanSpace.basisFun (Fin 3) ℝ) 2
    let T := InnerProductSpace.rankOne ℝ e e - InnerProductSpace.rankOne ℝ g g
    let H := InnerProductSpace.rankOne ℝ (f + g) (f + g)
    H e = 0 ∧ (T * H - H * T) f = -g ∧ ‖(T * H - H * T) f‖ = 1 := by
  dsimp only
  simp [sub_apply, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    inner_add_right, EuclideanSpace.inner_single_right]

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (q : E) (a : ℝ)
    (hq : T q = a • q) : T * InnerProductSpace.rankOne ℝ q q =
      InnerProductSpace.rankOne ℝ q q * T :=
  InnerProductSpace.rankOne_self_commutes_of_eigenvector T hT q a hq

-- A(t) = [[t²,t],[t,1]] is positive. At its kernel vector e and
-- increment -f, the curvature, cross term, and gradient square sum to zero.
example :
    let e := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
    let f := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
    let P := InnerProductSpace.rankOne ℝ e e
    let Q := InnerProductSpace.rankOne ℝ f f
    let G := InnerProductSpace.rankOne ℝ e f + InnerProductSpace.rankOne ℝ f e
    let A := fun t : ℝ ↦ t ^ 2 • P + t • G + Q
    let q := 2 * ⟪-f, A 0 (-f)⟫ + 4 * ⟪-f, deriv A 0 e⟫ + ⟪e, deriv (deriv A) 0 e⟫;
    0 ≤ q ∧ q = 0 := by
  let e := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
  let f := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
  let P := InnerProductSpace.rankOne ℝ e e
  let Q := InnerProductSpace.rankOne ℝ f f
  let G := InnerProductSpace.rankOne ℝ e f + InnerProductSpace.rankOne ℝ f e
  let A := fun t : ℝ ↦ t ^ 2 • P + t • G + Q
  have hA : ContDiffAt ℝ 2 A 0 := by dsimp [A]; fun_prop
  have hs : ∀ᶠ t in nhds (0 : ℝ), ∀ a b, ⟪A t a, b⟫ = ⟪a, A t b⟫ := by
    apply Filter.Eventually.of_forall
    intro t a b
    simp only [A, P, Q, G, add_apply, smul_apply, InnerProductSpace.rankOne_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm a e, real_inner_comm a f]
    ring
  have hp : ∀ᶠ t in nhds (0 : ℝ), ∀ w, 0 ≤ ⟪w, A t w⟫ := by
    apply Filter.Eventually.of_forall
    intro t w
    simp only [A, P, Q, G, add_apply, smul_apply, InnerProductSpace.rankOne_apply,
      inner_add_right, real_inner_smul_right, real_inner_comm w e, real_inner_comm w f]
    nlinarith only [sq_nonneg (t * ⟪w, e⟫ + ⟪w, f⟫)]
  have hk : A 0 e = 0 := by simp [A, Q, e, f, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left]
  have hd : deriv A = fun t ↦ (2 * t) • P + G := by
    funext t
    simpa [A] using
      (((((hasDerivAt_id t).pow 2).smul_const P).add ((hasDerivAt_id t).smul_const G)).add_const Q).deriv
  have hdd : deriv (deriv A) 0 = (2 : ℝ) • P := by
    rw [hd]
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id (0 : ℝ)).const_mul 2).smul_const P).add_const G).deriv
  constructor
  · exact PositiveOperatorKernelCurvature.second_order_form_nonneg hA hs hp e (-f) hk
  · change 2 * ⟪-f, A 0 (-f)⟫ + 4 * ⟪-f, deriv A 0 e⟫ + ⟪e, deriv (deriv A) 0 e⟫ = 0
    rw [hdd, hd]
    norm_num [A, P, Q, G, e, f, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left]

-- The local-minimum criterion permits a flat quartic minimum.
example : 0 ≤ deriv (deriv (fun t : ℝ ↦ t ^ 4)) 0 := by
  apply second_derivative_nonneg_of_isLocalMin
  · apply Filter.Eventually.of_forall
    intro t
    change (0 : ℝ) ^ 4 ≤ t ^ 4
    norm_num only [zero_pow]
    positivity
  · fun_prop

-- Constant-vector multiplication preserves curvature; the linear term has none.
example (v : EuclideanSpace ℝ (Fin 2)) :
    deriv (deriv (fun t : ℝ ↦ t ^ 2 • v - t • v)) 1 = (2 : ℝ) • v := by
  have h2 : deriv (fun t : ℝ ↦ t ^ 2) = fun t ↦ 2 * t := by
    funext t
    simp
  have h1 : deriv (fun t : ℝ ↦ t • v) = fun _ ↦ v := by
    funext t
    simpa using ((hasDerivAt_id t).smul_const v).deriv
  rw [deriv_deriv_smul_const_sub (by fun_prop) (by fun_prop) v, h2, h1]
  simp only [deriv_const, sub_zero]
  congr 1
  simp

-- The half-weight identity retains the inverse-weight image cost.
example (a b c d : EuclideanSpace ℝ (Fin 2)) :
    (1 / 2 : ℝ) * (‖c + b‖ ^ 2 + 2 * ⟪d, a⟫ - ‖a‖ ^ 2) +
        (1 / 2 : ℝ) * (‖c‖ ^ 2 + ‖d‖ ^ 2) =
      ‖c + (1 / 2 : ℝ) • b‖ ^ 2 + (1 / 2 : ℝ) * ‖d + a‖ ^ 2 +
        (1 / 4 : ℝ) * ‖b‖ ^ 2 - ‖a‖ ^ 2 := by
  have h := OrthogonalProjectionWeightedDiffusion.weighted_completed_squares
    (1 / 2) (by norm_num) c d a b
  norm_num at h ⊢
  exact h

-- With a transverse gradient chosen at the square's center, the cost is attained.
example (a : EuclideanSpace ℝ (Fin 2)) :
    (1 / 2 : ℝ) * (2 * ⟪-a, a⟫ - ‖a‖ ^ 2) + (1 / 2 : ℝ) * ‖-a‖ ^ 2 = -‖a‖ ^ 2 := by
  simp only [inner_neg_left, real_inner_self_eq_norm_sq, norm_neg]
  ring

-- A nonzero tangent swaps the two sectors; the completed square must
-- retain the complementary-gradient cross term for arbitrary v and w.
example (v w : EuclideanSpace ℝ (Fin 2)) :
    let e := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
    let f := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
    let P := InnerProductSpace.rankOne ℝ e e
    let G := InnerProductSpace.rankOne ℝ f e + InnerProductSpace.rankOne ℝ e f;
    -2 * ‖P v‖ ^ 2 - 4 * ⟪v, G w⟫ - 2 * ‖G ((1 - P) w)‖ ^ 2 =
      -4 * ⟪(1 - P) v, G (P w)⟫ - 2 * ‖P v + G ((1 - P) w)‖ ^ 2 := by
  let e := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
  let f := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
  let P := InnerProductSpace.rankOne ℝ e e
  let G := InnerProductSpace.rankOne ℝ f e + InnerProductSpace.rankOne ℝ e f
  have h00 : ⟪e, e⟫ = 1 := by simp [e]
  have h01 : ⟪e, f⟫ = 0 := by simp [e, f, EuclideanSpace.inner_single_left]
  have h10 : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact h01
  have hp : P * P = P := InnerProductSpace.isIdempotentElem_rankOne_self
    ((EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 0)
  have hs : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫ := by
    intro a b
    simp only [P, InnerProductSpace.rankOne_apply, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm a e]
    ring
  have ht : G * P + P * G = G := by
    apply ContinuousLinearMap.ext
    intro a
    simp only [P, G, add_apply, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      inner_add_right, real_inner_smul_right, h00, h01, h10, mul_one, mul_zero,
      zero_smul, add_zero, zero_add]
  simpa only [mul_one] using OrthogonalProjectionParabolic.gradient_completed_square P G hp hs ht 1 v w

-- A rank-one projection leaves a genuinely transverse cross term unpaid.
example :
    let e : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
    let z : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
    ¬ ∃ A B : ℝ, ∀ v : EuclideanSpace ℝ (Fin 2),
      -4 * ⟪v, z⟫ ≤ A * ‖InnerProductSpace.rankOne ℝ e e v‖ ^ 2 + B := by
  dsimp only
  apply KernelCrossTerm.not_exists_projectedSquare_bound _ ((EuclideanSpace.basisFun (Fin 2) ℝ) 1)
  · simp [InnerProductSpace.rankOne_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  · simp

-- The parabolic defect has opposite nonzero diagonal blocks.
example :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let W : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, -2]
    let K : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 2]
    P * W * P = P * K * P ∧
      (1 - P) * W * (1 - P) = -(1 - P) * K * (1 - P) ∧ W * P + P * W ≠ W := by
  dsimp only
  have hp : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, 0] = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two]
  have hw : (!![2, 0; 0, -2] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, 0] +
      !![1, 0; 0, 0] * !![2, 0; 0, -2] = !![2, 0; 0, -2] + !![2, 0; 0, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two, Matrix.add_apply]
  refine ⟨idempotent_defect_image_block _ _ _ hp hw,
    idempotent_defect_complement_block _ _ _ hp hw, ?_⟩
  intro he
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ ↦ A 0 0) he
  norm_num [Matrix.mul_fin_two, Matrix.add_apply] at h00

-- The root -2 is simple even when the other two roots 1±x coincide.
example : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (-2 : ℝ)) 0 := by
  apply contDiffAt_of_simple_implicit_root
    (f := fun p : ℝ × ℝ ↦ ((p.2 - 1) ^ 2 - p.1 ^ 2) * (p.2 + 2)) (c := 9)
  · fun_prop
  · simp
  · fun_prop
  · exact Filter.Eventually.of_forall (fun _ ↦ by norm_num)
  · convert! (((hasDerivAt_id (-2 : ℝ)).sub_const 1).pow 2).mul
      ((hasDerivAt_id (-2 : ℝ)).add_const 2) using 1 <;> norm_num
    rfl
  · norm_num

-- The vector-gradient and mixed terms contribute: <t,t·t> = t³ has second derivative 6 at 1.
example : HasDerivAt (deriv (fun t : ℝ ↦
    OperatorQuadraticForm.value (t • ContinuousLinearMap.id ℝ ℝ) t)) 6 1 := by
  let P : ℝ → ℝ →L[ℝ] ℝ := fun t ↦ t • ContinuousLinearMap.id ℝ ℝ
  have hP : ContDiffAt ℝ 2 P 1 := by dsimp [P]; fun_prop
  have hDP : deriv P = fun _ ↦ ContinuousLinearMap.id ℝ ℝ := by
    funext t
    convert! ((hasDerivAt_id t).smul_const (ContinuousLinearMap.id ℝ ℝ)).deriv using 1
    simp only [one_smul]
  have hs : ∀ᶠ t in nhds (1 : ℝ), ∀ a b, inner ℝ (P t a) b = inner ℝ a (P t b) := by
    apply Filter.Eventually.of_forall
    intro t a b
    simp [P, mul_comm, mul_left_comm]
  have h := OperatorQuadraticForm.hasDerivAt_deriv_value hP
    (contDiffAt_id : ContDiffAt ℝ 2 (fun t : ℝ ↦ t) 1) hs
  convert! h using 1
  norm_num [hDP, P]

-- A Lipschitz path with a corner at zero: the differential equation is only
-- almost everywhere, and the derivative forcing need not be continuous.
example (a b : ℝ) (hab : a ≤ b) :
    |b| ≤ |a| + ∫ t in a..b, ‖deriv (fun τ : ℝ ↦ ‖τ‖) t‖ := by
  have hu : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ ‖t‖) a b :=
    absolutelyContinuousOnInterval_norm
      (contDiff_id.contDiffOn.absolutelyContinuousOnInterval :
        AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t) a b)
  have h := norm_le_initial_add_integral_of_ae_dissipative
    (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) hab hu hu.intervalIntegrable_deriv
    (by
      filter_upwards [hu.ae_differentiableAt] with t ht hmem
      simpa using (ht hmem).hasDerivAt)
    (by simp)
  simpa only [Real.norm_eq_abs, abs_abs] using h

-- A forced solution crosses zero inside the interval.
example : ∀ t ∈ Icc (0 : ℝ) 1, |t - 1 / 2| ≤ 1 / 2 + t := by
  have h := norm_le_initial_add_integral_of_dissipative
    (a := 0) (b := 1) (u := fun t : ℝ ↦ t - 1 / 2) (f := fun _ ↦ (1 : ℝ))
    (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) (continuous_id.sub continuous_const).continuousOn
    continuous_const
    (fun t _ ↦ by simpa using ((hasDerivAt_id t).sub_const (1 / 2)).hasDerivWithinAt)
    (by simp)
  simpa using h

-- Variable Gronwall permits a negative growth coefficient without a sign
-- hypothesis on the compared function.
example {x x' : ℝ → ℝ} (hx : ContinuousOn x (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt x (x' t) (Icc (0 : ℝ) 1) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, x' t ≤ -x t) :
    ∀ t ∈ Icc (0 : ℝ) 1, x t ≤ x 0 * Real.exp (-t) := by
  have h := le_initial_mul_exp_integral_of_deriv_le_mul
    (g := fun _ ↦ -1) hx continuousOn_const hd (by simpa using hb)
  simpa using h

-- The scale estimate is not restricted to the source's quarter-power decay.
example {X C L W H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ C * (L + W * (-Real.log ε) + ε ^ (2 : ℝ) * H)) :
    X ≤ C * (L + W * (Real.log (Real.exp 1 + H) / 2) + 1) :=
  le_logarithmic_of_le_scale_bound hC hH (by norm_num) h

#print axioms Mettapedia.Analysis.ODE.norm_le_initial_add_integral_of_dissipative
#print axioms Mettapedia.Analysis.ODE.norm_le_initial_add_integral_of_ae_dissipative
#print axioms Mettapedia.Analysis.ODE.norm_div_le_initial_add_integral
#print axioms Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_integral_on
#print axioms Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_of_source_le
#print axioms Mettapedia.Analysis.ODE.le_initial_mul_exp_integral_of_deriv_le_mul
#print axioms Mettapedia.Analysis.exists_scale_rpow_mul_le_one
#print axioms Mettapedia.Analysis.le_logarithmic_of_le_scale_bound
#print axioms Mettapedia.Analysis.le_four_mul_logarithmic_of_le_quarter_scale_bound
