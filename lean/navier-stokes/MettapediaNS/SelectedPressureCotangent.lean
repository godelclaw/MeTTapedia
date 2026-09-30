import MettapediaNS.MemoryAgePressure
import MettapediaNS.WholeSpacePressureProduction
import Euler.OrdinaryRegularizedEquation

/-!
# Diffusion payment for the selected canonical pressure cotangent

The negative Helmholtz projection of the actual receiver divergence gives
`V`. Its local velocity cotangent is `-2 (∇u)ᵀ V`. Its square divided by
`1 + |∇u|²` is integrable and paid by the same two native diffusion legs
as the receiver, without a bound on the future velocity gradient.

The pressure variation is constructed from the actual canonical pressure
operator. Incompressibility makes the Lie bracket of two compatible
velocity fields solenoidal. This identifies the divergence-form pressure
work with the local cotangent work, retaining the complete projection.

Interpreting the Lipschitz receiver's divergence-form work as the selected
Hessian first variation still requires weak integration by parts. The
payment is spatial. It neither bounds its work on all evolving parents
nor supplies an arbitrary-history allowance for the joint reserve.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SelectedPressureCotangent

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical WholeSpaceBetchov WholeSpaceOrderEnergy WholeSpaceViscousEnergy
  WholeSpacePressureProduction WholeSpacePressureDiffusion WholeSpacePressureAugmentation
  WholeSpacePressureReceiver MiddleEigenvalueAlgebra MemoryAgePressure

open scoped Topology NNReal

/-- The representative modulo gradients is evaluated on the full pressure
receiver, not on a selected local Poisson source. -/
def localCotangent (B : GradMatrix) (V : Space) : Space :=
  ∑ j : Fin 3, (-2 * ∑ i : Fin 3, B i j * V i) • axis j

theorem localCotangent_coordinate (B : GradMatrix) (V : Space) (j : Fin 3) :
    localCotangent B V j = -2 * ∑ i : Fin 3, B i j * V i := by
  simp only [localCotangent, axis, Fin.sum_univ_three]
  fin_cases j <;> simp

private theorem matrix_square_nonneg (B : GradMatrix) : 0 ≤ normSq B := by
  unfold normSq
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The finite-dimensional Cauchy estimate keeps all orientations. -/
theorem localCotangent_square_le (B : GradMatrix) (V : Space) :
    ‖localCotangent B V‖ ^ 2 ≤ 4 * normSq B * ‖V‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [localCotangent_coordinate]
  calc
    _ = 4 * ∑ j : Fin 3, (∑ i : Fin 3, B i j * V i) ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
    _ ≤ 4 * ∑ j : Fin 3,
        (∑ i : Fin 3, (B i j) ^ 2) * ∑ i : Fin 3, (V i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun j _ ↦
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ B i j) (fun i ↦ V i)
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_comm]
      unfold normSq
      ring

/-- A positive denominator avoids a singularity at zero strain. -/
def cotangentCost (B : GradMatrix) (V : Space) : ℝ :=
  ‖localCotangent B V‖ ^ 2 / (1 + normSq B)

theorem cotangentCost_nonneg (B : GradMatrix) (V : Space) :
    0 ≤ cotangentCost B V := by
  unfold cotangentCost
  positivity [matrix_square_nonneg B]

theorem cotangentCost_le (B : GradMatrix) (V : Space) :
    cotangentCost B V ≤ 4 * ‖V‖ ^ 2 := by
  unfold cotangentCost
  apply (div_le_iff₀ (show 0 < 1 + normSq B by
    linarith [matrix_square_nonneg B])).2
  have hc := localCotangent_square_le B V
  nlinarith only [hc, sq_nonneg ‖V‖]

/-- The actual spatial velocity gradient and an ordinary `L²` receiver. -/
def cotangentDensity (u : SmoothL2Field Space) (V : L2) (x : Space) : ℝ :=
  cotangentCost (gradMatrix u x) (V x)

set_option backward.isDefEq.respectTransparency.types false in
theorem cotangentDensity_measurable (u : SmoothL2Field Space) (V : L2) :
    AEStronglyMeasurable (cotangentDensity u V) := by
  have hB (i j : Fin 3) : Continuous (fun x ↦ gradMatrix u x i j) :=
    (EuclideanSpace.proj i).continuous.comp (u.directionalField (axis j)).smooth.continuous
  have hV (i : Fin 3) : AEStronglyMeasurable (fun x ↦ V x i) :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
      (Lp.memLp V).aestronglyMeasurable
  have hr : Continuous (fun x ↦ normSq (gradMatrix u x)) := by
    unfold normSq
    exact continuous_finsetSum _ fun i _ ↦
      continuous_finsetSum _ fun j _ ↦ (hB i j).pow 2
  have hc : AEStronglyMeasurable (fun x ↦ localCotangent (gradMatrix u x) (V x)) := by
    unfold localCotangent
    have hs (j : Fin 3) :
        AEStronglyMeasurable (fun x ↦ ∑ i : Fin 3, gradMatrix u x i j * V x i) := by
      simpa only [Finset.sum_apply, Pi.mul_apply] using! Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ ↦ (hB i j).aestronglyMeasurable.mul (hV i))
    simpa only [Finset.sum_apply, Pi.mul_apply] using! Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ (aestronglyMeasurable_const.mul (hs j)).smul_const (axis j))
  have hd : Continuous (fun x ↦ (1 + normSq (gradMatrix u x))⁻¹) :=
    (continuous_const.add hr).inv₀ fun x ↦ by
      change 1 + normSq (gradMatrix u x) ≠ 0
      linarith [matrix_square_nonneg (gradMatrix u x)]
  simpa only [cotangentDensity, cotangentCost, div_eq_mul_inv,
    Pi.mul_apply, Pi.pow_apply] using!
    (hc.norm.pow 2).mul hd.aestronglyMeasurable

/-- Integrability is established from the receiver's `L²` construction. -/
theorem cotangentDensity_integrable (u : SmoothL2Field Space) (V : L2) :
    Integrable (cotangentDensity u V) := by
  have hv := (memLp_two_iff_integrable_sq_norm
    (Lp.memLp V).aestronglyMeasurable).1 (Lp.memLp V)
  apply (hv.const_mul 4).mono_nonneg (cotangentDensity_measurable u V)
  · exact Filter.Eventually.of_forall fun x ↦ cotangentCost_nonneg _ _
  · exact Filter.Eventually.of_forall fun x ↦ cotangentCost_le _ _

theorem integral_cotangentDensity_le (u : SmoothL2Field Space) (V : L2) :
    (∫ x, cotangentDensity u V x) ≤ 4 * ‖V‖ ^ 2 := by
  rw [EulerLpBochnerRealization.norm_sq_eq_integral, ← integral_const_mul]
  apply integral_mono (cotangentDensity_integrable u V)
    (((memLp_two_iff_integrable_sq_norm
      (Lp.memLp V).aestronglyMeasurable).1 (Lp.memLp V)).const_mul 4)
  intro x
  exact cotangentCost_le _ _

/-- Literal consumer of the complete canonical receiver, including the
selector's spatial derivative. No future supremum enters the constant. -/
theorem actual_cotangent_native_paid (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 < ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k)) :
    ν * (∫ x, cotangentDensity u (receiverPressureGradient u b z
      (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ)) x) ≤
        192 * receiverNativeCost u ν b h z := by
  have hi := mul_le_mul_of_nonneg_left
    (integral_cotangentDensity_le u (receiverPressureGradient u b z
      (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ))) hν.le
  have hp := actual_receiver_native_paid u ν b hν hb h z hh hz hP hJ
  nlinarith only [hi, hp]

/-- The polarized advection source of the true canonical pressure. -/
def polarizedAdvection (u v : SmoothL2Field Space) : SmoothL2Field Space :=
  addField (advectionField u v) (advectionField v u)

/-- The canonical pressure-gradient variation, including both parents. -/
def pressureVariation (u v : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldSub (solenoidalField (polarizedAdvection u v)) (polarizedAdvection u v)

theorem pressureVariation_toLp (u v : SmoothL2Field Space) :
    (pressureVariation u v).toLp =
      -gradientSpace.starProjection (polarizedAdvection u v).toLp := by
  rw [pressureVariation, toLp_fieldSub, solenoidalField_toLp]
  have hp := Submodule.starProjection_orthogonal gradientSpace
  have he := congrArg (fun L : L2 →L[ℝ] L2 ↦ L (polarizedAdvection u v).toLp) hp
  change solenoidalSpace.starProjection (polarizedAdvection u v).toLp =
    (polarizedAdvection u v).toLp -
      gradientSpace.starProjection (polarizedAdvection u v).toLp at he
  rw [show solenoidalProjection = solenoidalSpace.starProjection from rfl, he]
  abel

/-- Exact finite increment of the constructed pressure gradient, not a freely
supplied pressure tangent. -/
theorem pressure_increment (u v : SmoothL2Field Space) (c : ℝ) :
    (pressureField (addField u (scaleField c v))).toLp =
      (pressureField u).toLp + c • (pressureVariation u v).toLp +
        c ^ 2 • (pressureField v).toLp := by
  simp only [pressureField_toLp, pressureVariation, toLp_fieldSub,
    solenoidalField_toLp, polarizedAdvection, advection_add_left, advection_add_right,
    advection_smul_left, advection_smul_right, toLp_addField, scaleField_toLp,
    map_add, map_smul]
  module

/-- First variation in an actual smooth velocity direction. Applying it
to a time path still requires that path's differential regularity. -/
theorem pressureVariation_hasDerivAt (u v : SmoothL2Field Space) :
    HasDerivAt (fun c : ℝ ↦ (pressureField (addField u (scaleField c v))).toLp)
      (pressureVariation u v).toLp 0 := by
  have h₁ := (hasDerivAt_id (0 : ℝ)).smul_const (pressureVariation u v).toLp
  have h₂ := ((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (pressureField v).toLp
  have ht := ((hasDerivAt_const (0 : ℝ) (pressureField u).toLp).add h₁).add h₂
  simp_rw [pressure_increment]
  simpa only [Pi.add_apply, Pi.pow_apply, id_eq, one_smul, zero_smul,
    Nat.reduceSub, pow_one, mul_zero, zero_mul, add_zero, zero_add] using! ht

/-- Compatible velocity variations have a solenoidal Lie bracket. -/
def velocityBracket (u v : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldSub (advectionField u v) (advectionField v u)

private theorem mixed_gradient (u v : SmoothL2Field Space) (i j : Fin 3) (x : Space) :
    gradMatrix (advectionField u v) x i j =
      (∑ k : Fin 3, u.field x k * hessTensor v x k j i) +
        ∑ k : Fin 3, gradMatrix u x k j * gradMatrix v x i k := by
  change ((advectionField u v).directionalField (axis j)).field x i = _
  rw [advection_directional, addField_field, advectionField_field_sum,
    advectionField_field_sum]
  simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, gradMatrix, hessTensor]

private theorem bracket_gradient (u v : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (velocityBracket u v) x i j =
      gradMatrix (advectionField u v) x i j - gradMatrix (advectionField v u) x i j := by
  have he : (velocityBracket u v).field =
      (advectionField u v).field - (advectionField v u).field :=
    funext (fieldSub_field _ _)
  change (fderiv ℝ (velocityBracket u v).field x (axis j)) i = _
  rw [he, fderiv_sub ((advectionField u v).smooth.differentiable (by simp) x)
    ((advectionField v u).smooth.differentiable (by simp) x)]
  rfl

theorem velocityBracket_divergence (u v : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hv : v.toLp ∈ solenoidalSpace) (x : Space) :
    divergence (velocityBracket u v).field x = 0 := by
  have h₀u := hessTensor_trace u hu x 0
  have h₁u := hessTensor_trace u hu x 1
  have h₂u := hessTensor_trace u hu x 2
  have h₀v := hessTensor_trace v hv x 0
  have h₁v := hessTensor_trace v hv x 1
  have h₂v := hessTensor_trace v hv x 2
  rw [divergence_eq_coordinate_sum]
  change (∑ i : Fin 3, gradMatrix (velocityBracket u v) x i i) = 0
  simp only [bracket_gradient, mixed_gradient, hessTensor_symm v x,
    hessTensor_symm u x, Fin.sum_univ_three]
  simp only [hessTensor_symm v x, hessTensor_symm u x] at h₀u h₁u h₂u h₀v h₁v h₂v
  linear_combination u.field x 0 * h₀v + u.field x 1 * h₁v + u.field x 2 * h₂v -
    v.field x 0 * h₀u - v.field x 1 * h₁u - v.field x 2 * h₂u

theorem velocityBracket_solenoidal (u v : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hv : v.toLp ∈ solenoidalSpace) :
    (velocityBracket u v).toLp ∈ solenoidalSpace := by
  simpa only [SmoothL2Field.toLp] using smooth_mem_solenoidal
    (velocityBracket u v).field (velocityBracket u v).smooth
    (velocityBracket u v).memLp (velocityBracket_divergence u v hu hv)

/-- Incompressibility removes the bracket, retaining all of the pressure
projection. It does not replace that projection by a weighted local source. -/
theorem pressure_variation_work (u v : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hv : v.toLp ∈ solenoidalSpace) (D : L2) :
    -⟪D, (pressureVariation u v).toLp⟫_ℝ =
      -2 * ⟪-gradientSpace.starProjection D, (advectionField v u).toLp⟫_ℝ := by
  have hb := velocityBracket_solenoidal u v hu hv
  have hg : -gradientSpace.starProjection D ∈ gradientSpace :=
    gradientSpace.neg_mem (gradientSpace.starProjection_apply_mem _)
  have he := hb _ hg
  change ⟪-gradientSpace.starProjection D, (velocityBracket u v).toLp⟫_ℝ = 0 at he
  rw [velocityBracket, toLp_fieldSub, inner_sub_right] at he
  rw [pressureVariation_toLp, inner_neg_right, neg_neg,
    ← Submodule.inner_starProjection_left_eq_right]
  simp only [polarizedAdvection, toLp_addField, inner_add_right, inner_neg_left] at *
  linarith only [he]

theorem localCotangent_work (u v : SmoothL2Field Space) (V x : Space) :
    ⟪localCotangent (gradMatrix u x) V, v.field x⟫_ℝ =
      -2 * ⟪V, (advectionField v u).field x⟫_ℝ := by
  rw [advectionField_field_sum, inner_sum]
  simp only [inner_eq_sum, localCotangent_coordinate, real_inner_smul_right,
    gradMatrix, Fin.sum_univ_three]
  ring

theorem localCotangent_work_integrable (u v : SmoothL2Field Space) (V : L2) :
    Integrable (fun x ↦ ⟪localCotangent (gradMatrix u x) (V x), v.field x⟫_ℝ) := by
  apply ((MeasureTheory.L2.integrable_inner V (advectionField v u).toLp).const_mul
    (-2 : ℝ)).congr
  filter_upwards [(advectionField v u).toLp_ae] with x hx
  simp only [hx, localCotangent_work]

theorem integral_localCotangent_work (u v : SmoothL2Field Space) (V : L2) :
    (∫ x, ⟪localCotangent (gradMatrix u x) (V x), v.field x⟫_ℝ) =
      -2 * ⟪V, (advectionField v u).toLp⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(advectionField v u).toLp_ae] with x hx
  simp only [hx, localCotangent_work]

/-- Actual soft-excess receiver paired against the actual canonical
pressure variation. The divergence-form identity needs no smooth potential. -/
theorem actual_pressure_cotangent_work (u v : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hv : v.toLp ∈ solenoidalSpace)
    (ν b : ℝ) (hν : 0 < ν) (hb : 0 < b) (h z : Space → ℝ)
    (hh : ∀ x, 0 ≤ h x) {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k)) :
    -⟪(receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ).toLp
        (receiverDivergence u b z), (pressureVariation u v).toLp⟫_ℝ =
      ∫ x, ⟪localCotangent (gradMatrix u x)
        (receiverPressureGradient u b z
          (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ) x), v.field x⟫_ℝ := by
  rw [integral_localCotangent_work]
  exact pressure_variation_work u v hu hv _

/-- The actual canonical pressure operator preserves the time product
rule, with its derivative reconstructed from both evolving parents. -/
theorem timeDeriv_pressure {T : ℝ} {hT : 0 ≤ T}
    {A B : WholeSpaceTimeSmooth.FieldPath T} (h : WholeSpaceTimeSmooth.TimeDeriv hT A B) :
    WholeSpaceTimeSmooth.TimeDeriv hT (fun t ↦ pressureField (A t))
      (fun t ↦ pressureVariation (A t) (B t)) := by
  have ha := h.advection h
  have he : (fun t ↦ addField (advectionField (B t) (A t)) (advectionField (A t) (B t))) =
      fun t ↦ polarizedAdvection (A t) (B t) := by
    funext t
    apply field_ext
    funext x
    simp only [polarizedAdvection, addField_field]
    exact add_comm _ _
  rw [he] at ha
  exact ha.solenoidal.add (ha.map (-(ContinuousLinearMap.id ℝ Space)))

namespace NSEvolution

open Set WholeSpaceViscousFlow WholeSpaceTimeSmooth

variable {ν T : ℝ} {hT : 0 ≤ T}

set_option backward.isDefEq.respectTransparency.types false in
/-- The pressure-gradient time derivative along the complete actual NS
evolution, including viscosity, is the constructed pressure variation. -/
theorem pressureGradient_hasDerivAt (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ (pressureField (U.velocity (projIcc 0 T hT r))).toLp)
      (pressureVariation (U.velocity ⟨t, ht.1.le, ht.2.le⟩)
        (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩))).toLp t := by
  have hp := timeDeriv_pressure (U.timeDeriv hpos)
  simpa only [projected_rhs_eq] using! hp.toLp t ht

set_option backward.isDefEq.respectTransparency.types false in
/-- Every canonical pressure-Hessian entry has its literal time derivative,
with no pressure tangent or history supplied independently. -/
theorem pressureHessian_hasDerivAt (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) (i j : Fin 3) :
    HasDerivAt (fun r ↦ gradMatrix (pressureField (U.velocity (projIcc 0 T hT r))) x i j)
      (gradMatrix (pressureVariation (U.velocity ⟨t, ht.1.le, ht.2.le⟩)
        (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩))) x i j) t := by
  have hp := timeDeriv_pressure (U.timeDeriv hpos)
  have hd := (hp.directional j).deriv t ht x
  have hc := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
  simpa only [gradMatrix, projected_rhs_eq] using! hc

/-- Divergence-form selected pressure work on the actual physical time
derivative. Both solenoidality obligations follow from the NS evolution. -/
theorem pressure_cotangent_work (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (b : ℝ) (hν : 0 < ν) (hb : 0 < b)
    (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x) {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare (U.velocity ⟨t, ht.1.le, ht.2.le⟩) x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k)) :
    let u := U.velocity ⟨t, ht.1.le, ht.2.le⟩;
    -⟪(receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ).toLp
        (receiverDivergence u b z),
      deriv (fun r ↦ (pressureField (U.velocity (projIcc 0 T hT r))).toLp) t⟫_ℝ =
      ∫ x, ⟪localCotangent (gradMatrix u x)
        (receiverPressureGradient u b z
          (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ) x),
          (projectedNavierStokesRhs ν u).field x⟫_ℝ := by
  dsimp only
  rw [(pressureGradient_hasDerivAt U hpos t ht).deriv]
  exact actual_pressure_cotangent_work _ _ (U.solenoidal _)
    (projectedNavierStokesRhs_mem_solenoidal ν _ (U.solenoidal _))
    ν b hν hb h z hh hz hP hJ

end NSEvolution

end Mettapedia.FluidDynamics.NavierStokes.SelectedPressureCotangent
