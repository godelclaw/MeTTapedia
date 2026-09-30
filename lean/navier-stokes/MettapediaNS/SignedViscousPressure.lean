import MettapediaNS.JointReceiverDiffusion

/-!
# Signed viscous pressure source and a finite-initial-resource correction

The pressure of the actual source `G = (∇u)(∇u)ᵀ` is constructed from all
three derivative parents. Its unweighted gradient costs at most the local
strain-derivative density, with constant one. The scalar flux estimates
retain the selector derivative and an additional unselected diffusion leg.

The companion lab identifies the bilinear Hessian flux and the completed
matrix observable analytically. The correction `F + 8(Φ - Φ∞)` pays the
explicit canonical viscous source while retaining one quarter of its
diffusion. Its full signed nonlinear and compatible-history bound is open.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SignedViscousPressure

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  WholeSpaceBetchov WholeSpacePressureDiffusion WholeSpacePressureProduction
  WholeSpaceOrderEnergy MiddleEigenvalueAlgebra

open scoped Topology NNReal

/-- Divergence of `G` for a solenoidal velocity: every derivative parent
is retained. The literal tensor rows are constructed below. -/
def sourceAdvection (u : SmoothL2Field Space) : SmoothL2Field Space :=
  sumField Finset.univ (fun k : Fin 3 ↦
    advectionField (u.directionalField (axis k)) (u.directionalField (axis k)))

/-- Actual canonical pressure gradients of the three derivative parents. -/
def sourcePressure (u : SmoothL2Field Space) : SmoothL2Field Space :=
  sumField Finset.univ (fun k : Fin 3 ↦ pressureField (u.directionalField (axis k)))

/-- Row `i` of the actual positive source `(∇u)(∇u)ᵀ`. -/
def sourceRow (u : SmoothL2Field Space) (i : Fin 3) : SmoothL2Field Space :=
  sumField Finset.univ (fun k : Fin 3 ↦
    coordinateProduct i (u.directionalField (axis k)) (u.directionalField (axis k)))

theorem sourceRow_coordinate (u : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    (sourceRow u i).field x j =
      ∑ k : Fin 3, gradMatrix u x i k * gradMatrix u x j k := by
  simp only [sourceRow, sumField_field, coordinateProduct_field, WithLp.ofLp_sum,
    Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, gradMatrix]

private theorem coordinateProduct_directional (i j : Fin 3) (A B : SmoothL2Field Space) :
    (coordinateProduct i A B).directionalField (axis j) =
      addField (coordinateProduct i A (B.directionalField (axis j)))
        (coordinateProduct i (A.directionalField (axis j)) B) := by
  have he : (mapField (EuclideanSpace.proj i) A).directionalField (axis j) =
      mapField (EuclideanSpace.proj i) (A.directionalField (axis j)) :=
    wordField_map _ _ (fun _ : Fin 1 ↦ j)
  simp only [coordinateProduct, scalarProduct_directional, he]
  apply field_ext
  funext x
  simp only [addField_field]
  exact add_comm _ _

private theorem sourceRow_directional_coordinate (u : SmoothL2Field Space)
    (x : Space) (i j l : Fin 3) :
    ((sourceRow u i).directionalField (axis j)).field x l =
      ∑ k : Fin 3,
        (gradMatrix u x i k * gradMatrix (u.directionalField (axis k)) x l j +
          gradMatrix (u.directionalField (axis k)) x i j * gradMatrix u x l k) := by
  have he : (sourceRow u i).directionalField (axis j) =
      sumField Finset.univ (fun k : Fin 3 ↦
        (coordinateProduct i (u.directionalField (axis k))
          (u.directionalField (axis k))).directionalField (axis j)) :=
    wordField_sum Finset.univ _ (fun _ : Fin 1 ↦ j)
  simp only [he, sumField_field, coordinateProduct_directional, addField_field,
    coordinateProduct_field, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_add,
    Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, gradMatrix]

theorem sourceAdvection_coordinate (u : SmoothL2Field Space) (x : Space) (i : Fin 3) :
    (sourceAdvection u).field x i =
      ∑ k : Fin 3, ∑ j : Fin 3,
        gradMatrix u x j k * gradMatrix (u.directionalField (axis k)) x i j := by
  simp only [sourceAdvection, sumField_field, advectionField, coordinateProduct_field,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    gradMatrix]

/-- Incompressibility cancels the differentiated second factor in `div G`.
This is an identity of the actual smooth source, not a closure model. -/
theorem sourceRow_divergence (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace)
    (x : Space) (i : Fin 3) :
    (traceField (sourceRow u i)).field x = (sourceAdvection u).field x i := by
  have hs (k : Fin 3) : (u.directionalField (axis k)).toLp ∈ solenoidalSpace := by
    rw [d_eq_word]
    exact word_solenoidal u hu _
  have hz (k : Fin 3) := gradMatrix_trace (u.directionalField (axis k)) (hs k) x
  rw [traceField_field, sourceAdvection_coordinate]
  simp only [gradMatrix, sourceRow_directional_coordinate, Fin.sum_univ_three]
  simp only [gradMatrix] at hz
  linear_combination (u.directionalField (axis 0)).field x i * hz 0 +
    (u.directionalField (axis 1)).field x i * hz 1 +
    (u.directionalField (axis 2)).field x i * hz 2

/-- Cauchy--Schwarz keeps the entire tensor and all spatial directions. -/
theorem sourceAdvection_square_le (u : SmoothL2Field Space) (x : Space) :
    ‖(sourceAdvection u).field x‖ ^ 2 ≤ normSq (gradMatrix u x) *
      ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [sourceAdvection_coordinate]
  have hc (i : Fin 3) := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p ↦ gradMatrix u x p.2 p.1)
    (fun p ↦ gradMatrix (u.directionalField (axis p.1)) x i p.2)
  simp only [Fintype.sum_prod_type] at hc
  calc
    _ ≤ ∑ i : Fin 3,
        (∑ k : Fin 3, ∑ j : Fin 3, (gradMatrix u x j k) ^ 2) *
          ∑ k : Fin 3, ∑ j : Fin 3,
            (gradMatrix (u.directionalField (axis k)) x i j) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ hc i
    _ = _ := by
      simp only [normSq, Fin.sum_univ_three]
      ring

theorem sourcePressure_toLp (u : SmoothL2Field Space) :
    (sourcePressure u).toLp =
      solenoidalProjection (sourceAdvection u).toLp - (sourceAdvection u).toLp := by
  simp only [sourcePressure, sourceAdvection, toLp_sumField, pressureField_toLp,
    Finset.sum_sub_distrib, map_sum]

/-- The ordinary unweighted orthogonal projection is used. No selected
or memory-weighted contraction is inferred. -/
theorem sourcePressure_projection (u : SmoothL2Field Space) :
    (sourcePressure u).toLp = -gradientSpace.starProjection (sourceAdvection u).toLp := by
  rw [sourcePressure_toLp]
  have he := congrArg (fun L : L2 →L[ℝ] L2 ↦ L (sourceAdvection u).toLp)
    (Submodule.starProjection_orthogonal gradientSpace)
  change solenoidalProjection (sourceAdvection u).toLp =
    (sourceAdvection u).toLp - gradientSpace.starProjection (sourceAdvection u).toLp at he
  rw [he]
  abel

theorem sourcePressure_mem_gradient (u : SmoothL2Field Space) :
    (sourcePressure u).toLp ∈ gradientSpace := by
  rw [sourcePressure_projection]
  exact gradientSpace.neg_mem (gradientSpace.starProjection_apply_mem _)

/-- The literal Poisson source, with incompressibility of every parent
derived from the full velocity. It is not an independently supplied matrix. -/
theorem sourcePressure_trace (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace)
    (x : Space) :
    (traceField (sourcePressure u)).field x =
      -(∑ k : Fin 3, trSq (gradMatrix (u.directionalField (axis k)) x)) := by
  have hs (k : Fin 3) : (u.directionalField (axis k)).toLp ∈ solenoidalSpace := by
    rw [d_eq_word]
    exact word_solenoidal u hu _
  have hd (j : Fin 3) : (sourcePressure u).directionalField (axis j) =
      sumField Finset.univ (fun k : Fin 3 ↦
        (pressureField (u.directionalField (axis k))).directionalField (axis j)) :=
    wordField_sum Finset.univ _ (fun _ : Fin 1 ↦ j)
  have hp (k : Fin 3) := congrArg (fun A : SmoothL2Field ℝ ↦ A.field x)
    (traceField_pressureField (u.directionalField (axis k)) (hs k))
  simp only [traceField_field, fieldNeg_field, sourceField_field] at hp
  simp only [traceField_field, gradMatrix, hd, sumField_field, WithLp.ofLp_sum,
    Finset.sum_apply]
  rw [Finset.sum_comm]
  simpa only [gradMatrix, Finset.sum_neg_distrib] using congrArg
    (fun v : Fin 3 → ℝ ↦ ∑ k : Fin 3, v k) (funext hp)

/-- Genuine finite spatial integral of the local derivative-parent cost. -/
theorem parent_cost_integrable (u : SmoothL2Field Space) :
    Integrable (fun x ↦ normSq (gradMatrix u x) *
      ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)) := by
  simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ
    (fun k _ ↦ normSq_product_integrable u (u.directionalField (axis k)))

/-- The full actual source pressure has a uniform spatial payment. -/
theorem sourcePressure_norm_sq_le (u : SmoothL2Field Space) :
    ‖(sourcePressure u).toLp‖ ^ 2 ≤
      ∫ x, normSq (gradMatrix u x) *
        ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x) := by
  have hn : ‖(sourcePressure u).toLp‖ ≤ ‖(sourceAdvection u).toLp‖ := by
    rw [sourcePressure_projection, norm_neg]
    exact gradientSpace.norm_starProjection_apply_le _
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
  have hi := field_inner_integrable (sourceAdvection u) (sourceAdvection u)
  simp only [real_inner_self_eq_norm_sq] at hi
  calc
    _ ≤ ‖(sourceAdvection u).toLp‖ ^ 2 := hsq
    _ = ∫ x, ‖(sourceAdvection u).field x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, field_inner]
      simp only [real_inner_self_eq_norm_sq]
    _ ≤ _ := integral_mono hi (parent_cost_integrable u) (sourceAdvection_square_le u)

/-- One eighth of the full unselected completed diffusion pays this
pressure source. Matrix identification of `D` remains an explicit input. -/
theorem source_pressure_paid (u : SmoothL2Field Space) {ν D : ℝ} (hν : 0 ≤ ν)
    (hD : 8 * ν * (∫ x, normSq (gradMatrix u x) *
      ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)) ≤ D) :
    ν * ‖(sourcePressure u).toLp‖ ^ 2 ≤ D / 8 := by
  have hm := mul_le_mul_of_nonneg_left (sourcePressure_norm_sq_le u) hν
  linarith only [hm, hD]

/-- The Hessian localization flux uses `P+sI`, retaining the Poisson sign. -/
def pressureFluxMatrix (P : GradMatrix) (s : ℝ) : GradMatrix :=
  fun i j ↦ P i j + if i = j then s else 0

theorem pressureFluxMatrix_square (P : GradMatrix) (s : ℝ)
    (htrace : (∑ i : Fin 3, P i i) = -s) :
    normSq (pressureFluxMatrix P s) = normSq P + s ^ 2 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp [pressureFluxMatrix, normSq, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21]
  simp only [Fin.sum_univ_three] at htrace
  linear_combination 2 * s * htrace

/-- The literal canonical pressure supplies the trace condition, and its
flux matrix is paid by the proposed observable's explicit coercivity. -/
theorem actual_pressureFluxMatrix_paid (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (x : Space) (Φ : ℝ)
    (hΦ : normSq (gradMatrix (pressureField u) x) + (normSq (gradMatrix u x)) ^ 2 ≤ Φ) :
    normSq (pressureFluxMatrix (gradMatrix (pressureField u) x)
      ((sourceField u).field x)) ≤ Φ := by
  have ht := congrArg (fun A : SmoothL2Field ℝ ↦ A.field x) (traceField_pressureField u hu)
  simp only [traceField_field, fieldNeg_field] at ht
  rw [pressureFluxMatrix_square _ _ ht, sourceField_field]
  linarith only [trSq_sq_le_normSq_sq (gradMatrix u x), hΦ]

/-- Squaring the physical boundary flux and using the selection payment
gives this signed Young estimate, with its ordinary source cost retained. -/
theorem boundary_flux_paid (f J G : ℝ) (hJ : 0 ≤ J) (hG : 0 ≤ G)
    (hf : f ^ 2 ≤ 32 * J * G) : |f| ≤ J / 2 + 16 * G := by
  have hb : 0 ≤ J / 2 + 16 * G := by positivity
  have hs : f ^ 2 ≤ (J / 2 + 16 * G) ^ 2 := by
    nlinarith only [hf, sq_nonneg (J / 2 - 16 * G)]
  rw [← sq_abs] at hs
  exact (sq_le_sq₀ (abs_nonneg _) hb).mp hs

theorem selected_viscous_source_paid (S J D G L F : ℝ)
    (hG : G ≤ D / 8) (hlocal : |L| ≤ S / 2) (hflux : |F| ≤ J / 2 + 16 * G) :
    |L + F| ≤ S / 2 + J / 2 + 2 * D := by
  calc
    _ ≤ |L| + |F| := abs_add_le _ _
    _ ≤ S / 2 + (J / 2 + 16 * G) := add_le_add hlocal hflux
    _ ≤ _ := by linarith only [hG]

/-- With eight copies of the unselected initial reserve, both canonical
viscous terms cost at most three quarters of the complete diffusion. -/
theorem augmented_viscous_source_paid (S J D L F U : ℝ)
    (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hselected : |L + F| ≤ S / 2 + J / 2 + 2 * D) (hunselected : |U| ≤ D / 2) :
    |L + F + 8 * U| ≤ (3 / 4 : ℝ) * (S + J + 8 * D) := by
  have hsum := abs_add_le (L + F) (8 * U)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)] at hsum
  linarith only [hsum, hselected, hunselected, hS, hJ]

/-- The signed nonlinear production is preserved as an unpaid term. -/
theorem quarter_diffusion_survives (E N C S J D V : ℝ)
    (hbalance : E = N + V - C - (S + J + 8 * D))
    (hvisc : V ≤ (3 / 4 : ℝ) * (S + J + 8 * D)) :
    E + (S + J + 8 * D) / 4 ≤ N - C := by
  linarith only [hbalance, hvisc]

/-- The far-field constant is subtracted so this correction can have a
finite whole-space integral. The coefficient is fixed once, not per seam. -/
def augmentedExcess (X h b offset : ℝ) : ℝ :=
  ViscousMemorySoftExcess.excess X h b + 8 * (X - offset)

theorem augmentedExcess_nonneg (X h b offset : ℝ) (hX : 0 < X) (hoff : offset ≤ X) :
    0 ≤ augmentedExcess X h b offset := by
  have he := ViscousMemorySoftExcess.excess_nonneg X h b hX
  unfold augmentedExcess
  linarith only [he, hoff]

theorem soft_excess_le_augmented (X h b offset : ℝ) (hoff : offset ≤ X) :
    ViscousMemorySoftExcess.excess X h b ≤ augmentedExcess X h b offset := by
  unfold augmentedExcess
  linarith only [hoff]

/-- With the intended above-initial threshold, only the full initial
resource is deposited. This grants no new allowance during concatenation. -/
theorem initialized_augmentedExcess (X h b offset : ℝ) (hbX : X ≤ b * h) :
    augmentedExcess X h b offset = 8 * (X - offset) := by
  simp only [augmentedExcess, ViscousMemorySoftExcess.excess,
    not_lt.mpr hbX, ite_false, zero_add]

/-- A bound on the corrected reserve controls the same actual whole-space
continuation envelope. The missing physical history bound is not assumed
to follow from the spatial source payment. -/
theorem massEnvelope_of_augmented_excess (u : SmoothL2Field Space) (X h c : Space → ℝ)
    {b k B E offset : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hX : ∀ x, 0 < X x) (hoff : ∀ x, offset ≤ X x)
    (hh : ∀ x, 0 ≤ h x) (hhc : ∀ x, h x ≤ 1 + c x)
    (hc : Integrable c) (hc0 : ∀ x, 0 ≤ c x) (hcB : (∫ x, c x) ≤ B)
    (he : Integrable (fun x ↦ ViscousMemorySoftExcess.excess (X x) (h x) b))
    (hR : Integrable (fun x ↦ augmentedExcess (X x) (h x) b offset))
    (hRE : (∫ x, augmentedExcess (X x) (h x) b offset) ≤ E)
    (hcoerce : ∀ x, k * vortSq (gradMatrix u x) ^ 2 ≤ X x) :
    WholeSpaceMemoryEnvelope.MassEnvelope u (2 * b / k) (B + E / (2 * b)) := by
  have heE : (∫ x, ViscousMemorySoftExcess.excess (X x) (h x) b) ≤ E :=
    (integral_mono he hR (fun x ↦ soft_excess_le_augmented _ _ _ _ (hoff x))).trans hRE
  exact ViscousMemorySoftExcess.massEnvelope_of_soft_excess u X h c
    hb hk hX hh hhc hc hc0 hcB he heE hcoerce

end Mettapedia.FluidDynamics.NavierStokes.SignedViscousPressure
