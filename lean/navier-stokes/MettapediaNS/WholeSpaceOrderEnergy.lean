import Euler.OrdinaryTameEnergy
import Euler.OrdinaryH3Commutator
import Euler.OrdinarySobolevL4
import NavierStokes.R3CutoffSobolev
import NavierStokes.R3EnergyNorms
import MettapediaNS.WholeSpaceViscousEnergy

/-!
# Energies of a single derivative order on `ℝ³`

For a smooth field `A` with all derivatives in `L²`, `orderEnergy n A` is the sum of the
squared `L²` norms of its coordinate derivatives of order exactly `n`, so the upstream
`wordEnergy m A` is the sum of the order energies up to `m`. For the literal Navier–Stokes
right-hand side, the production of the order-`n` energy is exact:

```text
production_n = -2 Σ_{|w| = n} ⟪[∂_w, u·∇] u, ∂_w u⟫ - 2 ν orderEnergy (n+1),
```

the transport term `u·∇ ∂_w u` and the pressure drop out, and the viscous term is the next
order energy. The commutator is a sum of advection terms `(∂_a u · ∇) ∂_b u` with `a`
nonempty; Hölder's inequality bounds each pairing by `L⁴` and `L²` norms.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOrderEnergy

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  WholeSpaceViscousEnergy Finset
open scoped ENNReal

/-! ## Order energies and their production -/

/-- The energy of the derivatives of order exactly `n`. -/
def orderEnergy (n : ℕ) (A : SmoothL2Field Space) : ℝ :=
  ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ ^ 2

theorem orderEnergy_nonneg (n : ℕ) (A : SmoothL2Field Space) : 0 ≤ orderEnergy n A :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

theorem wordEnergy_succ (m : ℕ) (A : SmoothL2Field Space) :
    wordEnergy (m + 1) A = wordEnergy m A + orderEnergy (m + 1) A := by
  simp only [wordEnergy, orderEnergy]
  rw [sum_range_succ]

theorem wordEnergy_zero (A : SmoothL2Field Space) : wordEnergy 0 A = orderEnergy 0 A := by
  simp only [wordEnergy, orderEnergy, zero_add, range_one, sum_singleton]

theorem orderEnergy_le_wordEnergy {n m : ℕ} (h : n ≤ m) (A : SmoothL2Field Space) :
    orderEnergy n A ≤ wordEnergy m A := by
  simp only [wordEnergy]
  exact single_le_sum (f := fun n ↦ ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ ^ 2)
    (fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (mem_range.mpr (by omega))

/-- The production of the order-`n` energy by a rate `Q`. -/
def orderProduction (n : ℕ) (A Q : SmoothL2Field Space) : ℝ :=
  2 * ∑ w : Fin n → Fin 3, ⟪(wordField A w).toLp, (wordField Q w).toLp⟫_ℝ

theorem integerEnergyProduction_succ (m : ℕ) (A Q : SmoothL2Field Space) :
    integerEnergyProduction (m + 1) A Q =
      integerEnergyProduction m A Q + orderProduction (m + 1) A Q := by
  simp only [integerEnergyProduction, orderProduction]
  rw [sum_range_succ, mul_add]

/-- The next order energy is the dissipation of this order. -/
theorem orderEnergy_succ (n : ℕ) (A : SmoothL2Field Space) :
    orderEnergy (n + 1) A =
      ∑ w : Fin n → Fin 3, ∑ i : Fin 3, ‖((wordField A w).directionalField (axis i)).toLp‖ ^ 2 := by
  have h : ∑ w : Fin (n + 1) → Fin 3, ‖(wordField A w).toLp‖ ^ 2 =
      ∑ p : Fin 3 × (Fin n → Fin 3), ‖((wordField A p.2).directionalField (axis p.1)).toLp‖ ^ 2 :=
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin 3))
      (fun p ↦ ‖((wordField A p.2).directionalField (axis p.1)).toLp‖ ^ 2)
      (fun w ↦ ‖(wordField A w).toLp‖ ^ 2)
      (fun p ↦ by
        change _ = ‖(wordField A (Fin.cons p.1 p.2)).toLp‖ ^ 2
        rw [wordField_cons])).symm
  rw [orderEnergy, h, Fintype.sum_prod_type, Finset.sum_comm]

/-- **The exact order-`n` production of the Navier–Stokes right-hand side.** -/
theorem orderProduction_navierStokesRhs (n : ℕ) (ν : ℝ) (A P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    orderProduction n A (navierStokesRhs ν A P) =
      -2 * ∑ w : Fin n → Fin 3, ⟪(transportCommutator A A w).toLp, (wordField A w).toLp⟫_ℝ -
        2 * ν * orderEnergy (n + 1) A := by
  have hw (w : Fin n → Fin 3) :
      wordField (scaleField ν (laplacianField A)) w =
        scaleField ν (wordField (laplacianField A) w) :=
    wordField_map _ _ _
  have hv (w : Fin n → Fin 3) :
      ⟪(wordField A w).toLp, (wordField (navierStokesRhs ν A P) w).toLp⟫_ℝ =
        -⟪(transportCommutator A A w).toLp, (wordField A w).toLp⟫_ℝ -
          ν * ∑ i : Fin 3, ‖((wordField A w).directionalField (axis i)).toLp‖ ^ 2 := by
    rw [navierStokesRhs, wordField_add, toLp_addField, inner_add_right,
      eulerRhs_pairing A P hdiv hA hP w, hw, scaleField_toLp, real_inner_smul_right,
      wordField_laplacianField, inner_laplacianField]
    ring
  rw [orderProduction, orderEnergy_succ]
  simp only [hv, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  ring

/-! ## Hölder bounds for advection pairings -/

theorem holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩

/-- Hölder's inequality for three factors with exponents `4, 4, 2`. -/
theorem integral_triple_le {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : Space → E} {g : Space → F} {h : Space → G}
    (hf : MemLp f 4 volume) (hg : MemLp g 4 volume) (hh : MemLp h 2 volume) :
    Integrable (fun x ↦ ‖f x‖ * ‖g x‖ * ‖h x‖) ∧
      ∫ x, ‖f x‖ * ‖g x‖ * ‖h x‖ ≤
        lpNorm f 4 volume * lpNorm g 4 volume * lpNorm h 2 volume := by
  haveI := holderTriple_four_four_two
  have hfg : MemLp (fun x ↦ ‖f x‖ * ‖g x‖) 2 volume := hg.norm.mul' hf.norm
  have hfgh : MemLp (fun x ↦ ‖f x‖ * ‖g x‖ * ‖h x‖) 1 volume := hh.norm.mul' hfg
  have h1 := EulerMeanCutoffCurl.lpNorm_norm_mul_le (r := 2) hf hg
  have h2 := EulerMeanCutoffCurl.lpNorm_norm_mul_le (r := 1) hfg hh
  have he : (fun x ↦ ‖‖f x‖ * ‖g x‖‖ * ‖h x‖) = fun x ↦ ‖f x‖ * ‖g x‖ * ‖h x‖ := by
    funext x
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [he, lpNorm_one_eq_integral_norm hfgh.1] at h2
  have he2 : (fun x ↦ ‖‖f x‖ * ‖g x‖ * ‖h x‖‖) = fun x ↦ ‖f x‖ * ‖g x‖ * ‖h x‖ := by
    funext x
    exact Real.norm_of_nonneg (by positivity)
  rw [he2] at h2
  exact ⟨memLp_one_iff_integrable.mp hfgh,
    h2.trans (mul_le_mul_of_nonneg_right h1 lpNorm_nonneg)⟩

theorem advectionField_field_sum (C D : SmoothL2Field Space) (x : Space) :
    (advectionField C D).field x =
      ∑ i : Fin 3, C.field x i • (D.directionalField (axis i)).field x := by
  simp only [advectionField, sumField_field, coordinateProduct_field]

/-- The pairing with an advection term is bounded by the integrals of the pointwise
products of the three factors. -/
theorem abs_inner_advection_le (F C D : SmoothL2Field Space)
    (hint : ∀ i : Fin 3, Integrable
      (fun x ↦ ‖F.field x‖ * ‖C.field x‖ * ‖(D.directionalField (axis i)).field x‖)) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤
      ∑ i : Fin 3, ∫ x, ‖F.field x‖ * ‖C.field x‖ * ‖(D.directionalField (axis i)).field x‖ := by
  rw [real_inner_comm, field_inner, ← integral_finsetSum _ (fun i _ ↦ hint i),
    ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (integrable_finsetSum _ fun i _ ↦ hint i)
  filter_upwards with x
  rw [advectionField_field_sum, inner_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [real_inner_smul_right, norm_mul]
  have h1 : ‖C.field x i‖ ≤ ‖C.field x‖ := PiLp.norm_apply_le _ i
  have h2 : ‖⟪F.field x, (D.directionalField (axis i)).field x⟫_ℝ‖ ≤
      ‖F.field x‖ * ‖(D.directionalField (axis i)).field x‖ := by
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  calc ‖C.field x i‖ * ‖⟪F.field x, (D.directionalField (axis i)).field x⟫_ℝ‖ ≤
        ‖C.field x‖ * (‖F.field x‖ * ‖(D.directionalField (axis i)).field x‖) :=
      mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem memLp_four_field (A : SmoothL2Field Space) : MemLp A.field 4 volume :=
  (smooth_four_bound A.field A.smooth A.memLp A.derivative.memLp).1

/-- Allocation `4, 4, 2`: test field and advecting field in `L⁴`. -/
theorem advection_bound_442 (F C D : SmoothL2Field Space) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤
      ∑ i : Fin 3, lpNorm F.field 4 volume * lpNorm C.field 4 volume *
        ‖(D.directionalField (axis i)).toLp‖ := by
  have h (i : Fin 3) := integral_triple_le (memLp_four_field F) (memLp_four_field C)
    (D.directionalField (axis i)).memLp
  refine (abs_inner_advection_le F C D fun i ↦ (h i).1).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [← field_lpNorm]
  exact (h i).2

/-- Allocation `4, 2, 4`: test field and derivative in `L⁴`. -/
theorem advection_bound_424 (F C D : SmoothL2Field Space) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤
      ∑ i : Fin 3, lpNorm F.field 4 volume * ‖C.toLp‖ *
        lpNorm (D.directionalField (axis i)).field 4 volume := by
  have h (i : Fin 3) := integral_triple_le (memLp_four_field F)
    (memLp_four_field (D.directionalField (axis i))) C.memLp
  have he (i : Fin 3) : (fun x ↦ ‖F.field x‖ * ‖C.field x‖ *
      ‖(D.directionalField (axis i)).field x‖) = fun x ↦ ‖F.field x‖ *
        ‖(D.directionalField (axis i)).field x‖ * ‖C.field x‖ := by
    funext x
    ring
  refine (abs_inner_advection_le F C D fun i ↦ by rw [he]; exact (h i).1).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [he, ← field_lpNorm]
  calc _ ≤ _ := (h i).2
    _ = _ := by ring

/-- Allocation `2, 4, 4`: advecting field and derivative in `L⁴`. -/
theorem advection_bound_244 (F C D : SmoothL2Field Space) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤
      ∑ i : Fin 3, ‖F.toLp‖ * lpNorm C.field 4 volume *
        lpNorm (D.directionalField (axis i)).field 4 volume := by
  have h (i : Fin 3) := integral_triple_le (memLp_four_field C)
    (memLp_four_field (D.directionalField (axis i))) F.memLp
  have he (i : Fin 3) : (fun x ↦ ‖F.field x‖ * ‖C.field x‖ *
      ‖(D.directionalField (axis i)).field x‖) = fun x ↦ ‖C.field x‖ *
        ‖(D.directionalField (axis i)).field x‖ * ‖F.field x‖ := by
    funext x
    ring
  refine (abs_inner_advection_le F C D fun i ↦ by rw [he]; exact (h i).1).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [he, ← field_lpNorm]
  calc _ ≤ _ := (h i).2
    _ = _ := by ring

/-! ## `L⁴` and `L⁶` norms of a single field -/

/-- The directional dissipation of one field. -/
def gradEnergy (A : SmoothL2Field Space) : ℝ :=
  ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2

theorem gradEnergy_nonneg (A : SmoothL2Field Space) : 0 ≤ gradEnergy A :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem lpNorm_fderiv_sq_le (A : SmoothL2Field Space) :
    lpNorm (fderiv ℝ A.field) 2 volume ^ 2 ≤ 3 * gradEnergy A := by
  have hm : ∀ i : Fin 3, MemLp (A.directionalField (axis i)).field 2 volume :=
    fun i ↦ (A.directionalField (axis i)).memLp
  have hD : AEStronglyMeasurable (fderiv ℝ A.field) volume := A.derivative.memLp.1
  rw [NavierStokes.R3EnergyNorms.lpNorm_two_sq hD]
  have hpt (x : Space) : ‖fderiv ℝ A.field x‖ ^ 2 ≤
      3 * ∑ i : Fin 3, ‖(A.directionalField (axis i)).field x‖ ^ 2 := by
    have h := NavierStokes.R3CutoffSobolev.operator_norm_sq_le (fderiv ℝ A.field x)
    simp only [directionalField_field]
    exact h
  have hint (i : Fin 3) : Integrable (fun x ↦ ‖(A.directionalField (axis i)).field x‖ ^ 2) :=
    (hm i).integrable_norm_pow (by norm_num)
  calc ∫ x, ‖fderiv ℝ A.field x‖ ^ 2 ≤
        ∫ x, 3 * ∑ i : Fin 3, ‖(A.directionalField (axis i)).field x‖ ^ 2 :=
      integral_mono (A.derivative.memLp.integrable_norm_pow (by norm_num))
        ((integrable_finsetSum _ fun i _ ↦ hint i).const_mul 3) hpt
    _ = 3 * gradEnergy A := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i, gradEnergy]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← NavierStokes.R3EnergyNorms.lpNorm_two_sq (hm i).1, field_lpNorm]

/-- **Sobolev.** `‖A‖₆² ≤ 3 S² Σᵢ ‖∂ᵢA‖₂²`. -/
theorem lpNorm_six_sq_le (A : SmoothL2Field Space) :
    lpNorm A.field 6 volume ^ 2 ≤
      3 * (EulerMeanCutoffCurl.sobolevConstant : ℝ) ^ 2 * gradEnergy A := by
  have h := norm_six_le A.field A.smooth A.memLp A.derivative.memLp
  have hD : AEStronglyMeasurable (fderiv ℝ A.field) volume := A.derivative.memLp.1
  rw [toReal_eLpNorm hD, toReal_eLpNorm A.smooth.continuous.aestronglyMeasurable] at h
  have h2 := pow_le_pow_left₀ lpNorm_nonneg h 2
  calc lpNorm A.field 6 volume ^ 2 ≤
        ((EulerMeanCutoffCurl.sobolevConstant : ℝ) * lpNorm (fderiv ℝ A.field) 2 volume) ^ 2 := h2
    _ = (EulerMeanCutoffCurl.sobolevConstant : ℝ) ^ 2 * lpNorm (fderiv ℝ A.field) 2 volume ^ 2 := by
      ring
    _ ≤ (EulerMeanCutoffCurl.sobolevConstant : ℝ) ^ 2 * (3 * gradEnergy A) :=
      mul_le_mul_of_nonneg_left (lpNorm_fderiv_sq_le A) (sq_nonneg _)
    _ = _ := by ring

/-- **Interpolation.** `‖A‖₄⁴ ≤ ‖A‖₂ ‖A‖₆³`. -/
theorem lpNorm_four_pow_le (A : SmoothL2Field Space) :
    lpNorm A.field 4 volume ^ 4 ≤ ‖A.toLp‖ * lpNorm A.field 6 volume ^ 3 := by
  have h6 := memLp_six A.field A.smooth A.memLp A.derivative.memLp
  have hsq := norm_four_sq A.memLp h6
  have h3 := cube_memLp h6
  have hcs := NavierStokes.R3EnergyNorms.integral_mul_le A.memLp.norm h3
    (fun x ↦ norm_nonneg _) (fun x ↦ by positivity)
  rw [lpNorm_norm A.memLp.1, cube_norm h6, field_lpNorm] at hcs
  have hsq2 : lpNorm (fun x ↦ ‖A.field x‖ ^ 2) 2 volume ^ 2 = ∫ x, ‖A.field x‖ * ‖A.field x‖ ^ 3 := by
    rw [NavierStokes.R3EnergyNorms.lpNorm_two_sq (square_memLp A.memLp h6).1]
    congr 1
    funext x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    ring
  calc lpNorm A.field 4 volume ^ 4 = (lpNorm A.field 4 volume ^ 2) ^ 2 := by ring
    _ = ∫ x, ‖A.field x‖ * ‖A.field x‖ ^ 3 := by rw [hsq, hsq2]
    _ ≤ _ := hcs

/-! ## The transport commutator of short words -/

theorem wordField_advection_toLp (C B : SmoothL2Field Space) {n : ℕ} (v : Fin n → Fin 3) :
    (wordField (advectionField C B) v).toLp =
      (advectionField C (wordField B v)).toLp + (transportCommutator C B v).toLp := by
  rw [transportCommutator, toLp_fieldSub]
  abel

theorem transportCommutator_one (A B : SmoothL2Field Space) (i : Fin 3) :
    (transportCommutator A B (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i)).toLp =
      (advectionField (A.directionalField (axis i)) B).toLp := by
  rw [transportCommutator_snoc, toLp_addField, wordField_zero, transportCommutator_zero, add_zero]

theorem transportCommutator_two (A B : SmoothL2Field Space) (i j : Fin 3) :
    (transportCommutator A B (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) j)).toLp =
      (advectionField (A.directionalField (axis j)) (B.directionalField (axis i))).toLp +
      (advectionField ((A.directionalField (axis j)).directionalField (axis i)) B).toLp +
      (advectionField (A.directionalField (axis i)) (B.directionalField (axis j))).toLp := by
  rw [transportCommutator_snoc, toLp_addField, wordField_advection_toLp, transportCommutator_one,
    transportCommutator_one, wordField_snoc, wordField_zero]

theorem transportCommutator_three (A B : SmoothL2Field Space) (i j k : Fin 3) :
    (transportCommutator A B
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) j) k)).toLp =
      (advectionField (A.directionalField (axis k))
        ((B.directionalField (axis j)).directionalField (axis i))).toLp +
      ((advectionField ((A.directionalField (axis k)).directionalField (axis j))
          (B.directionalField (axis i))).toLp +
        (advectionField (((A.directionalField (axis k)).directionalField (axis j)).directionalField
          (axis i)) B).toLp +
        (advectionField ((A.directionalField (axis k)).directionalField (axis i))
          (B.directionalField (axis j))).toLp) +
      ((advectionField (A.directionalField (axis j))
          ((B.directionalField (axis k)).directionalField (axis i))).toLp +
        (advectionField ((A.directionalField (axis j)).directionalField (axis i))
          (B.directionalField (axis k))).toLp +
        (advectionField (A.directionalField (axis i))
          ((B.directionalField (axis k)).directionalField (axis j))).toLp) := by
  rw [transportCommutator_snoc, toLp_addField, wordField_advection_toLp, transportCommutator_two,
    transportCommutator_two, wordField_snoc, wordField_snoc, wordField_zero]

theorem word_one_eq (w : Fin 1 → Fin 3) : w = Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) (w 0) := by
  funext k
  fin_cases k
  rfl

theorem word_two_eq (w : Fin 2 → Fin 3) :
    w = Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) (w 0)) (w 1) := by
  funext k
  fin_cases k <;> rfl

theorem word_three_eq (w : Fin 3 → Fin 3) :
    w = Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) (w 0)) (w 1)) (w 2) := by
  funext k
  fin_cases k <;> rfl

/-! ## Iterated directional derivatives as words -/

theorem d_eq_word (A : SmoothL2Field Space) (a : Fin 3) :
    A.directionalField (axis a) = wordField A (Fin.cons a Fin.elim0) := by
  rw [wordField_cons, wordField_zero]

theorem dd_eq_word (A : SmoothL2Field Space) (a b : Fin 3) :
    (A.directionalField (axis a)).directionalField (axis b) =
      wordField A (Fin.cons b (Fin.cons a Fin.elim0)) := by
  rw [wordField_cons, wordField_cons, wordField_zero]

theorem ddd_eq_word (A : SmoothL2Field Space) (a b c : Fin 3) :
    ((A.directionalField (axis a)).directionalField (axis b)).directionalField (axis c) =
      wordField A (Fin.cons c (Fin.cons b (Fin.cons a Fin.elim0))) := by
  rw [wordField_cons, wordField_cons, wordField_cons, wordField_zero]

/-! ## Sums of `L⁴` norms over one order -/

/-- The sum of the squared `L⁴` norms of the derivatives of order `n`. -/
def quarticEnergy (n : ℕ) (A : SmoothL2Field Space) : ℝ :=
  ∑ w : Fin n → Fin 3, lpNorm (wordField A w).field 4 volume ^ 2

theorem quarticEnergy_nonneg (n : ℕ) (A : SmoothL2Field Space) : 0 ≤ quarticEnergy n A :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem sq_lpNorm_four_le (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    lpNorm (wordField A w).field 4 volume ^ 2 ≤ quarticEnergy n A :=
  Finset.single_le_sum (f := fun w ↦ lpNorm (wordField A w).field 4 volume ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ w)

theorem norm_le_sqrt_orderEnergy (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    ‖(wordField A w).toLp‖ ≤ Real.sqrt (orderEnergy n A) :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun w ↦ ‖(wordField A w).toLp‖ ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ w))

/-- Two `L⁴` factors and one `L²` factor. -/
theorem triple_le {a a' b Λ E : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 ≤ b)
    (haΛ : a ^ 2 ≤ Λ) (ha'Λ : a' ^ 2 ≤ Λ) (hbE : b ≤ Real.sqrt E) :
    a * a' * b ≤ Λ * Real.sqrt E := by
  have hΛ : a * a' ≤ Λ := by nlinarith [sq_nonneg (a - a')]
  exact mul_le_mul hΛ hbE hb ((mul_nonneg ha ha').trans hΛ)

/-! ## Commutator pairings of orders two and three -/

theorem bound_424 (F C D : SmoothL2Field Space) {Λ E : ℝ}
    (hF : lpNorm F.field 4 volume ^ 2 ≤ Λ) (hC : ‖C.toLp‖ ≤ Real.sqrt E)
    (hD : ∀ k : Fin 3, lpNorm (D.directionalField (axis k)).field 4 volume ^ 2 ≤ Λ) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤ 3 * (Λ * Real.sqrt E) := by
  refine (advection_bound_424 F C D).trans ?_
  calc _ ≤ ∑ _k : Fin 3, Λ * Real.sqrt E := Finset.sum_le_sum fun k _ ↦ by
        rw [mul_right_comm]
        exact triple_le lpNorm_nonneg lpNorm_nonneg (norm_nonneg _) hF (hD k) hC
    _ = 3 * (Λ * Real.sqrt E) := by simp

theorem bound_442 (F C D : SmoothL2Field Space) {Λ E : ℝ}
    (hF : lpNorm F.field 4 volume ^ 2 ≤ Λ) (hC : lpNorm C.field 4 volume ^ 2 ≤ Λ)
    (hD : ∀ k : Fin 3, ‖(D.directionalField (axis k)).toLp‖ ≤ Real.sqrt E) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤ 3 * (Λ * Real.sqrt E) := by
  refine (advection_bound_442 F C D).trans ?_
  calc _ ≤ ∑ _k : Fin 3, Λ * Real.sqrt E := Finset.sum_le_sum fun k _ ↦
        triple_le lpNorm_nonneg lpNorm_nonneg (norm_nonneg _) hF hC (hD k)
    _ = 3 * (Λ * Real.sqrt E) := by simp

theorem bound_244 (F C D : SmoothL2Field Space) {Λ E : ℝ}
    (hF : ‖F.toLp‖ ≤ Real.sqrt E) (hC : lpNorm C.field 4 volume ^ 2 ≤ Λ)
    (hD : ∀ k : Fin 3, lpNorm (D.directionalField (axis k)).field 4 volume ^ 2 ≤ Λ) :
    |⟪(advectionField C D).toLp, F.toLp⟫_ℝ| ≤ 3 * (Λ * Real.sqrt E) := by
  refine (advection_bound_244 F C D).trans ?_
  calc _ ≤ ∑ _k : Fin 3, Λ * Real.sqrt E := Finset.sum_le_sum fun k _ ↦
        (le_of_eq (by ring)).trans
          (triple_le lpNorm_nonneg lpNorm_nonneg (norm_nonneg _) hC (hD k) hF)
    _ = 3 * (Λ * Real.sqrt E) := by simp

theorem commutator_pairing_two (u : SmoothL2Field Space) (w : Fin 2 → Fin 3) :
    |⟪(transportCommutator u u w).toLp, (wordField u w).toLp⟫_ℝ| ≤
      9 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)) := by
  obtain ⟨i, j, rfl⟩ : ∃ i j, w = Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) j :=
    ⟨w 0, w 1, word_two_eq w⟩
  set F := wordField u (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) j)
  have hF : lpNorm F.field 4 volume ^ 2 ≤ quarticEnergy 2 u := sq_lpNorm_four_le u _
  have hL (a b : Fin 3) : lpNorm ((u.directionalField (axis a)).directionalField (axis b)).field 4
      volume ^ 2 ≤ quarticEnergy 2 u := by
    rw [dd_eq_word]
    exact sq_lpNorm_four_le u _
  have hN (a : Fin 3) : ‖(u.directionalField (axis a)).toLp‖ ≤ Real.sqrt (orderEnergy 1 u) := by
    rw [d_eq_word]
    exact norm_le_sqrt_orderEnergy u _
  rw [transportCommutator_two, inner_add_left, inner_add_left]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ 3 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)) +
        3 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)) +
        3 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)) :=
      add_le_add_three (bound_424 F _ _ hF (hN j) (hL i)) (bound_442 F _ u hF (hL j i) hN)
        (bound_424 F _ _ hF (hN i) (hL j))
    _ = _ := by ring

theorem commutator_pairing_three (u : SmoothL2Field Space) (w : Fin 3 → Fin 3) :
    |⟪(transportCommutator u u w).toLp, (wordField u w).toLp⟫_ℝ| ≤
      12 * (quarticEnergy 3 u * Real.sqrt (orderEnergy 1 u)) +
        9 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 3 u)) := by
  obtain ⟨i, j, k, rfl⟩ : ∃ i j k,
      w = Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) j) k :=
    ⟨w 0, w 1, w 2, word_three_eq w⟩
  set F := wordField u (Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 3) i) j) k)
  have hF4 : lpNorm F.field 4 volume ^ 2 ≤ quarticEnergy 3 u := sq_lpNorm_four_le u _
  have hF2 : ‖F.toLp‖ ≤ Real.sqrt (orderEnergy 3 u) := norm_le_sqrt_orderEnergy u _
  have hL2 (a b : Fin 3) : lpNorm ((u.directionalField (axis a)).directionalField (axis b)).field 4
      volume ^ 2 ≤ quarticEnergy 2 u := by
    rw [dd_eq_word]
    exact sq_lpNorm_four_le u _
  have hL3 (a b c : Fin 3) : lpNorm (((u.directionalField (axis a)).directionalField
      (axis b)).directionalField (axis c)).field 4 volume ^ 2 ≤ quarticEnergy 3 u := by
    rw [ddd_eq_word]
    exact sq_lpNorm_four_le u _
  have hN (a : Fin 3) : ‖(u.directionalField (axis a)).toLp‖ ≤ Real.sqrt (orderEnergy 1 u) := by
    rw [d_eq_word]
    exact norm_le_sqrt_orderEnergy u _
  rw [transportCommutator_three]
  simp only [inner_add_left]
  have t0 := bound_424 F _ _ hF4 (hN k) (hL3 j i)
  have t1 := bound_244 F _ _ hF2 (hL2 k j) (hL2 i)
  have t2 := bound_442 F _ u hF4 (hL3 k j i) hN
  have t3 := bound_244 F _ _ hF2 (hL2 k i) (hL2 j)
  have t4 := bound_424 F _ _ hF4 (hN j) (hL3 k i)
  have t5 := bound_244 F _ _ hF2 (hL2 j i) (hL2 k)
  have t6 := bound_424 F _ _ hF4 (hN i) (hL3 k j)
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ _ := add_le_add_three t0 ((abs_add_three _ _ _).trans (add_le_add_three t1 t2 t3))
        ((abs_add_three _ _ _).trans (add_le_add_three t4 t5 t6))
    _ = _ := by ring

/-! ## The quartic energy and the order energies -/

/-- The Sobolev constant of `‖f‖₆ ≤ S ‖∇f‖₂`, as a real number. -/
def sobolevReal : ℝ := (EulerMeanCutoffCurl.sobolevConstant : ℝ)

theorem sobolevReal_nonneg : 0 ≤ sobolevReal := NNReal.coe_nonneg _

theorem gradEnergy_word_sum (A : SmoothL2Field Space) (n : ℕ) :
    ∑ w : Fin n → Fin 3, gradEnergy (wordField A w) = orderEnergy (n + 1) A := by
  rw [orderEnergy_succ]
  rfl

theorem sum_cube_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 3 ≤ (∑ i ∈ s, f i) ^ 3 := by
  calc ∑ i ∈ s, f i ^ 3 ≤ ∑ i ∈ s, f i * (∑ j ∈ s, f j) ^ 2 := Finset.sum_le_sum fun i hi ↦ by
        have h2 : f i ^ 2 ≤ (∑ j ∈ s, f j) ^ 2 :=
          pow_le_pow_left₀ (hf i hi) (Finset.single_le_sum hf hi) 2
        calc f i ^ 3 = f i * f i ^ 2 := by ring
          _ ≤ f i * (∑ j ∈ s, f j) ^ 2 := mul_le_mul_of_nonneg_left h2 (hf i hi)
    _ = (∑ i ∈ s, f i) ^ 3 := by rw [← Finset.sum_mul]; ring

/-- **The quartic energy is controlled by two consecutive order energies:**
`Λₙ⁴ ≤ 9ⁿ · 27 S⁶ Eₙ Eₙ₊₁³`. -/
theorem quarticEnergy_pow_four_le (n : ℕ) (A : SmoothL2Field Space) :
    quarticEnergy n A ^ 4 ≤
      9 ^ n * (27 * sobolevReal ^ 6 * orderEnergy n A * orderEnergy (n + 1) A ^ 3) := by
  have hcard : ((Finset.univ : Finset (Fin n → Fin 3)).card : ℝ) = 3 ^ n := by simp
  have h1 : quarticEnergy n A ^ 2 ≤
      3 ^ n * ∑ w : Fin n → Fin 3, lpNorm (wordField A w).field 4 volume ^ 4 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun w : Fin n → Fin 3 ↦ lpNorm (wordField A w).field 4 volume ^ 2)
    rw [hcard] at h
    simpa only [quarticEnergy, ← pow_mul] using h
  have h2 : ∑ w : Fin n → Fin 3, lpNorm (wordField A w).field 4 volume ^ 4 ≤
      ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ * lpNorm (wordField A w).field 6 volume ^ 3 :=
    Finset.sum_le_sum fun w _ ↦ lpNorm_four_pow_le (wordField A w)
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun w : Fin n → Fin 3 ↦ ‖(wordField A w).toLp‖)
    (fun w : Fin n → Fin 3 ↦ lpNorm (wordField A w).field 6 volume ^ 3)
  have h4 : ∑ w : Fin n → Fin 3, (lpNorm (wordField A w).field 6 volume ^ 3) ^ 2 ≤
      27 * sobolevReal ^ 6 * orderEnergy (n + 1) A ^ 3 := by
    calc _ ≤ ∑ w : Fin n → Fin 3, 27 * sobolevReal ^ 6 * gradEnergy (wordField A w) ^ 3 :=
          Finset.sum_le_sum fun w _ ↦ by
            have h := lpNorm_six_sq_le (wordField A w)
            calc (lpNorm (wordField A w).field 6 volume ^ 3) ^ 2 =
                  (lpNorm (wordField A w).field 6 volume ^ 2) ^ 3 := by ring
              _ ≤ (3 * sobolevReal ^ 2 * gradEnergy (wordField A w)) ^ 3 :=
                pow_le_pow_left₀ (sq_nonneg _) h 3
              _ = _ := by ring
      _ = 27 * sobolevReal ^ 6 * ∑ w : Fin n → Fin 3, gradEnergy (wordField A w) ^ 3 := by
          rw [Finset.mul_sum]
      _ ≤ 27 * sobolevReal ^ 6 * orderEnergy (n + 1) A ^ 3 := by
          rw [← gradEnergy_word_sum]
          exact mul_le_mul_of_nonneg_left (sum_cube_le _ _ fun w _ ↦ gradEnergy_nonneg _)
            (by positivity [sobolevReal_nonneg])
  have h0 : 0 ≤ ∑ w : Fin n → Fin 3, lpNorm (wordField A w).field 4 volume ^ 4 :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have hE : ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ ^ 2 = orderEnergy n A := rfl
  rw [hE] at h3
  calc quarticEnergy n A ^ 4 = (quarticEnergy n A ^ 2) ^ 2 := by ring
    _ ≤ (3 ^ n * ∑ w : Fin n → Fin 3, lpNorm (wordField A w).field 4 volume ^ 4) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = 9 ^ n * (∑ w : Fin n → Fin 3, lpNorm (wordField A w).field 4 volume ^ 4) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    _ ≤ 9 ^ n * (∑ w : Fin n → Fin 3,
          ‖(wordField A w).toLp‖ * lpNorm (wordField A w).field 6 volume ^ 3) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 2) (by positivity)
    _ ≤ 9 ^ n * (orderEnergy n A *
          ∑ w : Fin n → Fin 3, (lpNorm (wordField A w).field 6 volume ^ 3) ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 9 ^ n * (orderEnergy n A * (27 * sobolevReal ^ 6 * orderEnergy (n + 1) A ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (orderEnergy_nonneg n A))
        (by positivity)
    _ = _ := by ring

/-! ## Absorbing the production into the dissipation -/

theorem four_mul_cube_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * a ^ 3 * b ≤ (a + b) ^ 4 := by
  have h : (a + b) ^ 4 = 4 * a ^ 3 * b + (a ^ 4 + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 + b ^ 4) := by
    ring
  rw [h]
  exact le_add_of_nonneg_right (by positivity)

/-- **Absorption.** If `x⁴ ≤ Q E F³`, then `x ≤ ν F + Q E / (4 ν³)`. -/
theorem absorb {x Q E F ν : ℝ} (hx : 0 ≤ x) (hQ : 0 ≤ Q) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hν : 0 < ν) (h : x ^ 4 ≤ Q * E * F ^ 3) : x ≤ ν * F + Q / (4 * ν ^ 3) * E := by
  have hc : 0 ≤ Q / (4 * ν ^ 3) * E := by positivity
  have hy : 0 ≤ ν * F + Q / (4 * ν ^ 3) * E := by positivity
  refine (pow_le_pow_iff_left₀ hx hy (by norm_num : (4 : ℕ) ≠ 0)).mp (h.trans ?_)
  have h4 := four_mul_cube_mul_le (mul_nonneg hν.le hF) hc
  have he : 4 * (ν * F) ^ 3 * (Q / (4 * ν ^ 3) * E) = Q * E * F ^ 3 := by
    field_simp
  linarith

/-- The constant of the order-two absorption. -/
def rungTwoConstant (ν Z : ℝ) : ℝ := 162 ^ 4 * 81 * 27 * sobolevReal ^ 6 * Z ^ 2 / (4 * ν ^ 3)

/-- The constant of the order-three absorption. -/
def rungThreeConstant (ν Z : ℝ) : ℝ := 648 ^ 4 * 729 * 27 * sobolevReal ^ 6 * Z ^ 2 / (4 * ν ^ 3)

/-- The growth coefficient of the order-three energy. -/
def rungThreeGrowth : ℝ := 486 * 7 * (1 + sobolevReal) ^ 2

theorem sqrt_pow_four {E : ℝ} (hE : 0 ≤ E) : Real.sqrt E ^ 4 = E ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hE]

/-- **The order-two energy grows at most linearly once the enstrophy is bounded.** -/
theorem orderProduction_two_le {ν : ℝ} (hν : 0 < ν) (u P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hA : u.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {Z : ℝ} (hZ : orderEnergy 1 u ≤ Z) :
    orderProduction 2 u (navierStokesRhs ν u P) ≤
      -(ν * orderEnergy 3 u) + rungTwoConstant ν Z * orderEnergy 2 u := by
  rw [orderProduction_navierStokesRhs 2 ν u P hdiv hA hP]
  have hE1 := orderEnergy_nonneg 1 u
  have hE2 := orderEnergy_nonneg 2 u
  have hE3 := orderEnergy_nonneg 3 u
  have hΛ := quarticEnergy_nonneg 2 u
  have hS : |∑ w : Fin 2 → Fin 3, ⟪(transportCommutator u u w).toLp, (wordField u w).toLp⟫_ℝ| ≤
      81 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun w _ ↦ commutator_pairing_two u w).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    exact le_of_eq (by push_cast; ring)
  have hx : 162 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)) ≤
      ν * orderEnergy 3 u + rungTwoConstant ν Z * orderEnergy 2 u := by
    have hQ : 0 ≤ 162 ^ 4 * 81 * 27 * sobolevReal ^ 6 * Z ^ 2 := by positivity
    have h := absorb (x := 162 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u)))
      (by positivity) hQ hE2 hE3 hν ?_
    · simpa only [rungTwoConstant] using h
    have hq := quarticEnergy_pow_four_le 2 u
    have hZ2 : orderEnergy 1 u ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hE1 hZ 2
    calc (162 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 1 u))) ^ 4 =
          162 ^ 4 * quarticEnergy 2 u ^ 4 * orderEnergy 1 u ^ 2 := by
            rw [mul_pow, mul_pow, sqrt_pow_four hE1]
            ring
      _ ≤ 162 ^ 4 * (9 ^ 2 * (27 * sobolevReal ^ 6 * orderEnergy 2 u * orderEnergy 3 u ^ 3)) *
          Z ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hZ2 (sq_nonneg _)
        positivity [sobolevReal_nonneg]
      _ = _ := by ring
  have hneg := neg_abs_le (∑ w : Fin 2 → Fin 3,
    ⟪(transportCommutator u u w).toLp, (wordField u w).toLp⟫_ℝ)
  show _ - 2 * ν * orderEnergy 3 u ≤ _
  linarith

theorem le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ≤ (1 + x) ^ 4 := by
  have h : (1 + x) ^ 4 = x + (1 + 3 * x + 6 * x ^ 2 + 4 * x ^ 3 + x ^ 4) := by ring
  rw [h]
  exact le_add_of_nonneg_right (by positivity)

/-- **The order-three energy grows at most with an integrable rate.** Once the enstrophy
is bounded, the order-three production is absorbed by the dissipation up to a rate that
is linear in the order-three energy, with a coefficient involving the order-two and
order-three energies. -/
theorem orderProduction_three_le {ν : ℝ} (hν : 0 < ν) (u P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hA : u.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {Z : ℝ} (hZ : orderEnergy 1 u ≤ Z) :
    orderProduction 3 u (navierStokesRhs ν u P) ≤
      -(ν * orderEnergy 4 u) + (rungThreeConstant ν Z +
        rungThreeGrowth * (1 + orderEnergy 2 u) * (1 + orderEnergy 3 u)) * orderEnergy 3 u := by
  rw [orderProduction_navierStokesRhs 3 ν u P hdiv hA hP]
  have hE1 := orderEnergy_nonneg 1 u
  have hE2 := orderEnergy_nonneg 2 u
  have hE3 := orderEnergy_nonneg 3 u
  have hE4 := orderEnergy_nonneg 4 u
  have hΛ2 := quarticEnergy_nonneg 2 u
  have hΛ3 := quarticEnergy_nonneg 3 u
  have hS := sobolevReal_nonneg
  have hsum : |∑ w : Fin 3 → Fin 3,
      ⟪(transportCommutator u u w).toLp, (wordField u w).toLp⟫_ℝ| ≤
      27 * (12 * (quarticEnergy 3 u * Real.sqrt (orderEnergy 1 u)) +
        9 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 3 u))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun w _ ↦ commutator_pairing_three u w).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    exact le_of_eq (by push_cast; ring)
  have ha : 648 * (quarticEnergy 3 u * Real.sqrt (orderEnergy 1 u)) ≤
      ν * orderEnergy 4 u + rungThreeConstant ν Z * orderEnergy 3 u := by
    have hQ : 0 ≤ 648 ^ 4 * 729 * 27 * sobolevReal ^ 6 * Z ^ 2 := by positivity
    have h := absorb (x := 648 * (quarticEnergy 3 u * Real.sqrt (orderEnergy 1 u)))
      (mul_nonneg (by norm_num) (mul_nonneg hΛ3 (Real.sqrt_nonneg _))) hQ hE3 hE4 hν ?_
    · simpa only [rungThreeConstant] using h
    have hq : quarticEnergy 3 u ^ 4 ≤
        9 ^ 3 * (27 * sobolevReal ^ 6 * orderEnergy 3 u * orderEnergy 4 u ^ 3) :=
      quarticEnergy_pow_four_le 3 u
    have hZ2 : orderEnergy 1 u ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hE1 hZ 2
    calc (648 * (quarticEnergy 3 u * Real.sqrt (orderEnergy 1 u))) ^ 4 =
          648 ^ 4 * quarticEnergy 3 u ^ 4 * orderEnergy 1 u ^ 2 := by
            rw [mul_pow, mul_pow, sqrt_pow_four hE1]
            ring
      _ ≤ 648 ^ 4 * (9 ^ 3 * (27 * sobolevReal ^ 6 * orderEnergy 3 u * orderEnergy 4 u ^ 3)) *
          Z ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hZ2 (sq_nonneg _)
        exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg hS 6)) hE3) (pow_nonneg hE4 3)))
      _ = _ := by ring
  have hb : 486 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 3 u)) ≤
      rungThreeGrowth * (1 + orderEnergy 2 u) * (1 + orderEnergy 3 u) * orderEnergy 3 u := by
    have hy : 0 ≤ rungThreeGrowth * (1 + orderEnergy 2 u) * (1 + orderEnergy 3 u) *
        orderEnergy 3 u := by
      have hG : 0 ≤ rungThreeGrowth := by
        unfold rungThreeGrowth
        exact mul_nonneg (by norm_num) (sq_nonneg _)
      exact mul_nonneg (mul_nonneg (mul_nonneg hG (by linarith)) (by linarith)) hE3
    refine (pow_le_pow_iff_left₀ (mul_nonneg (by norm_num) (mul_nonneg hΛ2
      (Real.sqrt_nonneg _))) hy (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
    have hq : quarticEnergy 2 u ^ 4 ≤
        9 ^ 2 * (27 * sobolevReal ^ 6 * orderEnergy 2 u * orderEnergy 3 u ^ 3) :=
      quarticEnergy_pow_four_le 2 u
    have hS6 : sobolevReal ^ 6 ≤ (1 + sobolevReal) ^ 8 := by
      calc sobolevReal ^ 6 ≤ (1 + sobolevReal) ^ 6 :=
            pow_le_pow_left₀ hS (by linarith) 6
        _ ≤ (1 + sobolevReal) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hc : 2187 * sobolevReal ^ 6 * orderEnergy 2 u * orderEnergy 3 u ≤
        2401 * (1 + sobolevReal) ^ 8 * (1 + orderEnergy 2 u) ^ 4 * (1 + orderEnergy 3 u) ^ 4 := by
      have h1 := le_one_add_pow_four hE2
      have h2 := le_one_add_pow_four hE3
      have hstep1 : 2187 * sobolevReal ^ 6 ≤ 2401 * (1 + sobolevReal) ^ 8 := by
        have h0 : 0 ≤ sobolevReal ^ 6 := pow_nonneg hS 6
        linarith
      calc 2187 * sobolevReal ^ 6 * orderEnergy 2 u * orderEnergy 3 u =
            (2187 * sobolevReal ^ 6) * (orderEnergy 2 u * orderEnergy 3 u) := by ring
        _ ≤ (2401 * (1 + sobolevReal) ^ 8) *
            ((1 + orderEnergy 2 u) ^ 4 * (1 + orderEnergy 3 u) ^ 4) :=
          mul_le_mul hstep1 (mul_le_mul h1 h2 hE3 (pow_nonneg (by linarith) 4))
            (mul_nonneg hE2 hE3) (mul_nonneg (by norm_num) (pow_nonneg (by linarith) 8))
        _ = _ := by ring
    calc (486 * (quarticEnergy 2 u * Real.sqrt (orderEnergy 3 u))) ^ 4 =
          486 ^ 4 * quarticEnergy 2 u ^ 4 * orderEnergy 3 u ^ 2 := by
            rw [mul_pow, mul_pow, sqrt_pow_four hE3]
            ring
      _ ≤ 486 ^ 4 * (9 ^ 2 * (27 * sobolevReal ^ 6 * orderEnergy 2 u * orderEnergy 3 u ^ 3)) *
          orderEnergy 3 u ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (sq_nonneg _)
      _ = 486 ^ 4 * (2187 * sobolevReal ^ 6 * orderEnergy 2 u * orderEnergy 3 u) *
          orderEnergy 3 u ^ 4 := by ring
      _ ≤ 486 ^ 4 * (2401 * (1 + sobolevReal) ^ 8 * (1 + orderEnergy 2 u) ^ 4 *
          (1 + orderEnergy 3 u) ^ 4) * orderEnergy 3 u ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
          (pow_nonneg hE3 4)
      _ = _ := by unfold rungThreeGrowth; ring
  have hneg := neg_abs_le (∑ w : Fin 3 → Fin 3,
    ⟪(transportCommutator u u w).toLp, (wordField u w).toLp⟫_ℝ)
  show _ - 2 * ν * orderEnergy 4 u ≤ _
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOrderEnergy

