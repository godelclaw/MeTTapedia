import MettapediaNS.NewtonianHessianPrincipalValue
import Mettapedia.FluidDynamics.NavierStokes.PlaneWaveSelfStrain

/-!
# Biot–Savart strain assembled from the imported singular-integral bounds

The strain is the existing symmetric gradient `strainRateApply` of the
actual upstream Biot–Savart velocity. Its entries use only off-diagonal
Newtonian Hessians and differences of diagonal Hessians, so the local
isotropic term cancels before any norm estimate.
-/

noncomputable section

open MeasureTheory EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart

open EulerBlowup Ring3D

/-- Coordinates of the existing symmetric gradient, using the upstream axes. -/
theorem strainRateApply_axis_apply {u : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) (i j : Fin 3) :
    strainRateApply u x (e3 j) i =
      (pd3 j (fun y ↦ u y i) x + pd3 i (fun y ↦ u y j) x) / 2 := by
  simp [strainRateApply, fderivTransposeApply, pd3, e3,
    fderiv_coordinate u x hu, Pi.single_apply, EuclideanSpace.inner_single_right]
  ring

theorem velocity_partial_eq_hessians {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (i j : Fin 3) (x : Space) :
    pd3 i (fun y ↦ velocity vort y j) x =
      -pd3 i (pd3 (j + 1) (newton3 (fun y ↦ vort y (j + 2)))) x +
        pd3 i (pd3 (j + 2) (newton3 (fun y ↦ vort y (j + 1)))) x := by
  have hs (k : Fin 3) : ContDiff ℝ ∞ (fun y ↦ vort y k) := contDiff_euclidean.mp hvort k
  have hcs (k : Fin 3) : HasCompactSupport (fun y ↦ vort y k) :=
    hc.comp_left (g := fun z : Space ↦ z k) rfl
  rw [velocity_partial_eq_integrals hvort hc,
    newtonianHessian_eq_integral (hs _) (hcs _),
    newtonianHessian_eq_integral (hs _) (hcs _)]

theorem strain_diagonal_eq_hessians {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (i : Fin 3) (x : Space) :
    strainRateApply (velocity vort) x (e3 i) i =
      -pd3 i (pd3 (i + 1) (newton3 (fun y ↦ vort y (i + 2)))) x +
        pd3 i (pd3 (i + 2) (newton3 (fun y ↦ vort y (i + 1)))) x := by
  rw [strainRateApply_axis_apply ((contDiff_velocity hvort hc).differentiable (by simp) x)]
  simp only [velocity_partial_eq_hessians hvort hc]
  ring

/-- Cyclic off-diagonal entries expose a difference of diagonal Hessians,
not two separately estimated singular diagonal terms. -/
theorem strain_cyclic_eq_hessians {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (i : Fin 3) (x : Space) :
    strainRateApply (velocity vort) x (e3 (i + 1)) i =
      ((pd3 i (pd3 i (newton3 (fun y ↦ vort y (i + 2)))) x -
          pd3 (i + 1) (pd3 (i + 1) (newton3 (fun y ↦ vort y (i + 2)))) x) +
        pd3 (i + 1) (pd3 (i + 2) (newton3 (fun y ↦ vort y (i + 1)))) x -
        pd3 i (pd3 (i + 2) (newton3 (fun y ↦ vort y i))) x) / 2 := by
  rw [strainRateApply_axis_apply ((contDiff_velocity hvort hc).differentiable (by simp) x)]
  simp only [velocity_partial_eq_hessians hvort hc]
  have h11 : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
  have h12 : i + 1 + 2 = i := by fin_cases i <;> rfl
  simp only [h11, h12]
  ring

theorem strain_axis_symm {u : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) (i j : Fin 3) :
    strainRateApply u x (e3 j) i = strainRateApply u x (e3 i) j := by
  rw [strainRateApply_axis_apply hu, strainRateApply_axis_apply hu, add_comm]

theorem strain_diagonal_eq_principalValue {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (i : Fin 3) (x : Space) :
    (strainRateApply (velocity vort) x (e3 i) i : ℂ) =
      (3 / (4 * Real.pi) : ℝ) *
        (NS.Lit.CZ.pvOp (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i (i + 1))
          (fun y ↦ (vort y (i + 2) : ℂ)) x -
        NS.Lit.CZ.pvOp (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i (i + 2))
          (fun y ↦ (vort y (i + 1) : ℂ)) x) := by
  have hs (k : Fin 3) : ContDiff ℝ ∞ (fun y ↦ vort y k) := contDiff_euclidean.mp hvort k
  have hcs (k : Fin 3) : HasCompactSupport (fun y ↦ vort y k) :=
    hc.comp_left (g := fun z : Space ↦ z k) rfl
  have hi1 : i ≠ i + 1 := by fin_cases i <;> decide
  have hi2 : i ≠ i + 2 := by fin_cases i <;> decide
  rw [strain_diagonal_eq_hessians hvort hc]
  push_cast
  rw [newtonianHessian_eq_principalValue (hs _) (hcs _) _ _ hi1,
    newtonianHessian_eq_principalValue (hs _) (hcs _) _ _ hi2]
  push_cast
  ring

theorem strain_cyclic_eq_principalValue {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (i : Fin 3) (x : Space) :
    (strainRateApply (velocity vort) x (e3 (i + 1)) i : ℂ) =
      (-(3 / (8 * Real.pi) : ℝ) : ℂ) *
        (NS.Lit.CZ.pvOp (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i (i + 1))
          (fun y ↦ (vort y (i + 2) : ℂ)) x +
        NS.Lit.CZ.pvOp (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct (i + 1) (i + 2))
          (fun y ↦ (vort y (i + 1) : ℂ)) x -
        NS.Lit.CZ.pvOp (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i (i + 2))
          (fun y ↦ (vort y i : ℂ)) x) := by
  have hs (k : Fin 3) : ContDiff ℝ ∞ (fun y ↦ vort y k) := contDiff_euclidean.mp hvort k
  have hcs (k : Fin 3) : HasCompactSupport (fun y ↦ vort y k) :=
    hc.comp_left (g := fun z : Space ↦ z k) rfl
  have h12 : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  have hi2 : i ≠ i + 2 := by fin_cases i <;> decide
  rw [strain_cyclic_eq_hessians hvort hc]
  push_cast
  rw [newtonianHessian_sub_eq_principalValue (hs _) (hcs _),
    newtonianHessian_eq_principalValue (hs _) (hcs _) _ _ h12,
    newtonianHessian_eq_principalValue (hs _) (hcs _) _ _ hi2]
  push_cast
  ring

private theorem continuous_hessian {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (i j : Fin 3) :
    Continuous (pd3 i (pd3 j (newton3 f))) :=
  (Lit3.newton3_poisson_aux_pdSmooth _
    (Lit3.newton3_poisson_aux_pdSmooth _ (Lit3.newton3_smooth _ hf hc).1 j) i).continuous

theorem exists_eLpNorm_strain_diagonal_le (i : Fin 3) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ vort : Space → Space, ContDiff ℝ ∞ vort → HasCompactSupport vort →
      eLpNorm (fun x ↦ strainRateApply (velocity vort) x (e3 i) i) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm vort (ENNReal.ofReal p) volume := by
  have hi1 : i ≠ i + 1 := by fin_cases i <;> decide
  have hi2 : i ≠ i + 2 := by fin_cases i <;> decide
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_eLpNorm_newtonianHessian_le i (i + 1) hi1 p hp
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_eLpNorm_newtonianHessian_le i (i + 2) hi2 p hp
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro vort hvort hc
  have hs (k : Fin 3) : ContDiff ℝ ∞ (fun y ↦ vort y k) := contDiff_euclidean.mp hvort k
  have hcs (k : Fin 3) : HasCompactSupport (fun y ↦ vort y k) :=
    hc.comp_left (g := fun z : Space ↦ z k) rfl
  have hcoord (k : Fin 3) : eLpNorm (fun y ↦ vort y k) (ENNReal.ofReal p) volume ≤
      eLpNorm vort (ENNReal.ofReal p) volume :=
    eLpNorm_mono (fun x ↦ PiLp.norm_apply_le (vort x) k)
  let A := pd3 i (pd3 (i + 1) (newton3 (fun y ↦ vort y (i + 2))))
  let B := pd3 i (pd3 (i + 2) (newton3 (fun y ↦ vort y (i + 1))))
  have hA : Continuous A := continuous_hessian (hs _) (hcs _) _ _
  have hB : Continuous B := continuous_hessian (hs _) (hcs _) _ _
  have hbA := (hb₁ _ (hs _) (hcs _)).trans (mul_le_mul_right (hcoord (i + 2)) _)
  have hbB := (hb₂ _ (hs _) (hcs _)).trans (mul_le_mul_right (hcoord (i + 1)) _)
  have hp' : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  simp_rw [strain_diagonal_eq_hessians hvort hc]
  change eLpNorm (-A + B) (ENNReal.ofReal p) volume ≤ _
  calc eLpNorm (-A + B) (ENNReal.ofReal p) volume
      ≤ eLpNorm (-A) (ENNReal.ofReal p) volume + eLpNorm B (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hA.neg.aestronglyMeasurable hB.aestronglyMeasurable hp'
    _ = eLpNorm A (ENNReal.ofReal p) volume + eLpNorm B (ENNReal.ofReal p) volume := by
      rw [eLpNorm_neg]
    _ ≤ ENNReal.ofReal C₁ * eLpNorm vort (ENNReal.ofReal p) volume +
        ENNReal.ofReal C₂ * eLpNorm vort (ENNReal.ofReal p) volume := add_le_add hbA hbB
    _ = _ := by rw [ENNReal.ofReal_add hC₁ hC₂, add_mul]

theorem exists_eLpNorm_strain_cyclic_le (i : Fin 3) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ vort : Space → Space, ContDiff ℝ ∞ vort → HasCompactSupport vort →
      eLpNorm (fun x ↦ strainRateApply (velocity vort) x (e3 (i + 1)) i) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm vort (ENNReal.ofReal p) volume := by
  have h12 : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  have hi2 : i ≠ i + 2 := by fin_cases i <;> decide
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_eLpNorm_newtonianHessian_sub_le i (i + 1) p hp
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_eLpNorm_newtonianHessian_le (i + 1) (i + 2) h12 p hp
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_eLpNorm_newtonianHessian_le i (i + 2) hi2 p hp
  refine ⟨C₀ + C₁ + C₂, add_nonneg (add_nonneg hC₀ hC₁) hC₂, ?_⟩
  intro vort hvort hc
  have hs (k : Fin 3) : ContDiff ℝ ∞ (fun y ↦ vort y k) := contDiff_euclidean.mp hvort k
  have hcs (k : Fin 3) : HasCompactSupport (fun y ↦ vort y k) :=
    hc.comp_left (g := fun z : Space ↦ z k) rfl
  have hcoord (k : Fin 3) : eLpNorm (fun y ↦ vort y k) (ENNReal.ofReal p) volume ≤
      eLpNorm vort (ENNReal.ofReal p) volume :=
    eLpNorm_mono (fun x ↦ PiLp.norm_apply_le (vort x) k)
  let D := fun x ↦ pd3 i (pd3 i (newton3 (fun y ↦ vort y (i + 2)))) x -
    pd3 (i + 1) (pd3 (i + 1) (newton3 (fun y ↦ vort y (i + 2)))) x
  let A := pd3 (i + 1) (pd3 (i + 2) (newton3 (fun y ↦ vort y (i + 1))))
  let B := pd3 i (pd3 (i + 2) (newton3 (fun y ↦ vort y i)))
  have hD : Continuous D := (continuous_hessian (hs (i + 2)) (hcs (i + 2)) i i).sub
    (continuous_hessian (hs (i + 2)) (hcs (i + 2)) (i + 1) (i + 1))
  have hA : Continuous A := continuous_hessian (hs (i + 1)) (hcs (i + 1)) (i + 1) (i + 2)
  have hB : Continuous B := continuous_hessian (hs i) (hcs i) i (i + 2)
  have hbD := (hb₀ (fun y ↦ vort y (i + 2)) (hs (i + 2)) (hcs (i + 2))).trans
    (mul_le_mul_right (hcoord (i + 2)) _)
  have hbA := (hb₁ (fun y ↦ vort y (i + 1)) (hs (i + 1)) (hcs (i + 1))).trans
    (mul_le_mul_right (hcoord (i + 1)) _)
  have hbB := (hb₂ (fun y ↦ vort y i) (hs i) (hcs i)).trans
    (mul_le_mul_right (hcoord i) _)
  have hp' : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  have hpoint (x : Space) : ‖strainRateApply (velocity vort) x (e3 (i + 1)) i‖ ≤
      ‖(D + A - B) x‖ := by
    rw [strain_cyclic_eq_hessians hvort hc]
    change ‖(D x + A x - B x) / 2‖ ≤ ‖D x + A x - B x‖
    rw [norm_div, show ‖(2 : ℝ)‖ = 2 by norm_num]
    exact div_le_self (norm_nonneg _) (by norm_num)
  calc eLpNorm (fun x ↦ strainRateApply (velocity vort) x (e3 (i + 1)) i)
        (ENNReal.ofReal p) volume
      ≤ eLpNorm (D + A - B) (ENNReal.ofReal p) volume := by
        exact eLpNorm_mono hpoint
    _ ≤ eLpNorm (D + A) (ENNReal.ofReal p) volume + eLpNorm B (ENNReal.ofReal p) volume :=
      by
        exact eLpNorm_sub_le (f := D + A) (g := B)
          (hD.add hA).aestronglyMeasurable hB.aestronglyMeasurable hp'
    _ ≤ (eLpNorm D (ENNReal.ofReal p) volume + eLpNorm A (ENNReal.ofReal p) volume) +
        eLpNorm B (ENNReal.ofReal p) volume :=
      by
        exact add_le_add (eLpNorm_add_le (f := D) (g := A)
          hD.aestronglyMeasurable hA.aestronglyMeasurable hp') le_rfl
    _ ≤ (ENNReal.ofReal C₀ * eLpNorm vort (ENNReal.ofReal p) volume +
        ENNReal.ofReal C₁ * eLpNorm vort (ENNReal.ofReal p) volume) +
        ENNReal.ofReal C₂ * eLpNorm vort (ENNReal.ofReal p) volume :=
      by
        exact add_le_add (add_le_add hbD hbA) hbB
    _ = _ := by rw [ENNReal.ofReal_add (add_nonneg hC₀ hC₁) hC₂,
      ENNReal.ofReal_add hC₀ hC₁, add_mul, add_mul]

/-- Every coordinate entry is controlled; symmetry supplies the other
three off-diagonal entries without another analytic estimate. -/
theorem exists_eLpNorm_strain_entry_le (i j : Fin 3) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ vort : Space → Space, ContDiff ℝ ∞ vort → HasCompactSupport vort →
      eLpNorm (fun x ↦ strainRateApply (velocity vort) x (e3 j) i) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm vort (ENNReal.ofReal p) volume := by
  have hcases : i = j ∨ j = i + 1 ∨ i = j + 1 := by fin_cases i <;> fin_cases j <;> decide
  rcases hcases with rfl | rfl | hij
  · exact exists_eLpNorm_strain_diagonal_le _ p hp
  · exact exists_eLpNorm_strain_cyclic_le _ p hp
  · obtain ⟨C, hC, hb⟩ := exists_eLpNorm_strain_cyclic_le j p hp
    refine ⟨C, hC, ?_⟩
    intro vort hvort hc
    have heq (x : Space) := strain_axis_symm
      ((contDiff_velocity hvort hc).differentiable (by simp) x) i j
    simp_rw [heq, hij]
    exact hb vort hvort hc

/-- The strain operator is mathlib's self-adjoint part of the actual gradient. -/
abbrev strainOperator (u : Space → Space) (x : Space) : Space →L[ℝ] Space :=
  (selfAdjointPart ℝ (fderiv ℝ u x) : Space →L[ℝ] Space)

theorem strainOperator_apply (u : Space → Space) (x v : Space) :
    strainOperator u x v = strainRateApply u x v := by
  have htrans : fderivTransposeApply u x v = (fderiv ℝ u x).adjoint v := by
    ext i
    have h := ContinuousLinearMap.adjoint_inner_right (fderiv ℝ u x) (e3 i) v
    simpa [fderivTransposeApply, e3, Pi.single_apply, EuclideanSpace.inner_single_left] using h.symm
  simp [strainOperator, selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint,
    strainRateApply, htrans]

theorem continuous_strainOperator {u : Space → Space} (hu : ContDiff ℝ ∞ u) :
    Continuous (strainOperator u) :=
  continuous_subtype_val.comp ((continuous_selfAdjointPart ℝ (Space →L[ℝ] Space)).comp
    (hu.continuous_fderiv (by simp)))

/-- The real operator estimate is the one-slot case of OpenAI's general
multilinear estimate, transported through mathlib's isometric currying. -/
theorem norm_linearMap_le_sum_axes (A : Space →L[ℝ] Space) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (e3 i)‖ := by
  have h := EulerSobolevDerivativeNorm.multilinear_norm_le_coordinate_sum 3 1
    ((continuousMultilinearCurryFin1 ℝ Space Space).symm A)
  rw [(continuousMultilinearCurryFin1 ℝ Space Space).symm.norm_map] at h
  simp only [continuousMultilinearCurryFin1_symm_apply] at h
  have he : (∑ w : Fin 1 → Fin 3, ‖A (EuclideanSpace.single (w 0) 1)‖) =
      ∑ i : Fin 3, ‖A (e3 i)‖ := by
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3))
    intro w
    rfl
  exact h.trans_eq he

theorem norm_strainOperator_le_sum_entries (u : Space → Space) (x : Space) :
    ‖strainOperator u x‖ ≤ ∑ j : Fin 3, ∑ i : Fin 3,
      ‖strainRateApply u x (e3 j) i‖ := by
  apply (norm_linearMap_le_sum_axes (strainOperator u x)).trans
  apply Finset.sum_le_sum
  intro j _
  rw [strainOperator_apply]
  exact EulerMeanCutoffCurl.norm_le_sum_coordinates _

/-- The actual Biot–Savart strain, in operator norm, inherits the imported
singular-integral bound for every finite exponent greater than one. The
constant is independent of the smooth compactly supported vorticity. -/
theorem exists_eLpNorm_strainOperator_le (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ vort : Space → Space, ContDiff ℝ ∞ vort → HasCompactSupport vort →
      eLpNorm (strainOperator (velocity vort)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm vort (ENNReal.ofReal p) volume := by
  choose C hC hb using fun j i : Fin 3 ↦ exists_eLpNorm_strain_entry_le i j p hp
  refine ⟨∑ j, ∑ i, C j i, Finset.sum_nonneg (fun j _ ↦
    Finset.sum_nonneg (fun i _ ↦ hC j i)), ?_⟩
  intro vort hvort hc
  have hS := continuous_strainOperator (contDiff_velocity hvort hc)
  have hentry (j i : Fin 3) :
      Continuous (fun x ↦ strainRateApply (velocity vort) x (e3 j) i) := by
    simp_rw [← strainOperator_apply]
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      (hS.clm_apply continuous_const)
  let H (j i : Fin 3) : Space → ℝ :=
    fun x ↦ ‖strainRateApply (velocity vort) x (e3 j) i‖
  have hH (j i : Fin 3) : Continuous (H j i) := (hentry j i).norm
  have hsum (j : Fin 3) : Continuous (∑ i, H j i) := by
    have he : (∑ i, H j i) = fun x ↦ ∑ i, H j i x := by
      funext x
      simp only [Finset.sum_apply]
    rw [he]
    exact continuous_finsetSum Finset.univ (fun i _ ↦ hH j i)
  have hp' : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  have hdom (x : Space) : ‖strainOperator (velocity vort) x‖ ≤ (∑ j, ∑ i, H j i) x := by
    simpa only [Finset.sum_apply] using norm_strainOperator_le_sum_entries (velocity vort) x
  have hconstants : ENNReal.ofReal (∑ j, ∑ i, C j i) = ∑ j, ∑ i, ENNReal.ofReal (C j i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ Finset.sum_nonneg (fun i _ ↦ hC j i))]
    apply Finset.sum_congr rfl
    intro j _
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hC j i)
  calc eLpNorm (strainOperator (velocity vort)) (ENNReal.ofReal p) volume
      ≤ eLpNorm (∑ j, ∑ i, H j i) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_ae_real (Filter.Eventually.of_forall hdom)
    _ ≤ ∑ j, eLpNorm (∑ i, H j i) (ENNReal.ofReal p) volume :=
      eLpNorm_sum_le (fun j _ ↦ (hsum j).aestronglyMeasurable) hp'
    _ ≤ ∑ j, ∑ i, eLpNorm (H j i) (ENNReal.ofReal p) volume :=
      Finset.sum_le_sum (fun j _ ↦
        eLpNorm_sum_le (fun i _ ↦ (hH j i).aestronglyMeasurable) hp')
    _ ≤ ∑ j, ∑ i, ENNReal.ofReal (C j i) * eLpNorm vort (ENNReal.ofReal p) volume := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      simpa only [H, eLpNorm_norm] using hb j i vort hvort hc
    _ = _ := by simp only [hconstants, Finset.sum_mul]

theorem memLp_strainOperator {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (p : ℝ) (hp : 1 < p) :
    MemLp (strainOperator (velocity vort)) (ENNReal.ofReal p) volume := by
  obtain ⟨C, _, hb⟩ := exists_eLpNorm_strainOperator_le p hp
  have hv : MemLp vort (ENNReal.ofReal p) volume :=
    hvort.continuous.memLp_of_hasCompactSupport hc
  exact ⟨(continuous_strainOperator (contDiff_velocity hvort hc)).aestronglyMeasurable,
    (hb vort hvort hc).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.eLpNorm_lt_top)⟩

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart
