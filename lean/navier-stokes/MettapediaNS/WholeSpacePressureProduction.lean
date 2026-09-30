import MettapediaNS.WholeSpacePressureAugmentation
import MettapediaNS.WholeSpaceTimeSmooth

/-!
# Signed evolution of the actual whole-space pressure source

The canonical pressure solves `-Δp = tr((∇u)²)`. Its source below is
the constructed smooth scalar field, and its tangent is evaluated on the
complete unforced Navier–Stokes right-hand side. The material equation
retains the cubic, canonical-pressure and crossed viscous terms. The
last term has no asserted sign.

The pointwise time law applies at every interior time of an actual smooth
NS evolution. It does not assert a finite-history production bound. The
unweighted pressure/source square identity does not identify the selected
observables pointwise; a varying selector still requires its flux terms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureProduction

open Set MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  WholeSpaceViscousEnergy WholeSpaceBetchov MiddleEigenvalueAlgebra
  WholeSpaceOrderEnergy WholeSpacePressureDiffusion WholeSpaceTimeSmooth
  WholeSpaceViscousFlow

/-- The crossed matrix contraction, not the Frobenius norm. -/
def tracePair (A B : GradMatrix) : ℝ := ∑ i, ∑ j, A j i * B i j

/-- The literal first variation of the canonical Poisson source. -/
def sourceTangent (u v : SmoothL2Field Space) : SmoothL2Field ℝ :=
  scaleField 2 (sumField Finset.univ (fun i : Fin 3 ↦
    sumField Finset.univ (fun j : Fin 3 ↦
      scalarProduct (coord (u.directionalField (axis i)) j)
        (coord (v.directionalField (axis j)) i))))

theorem sourceTangent_field (u v : SmoothL2Field Space) (x : Space) :
    (sourceTangent u v).field x = 2 * tracePair (gradMatrix u x) (gradMatrix v x) := by
  simp only [sourceTangent, scaleField_field, sumField_field, scalarProduct_field,
    smul_eq_mul, coord_field, tracePair, gradMatrix]

/-- The actual scalar Laplacian, retaining all three spatial directions. -/
def scalarLaplacian (s : SmoothL2Field ℝ) : SmoothL2Field ℝ :=
  sumField Finset.univ (fun k : Fin 3 ↦
    (s.directionalField (axis k)).directionalField (axis k))

theorem scalarLaplacian_field (s : SmoothL2Field ℝ) (x : Space) :
    (scalarLaplacian s).field x =
      ∑ k : Fin 3, ((s.directionalField (axis k)).directionalField (axis k)).field x := rfl

private theorem sum_directional {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} (s : Finset ι) (A : ι → SmoothL2Field V) (k : Fin 3) :
    (sumField s A).directionalField (axis k) =
      sumField s (fun i ↦ (A i).directionalField (axis k)) :=
  wordField_sum s A (fun _ : Fin 1 ↦ k)

private theorem add_directional {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : SmoothL2Field V) (k : Fin 3) :
    (addField A B).directionalField (axis k) =
      addField (A.directionalField (axis k)) (B.directionalField (axis k)) :=
  wordField_add A B (fun _ : Fin 1 ↦ k)

private theorem grad_add (A B : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (addField A B) x i j = gradMatrix A x i j + gradMatrix B x i j := by
  simp only [gradMatrix, add_directional, addField_field, WithLp.ofLp_add, Pi.add_apply]

private theorem grad_neg (A : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (fieldNeg A) x i j = -gradMatrix A x i j := by
  have h : (fieldNeg A).directionalField (axis j) =
      fieldNeg (A.directionalField (axis j)) := wordField_neg A (fun _ : Fin 1 ↦ j)
  change ((fieldNeg A).directionalField (axis j)).field x i = _
  rw [h]
  rfl

private theorem grad_scale (c : ℝ) (A : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (scaleField c A) x i j = c * gradMatrix A x i j := by
  simp only [gradMatrix, directionalField_field, scaleField_fderiv,
    smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

private theorem grad_directional (u : SmoothL2Field Space) (k : Fin 3)
    (x : Space) (i j : Fin 3) :
    gradMatrix (u.directionalField (axis k)) x i j = hessTensor u x k j i := by
  unfold gradMatrix hessTensor
  rw [directionalField_comm]

private theorem scalar_advection_sum (u : SmoothL2Field Space)
    (s : SmoothL2Field ℝ) (x : Space) :
    (advectionField u s).field x =
      ∑ k : Fin 3, u.field x k * (s.directionalField (axis k)).field x := by
  simp only [advectionField, sumField_field, coordinateProduct_field, smul_eq_mul]

private theorem grad_laplacian (u : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (laplacianField u) x i j =
      ∑ k : Fin 3, gradMatrix ((u.directionalField (axis k)).directionalField
        (axis k)) x i j := by
  have hc (k : Fin 3) :
      (((u.directionalField (axis k)).directionalField (axis k)).directionalField
        (axis j)) =
      (((u.directionalField (axis j)).directionalField (axis k)).directionalField
        (axis k)) := by
    rw [directionalField_comm (u.directionalField (axis k))]
    rw [directionalField_comm u]
  simp only [gradMatrix, laplacianField, sum_directional, sumField_field,
    WithLp.ofLp_sum, Finset.sum_apply, hc]

private theorem grad_rhs (ν : ℝ) (u : SmoothL2Field Space) (x : Space) (i j : Fin 3) :
    gradMatrix (projectedNavierStokesRhs ν u) x i j =
      -(∑ k : Fin 3, u.field x k * hessTensor u x k j i) -
      (∑ k : Fin 3, gradMatrix u x k j * gradMatrix u x i k) -
      gradMatrix (pressureField u) x i j +
      ν * ∑ k : Fin 3, gradMatrix ((u.directionalField (axis k)).directionalField
        (axis k)) x i j := by
  have ha : gradMatrix (advectionField u u) x i j =
      (∑ k : Fin 3, u.field x k * hessTensor u x k j i) +
        ∑ k : Fin 3, gradMatrix u x k j * gradMatrix u x i k := by
    simpa only [coord_directional_field, gradMatrix] using coord_advection_directional_field u j i x
  simp only [projectedNavierStokesRhs, navierStokesRhs, eulerRhs,
    grad_add, grad_neg, grad_scale, grad_laplacian, ha]
  ring

/-- Literal second spatial derivative of the actual crossed source. -/
theorem sourceField_second_directional (u : SmoothL2Field Space) (k : Fin 3) (x : Space) :
    (((sourceField u).directionalField (axis k)).directionalField (axis k)).field x =
      2 * trSq (gradMatrix (u.directionalField (axis k)) x) +
        2 * tracePair (gradMatrix u x)
          (gradMatrix ((u.directionalField (axis k)).directionalField (axis k)) x) := by
  have hc (i j : Fin 3) :
      (coord (u.directionalField (axis j)) i).directionalField (axis k) =
        coord ((u.directionalField (axis k)).directionalField (axis j)) i := by
    apply field_ext
    funext y
    rw [coord_directional_field, directionalField_comm]
    rfl
  have hc₂ (i j : Fin 3) :
      ((coord ((u.directionalField (axis k)).directionalField (axis j)) i).directionalField
        (axis k)).field x =
      gradMatrix ((u.directionalField (axis k)).directionalField (axis k)) x i j := by
    rw [coord_directional_field, directionalField_comm]
    rfl
  simp only [sourceField, sum_directional, scalarProduct_directional, add_directional,
    sumField_field, addField_field, scalarProduct_field, smul_eq_mul, hc, hc₂,
    coord_field, trSq, tracePair, gradMatrix, Fin.sum_univ_three]
  ring

/-- Complete unforced material source law. No matrix is supplied independently
of the smooth velocity and its canonical pressure. -/
theorem source_material_rhs (ν : ℝ) (u : SmoothL2Field Space) (x : Space) :
    (sourceTangent u (projectedNavierStokesRhs ν u)).field x +
      (advectionField u (sourceField u)).field x -
      ν * (scalarLaplacian (sourceField u)).field x =
    -2 * trCube (gradMatrix u x) -
      2 * tracePair (gradMatrix u x) (gradMatrix (pressureField u) x) -
      2 * ν * ∑ k : Fin 3, trSq (gradMatrix (u.directionalField (axis k)) x) := by
  have hs (k : Fin 3) : ((sourceField u).directionalField (axis k)).field x =
      2 * tracePair (gradMatrix u x) (gradMatrix (u.directionalField (axis k)) x) :=
    sourceField_directional_field u k x
  simp only [sourceTangent_field, tracePair, grad_rhs, scalar_advection_sum,
    hs, scalarLaplacian_field, sourceField_second_directional,
    trCube, trSq, Fin.sum_univ_three, grad_directional]
  ring

/-- The actual nonnegative source-square diffusion density. -/
def sourceSquareDiffusion (ν : ℝ) (u : SmoothL2Field Space) (x : Space) : ℝ :=
  2 * ν * ∑ k : Fin 3, (((sourceField u).directionalField (axis k)).field x) ^ 2

theorem sourceSquareDiffusion_nonneg {ν : ℝ} (hν : 0 ≤ ν)
    (u : SmoothL2Field Space) (x : Space) : 0 ≤ sourceSquareDiffusion ν u x := by
  unfold sourceSquareDiffusion
  exact mul_nonneg (mul_nonneg (by norm_num) hν)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

private theorem square_second (s : SmoothL2Field ℝ) (k : Fin 3) (x : Space) :
    (((scalarProduct s s).directionalField (axis k)).directionalField (axis k)).field x =
      2 * ((s.directionalField (axis k)).field x) ^ 2 +
        2 * s.field x * ((s.directionalField (axis k)).directionalField (axis k)).field x := by
  simp only [scalarProduct_directional, add_directional, addField_field,
    scalarProduct_field, smul_eq_mul]
  ring

/-- The square evolution keeps crossed viscous production separate from
the nonnegative diffusion. It is the unweighted source component. -/
theorem source_square_material_rhs (ν : ℝ) (u : SmoothL2Field Space) (x : Space) :
    2 * (sourceField u).field x *
        (sourceTangent u (projectedNavierStokesRhs ν u)).field x +
      (advectionField u (scalarProduct (sourceField u) (sourceField u))).field x -
      ν * (scalarLaplacian (scalarProduct (sourceField u) (sourceField u))).field x =
    -4 * (sourceField u).field x * trCube (gradMatrix u x) -
      4 * (sourceField u).field x *
        tracePair (gradMatrix u x) (gradMatrix (pressureField u) x) -
      4 * ν * (sourceField u).field x *
        (∑ k : Fin 3, trSq (gradMatrix (u.directionalField (axis k)) x)) -
      sourceSquareDiffusion ν u x := by
  have ha : (advectionField u (scalarProduct (sourceField u) (sourceField u))).field x =
      2 * (sourceField u).field x * (advectionField u (sourceField u)).field x := by
    simp only [scalar_advection_sum, scalarProduct_directional, addField_field,
      scalarProduct_field, smul_eq_mul, Fin.sum_univ_three]
    ring
  have hl : (scalarLaplacian (scalarProduct (sourceField u) (sourceField u))).field x =
      2 * (∑ k : Fin 3, (((sourceField u).directionalField (axis k)).field x) ^ 2) +
        2 * (sourceField u).field x * (scalarLaplacian (sourceField u)).field x := by
    simp only [scalarLaplacian_field, square_second, Fin.sum_univ_three]
    ring
  rw [ha, hl]
  calc
    _ = 2 * (sourceField u).field x *
        ((sourceTangent u (projectedNavierStokesRhs ν u)).field x +
          (advectionField u (sourceField u)).field x -
          ν * (scalarLaplacian (sourceField u)).field x) -
        sourceSquareDiffusion ν u x := by unfold sourceSquareDiffusion; ring
    _ = _ := by rw [source_material_rhs]; ring

/-- The crossed viscous contribution to the actual source-square reaction.
This quantity may be positive. -/
def crossedViscousProduction (ν : ℝ) (u : SmoothL2Field Space) (x : Space) : ℝ :=
  -(4 * ν * (sourceField u).field x *
    ∑ k : Fin 3, trSq (gradMatrix (u.directionalField (axis k)) x))

/-- The local strain-gradient density appearing in the completed diffusion
lower bound. Identification with the full candidate Hessian is separate. -/
def strainDerivativeDiffusion (ν : ℝ) (u : SmoothL2Field Space) (x : Space) : ℝ :=
  8 * ν * normSq (gradMatrix u x) *
    ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)

theorem abs_trSq_le_normSq (A : GradMatrix) : |trSq A| ≤ normSq A := by
  have hr : 0 ≤ normSq A := by unfold normSq; positivity
  have hs := trSq_sq_le_normSq_sq A
  rw [← sq_abs (trSq A)] at hs
  exact (sq_le_sq₀ (abs_nonneg _) hr).mp hs

/-- Half the actual local strain-gradient density pays the crossed term,
with no eigenframe or orientation hypothesis. It can retain any common
nonnegative selector in both cost and payment. -/
theorem crossed_viscous_absorption {ν : ℝ} (hν : 0 ≤ ν)
    (u : SmoothL2Field Space) (x : Space) :
    |crossedViscousProduction ν u x| ≤ strainDerivativeDiffusion ν u x / 2 := by
  have hr : 0 ≤ normSq (gradMatrix u x) := by unfold normSq; positivity
  have he : |∑ k : Fin 3, trSq (gradMatrix (u.directionalField (axis k)) x)| ≤
      ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x) := by
    calc
      _ ≤ ∑ k : Fin 3, |trSq (gradMatrix (u.directionalField (axis k)) x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ ↦ abs_trSq_le_normSq _
  have hp := mul_le_mul (abs_trSq_le_normSq (gradMatrix u x)) he (abs_nonneg _) hr
  have hc : 0 ≤ 4 * ν := mul_nonneg (by norm_num) hν
  calc
    _ = (4 * ν) * (|trSq (gradMatrix u x)| *
        |∑ k : Fin 3, trSq (gradMatrix (u.directionalField (axis k)) x)|) := by
      simp only [crossedViscousProduction, sourceField_field, abs_neg, abs_mul,
        abs_of_nonneg (show 0 ≤ (4 : ℝ) from by norm_num), abs_of_nonneg hν]
      ring
    _ ≤ (4 * ν) * (normSq (gradMatrix u x) *
        ∑ k : Fin 3, normSq (gradMatrix (u.directionalField (axis k)) x)) :=
      mul_le_mul_of_nonneg_left hp hc
    _ = _ := by unfold strainDerivativeDiffusion; ring

theorem selected_crossed_viscous_absorption {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a)
    (u : SmoothL2Field Space) (x : Space) :
    a * |crossedViscousProduction ν u x| ≤ a * strainDerivativeDiffusion ν u x / 2 := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (crossed_viscous_absorption hν u x) ha

/-- The native local density has a genuine finite spatial integral on each
smooth prefix; this does not bound its integral over all prefixes. -/
theorem strainDerivativeDiffusion_integrable (ν : ℝ) (u : SmoothL2Field Space) :
    Integrable (strainDerivativeDiffusion ν u) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (fun k _ ↦ normSq_product_integrable u (u.directionalField (axis k)))
  convert h.const_mul (8 * ν) using 1
  funext x
  simp only [strainDerivativeDiffusion, Finset.mul_sum, mul_assoc]

theorem crossedViscousProduction_integrable (ν : ℝ) (u : SmoothL2Field Space) :
    Integrable (crossedViscousProduction ν u) := by
  have h := field_inner_integrable (sourceField u)
    (sumField Finset.univ (fun k : Fin 3 ↦ sourceField (u.directionalField (axis k))))
  simp only [RCLike.inner_apply, conj_trivial, sumField_field, sourceField_field] at h
  convert h.const_mul (-4 * ν) using 1
  funext x
  simp only [crossedViscousProduction, sourceField_field]
  ring

/-- Genuine spatial absorption of the complete crossed term on a smooth
velocity, without assuming any future norm of its evolution. -/
theorem integral_crossed_viscous_absorption {ν : ℝ} (hν : 0 ≤ ν)
    (u : SmoothL2Field Space) :
    (∫ x, |crossedViscousProduction ν u x|) ≤
      (∫ x, strainDerivativeDiffusion ν u x) / 2 := by
  calc
    _ ≤ ∫ x, strainDerivativeDiffusion ν u x / 2 :=
      integral_mono (crossedViscousProduction_integrable ν u).abs
        ((strainDerivativeDiffusion_integrable ν u).div_const 2)
        (crossed_viscous_absorption hν u)
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]

/-- Agreement with the pressure-free RHS used by the evolution interface. -/
theorem projected_rhs_eq (ν : ℝ) (u : SmoothL2Field Space) :
    nsProjectedRhs ν u = projectedNavierStokesRhs ν u := by
  rw [projectedNavierStokesRhs_eq]
  rfl

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical source has the literal time derivative computed from the
full NS tangent, at every interior time of an actual evolution. -/
theorem source_hasDerivAt (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (fun r ↦ (sourceField (U.velocity (projIcc 0 T hT r))).field x)
      ((sourceTangent (U.velocity ⟨t, ht.1.le, ht.2.le⟩)
        (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩))).field x) t := by
  have hd (i j : Fin 3) :
      HasDerivAt (fun r ↦ gradMatrix (U.velocity (projIcc 0 T hT r)) x i j)
        (gradMatrix (projectedNavierStokesRhs ν
          (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) x i j) t := by
    have h : HasDerivAt (fun r ↦ gradMatrix (U.velocity (projIcc 0 T hT r)) x i j)
        (gradMatrix (nsProjectedRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) x i j) t :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
        (((U.timeDeriv hpos).directional j).deriv t ht x)
    simpa only [projected_rhs_eq] using h
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ (hd i j).mul (hd j i)))
  have he : (∑ i : Fin 3, ∑ j : Fin 3,
      (gradMatrix (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) x i j *
          gradMatrix (U.velocity (projIcc 0 T hT t)) x j i +
        gradMatrix (U.velocity (projIcc 0 T hT t)) x i j *
          gradMatrix (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) x j i)) =
      (sourceTangent (U.velocity ⟨t, ht.1.le, ht.2.le⟩)
        (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩))).field x := by
    simp only [sourceTangent_field, tracePair, projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩,
      Fin.sum_univ_three]
    ring
  rw [he] at hs
  simpa only [sourceField_field, trSq, Pi.mul_apply] using hs

set_option backward.isDefEq.respectTransparency.types false in
/-- The material equation holds along the actual physical time history;
the crossed viscosity term is retained with its sign. -/
theorem source_material_evolution (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    deriv (fun r ↦ (sourceField (U.velocity (projIcc 0 T hT r))).field x) t +
      (advectionField (U.velocity ⟨t, ht.1.le, ht.2.le⟩)
        (sourceField (U.velocity ⟨t, ht.1.le, ht.2.le⟩))).field x -
      ν * (scalarLaplacian (sourceField (U.velocity ⟨t, ht.1.le, ht.2.le⟩))).field x =
    -2 * trCube (gradMatrix (U.velocity ⟨t, ht.1.le, ht.2.le⟩) x) -
      2 * tracePair (gradMatrix (U.velocity ⟨t, ht.1.le, ht.2.le⟩) x)
        (gradMatrix (pressureField (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) x) -
      2 * ν * ∑ k : Fin 3,
        trSq (gradMatrix ((U.velocity ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis k)) x) := by
  rw [(source_hasDerivAt U hpos t ht x).deriv]
  exact source_material_rhs ν _ x

set_option backward.isDefEq.respectTransparency.types false in
/-- The source-square time derivative at every actual smooth NS prefix. -/
theorem source_square_hasDerivAt (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (fun r ↦ ((sourceField (U.velocity (projIcc 0 T hT r))).field x) ^ 2)
      (2 * (sourceField (U.velocity ⟨t, ht.1.le, ht.2.le⟩)).field x *
        (sourceTangent (U.velocity ⟨t, ht.1.le, ht.2.le⟩)
          (projectedNavierStokesRhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩))).field x) t := by
  have h := (source_hasDerivAt U hpos t ht x).fun_pow 2
  simpa only [projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] using! h

set_option backward.isDefEq.respectTransparency.types false in
/-- The squared source law on every actual smooth NS history, including
the separate nonnegative source diffusion and signed crossed viscosity. -/
theorem source_square_material_evolution (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    let u := U.velocity ⟨t, ht.1.le, ht.2.le⟩
    deriv (fun r ↦ ((sourceField (U.velocity (projIcc 0 T hT r))).field x) ^ 2) t +
      (advectionField u (scalarProduct (sourceField u) (sourceField u))).field x -
      ν * (scalarLaplacian (scalarProduct (sourceField u) (sourceField u))).field x =
    -4 * (sourceField u).field x * trCube (gradMatrix u x) -
      4 * (sourceField u).field x *
        tracePair (gradMatrix u x) (gradMatrix (pressureField u) x) +
      crossedViscousProduction ν u x - sourceSquareDiffusion ν u x := by
  dsimp only
  rw [(source_square_hasDerivAt U hpos t ht x).deriv]
  convert source_square_material_rhs ν (U.velocity ⟨t, ht.1.le, ht.2.le⟩) x using 1
  unfold crossedViscousProduction
  ring

/-- Identification of the canonical pressure source on the actual evolution,
with solenoidality discharged by the evolution rather than assumed again. -/
theorem canonical_pressure_source (U : NSEvolution ν T hT) (hpos : 0 < T)
    (t : Icc (0 : ℝ) T) :
    traceField (U.pressureForce t) = fieldNeg (sourceField (U.velocity t)) := by
  rw [U.pressureForce_eq hpos]
  exact traceField_pressureField _ (U.solenoidal t)

end NSEvolution

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureProduction
