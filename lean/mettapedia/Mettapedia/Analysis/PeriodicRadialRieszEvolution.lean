import Mettapedia.Analysis.PeriodicRadialRiesz
import Mettapedia.Analysis.UnitTorusSchwartzPeriodization
import Mettapedia.Analysis.RadialRieszCoefficientEvolution
import Mettapedia.Analysis.SignedCrossKernelSeries

/-!
# Differentiable real lifts of the radial Riesz periodization

The Euclidean tensor is assembled as an operator-valued Schwartz function.
Its lattice derivative series gives the derivative of the actual periodic
operator on every real lift, including lattice points. The signed radial
formula is used separately for nonzero image separations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszRegularization

open scoped SchwartzMap ContDiff RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def tensorSchwartz (N : ℕ) : 𝓢(Rd, Rd →L[ℝ] Rd) :=
  ∑ i, ∑ j, (kernel N i j).postcompCLM (Complex.reCLM.smulRight (PeriodicRieszOperator.basisOperator i j))

theorem tensorSchwartz_apply (N : ℕ) (x : Rd) : tensorSchwartz N x = tensor N x := by
  simp only [tensorSchwartz, tensor, sum_apply, SchwartzMap.postcompCLM_apply,
    ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply]

def tensorDerivative (N : ℕ) : 𝓢(Rd, Rd →L[ℝ] Rd →L[ℝ] Rd) :=
  SchwartzMap.fderivCLM ℝ Rd (Rd →L[ℝ] Rd) (tensorSchwartz N)

theorem hasFDerivAt_tensor (N : ℕ) (x : Rd) : HasFDerivAt (tensor N) (tensorDerivative N x) x := by
  have he : (tensorSchwartz (d := d) N : Rd → (Rd →L[ℝ] Rd)) = tensor N := funext (tensorSchwartz_apply N)
  simpa only [tensorDerivative, SchwartzMap.fderivCLM_apply, he] using (tensorSchwartz N).hasFDerivAt x

theorem pairedMaterialRate_tensor_eq (N n : ℕ) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    (a b h da db dh : EuclideanSpace ℝ (Fin 3)) (hh : h ≠ 0) :
    SignedCrossKernel.pairedMaterialRate n (tensor N h) (tensorDerivative N h dh) a b da db =
      SignedRadialStretch.rate n (radialCoefficient N e h)
        (radialCoefficientSlope N e h * ⟪h, dh⟫) a b h da db dh := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const da).const_add a
  have hb := ((hasDerivAt_id (0 : ℝ)).smul_const db).const_add b
  have hv := ((hasDerivAt_id (0 : ℝ)).smul_const dh).const_add h
  have hK := (hasFDerivAt_tensor N (h + (0 : ℝ) • dh)).comp_hasDerivAt 0 hv
  have h₁ := SignedCrossKernel.hasDerivAt_pairedStretch_movingKernel n ha hb hK
  have h₂ := hasDerivAt_pairedStretch_tensor N n e he ha hb hv (by simpa only [id_eq, zero_smul, add_zero] using hh)
  simpa only [Function.comp_def, id_eq, zero_smul, one_smul, add_zero] using h₁.unique h₂

end Mettapedia.Analysis.RadialRieszRegularization

namespace Mettapedia.Analysis.PeriodicRadialRiesz

open UnitTorusLattice UnitTorusPeriodization UnitTorusSchwartzLattice
open scoped SchwartzMap ContDiff RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)

theorem hasSum_tensor_images_lift (N : ℕ) (x : Rd) :
    HasSum (fun z : Lat ↦ RadialRieszRegularization.tensor N ((z : Rd) + x))
      (tensor N (torusProjection x)) := by
  have hs (i j : Fin d) : HasSum
      (fun z : Lat ↦ (RadialRieszRegularization.kernel N i j ((z : Rd) + x)).re •
        PeriodicRieszOperator.basisOperator i j)
      ((entry N i j (torusProjection x)).re • PeriodicRieszOperator.basisOperator i j) := by
    have h := (summable_norm_translates (RadialRieszRegularization.kernel N i j) x).of_norm.hasSum
    change HasSum _ (liftSum (RadialRieszRegularization.kernel N i j) x) at h
    rw [liftSum_eq_periodize] at h
    exact (Complex.reCLM.hasSum h).smul_const _
  exact hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.univ) (fun j _ ↦ hs i j))

theorem liftSum_tensorSchwartz_eq (N : ℕ) (x : Rd) :
    liftSum (RadialRieszRegularization.tensorSchwartz N) x = tensor N (torusProjection x) := by
  simp only [liftSum, RadialRieszRegularization.tensorSchwartz_apply]
  exact (hasSum_tensor_images_lift N x).tsum_eq

def liftedTensorDerivative (N : ℕ) (x : Rd) : Rd →L[ℝ] Rd →L[ℝ] Rd :=
  liftSum (RadialRieszRegularization.tensorDerivative N) x

theorem liftedTensorDerivative_eq_of_projection_eq (N : ℕ) {x y : Rd}
    (h : torusProjection x = torusProjection y) :
    liftedTensorDerivative N x = liftedTensorDerivative N y :=
  liftSum_eq_of_projection_eq _ h

theorem liftedTensorDerivative_eq_periodize (N : ℕ) (x : Rd) :
    liftedTensorDerivative N x =
      periodize (RadialRieszRegularization.tensorDerivative N) (torusProjection x) :=
  liftSum_eq_periodize _ x

theorem hasFDerivAt_tensor_lift (N : ℕ) (x : Rd) :
    HasFDerivAt (fun y : Rd ↦ tensor N (torusProjection y)) (liftedTensorDerivative N x) x := by
  have h := hasFDerivAt_liftSum (RadialRieszRegularization.tensorSchwartz N) x
  have he : liftSum (RadialRieszRegularization.tensorSchwartz (d := d) N) =
      fun y ↦ tensor N (torusProjection y) := funext (liftSum_tensorSchwartz_eq N)
  rw [he] at h
  exact h

theorem contDiff_one_tensor_lift (N : ℕ) : ContDiff ℝ 1 (fun x : Rd ↦ tensor N (torusProjection x)) := by
  have he : liftSum (RadialRieszRegularization.tensorSchwartz (d := d) N) =
      fun y ↦ tensor N (torusProjection y) := funext (liftSum_tensorSchwartz_eq N)
  rw [← he]
  exact contDiff_one_liftSum _

theorem continuous_tensor (N : ℕ) : Continuous (tensor (d := d) N) := by
  have he : periodize (RadialRieszRegularization.tensorSchwartz (d := d) N) = tensor N := by
    funext x
    have hs := liftSum_tensorSchwartz_eq N (representative x)
    simpa only [liftSum_eq_periodize, torusProjection_representative] using hs
  rw [← he]
  exact continuous_periodize _

theorem hasSum_tensorDerivative_images (N : ℕ) (x v : Rd) :
    HasSum (fun z : Lat ↦ RadialRieszRegularization.tensorDerivative N ((z : Rd) + x) v)
      (liftedTensorDerivative N x v) :=
  (ContinuousLinearMap.apply ℝ (Rd →L[ℝ] Rd) v).hasSum
    (summable_norm_translates (RadialRieszRegularization.tensorDerivative N) x).of_norm.hasSum

theorem hasSum_signedImageRates (N n : ℕ) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : torusProjection x ≠ 0)
    (a b da db dh : EuclideanSpace ℝ (Fin 3)) :
    HasSum (fun z : LatticeSubmodule (ι := Fin 3) ↦
      SignedRadialStretch.rate n (RadialRieszRegularization.radialCoefficient N e ((z : EuclideanSpace ℝ (Fin 3)) + x))
        (RadialRieszRegularization.radialCoefficientSlope N e ((z : EuclideanSpace ℝ (Fin 3)) + x) *
          ⟪(z : EuclideanSpace ℝ (Fin 3)) + x, dh⟫) a b ((z : EuclideanSpace ℝ (Fin 3)) + x) da db dh)
      (SignedCrossKernel.pairedMaterialRate n (tensor N (torusProjection x))
        (liftedTensorDerivative N x dh) a b da db) := by
  have hs := SignedCrossKernel.hasSum_pairedMaterialRate n
    (hasSum_tensor_images_lift N x) (hasSum_tensorDerivative_images N x dh) a b da db
  apply hs.congr_fun
  intro z
  have hp : torusProjection ((z : EuclideanSpace ℝ (Fin 3)) + x) = torusProjection x := by
    rw [torusProjection_add, (torusProjection_eq_zero_iff_mem _).mpr z.property, zero_add]
  have hz : (z : EuclideanSpace ℝ (Fin 3)) + x ≠ 0 := by
    have hn := norm_torusProjection_le ((z : EuclideanSpace ℝ (Fin 3)) + x)
    rw [hp] at hn
    exact norm_pos_iff.mp ((norm_pos_iff.mpr hx).trans_le hn)
  exact (RadialRieszRegularization.pairedMaterialRate_tensor_eq N n e he a b _ da db dh hz).symm

end Mettapedia.Analysis.PeriodicRadialRiesz
