import Mettapedia.Analysis.EuclideanBilinearCoordinates
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bilinear Schwartz kernels from scalar entries

Finite coordinate assembly preserves the actual Fourier transform and
controls every operator-norm spatial moment by the sum of the entry moments.
The construction uses Euclidean norms for both inputs and the output.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SchwartzBilinearKernel

open MeasureTheory EuclideanBilinearCoordinates
open scoped FourierTransform SchwartzMap RealInnerProductSpace

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℂ I
local notation "V" => EuclideanSpace ℂ J
local notation "W" => EuclideanSpace ℂ K
local notation "Op" => U →L[ℂ] V →L[ℂ] W

local instance : NormedAddCommGroup (V →L[ℂ] W) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (V →L[ℂ] W) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace W := PiLp.completeSpace 2 (fun _ : K ↦ ℂ)
local instance : CompleteSpace (V →L[ℂ] W) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

def lift (s : 𝓢(X, ℂ)) (B : Op) : 𝓢(X, Op) :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight B) s

omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
@[simp] theorem lift_apply (s : 𝓢(X, ℂ)) (B : Op) (x : X) : lift s B x = s x • B := rfl

omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem fourier_lift (s : 𝓢(X, ℂ)) (B : Op) (ξ : X) :
    (𝓕 (lift s B)) ξ = (𝓕 s) ξ • B := by
  simp_rw [SchwartzMap.fourier_coe, Real.fourier_eq, lift_apply, Circle.smul_def, smul_smul]
  exact integral_smul_const _ _

def assemble (s : K → I → J → 𝓢(X, ℂ)) : 𝓢(X, Op) :=
  ∑ i, ∑ j, ∑ l, lift (s i j l) (elementary i j l)

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem assemble_apply (s : K → I → J → 𝓢(X, ℂ)) (x : X) :
    assemble s x = reconstruct (fun i j l ↦ s i j l x) := by
  simp [assemble, reconstruct]

omit [DecidableEq I] [DecidableEq J] in
theorem fourier_assemble (s : K → I → J → 𝓢(X, ℂ)) (ξ : X) :
    (𝓕 (assemble s)) ξ = reconstruct (fun i j l ↦ (𝓕 (s i j l)) ξ) := by
  simp [assemble, FourierTransform.fourier_sum, fourier_lift, reconstruct]

omit [DecidableEq I] [DecidableEq J] in
theorem norm_assemble_le (s : K → I → J → 𝓢(X, ℂ)) (x : X) :
    ‖assemble s x‖ ≤ ∑ i, ∑ j, ∑ l, ‖s i j l x‖ := by
  rw [assemble_apply]
  exact norm_reconstruct_le _

omit [DecidableEq I] [DecidableEq J] in
theorem moment_assemble_le (s : K → I → J → 𝓢(X, ℂ)) (m : ℕ) :
    (∫ x : X, ‖x‖ ^ m * ‖assemble s x‖) ≤
      ∑ i, ∑ j, ∑ l, ∫ x : X, ‖x‖ ^ m * ‖s i j l x‖ := by
  have h1 (i : K) (j : I) : Integrable (fun x : X ↦ ∑ l, ‖x‖ ^ m * ‖s i j l x‖) :=
    integrable_finsetSum _ (fun l _ ↦ (s i j l).integrable_pow_mul volume m)
  have h2 (i : K) : Integrable (fun x : X ↦ ∑ j, ∑ l, ‖x‖ ^ m * ‖s i j l x‖) :=
    integrable_finsetSum _ (fun j _ ↦ h1 i j)
  calc
    _ ≤ ∫ x : X, ∑ i, ∑ j, ∑ l, ‖x‖ ^ m * ‖s i j l x‖ := by
      apply integral_mono ((assemble s).integrable_pow_mul volume m)
        (integrable_finsetSum _ (fun i _ ↦ h2 i))
      intro x
      simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (norm_assemble_le s x)
        (pow_nonneg (norm_nonneg _) m)
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ h2 i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ ↦ h1 i j)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ (fun l _ ↦ (s i j l).integrable_pow_mul volume m)

end Mettapedia.Analysis.SchwartzBilinearKernel
