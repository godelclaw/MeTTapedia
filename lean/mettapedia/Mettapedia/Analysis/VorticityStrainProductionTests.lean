import Mettapedia.Analysis.VorticityStrainProduction

/-!
# A perfectly aligned pancake jet still has anisotropic production

The gradient is trace-free, its axial vector lies in its expanding plane,
and the vorticity jet is divergence-free. Its normal derivative vanishes,
but its curl points in the compressing normal direction. The combined
weighted production is positive. This is an algebraic compatibility test,
not a constructed periodic Navier–Stokes solution or blowup example.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.VorticityStrainProductionTests

open scoped RealInnerProductSpace
open VorticityJetSource VorticityStrainProduction WeightedCurlCancellation RegularizedProjection
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def pancakeRows (σ : ℝ) : Fin 3 → R3 :=
  ![WithLp.toLp 2 ![σ, 0, 0], WithLp.toLp 2 ![0, σ, -1/2], WithLp.toLp 2 ![0, 1/2, -2*σ]]

def tangentialJet : Fin 3 → R3 := ![EuclideanSpace.single 1 1, 0, 0]

theorem pancakeRows_trace (σ : ℝ) : (∑ j : Fin 3, pancakeRows σ j j) = 0 := by
  simp [pancakeRows, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem pancakeRows_axial (σ : ℝ) : axialVector (pancakeRows σ) = EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> norm_num [axialVector, pancakeRows, Matrix.cons_val_two]

theorem tangentialJet_divergence : (∑ j : Fin 3, tangentialJet j j) = 0 := by
  simp [tangentialJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem tangentialJet_curl : curlJet tangentialJet = EuclideanSpace.single 2 1 := by
  ext i
  fin_cases i <;> simp [curlJet, tangentialJet, Matrix.cons_val_two]

theorem pancake_axial_aligned (σ : ℝ) :
    rowAction (strainRows (pancakeRows σ)) (EuclideanSpace.single 0 1) =
      σ • EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [rowAction, strainRows, pancakeRows,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.cons_val_two]

theorem pancake_curl_compressed (σ : ℝ) :
    rowAction (strainRows (pancakeRows σ)) (EuclideanSpace.single 2 1) =
      (-2*σ) • EuclideanSpace.single 2 1 := by
  ext i
  fin_cases i <;> simp [rowAction, strainRows, pancakeRows,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.cons_val_two]
  all_goals ring

theorem pancake_shift_rankOne (σ : ℝ) :
    scalarShift σ (strainRows (pancakeRows σ)) = rankOneRows (-3*σ) (EuclideanSpace.single 2 1) := by
  funext m
  ext j
  fin_cases m <;> fin_cases j <;>
    simp [scalarShift, strainRows, pancakeRows, rankOneRows, Matrix.cons_val_two] <;> ring

theorem tangentialJet_normalDerivative_zero :
    (∑ m : Fin 3, (EuclideanSpace.single 2 (1 : ℝ)) m • tangentialJet m) = 0 := by
  simp [tangentialJet, Matrix.cons_val_two]

theorem pancake_source (σ : ℝ) :
    source (strainRows (pancakeRows σ)) tangentialJet = (-2*σ) • EuclideanSpace.single 2 1 := by
  have h : source (scalarShift σ (strainRows (pancakeRows σ))) tangentialJet = 0 := by
    rw [pancake_shift_rankOne, source_rankOneRows, tangentialJet_normalDerivative_zero]
    simp
  rw [source_scalarShift, tangentialJet_curl] at h
  have he := eq_neg_of_add_eq_zero_left h
  simpa only [neg_smul, neg_mul] using he

theorem pancake_weightedProduction (σ : ℝ) :
    weightedProduction 1 (axialVector (pancakeRows σ)) (curlJet tangentialJet)
      tangentialJet (strainRows (pancakeRows σ)) = 6*σ := by
  rw [pancakeRows_axial, tangentialJet_curl]
  have hc : coefficient 1 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (EuclideanSpace.single 2 1) = 0 := by
    simp [coefficient, EuclideanSpace.inner_single_left]
  have hr : residual 1 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (EuclideanSpace.single 2 1) =
      EuclideanSpace.single 2 1 := by simp [RegularizedProjection.residual, hc]
  have he : energy 1 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (EuclideanSpace.single 2 1) = 1 := by
    simp [energy, hr, hc, PiLp.norm_single]
  simp only [weightedProduction, hc, hr, he, pancake_axial_aligned, pancake_curl_compressed,
    pancake_source, PiLp.norm_single, Real.norm_eq_abs, abs_one, one_pow, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  norm_num

theorem positive_aligned_pancake_production (σ : ℝ) (hσ : 0 < σ) :
    0 < weightedProduction 1 (axialVector (pancakeRows σ)) (curlJet tangentialJet)
      tangentialJet (strainRows (pancakeRows σ)) := by
  rw [pancake_weightedProduction]
  positivity

end Mettapedia.Analysis.VorticityStrainProductionTests
