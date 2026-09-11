import Mettapedia.Analysis.FiniteCharacterConvolution
import Mathlib.Tactic.NormNum

/-! Regression tests for collected vector convolution and character evaluation. -/

open scoped BigOperators
open Mettapedia.Analysis.FiniteMultiplierLocalization

example : vectorConvolution ({0, 1} : Finset ℤ) {0, 1}
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) 1 = 2 := by
  simp only [vectorConvolution, Finset.sum_filter, Finset.sum_product]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton]

example : (∑ q ∈ ({0, 1, 2} : Finset ℤ),
    ‖vectorConvolution {0, 1} {0, 1} (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) q‖ ^ 2) = 6 := by
  simp only [vectorConvolution, Finset.sum_filter, Finset.sum_product]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton]

example : (∑ q ∈ ({0, 1, 2} : Finset ℤ),
    vectorConvolution {0, 1} {0, 1} (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) q) =
      (∑ _a ∈ ({0, 1} : Finset ℤ), (1 : ℝ)) * ∑ _p ∈ ({0, 1} : Finset ℤ), (1 : ℝ) := by
  simp only [vectorConvolution, Finset.sum_filter, Finset.sum_product]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton]

#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.vectorConvolution_sub
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.sum_norm_vectorConvolution_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.sum_norm_vectorConvolution_sq_le
#print axioms Mettapedia.Analysis.FiniteMultiplierLocalization.sum_character_smul_vectorConvolution
