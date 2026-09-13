import Mettapedia.Analysis.VorticityJetSource

/-!
# Compatible rotation-source sign tests

The velocity-gradient rows have the prescribed axial vector. The vorticity
jet is trace-free and its curl is the receiver. Its rotational pairing can
have either sign: spatial flux cancellation is not a pointwise cancellation.
These are algebraic jets, not asserted periodic Navier–Stokes solutions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.VorticityJetSourceTests

open scoped RealInnerProductSpace
open VorticityJetSource WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def rotationRows : Fin 3 → R3 :=
  ![0, WithLp.toLp 2 ![0, 0, -1/2], WithLp.toLp 2 ![0, 1/2, 0]]

def vorticityJet (c : ℝ) : Fin 3 → R3 :=
  ![WithLp.toLp 2 ![0, 1, c], 0, WithLp.toLp 2 ![c, 0, 0]]

theorem rotationRows_axial : axialVector rotationRows = WithLp.toLp 2 ![(1 : ℝ), 0, 0] := by
  ext i
  fin_cases i <;> norm_num [axialVector, rotationRows, Matrix.cons_val_two]

theorem rotationRows_strain : strainRows rotationRows = 0 := by
  funext m
  ext j
  fin_cases m <;> fin_cases j <;> norm_num [strainRows, rotationRows, Matrix.cons_val_two]

theorem vorticityJet_divergence (c : ℝ) : (∑ j : Fin 3, vorticityJet c j j) = 0 := by
  simp [vorticityJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem vorticityJet_curl (c : ℝ) : curlJet (vorticityJet c) = WithLp.toLp 2 ![(0 : ℝ), 0, 1] := by
  ext i
  fin_cases i <;> simp [curlJet, vorticityJet, Matrix.cons_val_two]

theorem rotation_source_value (c : ℝ) :
    source rotationRows (vorticityJet c) = WithLp.toLp 2 ![(0 : ℝ), 0, c] := by
  rw [source_eq_strain_add_amplitudeGradient _ _ (vorticityJet_divergence c),
    rotationRows_strain, rotationRows_axial]
  ext i
  fin_cases i <;> simp [source, amplitudeGradient, vorticityJet,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem rotation_pairing_value (c : ℝ) :
    ⟪curlJet (vorticityJet c), source rotationRows (vorticityJet c)⟫ = c := by
  rw [vorticityJet_curl, rotation_source_value]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem rotation_pairing_both_signs :
    ⟪curlJet (vorticityJet 1), source rotationRows (vorticityJet 1)⟫ = 1 ∧
    ⟪curlJet (vorticityJet (-1)), source rotationRows (vorticityJet (-1))⟫ = -1 :=
  ⟨rotation_pairing_value 1, rotation_pairing_value (-1)⟩

end Mettapedia.Analysis.VorticityJetSourceTests
