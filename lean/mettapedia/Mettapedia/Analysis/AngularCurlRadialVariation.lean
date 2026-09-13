import Mettapedia.Analysis.AngularCurlTransport

/-!
# Pointwise radial component of the angular variational gradient

Jet-gradient orthogonality differentiates to cancel every second-jet term
in the radial pairing. The resulting transverse gradient is polynomial,
including at zero amplitude; no normalized direction is required.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem angularJet_add_radial (a : R3) (D : Fin 3 → R3) (c : Fin 3 → ℝ) :
    angularJet a (fun j ↦ D j + c j • a) = angularJet a D := by
  funext j
  simp only [angularJet, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  module

theorem angularCurl_add_radial (a : R3) (D : Fin 3 → R3) (c : Fin 3 → ℝ) :
    angularCurl a (fun j ↦ D j + c j • a) = angularCurl a D := by
  simp only [angularCurl, angularJet_add_radial]

theorem deformationWork_add_radial (a : R3) (D : Fin 3 → R3)
    (c : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    deformationWork a (fun j ↦ D j + c j • a) B = deformationWork a D B := by
  simp only [deformationWork, deformationStress_eq_angularJet,
    angularCurl_add_radial, angularJet_add_radial]

theorem inner_jetGradientRate_value (a : R3) (D : Fin 3 → R3) (v : R3) (E : Fin 3 → R3) (j : Fin 3) :
    ⟪jetGradientRate a D v E j, a⟫ = -⟪jetGradient a D j, v⟫ := by
  simp only [jetGradientRate, jetGradient, inner_sub_left, inner_add_left,
    real_inner_smul_left, inner_curlJetAdjoint, real_inner_self_eq_norm_sq,
    real_inner_comm v a, PiLp.add_apply]
  ring

theorem inner_variationalGradient_value (a : R3) (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3) :
    ⟪variationalGradient a D E, a⟫ = 8 * angularCurlDensity a D := by
  simp only [variationalGradient, inner_sub_left, sum_inner, inner_jetGradientRate_value,
    Finset.sum_neg_distrib, sub_neg_eq_add]
  exact gradient_pairing_self a D

def transverseGradient (a : R3) (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3) : R3 :=
  variationalGradient a D E - (8 * ‖angularCurl a D‖ ^ 2) • a

theorem inner_transverseGradient_value (a : R3) (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3) :
    ⟪transverseGradient a D E, a⟫ = 0 := by
  simp only [transverseGradient, inner_sub_left, inner_variationalGradient_value,
    real_inner_smul_left, real_inner_self_eq_norm_sq, angularCurlDensity]
  ring

/-- Subtracting any scalar multiple of the value from the source changes
only the explicit radial work. No derivative or regularity of the scalar
is needed for this pointwise identity. -/
theorem inner_variationalGradient_source (a : R3) (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3)
    (f : R3) (c : ℝ) :
    ⟪variationalGradient a D E, f⟫ = 8 * ‖angularCurl a D‖ ^ 2 * ⟪a, f⟫ +
      ⟪transverseGradient a D E, f - c • a⟫ := by
  rw [inner_sub_right, real_inner_smul_right, inner_transverseGradient_value, mul_zero, sub_zero]
  simp only [transverseGradient, inner_sub_left, real_inner_smul_left]
  ring

end Mettapedia.Analysis.AngularCurlDecomposition
