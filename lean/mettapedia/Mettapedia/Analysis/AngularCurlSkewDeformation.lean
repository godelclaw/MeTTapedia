import Mettapedia.Analysis.AngularCurlTransport

/-!
# Rotational angular transport as longitudinal helicity

The skew matrix uses the derivative-first convention: its `(j,k)` entry
is half the oriented vorticity component. Its angular stress contraction
reduces to a trace term and, for divergence-free first jets, to the negative
longitudinal-helicity density. No sign is assigned to that density.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace
open WeightedCurlCancellation EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def skewDeformation (a : R3) : Fin 3 → Fin 3 → ℝ :=
  ![![0, a 2 / 2, -a 1 / 2], ![-a 2 / 2, 0, a 0 / 2], ![a 1 / 2, -a 0 / 2, 0]]

theorem skewDeformation_adjoint_pairing (a H : R3) (J : Fin 3 → R3) :
    (∑ j : Fin 3, ∑ k : Fin 3, skewDeformation a j k * ⟪curlJetAdjoint H j, J k⟫) =
      (⟪a, H⟫ * (∑ k : Fin 3, J k k) - ∑ k : Fin 3, H k * ⟪a, J k⟫) / 2 := by
  simp [skewDeformation, curlJetAdjoint, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem deformationWork_add (a : R3) (D : Fin 3 → R3)
    (B C : Fin 3 → Fin 3 → ℝ) :
    deformationWork a D (fun j k ↦ B j k + C j k) = deformationWork a D B + deformationWork a D C := by
  simp only [deformationWork, add_mul, Finset.sum_add_distrib]

theorem deformationWork_skew_eq_trace (a : R3) (D : Fin 3 → R3) :
    deformationWork a D (skewDeformation a) =
      ‖a‖ ^ 2 * ⟪a, angularCurl a D⟫ * (∑ j : Fin 3, angularJet a D j j) := by
  have h := skewDeformation_adjoint_pairing a (angularCurl a D) (angularJet a D)
  simp only [inner_angularJet, mul_zero, Finset.sum_const_zero, sub_zero] at h
  calc
    _ = (2 * ‖a‖ ^ 2) *
        (∑ j : Fin 3, ∑ k : Fin 3, skewDeformation a j k *
          ⟪curlJetAdjoint (angularCurl a D) j, angularJet a D k⟫) := by
      simp only [deformationWork, deformationStress_eq_angularJet, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [h]; ring

def longitudinalHelicityDensity (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 2 * (∑ j : Fin 3, a j * ⟪a, D j⟫) * ⟪a, angularCurl a D⟫

theorem deformationWork_skew_eq_neg_helicity (a : R3) (D : Fin 3 → R3)
    (hdiv : ∑ j : Fin 3, D j j = 0) :
    deformationWork a D (skewDeformation a) = -longitudinalHelicityDensity a D := by
  have htr : (∑ j : Fin 3, angularJet a D j j) = -(∑ j : Fin 3, a j * ⟪a, D j⟫) := by
    simp only [angularJet, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hdiv, mul_zero, zero_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [deformationWork_skew_eq_trace, htr]
  unfold longitudinalHelicityDensity
  ring

end Mettapedia.Analysis.AngularCurlDecomposition
