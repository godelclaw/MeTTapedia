import Mettapedia.Analysis.LongitudinalHelicityBudget

/-!
# Centering the curl-helicity factor without altering radial derivatives

A skew correction to a first jet subtracts `rho*a` from its curl and
preserves every radial derivative. This is an algebraic device for reusing
the absorption estimates, not the derivative of an asserted new field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CurlHelicityCentering

open WeightedCurlCancellation WeightedCurlHelicity LongitudinalHelicityBudget EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) (j : Fin 3) : R3 :=
  D j + (ρ / 2) • cross (EuclideanSpace.single j 1) a

theorem inner_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) (j : Fin 3) :
    ⟪a, shiftJet ρ a D j⟫ = ⟪a, D j⟫ := by
  simp only [shiftJet, inner_add_right, real_inner_smul_right, inner_cross_self,
    mul_zero, add_zero]

theorem curlJet_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    curlJet (shiftJet ρ a D) = curlJet D - ρ • a := by
  ext i
  fin_cases i <;>
    simp [curlJet, shiftJet, cross, cross_apply, Matrix.cons_val_two] <;> ring

theorem helicity_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    helicity a (shiftJet ρ a D) = helicity a D - ρ * ‖a‖ ^ 2 := by
  rw [helicity, curlJet_shiftJet, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rfl

theorem radialDensity_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    radialDensity a (shiftJet ρ a D) = radialDensity a D := by
  simp only [radialDensity, inner_shiftJet]

def centeredDefect (ρ : ℝ) (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 4 * longitudinalAmplitude a D * (helicity a D - ρ * ‖a‖ ^ 2)

def centeredHelicityDensity (ρ : ℝ) (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 6 * (helicity a D - ρ * ‖a‖ ^ 2) ^ 2

def centeredDirectionalDensity (ρ : ℝ) (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 4 * longitudinalAmplitude a D ^ 2 / amplitudeGradientSquare a D *
    (helicity a D - ρ * ‖a‖ ^ 2) ^ 2

theorem longitudinalDefect_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    longitudinalDefect a (shiftJet ρ a D) = centeredDefect ρ a D := by
  simp only [longitudinalDefect, centeredDefect, longitudinalAmplitude, inner_shiftJet, helicity_shiftJet]

theorem helicityDensity_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    helicityDensity a (shiftJet ρ a D) = centeredHelicityDensity ρ a D := by
  simp only [helicityDensity, centeredHelicityDensity, helicity_shiftJet]

theorem directionalHelicityDensity_shiftJet (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    directionalHelicityDensity a (shiftJet ρ a D) = centeredDirectionalDensity ρ a D := by
  simp only [directionalHelicityDensity, centeredDirectionalDensity, longitudinalAmplitude,
    amplitudeGradientSquare, inner_shiftJet, helicity_shiftJet]

theorem centeredDirectionalDensity_nonneg (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    0 ≤ centeredDirectionalDensity ρ a D := by
  rw [← directionalHelicityDensity_shiftJet]
  exact directionalHelicityDensity_nonneg _ _

theorem centeredDirectionalDensity_le (ρ : ℝ) (a : R3) (D : Fin 3 → R3) :
    centeredDirectionalDensity ρ a D ≤ centeredHelicityDensity ρ a D := by
  rw [← directionalHelicityDensity_shiftJet, ← helicityDensity_shiftJet]
  exact directionalHelicityDensity_le _ _

theorem abs_centeredDefect_le (ρ : ℝ) (a : R3) (D : Fin 3 → R3) (η : ℝ) (hη : 0 < η) :
    |centeredDefect ρ a D| ≤ η * radialDensity a D + centeredDirectionalDensity ρ a D / (4 * η) := by
  simpa only [longitudinalDefect_shiftJet, radialDensity_shiftJet, directionalHelicityDensity_shiftJet]
    using LongitudinalHelicityBudget.abs_longitudinalDefect_le a (shiftJet ρ a D) η hη

theorem centeredDirectionalDensity_zero (a : R3) (D : Fin 3 → R3) :
    centeredDirectionalDensity 0 a D = directionalHelicityDensity a D := by
  simp [centeredDirectionalDensity, directionalHelicityDensity]

theorem centeredDirectionalDensity_eq_zero_of_curl_eq (ρ : ℝ) (a : R3) (D : Fin 3 → R3)
    (h : curlJet D = ρ • a) : centeredDirectionalDensity ρ a D = 0 := by
  simp [centeredDirectionalDensity, helicity, h, real_inner_smul_right]

theorem continuous_centeredDefect {X : Type*} [TopologicalSpace X]
    (ρ : ℝ) (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ centeredDefect ρ (a x) (fun j ↦ D j x)) :=
  ((ha.norm.pow 4).mul (continuous_finsetSum _ (fun j _ ↦
    ((PiLp.continuous_apply 2 _ j).comp ha).mul (ha.inner (hD j))))).mul
      ((continuous_helicity a D ha hD).sub ((ha.norm.pow 2).const_mul ρ))

theorem continuous_centeredHelicityDensity {X : Type*} [TopologicalSpace X]
    (ρ : ℝ) (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ centeredHelicityDensity ρ (a x) (fun j ↦ D j x)) :=
  (ha.norm.pow 6).mul (((continuous_helicity a D ha hD).sub ((ha.norm.pow 2).const_mul ρ)).pow 2)

theorem measurable_centeredDirectionalDensity {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (ρ : ℝ) (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Measurable (fun x ↦ centeredDirectionalDensity ρ (a x) (fun j ↦ D j x)) := by
  have hA : Continuous (fun x ↦ longitudinalAmplitude (a x) (fun j ↦ D j x)) :=
    continuous_finsetSum _ (fun j _ ↦
      ((PiLp.continuous_apply 2 _ j).comp ha).mul (ha.inner (hD j)))
  have hB : Continuous (fun x ↦ amplitudeGradientSquare (a x) (fun j ↦ D j x)) :=
    continuous_finsetSum _ (fun j _ ↦ (ha.inner (hD j)).pow 2)
  exact (((ha.norm.pow 4).mul (hA.pow 2)).measurable.div hB.measurable).mul
    (((continuous_helicity a D ha hD).sub ((ha.norm.pow 2).const_mul ρ)).pow 2).measurable

end Mettapedia.Analysis.CurlHelicityCentering
