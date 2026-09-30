import MettapediaNS.WholeSpacePressureLocalization
import MettapediaNS.ViscousMemorySoftExcess

/-!
# Canonical pressure augmentation of the joint memory observable

Adding the squared actual pressure Hessian supplies a second diffusion cost.
Together with the completed observer diffusion, it pays the memory-pressure
gradient pointwise, even under a varying bounded measurable selector. There
is no elliptic localization flux in this payment.

The addition has finite initial cost from the full solenoidal datum and
preserves the sufficient memory-capacity continuation comparison. It also
adds pressure production to the physical evolution. Payment of that signed
production over arbitrary histories is not asserted here. The full matrix
Hessian lower bound and the evolving memory construction remain explicit
application obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureAugmentation

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical EulerMeanPressure WholeSpaceViscousEnergy WholeSpaceBetchov
  MiddleEigenvalueAlgebra WholeSpaceOrderEnergy WholeSpacePressureDiffusion
  WholeSpacePressureLocalization WholeSpaceMemoryEnvelope

/-- The canonical full-fluid pressure, not an independent observer slot. -/
def pressureSquare (u : SmoothL2Field Space) (x : Space) : ℝ :=
  normSq (gradMatrix (pressureField u) x)

theorem pressureSquare_nonneg (u : SmoothL2Field Space) (x : Space) :
    0 ≤ pressureSquare u x := by
  simp only [pressureSquare, normSq]
  positivity

theorem pressureSquare_integrable (u : SmoothL2Field Space) :
    Integrable (pressureSquare u) := normSq_integrable (pressureField u)

/-- The scalar addition has finite datum cost controlled by the velocity
gradient quartic. Solenoidality is used in this actual pressure estimate. -/
theorem integral_pressureSquare_le (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) :
    (∫ x, pressureSquare u x) ≤ ∫ x, normSq (gradMatrix u x) ^ 2 :=
  integral_pressure_hessian_sq_le u hu

private theorem sumField_directional {ι : Type*} (s : Finset ι)
    (A : ι → SmoothL2Field ℝ) (k : Fin 3) :
    (sumField s A).directionalField (axis k) =
      sumField s (fun i ↦ (A i).directionalField (axis k)) :=
  wordField_sum s A (fun _ : Fin 1 ↦ k)

private theorem addField_directional (A B : SmoothL2Field ℝ) (k : Fin 3) :
    (addField A B).directionalField (axis k) =
      addField (A.directionalField (axis k)) (B.directionalField (axis k)) :=
  wordField_add A B (fun _ : Fin 1 ↦ k)

/-- The literal second spatial derivative of a smooth gradient square.
The first term is the additional diffusion supplied by that square. -/
theorem gradientNormField_second_directional (A : SmoothL2Field Space)
    (k : Fin 3) (x : Space) :
    (((gradientNormField A).directionalField (axis k)).directionalField
      (axis k)).field x =
      2 * normSq (gradMatrix (A.directionalField (axis k)) x) +
        2 * ∑ i : Fin 3, ∑ j : Fin 3,
          gradMatrix A x i j *
            gradMatrix ((A.directionalField (axis k)).directionalField (axis k)) x i j := by
  have hc (i j : Fin 3) :
      (coord (A.directionalField (axis j)) i).directionalField (axis k) =
        coord ((A.directionalField (axis k)).directionalField (axis j)) i := by
    apply field_ext
    funext y
    rw [coord_directional_field, directionalField_comm]
    rfl
  have hc₂ (i j : Fin 3) :
      ((coord ((A.directionalField (axis k)).directionalField (axis j)) i).directionalField
        (axis k)).field x =
        gradMatrix ((A.directionalField (axis k)).directionalField (axis k)) x i j := by
    rw [coord_directional_field, directionalField_comm]
    rfl
  simp only [gradientNormField, sumField_directional, scalarProduct_directional,
    addField_directional, sumField_field, addField_field, scalarProduct_field,
    smul_eq_mul, hc, hc₂, coord_field, normSq, gradMatrix, Fin.sum_univ_three]
  ring

/-- Apply the square diffusion identity to the constructed fluid pressure.
No L² hypothesis on the scalar pressure potential is needed. -/
theorem pressureSquare_second_directional (u : SmoothL2Field Space)
    (k : Fin 3) (x : Space) :
    (((gradientNormField (pressureField u)).directionalField (axis k)).directionalField
      (axis k)).field x =
      2 * normSq (gradMatrix ((pressureField u).directionalField (axis k)) x) +
        2 * ∑ i : Fin 3, ∑ j : Fin 3,
          gradMatrix (pressureField u) x i j *
            gradMatrix (((pressureField u).directionalField (axis k)).directionalField
              (axis k)) x i j :=
  gradientNormField_second_directional (pressureField u) k x

/-- Augmentation of an observable by the canonical pressure square. -/
def augmented (u : SmoothL2Field Space) (X : Space → ℝ) (x : Space) : ℝ :=
  X x + pressureSquare u x

theorem le_augmented (u : SmoothL2Field Space) (X : Space → ℝ) (x : Space) :
    X x ≤ augmented u X x := by
  have h := pressureSquare_nonneg u x
  unfold augmented
  linarith

/-- The new initial reserve costs one additional velocity quartic. The
constant background is subtracted before integration on the whole space. -/
theorem integral_augmented_offset_le (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (X : Space → ℝ) (background B : ℝ)
    (hX : Integrable (fun x ↦ X x - background))
    (hB : (∫ x, X x - background) ≤ B) :
    (∫ x, augmented u X x - background) ≤
      B + ∫ x, normSq (gradMatrix u x) ^ 2 := by
  have he : (fun x ↦ augmented u X x - background) =
      fun x ↦ (X x - background) + pressureSquare u x := by
    funext x
    simp only [augmented]
    ring
  rw [he, integral_add hX (pressureSquare_integrable u)]
  exact add_le_add hB (integral_pressureSquare_le u hu)

/-- The actual square contributes `2ν|∂P|²` to the local diffusion. -/
def augmentedDirectionalDiffusion (u : SmoothL2Field Space) (k : Fin 3)
    (ν : ℝ) (D : Space → ℝ) (x : Space) : ℝ :=
  D x + 2 * ν * normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)

private theorem fieldSub_directional (A B : SmoothL2Field Space) (k : Fin 3) :
    (fieldSub A B).directionalField (axis k) =
      fieldSub (A.directionalField (axis k)) (B.directionalField (axis k)) := by
  change wordField (fieldSub A B) (fun _ : Fin 1 ↦ k) =
    fieldSub (wordField A (fun _ : Fin 1 ↦ k)) (wordField B (fun _ : Fin 1 ↦ k))
  simp only [fieldSub, wordField_add, fieldNeg, wordField_map]

/-- Pointwise absorption with coefficient `33/56`, for any nonnegative
selector. The displayed observer-Hessian lower bound is an application
obligation; no derivative or positive lower bound of the selector is used. -/
theorem selected_memory_gradient_paid_pointwise (u observed : SmoothL2Field Space)
    (k : Fin 3) (ν : ℝ) (hν : 0 ≤ ν) (w D : Space → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hlower : ∀ x, (56 / 5 : ℝ) * ν *
      normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D x)
    (x : Space) :
    ν * w x * normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x) ≤
      (33 / 56 : ℝ) * w x * augmentedDirectionalDiffusion u k ν D x := by
  rw [fieldSub_directional]
  have hm := mul_le_mul_of_nonneg_left
    (normSq_gradMatrix_sub_le (observed.directionalField (axis k))
      ((pressureField u).directionalField (axis k)) x)
    (mul_nonneg hν (hw x))
  have hd := mul_le_mul_of_nonneg_left (hlower x)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 33 / 56) (hw x))
  unfold augmentedDirectionalDiffusion
  nlinarith only [hm, hd]

private theorem bounded_weight_integrable (w g : Space → ℝ)
    (hw : AEStronglyMeasurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x, w x ≤ 1) (hg : Integrable g) :
    Integrable (fun x ↦ w x * g x) := by
  apply hg.bdd_mul hw
  exact Filter.Eventually.of_forall (fun x ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using hw1 x)

/-- Integrated absorption under a bounded measurable selector. This can
consume the soft-excess weight directly, without a smooth-weight limit. -/
theorem selected_memory_gradient_paid (u observed : SmoothL2Field Space)
    (k : Fin 3) (ν : ℝ) (hν : 0 ≤ ν) (w D : Space → ℝ)
    (hw : AEStronglyMeasurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x, w x ≤ 1) (hD : Integrable D)
    (hlower : ∀ x, (56 / 5 : ℝ) * ν *
      normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D x) :
    ν * (∫ x, w x * normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
      (33 / 56 : ℝ) * ∫ x, w x * augmentedDirectionalDiffusion u k ν D x := by
  have hd : Integrable (augmentedDirectionalDiffusion u k ν D) :=
    hD.add ((normSq_integrable ((pressureField u).directionalField (axis k))).const_mul
      (2 * ν))
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_mono
    ((bounded_weight_integrable w _ hw hw0 hw1 (normSq_integrable _)).const_mul ν)
    ((bounded_weight_integrable w _ hw hw0 hw1 hd).const_mul (33 / 56))
  intro x
  simpa only [mul_assoc] using
    selected_memory_gradient_paid_pointwise u observed k ν hν w D hw0 hlower x

/-- Continuous soft-excess receiver weight on the physical domain `z>0`.
Unlike a sharp active-set indicator it vanishes continuously at `z=b`. -/
def receiverWeight (b z : ℝ) : ℝ := max (1 - b ^ 2 / z ^ 2) 0

theorem receiverWeight_nonneg (b z : ℝ) : 0 ≤ receiverWeight b z :=
  le_max_right _ _

theorem receiverWeight_le_one (b z : ℝ) : receiverWeight b z ≤ 1 := by
  apply max_le
  · have h : 0 ≤ b ^ 2 / z ^ 2 := div_nonneg (sq_nonneg b) (sq_nonneg z)
    linarith
  · norm_num

/-- Identification with the active derivative of the perspective excess. -/
theorem receiverWeight_eq_active (b z : ℝ) (hb : 0 ≤ b) (hz : 0 < z) :
    receiverWeight b z = if b < z then 1 - b ^ 2 / z ^ 2 else 0 := by
  unfold receiverWeight
  split_ifs with ha
  · apply max_eq_left
    have hbz : b ^ 2 ≤ z ^ 2 := by gcongr
    have h : b ^ 2 / z ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hz)).2 hbz
    linarith
  · apply max_eq_right
    have hzb : z ≤ b := le_of_not_gt ha
    have hsq : z ^ 2 ≤ b ^ 2 := by gcongr
    have h : 1 ≤ b ^ 2 / z ^ 2 := (one_le_div (sq_pos_of_pos hz)).2 hsq
    linarith

theorem receiverWeight_measurable (b : ℝ) (z : Space → ℝ) (hz : Measurable z) :
    Measurable (fun x ↦ receiverWeight b (z x)) := by
  exact (measurable_const.sub (measurable_const.div (hz.pow_const 2))).max measurable_const

/-- The actual soft selector needs no spatial differentiability assumption
in this pressure-gradient payment. Its weak evolution chain rule remains
a separate obligation. -/
theorem soft_memory_gradient_paid (u observed : SmoothL2Field Space)
    (k : Fin 3) (ν : ℝ) (hν : 0 ≤ ν) (b : ℝ) (z D : Space → ℝ)
    (hz : Measurable z) (hD : Integrable D)
    (hlower : ∀ x, (56 / 5 : ℝ) * ν *
      normSq (gradMatrix (observed.directionalField (axis k)) x) ≤ D x) :
    ν * (∫ x, receiverWeight b (z x) * normSq
      (gradMatrix ((fieldSub observed (pressureField u)).directionalField (axis k)) x)) ≤
      (33 / 56 : ℝ) * ∫ x, receiverWeight b (z x) *
        augmentedDirectionalDiffusion u k ν D x := by
  exact selected_memory_gradient_paid u observed k ν hν
    (fun x ↦ receiverWeight b (z x)) D
    (receiverWeight_measurable b z hz).aestronglyMeasurable
    (fun x ↦ receiverWeight_nonneg b (z x))
    (fun x ↦ receiverWeight_le_one b (z x)) hD hlower

/-- Any soft-excess bound for the augmented observable is still sufficient
for actual vorticity continuation. It is a stronger hypothesis than a bound
for the original observable; its physical history estimate is not proved. -/
theorem massEnvelope_of_augmented_soft_excess (u : SmoothL2Field Space)
    (X h c : Space → ℝ) {b k B E : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hX : ∀ x, 0 < X x) (hh : ∀ x, 0 ≤ h x) (hhc : ∀ x, h x ≤ 1 + c x)
    (hc : Integrable c) (hc0 : ∀ x, 0 ≤ c x) (hcB : (∫ x, c x) ≤ B)
    (he : Integrable (fun x ↦ ViscousMemorySoftExcess.excess (augmented u X x) (h x) b))
    (heE : (∫ x, ViscousMemorySoftExcess.excess (augmented u X x) (h x) b) ≤ E)
    (hcoerce : ∀ x, k * vortSq (gradMatrix u x) ^ 2 ≤ X x) :
    MassEnvelope u (2 * b / k) (B + E / (2 * b)) := by
  exact ViscousMemorySoftExcess.massEnvelope_of_soft_excess u (augmented u X) h c
    hb hk (fun x ↦ (hX x).trans_le (le_augmented u X x)) hh hhc hc hc0 hcB he heE
    (fun x ↦ (hcoerce x).trans (le_augmented u X x))

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureAugmentation
