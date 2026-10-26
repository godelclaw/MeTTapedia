import Mettapedia.CognitiveArchitecture.MetaMo.Appraisal
import Mettapedia.CognitiveArchitecture.MetaMo.Decision

/-!
# Commutation of fixed motivational weights

Commuting coefficients preserve the final state under reordering. These laws do
not identify intermediate histories or permit reordering state-dependent choices.
-/

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

theorem appraisal_decision_commute_of_comm (q_sens q_dec : Q)
    (h_comm : q_sens * q_dec = q_dec * q_sens) (θ : Θ) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) := by
  simp only [appraisalFunctor_apply, decisionFunctor_apply]
  rw [← mul_smul, ← mul_smul, h_comm]

theorem appraisal_decision_commute (q_sens q_dec : Q) (θ : Θ) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) :=
  appraisal_decision_commute_of_comm q_sens q_dec (mul_comm q_sens q_dec) θ

theorem appraisal_decision_commute_comp (q_sens q_dec : Q) :
    appraisalFunctor (Θ := Θ) q_sens ∘ decisionFunctor q_dec =
    decisionFunctor q_dec ∘ appraisalFunctor q_sens := by
  ext θ
  exact appraisal_decision_commute q_sens q_dec θ

theorem appraisalEndo_decisionEndo_commute (q_sens q_dec : Q) :
    (appraisalEndo (Θ := Θ) q_sens).comp (decisionEndo q_dec) =
    (decisionEndo q_dec).comp (appraisalEndo q_sens) := by
  ext θ
  simp only [ScalarEquivariantEndo.comp_apply, appraisalEndo_apply, decisionEndo_apply]
  exact appraisal_decision_commute q_sens q_dec θ

theorem appraisal_comp_decision (q_sens q_dec : Q) :
    appraisalFunctor (Θ := Θ) q_sens ∘ decisionFunctor q_dec =
    (fun θ => QModule.smul (q_sens * q_dec) θ) :=
  scalarAction_comp q_sens q_dec

theorem appraisal_decision_product (q_sens q_dec : Q) (θ : Θ) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) = QModule.smul (Q := Q) (q_sens * q_dec) θ := by
  simp only [appraisalFunctor_apply, decisionFunctor_apply]
  exact (mul_smul q_sens q_dec θ).symm

theorem triple_dynamics_assoc (q₁ q₂ q₃ : Q) (θ : Θ) :
    (q₁ • (q₂ • (q₃ • θ))) = ((q₁ * q₂ * q₃) • θ) := by
  rw [mul_smul, mul_smul]

theorem triple_dynamics_perm (q₁ q₂ q₃ : Q) (θ : Θ) :
    q₁ • (q₂ • (q₃ • θ)) = q₂ • (q₃ • (q₁ • θ)) := by
  rw [triple_dynamics_assoc, triple_dynamics_assoc]
  congr 1
  simp only [mul_comm, mul_left_comm]

theorem double_cycle_commute (q_s₁ q_d₁ q_s₂ q_d₂ : Q) (θ : Θ) :
    appraisalFunctor q_s₁ (decisionFunctor q_d₁
      (appraisalFunctor q_s₂ (decisionFunctor q_d₂ θ))) =
    appraisalFunctor q_s₂ (decisionFunctor q_d₂
      (appraisalFunctor q_s₁ (decisionFunctor q_d₁ θ))) := by
  simp only [appraisalFunctor_apply, decisionFunctor_apply]
  rw [← mul_smul, ← mul_smul, ← mul_smul]
  rw [← mul_smul, ← mul_smul, ← mul_smul]
  congr 1
  simp only [mul_comm, mul_left_comm]

end Mettapedia.CognitiveArchitecture.MetaMo
