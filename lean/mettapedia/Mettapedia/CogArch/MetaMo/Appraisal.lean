import Mettapedia.CogArch.MetaMo.Basic

/-!
# Fixed-weight appraisal

Appraisal uses the shared scalar action. Monotonicity in the state follows from
join preservation; monotonicity in sensitivity requires its own hypothesis.
-/

namespace Mettapedia.CogArch.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-- Fixed-weight appraisal; the role is semantic, and the action is shared. -/
def appraisalFunctor (q_sens : Q) : Θ → Θ := fun θ => q_sens • θ

abbrev App (q_sens : Q) : Θ → Θ := appraisalFunctor q_sens

@[simp]
theorem appraisalFunctor_apply (q_sens : Q) (θ : Θ) :
    appraisalFunctor q_sens θ = q_sens • θ := rfl

@[simp]
theorem appraisalFunctor_one : appraisalFunctor (1 : Q) = (id : Θ → Θ) :=
  (scalarAction (Q := Q) (Θ := Θ)).map_one

theorem appraisalFunctor_map_smul (q_sens q : Q) (θ : Θ) :
    appraisalFunctor q_sens (q • θ) = q • appraisalFunctor q_sens θ :=
  smul_smul_comm q_sens q θ

def appraisalEndo (q_sens : Q) : ScalarEquivariantEndo Q Θ :=
  smulEndo q_sens

@[simp]
theorem appraisalEndo_apply (q_sens : Q) (θ : Θ) :
    appraisalEndo q_sens θ = q_sens • θ := rfl

theorem appraisalFunctor_comp (q₁ q₂ : Q) :
    appraisalFunctor (Θ := Θ) q₁ ∘ appraisalFunctor q₂ = appraisalFunctor (q₁ * q₂) :=
  scalarAction_comp q₁ q₂

theorem appraisalFunctor_comm (q₁ q₂ : Q) :
    appraisalFunctor (Θ := Θ) q₁ ∘ appraisalFunctor q₂ =
    appraisalFunctor q₂ ∘ appraisalFunctor q₁ := by
  rw [appraisalFunctor_comp, appraisalFunctor_comp, mul_comm]

theorem appraisalEndo_comp (q₁ q₂ : Q) :
    (appraisalEndo (Θ := Θ) q₁).comp (appraisalEndo q₂) =
    appraisalEndo (q₁ * q₂) :=
  smulEndo_comp q₁ q₂

theorem appraisalFunctor_mono_state (q_sens : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    appraisalFunctor q_sens θ₁ ≤ appraisalFunctor q_sens θ₂ :=
  smul_mono_right q_sens h

theorem appraisalFunctor_sup (q_sens : Q) (θ₁ θ₂ : Θ) :
    appraisalFunctor q_sens (θ₁ ⊔ θ₂) =
    appraisalFunctor q_sens θ₁ ⊔ appraisalFunctor q_sens θ₂ :=
  smul_sup q_sens θ₁ θ₂

section SensitivityOrdering

/-- Monotonicity in the scalar is a separate assumption, not a positivity condition. -/
class ScalarMonotoneQModule (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] [QModule Q Θ] where
  smul_mono_left : ∀ {q₁ q₂ : Q}, q₁ ≤ q₂ → ∀ θ : Θ, q₁ • θ ≤ q₂ • θ

variable [ScalarMonotoneQModule Q Θ]

theorem appraisalFunctor_mono_sens {q₁ q₂ : Q} (h : q₁ ≤ q₂) (θ : Θ) :
    appraisalFunctor q₁ θ ≤ appraisalFunctor q₂ θ := by
  simp only [appraisalFunctor_apply]
  exact ScalarMonotoneQModule.smul_mono_left h θ

end SensitivityOrdering

end Mettapedia.CogArch.MetaMo
