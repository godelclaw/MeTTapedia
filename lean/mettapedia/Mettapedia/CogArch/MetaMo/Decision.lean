import Mettapedia.CogArch.MetaMo.Basic

/-!
# Fixed-weight decision

Decision uses the same action as appraisal, with a different application role.
The abstract laws alone assign no filtering interpretation to small scalars.
-/

namespace Mettapedia.CogArch.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-- Fixed-weight decision; the role is semantic, and the action is shared. -/
def decisionFunctor (q_dec : Q) : Θ → Θ := fun θ => q_dec • θ

abbrev Dec (q_dec : Q) : Θ → Θ := decisionFunctor q_dec

@[simp]
theorem decisionFunctor_apply (q_dec : Q) (θ : Θ) :
    decisionFunctor q_dec θ = q_dec • θ := rfl

@[simp]
theorem decisionFunctor_one : decisionFunctor (1 : Q) = (id : Θ → Θ) :=
  (scalarAction (Q := Q) (Θ := Θ)).map_one

theorem decisionFunctor_map_smul (q_dec q : Q) (θ : Θ) :
    decisionFunctor q_dec (q • θ) = q • decisionFunctor q_dec θ :=
  smul_smul_comm q_dec q θ

def decisionEndo (q_dec : Q) : ScalarEquivariantEndo Q Θ :=
  smulEndo q_dec

@[simp]
theorem decisionEndo_apply (q_dec : Q) (θ : Θ) :
    decisionEndo q_dec θ = q_dec • θ := rfl

theorem decisionFunctor_comp (q₁ q₂ : Q) :
    decisionFunctor (Θ := Θ) q₁ ∘ decisionFunctor q₂ = decisionFunctor (q₁ * q₂) :=
  scalarAction_comp q₁ q₂

theorem decisionFunctor_comm (q₁ q₂ : Q) :
    decisionFunctor (Θ := Θ) q₁ ∘ decisionFunctor q₂ =
    decisionFunctor q₂ ∘ decisionFunctor q₁ := by
  rw [decisionFunctor_comp, decisionFunctor_comp, mul_comm]

theorem decisionEndo_comp (q₁ q₂ : Q) :
    (decisionEndo (Θ := Θ) q₁).comp (decisionEndo q₂) =
    decisionEndo (q₁ * q₂) :=
  smulEndo_comp q₁ q₂

theorem decisionFunctor_mono_state (q_dec : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    decisionFunctor q_dec θ₁ ≤ decisionFunctor q_dec θ₂ :=
  smul_mono_right q_dec h

theorem decisionFunctor_sup (q_dec : Q) (θ₁ θ₂ : Θ) :
    decisionFunctor q_dec (θ₁ ⊔ θ₂) =
    decisionFunctor q_dec θ₁ ⊔ decisionFunctor q_dec θ₂ :=
  smul_sup q_dec θ₁ θ₂

end Mettapedia.CogArch.MetaMo
