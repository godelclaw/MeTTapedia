import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Complete comprehension readouts of equal type presentations

The canonical equality comparison of source types carries the original
context, type and term readouts coherently. These heterogeneous equations
retain equality adjustments without identifying distinct type codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualComprehensionTypeEquality

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'
variable {C : Cwf.{u, v, w, w'}}

theorem equality_substitution {Γ : C.Ctx} {A₀ A₁ : C.Ty Γ} (domains : A₀ = A₁) :
    HEq (TypeOver.isoOfValEq (A := ⟨A₀⟩) (B := ⟨A₁⟩) domains).hom.substitution
      (C.idS (C.ext Γ A₁)) := by
  cases domains
  rfl

theorem equality_type_readout {Γ : C.Ctx} {A₀ A₁ : C.Ty Γ} (domains : A₀ = A₁)
    (B : C.Ty (C.ext Γ A₁)) :
    HEq (C.tySub B
      (TypeOver.isoOfValEq (A := ⟨A₀⟩) (B := ⟨A₁⟩) domains).hom.substitution) B := by
  cases domains
  exact heq_of_eq (C.tySub_id B)

theorem equality_term_readout {Γ : C.Ctx} {A₀ A₁ : C.Ty Γ} (domains : A₀ = A₁)
    {B : C.Ty (C.ext Γ A₁)} (body : C.Tm (C.ext Γ A₁) B) :
    HEq (C.tmSub body
      (TypeOver.isoOfValEq (A := ⟨A₀⟩) (B := ⟨A₁⟩) domains).hom.substitution) body := by
  cases domains
  exact (heq_of_eq (C.tmSub_id body)).trans (cast_heq _ _)

end Mettapedia.TypeTheory.ContextualComprehensionTypeEquality
