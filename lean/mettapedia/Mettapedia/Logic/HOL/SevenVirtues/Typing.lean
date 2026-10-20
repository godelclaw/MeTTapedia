import Mettapedia.Logic.HOL.CheckableFragment

/-!
# Virtue 1, typing: types are unique and checking is decidable

The tree's terms are intrinsically typed, so every term carries its type. For
raw, Church-annotated certificates (binder types as the only hints) the
elaborator of `CheckableFragment` decides typability by one syntax-directed
pass (`elaborate?_sound`, `elaborate?_erase`). Two consequences:

* `typing_unique`: a raw certificate has at most one typing, type and term
  together;
* `typable_iff`: a raw certificate is typable exactly when elaboration
  succeeds, so typability is decidable (`decidableTypable`).

Negative example: the self-application `Ω` has no typing at any hint
(`CheckableFragment.Controls.omega_untypable`), restated as `omega_not_typable`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.Typing

open CheckableFragment

universe u v

variable {Base : Type u} {Const : Ty Base → Type v} [DecidableEq Base]

/-- **Unique typing.** Two typed terms with the same raw certificate have the
same type and are the same term. -/
theorem typing_unique {Γ : Ctx Base} {τ₁ τ₂ : Ty Base} (t₁ : Term Const Γ τ₁)
    (t₂ : Term Const Γ τ₂) (h : erase t₁ = erase t₂) :
    (⟨τ₁, t₁⟩ : Σ τ : Ty Base, Term Const Γ τ) = ⟨τ₂, t₂⟩ := by
  have h₁ := elaborate?_erase t₁
  rw [h, elaborate?_erase t₂] at h₁
  exact (Option.some.inj h₁).symm

/-- **Decidable typing.** A raw certificate is typable exactly when
elaboration succeeds. -/
theorem typable_iff (Γ : Ctx Base) (raw : Raw Base Const Γ.length) :
    (∃ (τ : Ty Base) (t : Term Const Γ τ), erase t = raw) ↔ (elaborate? Γ raw).isSome := by
  constructor
  · rintro ⟨τ, t, rfl⟩
    rw [elaborate?_erase]
    rfl
  · intro h
    obtain ⟨⟨τ, t⟩, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨τ, t, elaborate?_sound Γ raw ht⟩

instance decidableTypable (Γ : Ctx Base) (raw : Raw Base Const Γ.length) :
    Decidable (∃ (τ : Ty Base) (t : Term Const Γ τ), erase t = raw) :=
  decidable_of_iff _ (typable_iff Γ raw).symm

/-- The self-application `Ω` is not typable, at any binder hint. -/
theorem omega_not_typable (σ : Ty Unit) :
    ¬ ∃ (τ : Ty Unit) (t : Term ContextualTrinity.Controls.NoConstant [] τ),
      erase t = Controls.omega σ := by
  rw [typable_iff, Controls.omega_untypable]
  simp

#print axioms typing_unique
#print axioms typable_iff
#print axioms omega_not_typable

end Mettapedia.Logic.HOL.SevenVirtues.Typing
