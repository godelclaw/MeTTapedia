import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Isomorphism invariance of full-domain Henkin models

An equivalence of base carriers lifts to every simple type: identity at `prop`,
the given equivalence at a base type, and conjugation at function types
(`liftEquiv`). If the constants of two full-domain Henkin models correspond
under the lifted equivalence, then every term denotes corresponding values at
corresponding valuations (`denote_transport`), extensional equality is
preserved and reflected (`eqv_transport`), and the two models satisfy exactly
the same closed formulas (`models_transport`).

The carriers may live in different universes. Full domains are required: the
quantifiers of both models range over whole carriers, so the lifted
equivalences need no admissibility condition. Standard models have full
domains (`HenkinModel.fullDomains_standard`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.StandardTransport

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v}

section Lift

variable {Source : Base → Type (max (u + 1) w)} {Target : Base → Type (max (u + 1) w')}

/-- Lift an equivalence of base carriers to every simple type. -/
def liftEquiv (base : ∀ b, Source b ≃ Target b) :
    ∀ τ : Ty Base, Ty.denote Source τ ≃ Ty.denote Target τ
  | .prop => Equiv.ulift.trans Equiv.ulift.symm
  | .base b => base b
  | .arr σ τ => Equiv.arrowCongr (liftEquiv base σ) (liftEquiv base τ)

@[simp] theorem liftEquiv_prop_down (base : ∀ b, Source b ≃ Target b)
    (value : Ty.denote Source .prop) :
    (liftEquiv base .prop value).down = value.down := rfl

theorem liftEquiv_arr_apply (base : ∀ b, Source b ≃ Target b) {σ τ : Ty Base}
    (function : Ty.denote Source σ → Ty.denote Source τ) (argument : Ty.denote Source σ) :
    liftEquiv base (σ ⇒ τ) function (liftEquiv base σ argument) =
      liftEquiv base τ (function argument) := by
  show liftEquiv base τ (function ((liftEquiv base σ).symm (liftEquiv base σ argument))) = _
  rw [Equiv.symm_apply_apply]

end Lift

section Models

variable (source : HenkinModel.{u, v, w} Base Const) (target : HenkinModel.{u, v, w'} Base Const)
variable (sourceFull : source.FullDomains) (targetFull : target.FullDomains)
variable (base : ∀ b, source.Carrier b ≃ target.Carrier b)
include sourceFull targetFull

/-- Extensional equality of full-domain models is preserved and reflected. -/
theorem eqv_transport :
    ∀ (τ : Ty Base) (left right : Ty.denote source.Carrier τ),
      PreModel.Eqv target.toPreModel τ (liftEquiv base τ left) (liftEquiv base τ right) ↔
        PreModel.Eqv source.toPreModel τ left right
  | .prop, left, right => Iff.rfl
  | .base b, left, right => (base b).apply_eq_iff_eq
  | .arr σ τ, left, right => by
      simp only [PreModel.eqv_arr]
      constructor
      · intro related argument _
        have := related (liftEquiv base σ argument) (targetFull _ _)
        rw [liftEquiv_arr_apply base left, liftEquiv_arr_apply base right] at this
        exact (eqv_transport τ _ _).mp this
      · intro related argument _
        obtain ⟨preimage, rfl⟩ := (liftEquiv base σ).surjective argument
        rw [liftEquiv_arr_apply base left, liftEquiv_arr_apply base right]
        exact (eqv_transport τ _ _).mpr (related preimage (sourceFull _ _))

omit sourceFull targetFull in
/-- Extending corresponding valuations by corresponding values. -/
theorem extend_transport {Γ : Ctx Base} {σ : Ty Base}
    (valuation : HenkinModel.Valuation source Γ) (value : Ty.denote source.Carrier σ) :
    (HenkinModel.extend target (fun {τ} index => liftEquiv base τ (valuation index))
        (liftEquiv base σ value) : HenkinModel.Valuation target (σ :: Γ)) =
      fun {τ} index => liftEquiv base τ (HenkinModel.extend source valuation value index) := by
  funext τ index
  cases index <;> rfl

/-- **Denotation commutes with the lifted equivalence.** -/
theorem denote_transport
    (constants : ∀ {τ : Ty Base} (constant : Const τ),
      liftEquiv base τ (source.constDen constant) = target.constDen constant) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ)
      (valuation : HenkinModel.Valuation source Γ),
      HenkinModel.denote target term (fun {τ} index => liftEquiv base τ (valuation index)) =
        liftEquiv base τ (HenkinModel.denote source term valuation)
  | _, _, .var index, valuation => rfl
  | _, _, .const constant, valuation => (constants constant).symm
  | _, _, .app function argument, valuation => by
      change (HenkinModel.denote target function _) (HenkinModel.denote target argument _) = _
      rw [denote_transport constants function valuation,
        denote_transport constants argument valuation]
      exact liftEquiv_arr_apply base _ _
  | _, _, .lam body, valuation => by
      funext argument
      obtain ⟨preimage, rfl⟩ := (liftEquiv base _).surjective argument
      change HenkinModel.denote target body (HenkinModel.extend target _ _) =
        liftEquiv base (_ ⇒ _) (fun value => HenkinModel.denote source body
          (HenkinModel.extend source valuation value)) (liftEquiv base _ preimage)
      rw [extend_transport, denote_transport constants body]
      exact (liftEquiv_arr_apply base
        (fun value => HenkinModel.denote source body (HenkinModel.extend source valuation value))
        preimage).symm
  | _, _, .top, valuation => rfl
  | _, _, .bot, valuation => rfl
  | _, _, .and left right, valuation => by
      apply ULift.ext
      change ((HenkinModel.denote target left _).down ∧ (HenkinModel.denote target right _).down) =
        ((HenkinModel.denote source left _).down ∧ (HenkinModel.denote source right _).down)
      rw [denote_transport constants left valuation, denote_transport constants right valuation]
      rfl
  | _, _, .or left right, valuation => by
      apply ULift.ext
      change ((HenkinModel.denote target left _).down ∨ (HenkinModel.denote target right _).down) =
        ((HenkinModel.denote source left _).down ∨ (HenkinModel.denote source right _).down)
      rw [denote_transport constants left valuation, denote_transport constants right valuation]
      rfl
  | _, _, .imp left right, valuation => by
      apply ULift.ext
      change ((HenkinModel.denote target left _).down → (HenkinModel.denote target right _).down) =
        ((HenkinModel.denote source left _).down → (HenkinModel.denote source right _).down)
      rw [denote_transport constants left valuation, denote_transport constants right valuation]
      rfl
  | _, _, .not body, valuation => by
      apply ULift.ext
      change (¬ (HenkinModel.denote target body _).down) =
        (¬ (HenkinModel.denote source body _).down)
      rw [denote_transport constants body valuation]
      rfl
  | _, _, .eq left right, valuation => by
      apply ULift.ext
      change PreModel.Eqv target.toPreModel _ (HenkinModel.denote target left _)
          (HenkinModel.denote target right _) =
        PreModel.Eqv source.toPreModel _ (HenkinModel.denote source left _)
          (HenkinModel.denote source right _)
      rw [denote_transport constants left valuation, denote_transport constants right valuation]
      exact propext (eqv_transport source target sourceFull targetFull base _ _ _)
  | _, _, .all body, valuation => by
      apply ULift.ext
      apply propext
      change (∀ argument, target.adm _ argument →
          (HenkinModel.denote target body (HenkinModel.extend target _ argument)).down) ↔
        (∀ argument, source.adm _ argument →
          (HenkinModel.denote source body (HenkinModel.extend source valuation argument)).down)
      constructor
      · intro holds argument _
        have := holds (liftEquiv base _ argument) (targetFull _ _)
        rw [extend_transport, denote_transport constants body] at this
        exact this
      · intro holds argument _
        obtain ⟨preimage, rfl⟩ := (liftEquiv base _).surjective argument
        rw [extend_transport, denote_transport constants body]
        exact holds preimage (sourceFull _ _)
  | _, _, .ex body, valuation => by
      apply ULift.ext
      apply propext
      change (∃ argument, target.adm _ argument ∧
          (HenkinModel.denote target body (HenkinModel.extend target _ argument)).down) ↔
        (∃ argument, source.adm _ argument ∧
          (HenkinModel.denote source body (HenkinModel.extend source valuation argument)).down)
      constructor
      · rintro ⟨argument, _, holds⟩
        obtain ⟨preimage, rfl⟩ := (liftEquiv base _).surjective argument
        rw [extend_transport, denote_transport constants body] at holds
        exact ⟨preimage, sourceFull _ _, holds⟩
      · rintro ⟨argument, _, holds⟩
        refine ⟨liftEquiv base _ argument, targetFull _ _, ?_⟩
        rw [extend_transport, denote_transport constants body]
        exact holds

/-- **Corresponding full-domain models satisfy the same closed formulas.** -/
theorem models_transport
    (constants : ∀ {τ : Ty Base} (constant : Const τ),
      liftEquiv base τ (source.constDen constant) = target.constDen constant)
    (formula : ClosedFormula Const) :
    HenkinModel.models target formula ↔ HenkinModel.models source formula := by
  have transported := congrArg ULift.down
    (denote_transport source target sourceFull targetFull base constants formula
      (fun index => nomatch index))
  have empty : (fun {τ} (index : Var [] τ) =>
      liftEquiv base τ (nomatch index : Ty.denote source.Carrier τ)) =
      (fun {τ} (index : Var [] τ) => (nomatch index : Ty.denote target.Carrier τ)) := by
    funext τ index
    cases index
  rw [empty] at transported
  exact Iff.of_eq transported

end Models

end Mettapedia.Logic.HOL.StandardTransport
