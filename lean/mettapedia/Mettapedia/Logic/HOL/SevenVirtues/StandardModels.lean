import Mettapedia.Logic.HOL.Semantics.StandardTransport
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.Logic.HOL.Soundness

/-!
# Virtue 2: the semantics rests on a few established ideas

The semantics of the tree's simple type theory is one recursion
(`PreModel.denote`): values in domains of individuals, truth values in `Prop`,
functions as functions, and quantifiers over the admissible values of a type.
This file records the facts that make that semantics well behaved and pins
down which general models are the standard ones.

* `fullDomains_iff_andrewsFull`: a general model has full domains exactly when
  it is full in Andrews' sense, i.e. every map of admissible values that
  respects extensional equality is the value of an admissible function.
* `fullDomains_iff_eqv_eq`: a general model has full domains exactly when its
  extensional equality is literal equality at every type.
* `fullDomains_iff_standard`: full-domain models are exactly the standard
  models `HenkinModel.standard C I` on their own carriers.
* `standard_models_iff`: standard models whose base carriers correspond by
  bijections preserving the constants satisfy the same sentences (Farmer's
  Theorem 1, via `StandardTransport.models_transport`).
* `denote_instantiate`: denotation is compositional; substitution is
  evaluation in the extended valuation (`Soundness.denote_instantiate_term`).

Negative example: in a general model without full domains, extensional
equality identifies ambient functions that differ (`exists_eqv_ne_of_not_full`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinModelFacts

variable (M : HenkinModel.{u, v, w} Base Const)

/-- Andrews' fullness: every map of admissible values that respects
extensional equality is represented by an admissible function. -/
def AndrewsFull : Prop :=
  ∀ (σ τ : Ty Base) (g : Ty.denote M.Carrier σ → Ty.denote M.Carrier τ),
    (∀ x, M.adm σ x → M.adm τ (g x)) →
    (∀ x y, M.adm σ x → M.adm σ y → M.Eqv σ x y → M.Eqv τ (g x) (g y)) →
    ∃ f : Ty.denote M.Carrier (σ ⇒ τ), M.adm (σ ⇒ τ) f ∧
      ∀ x, M.adm σ x → M.Eqv τ (f x) (g x)

theorem eqv_prop_iff_eq (p q : Ty.denote M.Carrier .prop) : M.Eqv .prop p q ↔ p = q := by
  constructor
  · intro h
    exact ULift.ext _ _ (propext h)
  · rintro rfl
    exact Iff.rfl

/-- Andrews-fullness makes every ambient value admissible and every
extensional equality literal. -/
theorem full_and_eqv_eq_of_andrewsFull (h : AndrewsFull M) :
    ∀ τ : Ty Base, (∀ x, M.adm τ x) ∧ ∀ x y, M.Eqv τ x y ↔ x = y
  | .prop => ⟨fun x => M.prop_mem x, eqv_prop_iff_eq M⟩
  | .base b => ⟨fun x => M.base_mem b x, fun _ _ => Iff.rfl⟩
  | .arr σ τ => by
      obtain ⟨admσ, eqvσ⟩ := full_and_eqv_eq_of_andrewsFull h σ
      obtain ⟨admτ, eqvτ⟩ := full_and_eqv_eq_of_andrewsFull h τ
      have eqvArr : ∀ f g : Ty.denote M.Carrier (σ ⇒ τ), M.Eqv (σ ⇒ τ) f g ↔ f = g := by
        intro f g
        constructor
        · intro hfg
          funext x
          exact (eqvτ _ _).mp (hfg x (admσ x))
        · rintro rfl x _
          exact (eqvτ _ _).mpr rfl
      refine ⟨fun g => ?_, eqvArr⟩
      obtain ⟨f, hf, hfg⟩ := h σ τ g (fun x _ => admτ (g x))
        (fun x y _ _ hxy => (eqvτ _ _).mpr (congrArg g ((eqvσ x y).mp hxy)))
      have : f = g := by
        funext x
        exact (eqvτ _ _).mp (hfg x (admσ x))
      exact this ▸ hf

/-- **Andrews' full general models are exactly the full-domain models.** -/
theorem fullDomains_iff_andrewsFull : M.FullDomains ↔ AndrewsFull M := by
  constructor
  · intro full σ τ g _ _
    exact ⟨g, full (σ ⇒ τ) g, fun x _ => M.eqv_refl (full τ (g x))⟩
  · intro h τ x
    exact (full_and_eqv_eq_of_andrewsFull M h τ).1 x

/-- **A general model has full domains exactly when its extensional equality
is literal equality at every type.** -/
theorem fullDomains_iff_eqv_eq :
    M.FullDomains ↔ ∀ (τ : Ty Base) (x y : Ty.denote M.Carrier τ), M.Eqv τ x y ↔ x = y := by
  classical
  constructor
  · intro full τ x y
    exact HenkinModel.eqv_iff_eq_of_fullDomains M full x y
  · intro h σ x₀
    by_contra hx₀
    let f : Ty.denote M.Carrier (σ ⇒ .prop) := fun _ => .up True
    let g : Ty.denote M.Carrier (σ ⇒ .prop) := fun x => .up (x ≠ x₀)
    have hfg : M.Eqv (σ ⇒ .prop) f g := by
      intro x hx
      change True ↔ x ≠ x₀
      exact ⟨fun _ hEq => hx₀ (hEq ▸ hx), fun _ => trivial⟩
    have hne : f ≠ g := by
      intro hEq
      have := congrArg (fun k => (k x₀).down) hEq
      simp only [f, g, ne_eq, not_true_eq_false] at this
      exact this ▸ trivial
    exact hne ((h _ f g).mp hfg)

/-- **Negative example.** Without full domains, extensional equality
identifies ambient functions that differ: the constant truth predicate and the
predicate false only at a non-admissible value. -/
theorem exists_eqv_ne_of_not_full (h : ¬ M.FullDomains) :
    ∃ (τ : Ty Base) (x y : Ty.denote M.Carrier τ), M.Eqv τ x y ∧ x ≠ y := by
  classical
  simp only [HenkinModel.FullDomains, not_forall] at h
  obtain ⟨σ, x₀, hx₀⟩ := h
  refine ⟨σ ⇒ .prop, fun _ => .up True, fun x => .up (x ≠ x₀), ?_, ?_⟩
  · intro x hx
    change True ↔ x ≠ x₀
    exact ⟨fun _ hEq => hx₀ (hEq ▸ hx), fun _ => trivial⟩
  · intro hEq
    have := congrArg (fun k : Ty.denote M.Carrier (σ ⇒ .prop) => (k x₀).down) hEq
    simp only [ne_eq, not_true_eq_false] at this
    exact this ▸ trivial

/-- **Full-domain models are exactly the standard models on their carriers.** -/
theorem fullDomains_iff_standard :
    M.FullDomains ↔ HenkinModel.standard M.Carrier M.constDen = M :=
  (HenkinModel.standard_eq_iff_fullDomains M).symm

/-- **Compositionality.** Substituting a term is evaluating it and extending
the valuation. -/
theorem denote_instantiate {Γ : Ctx Base} {σ τ : Ty Base} (t : Term Const Γ σ)
    (body : Term Const (σ :: Γ) τ) (ρ : M.Valuation Γ) :
    M.denote (instantiate t body) ρ = M.denote body (M.extend ρ (M.denote t ρ)) :=
  Soundness.denote_instantiate_term M t body ρ

end HenkinModelFacts

/-- **Farmer's Theorem 1.** Standard models whose base carriers correspond by
bijections, and whose constants correspond under the induced bijections at all
types, satisfy the same sentences. -/
theorem standard_models_iff
    (C : Base → Type (max (u + 1) w)) (D : Base → Type (max (u + 1) w'))
    (I : {τ : Ty Base} → Const τ → Ty.denote C τ) (J : {τ : Ty Base} → Const τ → Ty.denote D τ)
    (base : ∀ b, C b ≃ D b)
    (constants : ∀ {τ : Ty Base} (c : Const τ), StandardTransport.liftEquiv base τ (I c) = J c)
    (φ : ClosedFormula Const) :
    (HenkinModel.standard C I).models φ ↔ (HenkinModel.standard D J).models φ :=
  (StandardTransport.models_transport (HenkinModel.standard C I) (HenkinModel.standard D J)
    (HenkinModel.fullDomains_standard _ _) (HenkinModel.fullDomains_standard _ _) base
    constants φ).symm

#print axioms HenkinModelFacts.fullDomains_iff_andrewsFull
#print axioms HenkinModelFacts.fullDomains_iff_eqv_eq
#print axioms HenkinModelFacts.exists_eqv_ne_of_not_full
#print axioms HenkinModelFacts.fullDomains_iff_standard
#print axioms standard_models_iff

end Mettapedia.Logic.HOL.SevenVirtues
