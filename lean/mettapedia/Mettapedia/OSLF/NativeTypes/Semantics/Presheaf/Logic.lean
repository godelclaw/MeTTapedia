import Mettapedia.GSLT.Topos.PresheafPredicateHeyting

/-!
# Intuitionistic generated formulas in genuine presheaf predicate fibres

Finite syntax is interpreted in actual subfunctors. Independent satisfaction
quantifies over every restriction at implication, rather than complementing
the truth value at the current world. Formula substitution is different from
presheaf substitution; both comparison laws are proved below.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Logic

open _root_.CategoryTheory Mettapedia.GSLT.Topos

universe u v w z z'

/-- Finite intuitionistic syntax, parameterized by generated native atoms. -/
inductive Formula (Atom : Type z) where
  | atom : Atom → Formula Atom
  | top : Formula Atom
  | bot : Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | impl : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

namespace Formula

variable {Atom : Type z} {Other : Type z'}

def negation (formula : Formula Atom) : Formula Atom := .impl formula .bot

/-- Substitute finite formulas for the generated atoms. -/
def substitute (assignment : Atom → Formula Other) : Formula Atom → Formula Other
  | .atom name => assignment name
  | .top => .top
  | .bot => .bot
  | .conj left right => .conj (substitute assignment left) (substitute assignment right)
  | .disj left right => .disj (substitute assignment left) (substitute assignment right)
  | .impl left right => .impl (substitute assignment left) (substitute assignment right)

def rename (renameMap : Atom → Other) : Formula Atom → Formula Other :=
  substitute (fun atom => .atom (renameMap atom))

@[simp] theorem substitute_identity (formula : Formula Atom) :
    substitute Formula.atom formula = formula := by
  induction formula with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj _ _ left right => simp [substitute, left, right]
  | disj _ _ left right => simp [substitute, left, right]
  | impl _ _ left right => simp [substitute, left, right]

theorem substitute_composition {Third : Type*}
    (first : Atom → Formula Other) (second : Other → Formula Third)
    (formula : Formula Atom) :
    substitute second (substitute first formula) =
      substitute (fun atom => substitute second (first atom)) formula := by
  induction formula with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj _ _ left right => simp [substitute, left, right]
  | disj _ _ left right => simp [substitute, left, right]
  | impl _ _ left right => simp [substitute, left, right]

end Formula

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w} {Atom : Type z}

/-- Interpretation uses the actual Heyting implication of the fibre. -/
noncomputable def denote (atoms : Atom → Subfunctor P) : Formula Atom → Subfunctor P
  | .atom atom => atoms atom
  | .top => ⊤
  | .bot => ⊥
  | .conj left right => denote atoms left ⊓ denote atoms right
  | .disj left right => denote atoms left ⊔ denote atoms right
  | .impl left right => denote atoms left ⇨ denote atoms right

/-- Independently specified Kripke--Joyal reading of the finite fragment. -/
def Satisfaction (atoms : Atom → Subfunctor P) :
    Formula Atom → (world : C) → P.obj world → Prop
  | .atom atom, world, sectionValue => sectionValue ∈ (atoms atom).obj world
  | .top, _, _ => True
  | .bot, _, _ => False
  | .conj left right, world, sectionValue =>
      Satisfaction atoms left world sectionValue ∧
        Satisfaction atoms right world sectionValue
  | .disj left right, world, sectionValue =>
      Satisfaction atoms left world sectionValue ∨
        Satisfaction atoms right world sectionValue
  | .impl left right, world, sectionValue =>
      ∀ (future : C) (restriction : world ⟶ future),
        Satisfaction atoms left future (P.map restriction sectionValue) →
          Satisfaction atoms right future (P.map restriction sectionValue)

/-- The actual fibre construction agrees with independently specified
satisfaction for every formula and generalized element. -/
theorem denote_iff_satisfaction (atoms : Atom → Subfunctor P)
    (formula : Formula Atom) (world : C) (sectionValue : P.obj world) :
    sectionValue ∈ (denote atoms formula).obj world ↔
      Satisfaction atoms formula world sectionValue := by
  induction formula generalizing world with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj _ _ left right => exact and_congr (left world _) (right world _)
  | disj _ _ left right => exact or_congr (left world _) (right world _)
  | impl leftFormula rightFormula left right =>
      change sectionValue ∈
        (denote atoms leftFormula ⇨ denote atoms rightFormula).obj world ↔ _
      rw [← himpPointwise_eq_himp]
      change (∀ future restriction,
        P.map restriction sectionValue ∈ (denote atoms leftFormula).obj future →
          P.map restriction sectionValue ∈ (denote atoms rightFormula).obj future) ↔ _
      simp only [Satisfaction, left, right]

theorem satisfaction_restrict (atoms : Atom → Subfunctor P)
    (formula : Formula Atom) {world future : C} (restriction : world ⟶ future)
    {sectionValue : P.obj world} (holds : Satisfaction atoms formula world sectionValue) :
    Satisfaction atoms formula future (P.map restriction sectionValue) := by
  apply (denote_iff_satisfaction atoms formula _ _).mp
  exact (denote atoms formula).map restriction
    ((denote_iff_satisfaction atoms formula _ _).mpr holds)

/-- Substitution of formulas preserves their independently interpreted meaning. -/
theorem denote_substitute {Other : Type z'} (atoms : Other → Subfunctor P)
    (assignment : Atom → Formula Other) (formula : Formula Atom) :
    denote atoms (formula.substitute assignment) =
      denote (fun atom => denote atoms (assignment atom)) formula := by
  induction formula with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj _ _ left right => simp [Formula.substitute, denote, left, right]
  | disj _ _ left right => simp [Formula.substitute, denote, left, right]
  | impl _ _ left right => simp [Formula.substitute, denote, left, right]

theorem denote_rename {Other : Type z'} (atoms : Other → Subfunctor P)
    (renameMap : Atom → Other) (formula : Formula Atom) :
    denote atoms (formula.rename renameMap) = denote (atoms ∘ renameMap) formula :=
  denote_substitute atoms (fun atom => .atom (renameMap atom)) formula

/-- Actual context substitution is inverse image along a presheaf map.
This theorem does not assert preservation under changing the indexing theory. -/
theorem reindex_denote (atoms : Atom → Subfunctor Q) (σ : P ⟶ Q)
    (formula : Formula Atom) :
    (denote atoms formula).preimage σ =
      denote (fun atom => (atoms atom).preimage σ) formula := by
  induction formula with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj leftFormula rightFormula left right =>
      change (denote atoms leftFormula).preimage σ ⊓
        (denote atoms rightFormula).preimage σ = _
      rw [left, right]
      rfl
  | disj leftFormula rightFormula left right =>
      change (denote atoms leftFormula).preimage σ ⊔
        (denote atoms rightFormula).preimage σ = _
      rw [left, right]
      rfl
  | impl leftFormula rightFormula left right =>
      change (denote atoms leftFormula ⇨ denote atoms rightFormula).preimage σ = _
      rw [preimage_himp, left, right]
      rfl

theorem satisfaction_substitution (atoms : Atom → Subfunctor Q) (σ : P ⟶ Q)
    (formula : Formula Atom) (world : C) (sectionValue : P.obj world) :
    Satisfaction (fun atom => (atoms atom).preimage σ) formula world sectionValue ↔
      Satisfaction atoms formula world (σ.app world sectionValue) := by
  rw [← denote_iff_satisfaction, ← reindex_denote, ← denote_iff_satisfaction]
  rfl

theorem negation_iff_all_restrictions (atoms : Atom → Subfunctor P)
    (formula : Formula Atom) (world : C) (sectionValue : P.obj world) :
    Satisfaction atoms formula.negation world sectionValue ↔
      ∀ (future : C) (restriction : world ⟶ future),
        ¬ Satisfaction atoms formula future (P.map restriction sectionValue) := Iff.rfl

/-- The supplied antecedent and its implication determine the consequent at
the current world, by using the identity restriction. -/
theorem implication_elimination (atoms : Atom → Subfunctor P)
    (left right : Formula Atom) (world : C) (sectionValue : P.obj world)
    (function : Satisfaction atoms (.impl left right) world sectionValue)
    (argument : Satisfaction atoms left world sectionValue) :
    Satisfaction atoms right world sectionValue := by
  have result := function world (𝟙 world)
  rw [Functor.map_id_apply] at result
  exact result argument

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Logic
