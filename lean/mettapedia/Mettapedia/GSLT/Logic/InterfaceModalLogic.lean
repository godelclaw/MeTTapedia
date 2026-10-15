import Mettapedia.GSLT.Logic.RedexRelativeCongruence

/-!
# Finitary modal observations at every actual reaction interface

A formula retains the source and target of each complete context arrow.
Its diamond uses the independently constructed idem-pushout firing relation,
including the selected reaction and full result. Formula syntax and
satisfaction are independent of bisimilarity and of structural tests.

Every interface-indexed IPO bisimulation preserves this full modal grammar.
The converse requires a separate branching or separating-domain argument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceModalLogic

open _root_.CategoryTheory
open RedexRelativeCongruence

universe u v

variable {C : Type u} [Category.{v} C] {origin : C}

inductive Formula (C : Type u) [Category.{v} C] : C → Type (max u v) where
  | top {interface} : Formula C interface
  | conj {interface} (first second : Formula C interface) : Formula C interface
  | neg {interface} (inner : Formula C interface) : Formula C interface
  | diamond {first last} (label : first ⟶ last) (inner : Formula C last) : Formula C first

def Formula.conjList {interface : C} : List (Formula C interface) → Formula C interface
  | [] => .top
  | first :: rest => .conj first (Formula.conjList rest)

def Holds (rules : ReactionRule origin → Prop) :
    {interface : C} → Formula C interface → (origin ⟶ interface) → Prop
  | _, .top, _ => True
  | _, .conj first second, agent => Holds rules first agent ∧ Holds rules second agent
  | _, .neg inner, agent => ¬Holds rules inner agent
  | _, .diamond label inner, agent =>
      ∃ target, ActIPO rules label agent target ∧ Holds rules inner target

variable (rules : ReactionRule origin → Prop)

theorem holds_conjList {interface : C} (formulas : List (Formula C interface))
    (agent : origin ⟶ interface) :
    Holds rules (Formula.conjList formulas) agent ↔
      ∀ formula ∈ formulas, Holds rules formula agent := by
  induction formulas with
  | nil => simp [Formula.conjList, Holds]
  | cons first rest inductionHypothesis =>
    simp only [Formula.conjList, Holds, List.mem_cons, forall_eq_or_imp, inductionHypothesis]

def LogicallyEquivalent {interface : C} (first second : origin ⟶ interface) : Prop :=
  ∀ formula : Formula C interface, Holds rules formula first ↔ Holds rules formula second

theorem logicallyEquivalent_refl {interface : C} (agent : origin ⟶ interface) :
    LogicallyEquivalent rules agent agent := fun _ => Iff.rfl

theorem logicallyEquivalent_symm {interface : C} {first second : origin ⟶ interface}
    (related : LogicallyEquivalent rules first second) : LogicallyEquivalent rules second first :=
  fun formula => (related formula).symm

theorem logicallyEquivalent_trans {interface : C} {first middle last : origin ⟶ interface}
    (before : LogicallyEquivalent rules first middle) (after : LogicallyEquivalent rules middle last) :
    LogicallyEquivalent rules first last := fun formula => (before formula).trans (after formula)

theorem holds_iff_of_bisimulation
    (relation : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop)
    (bisimulation : IsIPOBisimulation rules relation) {interface : C}
    (formula : Formula C interface) :
    ∀ (first second : origin ⟶ interface), relation interface first second →
      (Holds rules formula first ↔ Holds rules formula second) := by
  apply @Formula.rec C inferInstance
    (fun interface formula => ∀ (first second : origin ⟶ interface), relation interface first second →
      (Holds rules formula first ↔ Holds rules formula second)) (t := formula)
  · intro interface first second related
    exact Iff.rfl
  · intro interface firstFormula secondFormula firstRead secondRead first second related
    exact and_congr (firstRead first second related) (secondRead first second related)
  · intro interface inner inductionHypothesis first second related
    exact not_congr (inductionHypothesis first second related)
  · intro firstInterface lastInterface label inner inductionHypothesis first second related
    constructor
    · rintro ⟨next, step, holds⟩
      obtain ⟨matched, actual, successors⟩ := (bisimulation first second related).1 label next step
      exact ⟨matched, actual, (inductionHypothesis next matched successors).mp holds⟩
    · rintro ⟨next, step, holds⟩
      obtain ⟨matched, actual, successors⟩ := (bisimulation first second related).2 label next step
      exact ⟨matched, actual, (inductionHypothesis matched next successors).mpr holds⟩

theorem logicallyEquivalent_of_ipoBisimilar {interface : C} {first second : origin ⟶ interface}
    (related : IPOBisimilar rules first second) : LogicallyEquivalent rules first second := by
  obtain ⟨relation, bisimulation, pair⟩ := related
  exact fun formula => holds_iff_of_bisimulation rules relation bisimulation formula first second pair

end Mettapedia.GSLT.InterfaceModalLogic
