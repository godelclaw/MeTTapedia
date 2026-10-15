import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Codes

open Mettapedia.OSLF.Framework

/-!
# Propositional codes at a selected carrier and universe

The input leaves are actual native codes, possibly at different carriers and
universes. A recursive checker forms the requested expression only when every
used leaf has the requested carrier and universe and every connective is enabled
by the generated fragment. Its independent formation judgment records both
checks. Unavailable syntax is an elaboration refusal, distinct from a formed
code with no inhabitants.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (LeafCodes leafCarriers leafSorts)
open Mettapedia.OSLF.NativeTypes.Structural (Connective ConnectiveFragment)
open ModalHypercube (HSort)

inductive Expression where
  | leaf (index : Nat)
  | top | bottom
  | conjunction (first second : Expression)
  | disjunction (first second : Expression)
  | implication (first second : Expression)
  | negation (inner : Expression)
  deriving DecidableEq, Repr

inductive Formed (fragment : ConnectiveFragment) (carriers : Nat → TypeExpr)
    (sorts : Nat → HSort) (carrier : TypeExpr) (sort : HSort) : Expression → Prop where
  | leaf (index : Nat) (carried : carriers index = carrier) (kinded : sorts index = sort) :
      Formed fragment carriers sorts carrier sort (.leaf index)
  | top (enabled : fragment.admits .top = true) :
      Formed fragment carriers sorts carrier sort .top
  | bottom (enabled : fragment.admits .bottom = true) :
      Formed fragment carriers sorts carrier sort .bottom
  | conjunction {first second : Expression} (enabled : fragment.admits .conjunction = true)
      (left : Formed fragment carriers sorts carrier sort first)
      (right : Formed fragment carriers sorts carrier sort second) :
      Formed fragment carriers sorts carrier sort (.conjunction first second)
  | disjunction {first second : Expression} (enabled : fragment.admits .disjunction = true)
      (left : Formed fragment carriers sorts carrier sort first)
      (right : Formed fragment carriers sorts carrier sort second) :
      Formed fragment carriers sorts carrier sort (.disjunction first second)
  | implication {first second : Expression} (enabled : fragment.admits .implication = true)
      (left : Formed fragment carriers sorts carrier sort first)
      (right : Formed fragment carriers sorts carrier sort second) :
      Formed fragment carriers sorts carrier sort (.implication first second)
  | negation {inner : Expression} (enabled : fragment.admits .negation = true)
      (inside : Formed fragment carriers sorts carrier sort inner) :
      Formed fragment carriers sorts carrier sort (.negation inner)

def checkFormation (fragment : ConnectiveFragment) (carriers : Nat → TypeExpr)
    (sorts : Nat → HSort) (carrier : TypeExpr) (sort : HSort) : Expression → Bool
  | .leaf index => decide (carriers index = carrier) && decide (sorts index = sort)
  | .top => fragment.admits .top
  | .bottom => fragment.admits .bottom
  | .conjunction first second => fragment.admits .conjunction &&
      checkFormation fragment carriers sorts carrier sort first &&
      checkFormation fragment carriers sorts carrier sort second
  | .disjunction first second => fragment.admits .disjunction &&
      checkFormation fragment carriers sorts carrier sort first &&
      checkFormation fragment carriers sorts carrier sort second
  | .implication first second => fragment.admits .implication &&
      checkFormation fragment carriers sorts carrier sort first &&
      checkFormation fragment carriers sorts carrier sort second
  | .negation inner => fragment.admits .negation &&
      checkFormation fragment carriers sorts carrier sort inner

theorem checkFormation_complete {fragment : ConnectiveFragment} {carriers : Nat → TypeExpr}
    {sorts : Nat → HSort} {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    (formed : Formed fragment carriers sorts carrier sort expression) :
    checkFormation fragment carriers sorts carrier sort expression = true := by
  induction formed <;> simp_all [checkFormation]

theorem checkFormation_sound (fragment : ConnectiveFragment) (carriers : Nat → TypeExpr)
    (sorts : Nat → HSort) (carrier : TypeExpr) (sort : HSort) (expression : Expression) :
    checkFormation fragment carriers sorts carrier sort expression = true →
      Formed fragment carriers sorts carrier sort expression := by
  induction expression with
  | leaf index =>
      intro checked
      simp only [checkFormation, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact .leaf index checked.1 checked.2
  | top => exact Formed.top
  | bottom => exact Formed.bottom
  | conjunction first second ihFirst ihSecond =>
      intro checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .conjunction checked.1.1 (ihFirst checked.1.2) (ihSecond checked.2)
  | disjunction first second ihFirst ihSecond =>
      intro checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .disjunction checked.1.1 (ihFirst checked.1.2) (ihSecond checked.2)
  | implication first second ihFirst ihSecond =>
      intro checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .implication checked.1.1 (ihFirst checked.1.2) (ihSecond checked.2)
  | negation inner ih =>
      intro checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .negation checked.1 (ih checked.2)

theorem checkFormation_exact (fragment : ConnectiveFragment) (carriers : Nat → TypeExpr)
    (sorts : Nat → HSort) (carrier : TypeExpr) (sort : HSort) (expression : Expression) :
    checkFormation fragment carriers sorts carrier sort expression = true ↔
      Formed fragment carriers sorts carrier sort expression :=
  ⟨checkFormation_sound fragment carriers sorts carrier sort expression, checkFormation_complete⟩

def rawMeaning {generated : Generated} {bound : List TypeExpr}
    (leaves : LeafCodes generated bound) : Expression → Pattern → Prop
  | .leaf index, term => (leaves index).2.2.meaning term
  | .top, _ => True
  | .bottom, _ => False
  | .conjunction first second, term => rawMeaning leaves first term ∧ rawMeaning leaves second term
  | .disjunction first second, term => rawMeaning leaves first term ∨ rawMeaning leaves second term
  | .implication first second, term => rawMeaning leaves first term → rawMeaning leaves second term
  | .negation inner, term => ¬ rawMeaning leaves inner term

def meaning (generated : Generated) (bound : List TypeExpr) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (expression : Expression) (term : Pattern) : Prop :=
  HasType generated.snapshot.language generated.snapshot.free bound term carrier ∧
    rawMeaning leaves expression term

structure ClassifiedCode (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) where
  expression : Expression
  formation : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves)
    carrier sort expression
  code : TypeCode generated.plan bound carrier sort
  readout : ∀ term, code.meaning term ↔ meaning generated bound leaves carrier expression term

def classify (generated : Generated) (bound : List TypeExpr) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves)
      carrier sort expression) : ClassifiedCode generated bound leaves carrier sort where
  expression := expression
  formation := formed
  code := {
    meaning := meaning generated bound leaves carrier expression
    bounded := fun _ inhabited => inhabited.1}
  readout _ := Iff.rfl

def firstDenied (fragment : ConnectiveFragment) : Expression → Option Connective
  | .leaf _ => none
  | .top => if fragment.admits .top then none else some .top
  | .bottom => if fragment.admits .bottom then none else some .bottom
  | .conjunction first second => if fragment.admits .conjunction then
      (firstDenied fragment first).or (firstDenied fragment second) else some .conjunction
  | .disjunction first second => if fragment.admits .disjunction then
      (firstDenied fragment first).or (firstDenied fragment second) else some .disjunction
  | .implication first second => if fragment.admits .implication then
      (firstDenied fragment first).or (firstDenied fragment second) else some .implication
  | .negation inner => if fragment.admits .negation then firstDenied fragment inner else some .negation

inductive Refusal where
  | unavailable (connective : Connective)
  | incompatibleCarrierOrUniverse
  deriving DecidableEq, Repr

def compilePropositionalCode (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (expression : Expression) :
    Except Refusal (ClassifiedCode generated bound leaves carrier sort) :=
  match firstDenied generated.logicFragment expression with
  | some connective => .error (.unavailable connective)
  | none =>
      if checked : checkFormation generated.logicFragment (leafCarriers leaves) (leafSorts leaves)
          carrier sort expression = true then
        .ok (classify generated bound leaves carrier sort expression
          ((checkFormation_exact _ _ _ _ _ _).mp checked))
      else .error .incompatibleCarrierOrUniverse

theorem formed_no_denied {fragment : ConnectiveFragment} {carriers : Nat → TypeExpr}
    {sorts : Nat → HSort} {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    (formed : Formed fragment carriers sorts carrier sort expression) :
    firstDenied fragment expression = none := by
  induction formed <;> simp_all [firstDenied]

theorem generated_propositional_formation_complete (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves)
      carrier sort expression) :
    ∃ output, compilePropositionalCode generated bound leaves carrier sort expression = .ok output ∧
      output.expression = expression := by
  simp only [compilePropositionalCode, formed_no_denied formed, checkFormation_complete formed,
    dite_true]
  exact ⟨_, rfl, rfl⟩

theorem generated_propositional_formation_sound {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    {expression : Expression} {output : ClassifiedCode generated bound leaves carrier sort}
    (compiled : compilePropositionalCode generated bound leaves carrier sort expression = .ok output) :
    output.expression = expression ∧
      Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression := by
  unfold compilePropositionalCode at compiled
  split at compiled
  · cases compiled
  · split at compiled
    · cases compiled
      exact ⟨rfl, (checkFormation_exact _ _ _ _ _ _).mp (by assumption)⟩
    · cases compiled

theorem generated_propositional_readout {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    {expression : Expression} {output : ClassifiedCode generated bound leaves carrier sort}
    (compiled : compilePropositionalCode generated bound leaves carrier sort expression = .ok output)
    (term : Pattern) : output.code.meaning term ↔
      HasType generated.snapshot.language generated.snapshot.free bound term carrier ∧
        rawMeaning leaves expression term := by
  rw [output.readout term, (generated_propositional_formation_sound compiled).1]
  rfl

theorem meaning_top (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (term : Pattern) :
    meaning generated bound leaves carrier .top term ↔
      HasType generated.snapshot.language generated.snapshot.free bound term carrier := by
  simp [meaning, rawMeaning]

theorem meaning_bottom (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (term : Pattern) :
    ¬ meaning generated bound leaves carrier .bottom term := by
  simp [meaning, rawMeaning]

theorem meaning_conjunction (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (first second : Expression) (term : Pattern) :
    meaning generated bound leaves carrier (.conjunction first second) term ↔
      meaning generated bound leaves carrier first term ∧ meaning generated bound leaves carrier second term := by
  simp [meaning, rawMeaning, and_left_comm, and_assoc]

theorem meaning_disjunction (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (first second : Expression) (term : Pattern) :
    meaning generated bound leaves carrier (.disjunction first second) term ↔
      meaning generated bound leaves carrier first term ∨ meaning generated bound leaves carrier second term := by
  simp [meaning, rawMeaning, and_or_left]

theorem meaning_implication (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (first second : Expression) (term : Pattern) :
    meaning generated bound leaves carrier (.implication first second) term ↔
      HasType generated.snapshot.language generated.snapshot.free bound term carrier ∧
        (meaning generated bound leaves carrier first term → meaning generated bound leaves carrier second term) := by
  constructor
  · intro inhabited
    exact ⟨inhabited.1, fun first => ⟨inhabited.1, inhabited.2 first.2⟩⟩
  · intro inhabited
    exact ⟨inhabited.1, fun first => (inhabited.2 ⟨inhabited.1, first⟩).2⟩

theorem meaning_negation (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (inner : Expression) (term : Pattern) :
    meaning generated bound leaves carrier (.negation inner) term ↔
      HasType generated.snapshot.language generated.snapshot.free bound term carrier ∧
        ¬ meaning generated bound leaves carrier inner term := by
  constructor
  · intro inhabited
    exact ⟨inhabited.1, fun inside => inhabited.2 inside.2⟩
  · intro inhabited
    exact ⟨inhabited.1, fun inside => inhabited.2 ⟨inhabited.1, inside⟩⟩

theorem disabled_negation_refused (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (inner : Expression)
    (disabled : generated.logicFragment.admits .negation = false) :
    compilePropositionalCode generated bound leaves carrier sort (.negation inner) =
      .error (.unavailable .negation) := by
  simp [compilePropositionalCode, firstDenied, disabled]

theorem mixed_universe_leaf_rejected (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (index : Nat)
    (different : leafSorts leaves index ≠ sort) :
    compilePropositionalCode generated bound leaves carrier sort (.leaf index) =
      .error .incompatibleCarrierOrUniverse := by
  simp [compilePropositionalCode, firstDenied, checkFormation, different]

end Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes
