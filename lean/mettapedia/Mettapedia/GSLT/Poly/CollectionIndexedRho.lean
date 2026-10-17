import Mettapedia.GSLT.Poly.CollectionIndexedEquiv
import Mathlib.Logic.Equiv.Defs

/-!
# Root bag permutation of closed ρ processes

`rhoCalc` is in the collection fragment. Closed processes at `Proc` are the
indexed trees at the empty context. Permuting the elements of one outermost
hash bag, and no other equation, is the same equivalence on those trees and
on the closed patterns. Permuting the payload of an output is a contextual
step and is not one of those outermost steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedRho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.CollectionIndexed
open Mettapedia.GSLT.Poly.CollectionIndexedEquiv
open Mettapedia.GSLT.Poly.RhoCalcControl

/-- A bare collection in `rhoCalc` is the parallel bag. -/
theorem rhoCalc_uniqueBare : UniqueBare rhoCalc := by
  intro rule₁ rule₂ kind element₁ element₂ mem₁ mem₂ _category bare₁ bare₂
  simp only [rhoCalc, List.mem_cons, List.mem_nil_iff, or_false] at mem₁ mem₂
  rcases mem₁ with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [bareCollection?] at bare₁
  · simp [bareCollection?, TypeExpr.name, TypeExpr.baseType] at bare₁
  · simp [bareCollection?, TypeExpr.proc, TypeExpr.baseType] at bare₁
  · rcases mem₂ with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [bareCollection?] at bare₂
    · simp [bareCollection?, TypeExpr.name, TypeExpr.baseType] at bare₂
    · simp [bareCollection?, TypeExpr.proc, TypeExpr.baseType] at bare₂
    · rfl
    · simp [bareCollection?, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at bare₂
    · simp [bareCollection?, TypeExpr.funType, TypeExpr.name, TypeExpr.proc,
        TypeExpr.baseType] at bare₂
  · simp [bareCollection?, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at bare₁
  · simp [bareCollection?, TypeExpr.funType, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType] at bare₁

/-- Outermost bag permutation of an indexed tree at `Proc`. -/
def rhoRootSetoid : Setoid (Tree rhoCalc ([], "Proc")) where
  r left right :=
    Relation.EqvGen RhoBagStep (toPattern left) (toPattern right)
  iseqv :=
    { refl := fun tree => Relation.EqvGen.refl (toPattern tree)
      symm := fun related => Relation.EqvGen.symm _ _ related
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Closed processes modulo outermost bag permutation are the indexed trees
modulo the same relation. -/
noncomputable def rhoRootQuotientEquiv :
    Quotient rhoRootSetoid ≃ Quotient rhoBagSetoid :=
  Quotient.congr
    (closedIndexedEquiv rhoCalc_fragment rhoCalc_labels rhoCalc_uniqueBare "Proc")
    (fun left right => by
      show Relation.EqvGen RhoBagStep (toPattern left) (toPattern right) ↔
        Relation.EqvGen RhoBagStep
          ((closedIndexedEquiv rhoCalc_fragment rhoCalc_labels rhoCalc_uniqueBare "Proc")
            left).1
          ((closedIndexedEquiv rhoCalc_fragment rhoCalc_labels rhoCalc_uniqueBare "Proc")
            right).1
      rfl)

/-- An output whose payload is the ordered parallel bag. -/
def outputOrdered : Pattern :=
  .apply "POutput" [.apply "NQuote" [procZero], orderedPar]

/-- The same output with the payload bag reversed. -/
def outputSwapped : Pattern :=
  .apply "POutput" [.apply "NQuote" [procZero], swappedPar]

theorem outputOrdered_typed :
    HasType rhoCalc FreeTypeContext.empty [] outputOrdered (.base "Proc") := by
  have arguments : ArgumentsHaveTypes rhoCalc FreeTypeContext.empty []
      [.apply "NQuote" [procZero], orderedPar] outputRule.params := by
    rw [outputRule_params]
    exact .cons trivial rfl quoteZero_typed
      (.cons trivial rfl orderedPar_typed (ArgumentsHaveTypes.nil (bound := [])))
  have typed := HasType.constructor (rule := outputRule) (ruleAt_mem 4 output_bound)
    not_bare_output arguments
  simpa [outputOrdered, outputRule_label, outputRule_category] using typed

theorem outputSwapped_typed :
    HasType rhoCalc FreeTypeContext.empty [] outputSwapped (.base "Proc") := by
  have arguments : ArgumentsHaveTypes rhoCalc FreeTypeContext.empty []
      [.apply "NQuote" [procZero], swappedPar] outputRule.params := by
    rw [outputRule_params]
    exact .cons trivial rfl quoteZero_typed
      (.cons trivial rfl swappedPar_typed (ArgumentsHaveTypes.nil (bound := [])))
  have typed := HasType.constructor (rule := outputRule) (ruleAt_mem 4 output_bound)
    not_bare_output arguments
  simpa [outputSwapped, outputRule_label, outputRule_category] using typed

theorem outputOrdered_object : isObjectPattern outputOrdered = true := by
  simp [outputOrdered, orderedPar, procDrop, procOutput, procZero, isObjectPattern,
    isObjectPatternList]

theorem outputSwapped_object : isObjectPattern outputSwapped = true := by
  simp [outputSwapped, swappedPar, procDrop, procOutput, procZero, isObjectPattern,
    isObjectPatternList]

def outputOrderedClosed : ClosedObject rhoCalc "Proc" :=
  ⟨outputOrdered, outputOrdered_typed, outputOrdered_object⟩

def outputSwappedClosed : ClosedObject rhoCalc "Proc" :=
  ⟨outputSwapped, outputSwapped_typed, outputSwapped_object⟩

/-- A pattern that is itself a hash bag. -/
def IsHashBag (pattern : Pattern) : Prop :=
  ∃ elements, pattern = .collection .hashBag elements none

theorem rhoBagStep_bags {left right : Pattern} (step : RhoBagStep left right) :
    IsHashBag left ∧ IsHashBag right := by
  cases step with
  | @perm elements swapped _permutation =>
      exact ⟨⟨elements, rfl⟩, ⟨swapped, rfl⟩⟩

/-- An outermost bag step never rewrites an application. Two applications are
related only when they are the same pattern. -/
theorem eqvGen_eq_or_bags {left right : Pattern}
    (related : Relation.EqvGen RhoBagStep left right) :
    left = right ∨ (IsHashBag left ∧ IsHashBag right) := by
  induction related with
  | rel _ _ step => exact Or.inr (rhoBagStep_bags step)
  | refl => exact Or.inl rfl
  | symm _ _ _ inductionHypothesis =>
      cases inductionHypothesis with
      | inl equal => exact Or.inl equal.symm
      | inr both => exact Or.inr ⟨both.2, both.1⟩
  | trans _ _ _ _ _ first second =>
      cases first with
      | inl equal =>
          subst equal
          exact second
      | inr bothLeft =>
          cases second with
          | inl equal =>
              subst equal
              exact Or.inr bothLeft
          | inr bothRight => exact Or.inr ⟨bothLeft.1, bothRight.2⟩

theorem output_swap_not_root :
    ¬ Relation.EqvGen RhoBagStep outputOrdered outputSwapped := by
  intro related
  cases eqvGen_eq_or_bags related with
  | inl equal =>
      simp [outputOrdered, outputSwapped, orderedPar, swappedPar, procDrop, procOutput,
        procZero, Pattern.apply.injEq, Pattern.collection.injEq] at equal
  | inr both =>
      obtain ⟨_, equal⟩ := both.1
      simp [outputOrdered] at equal

/-- Reversing the payload bag is a contextual pattern step. -/
theorem output_swap_contextual : PatternCong outputOrdered outputSwapped :=
  PatternCong.applyAt (before := [.apply "NQuote" [procZero]])
    (PatternCong.bagPerm (List.Perm.swap procDrop procOutput []).symm)

/-- The outermost bag relation is not the contextual pattern congruence. -/
theorem root_relation_not_contextual :
    ¬ (∀ left right : ClosedObject rhoCalc "Proc",
        (patternSetoid (language := rhoCalc) "Proc").r left right ↔
          rhoBagSetoid.r left right) := by
  intro agree
  have contextual :
      (patternSetoid (language := rhoCalc) "Proc").r outputOrderedClosed outputSwappedClosed :=
    output_swap_contextual
  have rooted := (agree outputOrderedClosed outputSwappedClosed).mp contextual
  exact output_swap_not_root rooted

end Mettapedia.GSLT.Poly.CollectionIndexedRho
