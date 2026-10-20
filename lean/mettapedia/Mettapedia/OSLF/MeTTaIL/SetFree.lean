import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Patterns that decompose no set

A set-kinded collection is a term modulo the order and the repetition of its elements. Matching a
pattern against one is not yet modulo repetition: a bag match of `{X, Y}` against the presentation
`{a, a}` has no counterpart at the set `{a}`. Until it is, a rule may not decompose a set: the
patterns it matches hold no set-kinded collection (`setFree`): its left side and every premise
(`setFreePremise`). Its right side only builds, so it may build a set. An equation is matched by either
side, so both are asked. A set met by a metavariable is captured whole.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax

mutual
  /-- A pattern with no set-kinded collection: it decomposes bags and vectors, never a set, so a
  set it meets is captured whole. -/
  def setFree : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ arguments => setFreeList arguments
    | .lambda _ body => setFree body
    | .multiLambda _ _ body => setFree body
    | .subst body replacement => setFree body && setFree replacement
    | .collection kind elements _ => !decide (kind = .hashSet) && setFreeList elements

  /-- Every pattern of a list decomposes no set. -/
  def setFreeList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => setFree pattern && setFreeList patterns
end

theorem setFreeList_iff : ∀ {items : List Pattern}, setFreeList items = true ↔ ∀ item ∈ items, setFree item = true
  | [] => by simp [setFreeList]
  | item :: items => by simp [setFreeList, setFreeList_iff]

theorem setFree_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (free : setFree (.collection kind elements rest) = true) :
    kind ≠ .hashSet ∧ ∀ element ∈ elements, setFree element = true := by
  simp only [setFree, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at free
  exact ⟨free.1, setFreeList_iff.mp free.2⟩

/-- A premise that decomposes no set: none of its patterns holds a set-kinded collection. -/
def setFreePremise : Premise → Bool
  | .freshness condition => setFree condition.term
  | .congruence source target => setFree source && setFree target
  | .scopedStep step => setFree step.source && setFree step.target
  | .relationQuery _ arguments => setFreeList arguments
  | .forAll _ _ body => setFreePremise body

/-- A rule that decomposes no set: its left side and every premise. Its right side builds, and
decomposes nothing. -/
def setFreeRule (rule : RewriteRule) : Bool :=
  setFree rule.left && rule.premises.all setFreePremise

/-- An equation that decomposes no set: both sides and every premise. -/
def setFreeEquation (equation : Equation) : Bool :=
  setFree equation.left && setFree equation.right && equation.premises.all setFreePremise

/-! ## Controls -/

/-- A bag pattern with a rest decomposes no set. -/
example : setFree (.collection .hashBag [.fvar "X"] (some "rest")) = true := by decide

/-- A set pattern does, wherever it sits. -/
example : setFree (.apply "f" [.collection .hashSet [.fvar "X"] (some "rest")]) = false := by decide

/-- A rule that builds a set on its right side and matches a bag decomposes no set. -/
example : setFreeRule
    { name := "sum", typeContext := [], premises := [],
      left := .collection .hashBag [.fvar "X", .fvar "Y"] none,
      right := .collection .hashSet [.fvar "X", .fvar "Y"] none } = true := by decide

/-- A rule that matches a set on its left side does. -/
example : setFreeRule
    { name := "split", typeContext := [], premises := [],
      left := .collection .hashSet [.fvar "X", .fvar "Y"] none,
      right := .collection .hashBag [.fvar "X", .fvar "Y"] none } = false := by decide

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
