import Mettapedia.GSLT.Parsing.CanonicalGrammar
import Mettapedia.GSLT.Parsing.ExactPresentation

/-!
# Reified abbreviations with a recursive exact-constructor fallback

Rules contain a head, an arity and a constructor template. Their interpretation
is executable and refuses duplicate dispatch keys and missing template slots.
A view may propose arbitrary abbreviations; an expansion check keeps only
ones that reconstruct the original abstract syntax tree. Fallback keeps the exact
constructor while recursively retaining child views.

This is a structural tree interpreter over the existing GSLT term carrier.
It is not the native compact C adapter: sort admission, atom serialization,
source lexing, binding and C-specific declaration views remain separate.
The rules are data, but no self-modifying operational calculus is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CheckedTreePresentation

open CanonicalGrammar (CanonicalTerm)
open ExactPresentation (Presentation checkedChoice checkedChoice_exact)

/-! Equality is constructive over the existing nested term carrier. -/

mutual
  def equalTree : CanonicalTerm → CanonicalTerm → Bool
    | .text first, .text second => first == second
    | .node first children, .node second others => first == second && equalTrees children others
    | .seq elements, .seq others => equalTrees elements others
    | _, _ => false

  def equalTrees : List CanonicalTerm → List CanonicalTerm → Bool
    | [], [] => true
    | first :: rest, second :: others => equalTree first second && equalTrees rest others
    | _, _ => false
end

mutual
  theorem equalTree_self (tree : CanonicalTerm) : equalTree tree tree = true := by
    cases tree with
    | text spelling => simp [equalTree]
    | node name children => simp [equalTree, equalTrees_self children]
    | seq elements => exact equalTrees_self elements
  termination_by sizeOf tree

  theorem equalTrees_self (trees : List CanonicalTerm) : equalTrees trees trees = true := by
    cases trees with
    | nil => rfl
    | cons first rest => simp [equalTrees, equalTree_self first, equalTrees_self rest]
  termination_by sizeOf trees
end

mutual
  theorem equalTree_reflects (first second : CanonicalTerm)
      (equal : equalTree first second = true) : first = second := by
    cases first <;> cases second <;> simp only [equalTree] at equal
    · rename_i name children otherName others
      simp only [Bool.and_eq_true] at equal
      rcases equal with ⟨names, arguments⟩
      have sameName := beq_iff_eq.mp names
      have sameArguments := equalTrees_reflects children others arguments
      subst otherName
      subst others
      rfl
    · cases equal
    · cases equal
    · cases equal
    · exact congrArg CanonicalTerm.text (beq_iff_eq.mp equal)
    · cases equal
    · cases equal
    · cases equal
    · exact congrArg CanonicalTerm.seq (equalTrees_reflects _ _ equal)
  termination_by sizeOf first

  theorem equalTrees_reflects (first second : List CanonicalTerm)
      (equal : equalTrees first second = true) : first = second := by
    cases first with
    | nil => cases second <;> simp_all [equalTrees]
    | cons tree rest =>
        cases second with
        | nil => cases equal
        | cons other others =>
            simp only [equalTrees, Bool.and_eq_true] at equal
            rcases equal with ⟨head, tail⟩
            have sameHead := equalTree_reflects tree other head
            have sameTail := equalTrees_reflects rest others tail
            subst other
            subst others
            rfl
  termination_by sizeOf first
end

def decidableTreeEquality : DecidableEq CanonicalTerm := fun first second =>
  if equal : equalTree first second = true then
    isTrue (equalTree_reflects first second equal)
  else
    isFalse (fun same => equal (same ▸ equalTree_self first))

local instance : DecidableEq CanonicalTerm := decidableTreeEquality

inductive Template where
  | slot (index : Nat)
  | text (spelling : String)
  | node (name : String) (children : List Template)
  | seq (elements : List Template)
  deriving Repr

mutual
  def instantiate (arguments : List CanonicalTerm) : Template → Option CanonicalTerm
    | .slot index => arguments[index]?
    | .text spelling => some (.text spelling)
    | .node name children => (instantiateMany arguments children).map (.node name)
    | .seq elements => (instantiateMany arguments elements).map .seq

  def instantiateMany (arguments : List CanonicalTerm) :
      List Template → Option (List CanonicalTerm)
    | [] => some []
    | first :: rest => do
        return (← instantiate arguments first) :: (← instantiateMany arguments rest)
end

structure Rule where
  head : String
  arity : Nat
  body : Template
  deriving Repr

/-- Dispatch cannot resolve two applicable rules by their list order. -/
def interpret (rules : List Rule) (head : String) (arguments : List CanonicalTerm) :
    Option CanonicalTerm :=
  match rules.filter (fun rule => rule.head == head && rule.arity == arguments.length) with
  | [rule] => instantiate arguments rule.body
  | _ => none

inductive Surface where
  | text (spelling : String)
  | node (name : String) (children : List Surface)
  | seq (elements : List Surface)
  | form (head : String) (arguments : List Surface)
  deriving Repr

mutual
  def expand (rules : List Rule) : Surface → Option CanonicalTerm
    | .text spelling => some (.text spelling)
    | .node name children => (expandMany rules children).map (.node name)
    | .seq elements => (expandMany rules elements).map .seq
    | .form head arguments => do
        interpret rules head (← expandMany rules arguments)

  def expandMany (rules : List Rule) : List Surface → Option (List CanonicalTerm)
    | [] => some []
    | first :: rest => do
        return (← expand rules first) :: (← expandMany rules rest)
end

/-- The proposer sees both the original node and the recursively constructed
child views. It supplies a candidate, not evidence that the candidate is exact. -/
abbrev Proposer := CanonicalTerm → List Surface → Option Surface

mutual
  def view (rules : List Rule) (propose : Proposer) : CanonicalTerm → Surface
    | tree@(.text spelling) =>
        checkedChoice (expand rules) (.text spelling) (propose tree []) tree
    | tree@(.node name children) =>
        let views := viewMany rules propose children
        checkedChoice (expand rules) (.node name views) (propose tree views) tree
    | tree@(.seq elements) =>
        let views := viewMany rules propose elements
        checkedChoice (expand rules) (.seq views) (propose tree views) tree

  def viewMany (rules : List Rule) (propose : Proposer) : List CanonicalTerm → List Surface
    | [] => []
    | first :: rest => view rules propose first :: viewMany rules propose rest
end

mutual
  /-- Structural induction derives total exactness even for a faulty proposer
  or ambiguous rules. Children retain compact views inside exact fallback. -/
  theorem expand_view (rules : List Rule) (propose : Proposer) (tree : CanonicalTerm) :
      expand rules (view rules propose tree) = some tree := by
    cases tree with
    | text spelling =>
        exact checkedChoice_exact _ _ _ _ rfl
    | node name children =>
        apply checkedChoice_exact
        simp only [expand, expand_viewMany rules propose children, Option.map_some]
    | seq elements =>
        apply checkedChoice_exact
        simp only [expand, expand_viewMany rules propose elements, Option.map_some]
  termination_by sizeOf tree

  theorem expand_viewMany (rules : List Rule) (propose : Proposer)
      (trees : List CanonicalTerm) :
      expandMany rules (viewMany rules propose trees) = some trees := by
    cases trees with
    | nil => rfl
    | cons first rest =>
        simp [viewMany, expandMany, expand_view rules propose first,
          expand_viewMany rules propose rest]
  termination_by sizeOf trees
end

/-- One untyped tree section. A sorted C presentation additionally supplies
its schema admission obligations; no sort check is inferred from this model. -/
def presentation (key : ExactPresentation.Key) (rules : List Rule) (propose : Proposer) :
    Presentation (fun _ : Unit => CanonicalTerm) (fun _ : Unit => Surface) where
  key := key
  expand := expand rules
  view := view rules propose
  expand_view := expand_view rules propose

end Mettapedia.GSLT.Parsing.CheckedTreePresentation
