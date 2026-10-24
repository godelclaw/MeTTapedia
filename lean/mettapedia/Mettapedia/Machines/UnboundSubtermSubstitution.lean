import Mathlib.Data.Finset.Basic

/-!
# Substitution can retain a subterm with unbound support

The independent rewrite relation follows the current environment, including
transitive images. Unrelated bindings may be cyclic. A constructor subtree
whose support is unbound has exactly its original image; its syntax need not
be traversed again after this support fact has been established.

Cells can include a lexical identity. Native metadata must describe those
same materialized identities. Custom rewrite hooks and contextual renaming
are outside the native shortcut. This model does not verify C metadata,
ownership, concurrent mutation, or implementation cost.
-/
set_option autoImplicit false
namespace Mettapedia.Machines.UnboundSubtermSubstitution

inductive Term (Cell Literal : Type) where
  | literal (value : Literal)
  | var (cell : Cell)
  | pair (left right : Term Cell Literal)
  deriving DecidableEq

variable {Cell Literal : Type} [DecidableEq Cell]

def support : Term Cell Literal → Finset Cell
  | .literal _ => ∅
  | .var cell => {cell}
  | .pair left right => support left ∪ support right

abbrev Environment (Cell Literal : Type) := Cell → Option (Term Cell Literal)

inductive Rewrites (environment : Environment Cell Literal) :
    Term Cell Literal → Term Cell Literal → Prop where
  | literal (value : Literal) : Rewrites environment (.literal value) (.literal value)
  | free {cell : Cell} : environment cell = none →
      Rewrites environment (.var cell) (.var cell)
  | bound {cell : Cell} {image result : Term Cell Literal} :
      environment cell = some image → Rewrites environment image result →
      Rewrites environment (.var cell) result
  | pair {left right leftImage rightImage : Term Cell Literal} :
      Rewrites environment left leftImage → Rewrites environment right rightImage →
      Rewrites environment (.pair left right) (.pair leftImage rightImage)

theorem unbound_support_realizes_identity (environment : Environment Cell Literal)
    (term : Term Cell Literal)
    (unbound : ∀ cell ∈ support term, environment cell = none) :
    Rewrites environment term term := by
  induction term with
  | literal value => exact .literal value
  | var cell => exact .free (unbound cell (by simp [support]))
  | pair left right ihLeft ihRight =>
      exact .pair
        (ihLeft (fun cell member => unbound cell (Finset.mem_union_left _ member)))
        (ihRight (fun cell member => unbound cell (Finset.mem_union_right _ member)))

theorem unbound_support_has_only_identity {environment : Environment Cell Literal}
    {term result : Term Cell Literal} (execution : Rewrites environment term result)
    (unbound : ∀ cell ∈ support term, environment cell = none) : result = term := by
  induction execution with
  | literal => rfl
  | free => rfl
  | @bound cell image result bound child ih =>
      have absent := unbound cell (by simp [support])
      rw [bound] at absent
      contradiction
  | @pair left right leftImage rightImage leftStep rightStep ihLeft ihRight =>
      have l := ihLeft (fun cell member => unbound cell (Finset.mem_union_left _ member))
      have r := ihRight (fun cell member => unbound cell (Finset.mem_union_right _ member))
      exact congrArg₂ Term.pair l r

theorem singleton_subterm {environment : Environment Cell Literal}
    (term : Term Cell Literal) (cell : Cell) (single : support term = {cell})
    (unbound : environment cell = none) :
    Rewrites environment term term ∧
      ∀ result, Rewrites environment term result → result = term := by
  have clear : ∀ atCell ∈ support term, environment atCell = none := by
    intro atCell member
    have same : atCell = cell := by simpa only [single, Finset.mem_singleton] using member
    simpa only [same] using unbound
  exact ⟨unbound_support_realizes_identity environment term clear,
    fun _ execution => unbound_support_has_only_identity execution clear⟩

namespace Controls

def exampleTerm : Term Nat Nat := .pair (.literal 4) (.pair (.var 0) (.var 0))
def unrelatedCycle : Environment Nat Nat := fun cell =>
  if cell = 1 then some (.pair (.literal 8) (.var 1)) else none

theorem unrelated_cycle_does_not_rewrite : Rewrites unrelatedCycle exampleTerm exampleTerm := by
  apply unbound_support_realizes_identity
  intro cell member
  simp [exampleTerm, support] at member
  subst cell
  simp [unrelatedCycle]

def boundEnvironment : Environment Nat Nat := fun cell =>
  if cell = 0 then some (.literal 9) else none

theorem changed_binding_changes_image : Rewrites boundEnvironment (.var 0) (.literal 9) :=
  .bound (by simp [boundEnvironment]) (.literal 9)

theorem bound_variable_cannot_be_skipped : ¬ Rewrites boundEnvironment (.var 0) (.var 0) := by
  intro execution
  cases execution with
  | free absent => simp [boundEnvironment] at absent
  | @bound cell image result present child =>
      have image_eq : image = Term.literal 9 := by
        simpa [boundEnvironment] using present.symm
      subst image
      have same := unbound_support_has_only_identity child (by simp [support])
      cases same


end Controls
end Mettapedia.Machines.UnboundSubtermSubstitution
