import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Query classification before substitution

A nested `match` may receive its query from an earlier match. A variable can
then become a conjunction or disjunction; a variable in head position can
become the connective symbol. Compiling either as an atomic query beforehand
changes its interpretation.

This module characterizes exactly which query roots remain atomic under every
simultaneous substitution. Variables below a fixed head remain admissible.
The result licenses only root classification. Join reordering, read windows,
effect ordering, ownership and native implementation adequacy are separate
obligations. The pipe connective is a CeTTa extension to the HE query grammar.
-/

namespace Mettapedia.Languages.MeTTa.QueryRootStability

open OSLFCore (Atom)
open SubstitutionAlgebra

inductive Form where
  | atomic
  | conjunction
  | disjunction
  deriving DecidableEq, Repr

def form : Atom → Form
  | .expression (.symbol head :: _) =>
      if head = "," then .conjunction
      else if head = "|" then .disjunction
      else .atomic
  | _ => .atomic

/-- Admission depends only on the root and its immediate head, not on whether
the complete query is ground. -/
def canFlatten : Atom → Bool
  | .var _ => false
  | .expression (.var _ :: _) => false
  | query => decide (form query = .atomic)

/-- Every admitted root is still an atomic pattern after any substitution. -/
theorem canFlatten_sound (query : Atom) (accepted : canFlatten query = true)
    (σ : Subst) : form (subst σ query) = .atomic := by
  cases query with
  | symbol name => rfl
  | grounded value => rfl
  | var name => simp [canFlatten] at accepted
  | expression atoms =>
      cases atoms with
      | nil => rfl
      | cons head tail =>
          cases head with
          | symbol name =>
              have atomic : form (.expression (.symbol name :: tail)) = .atomic :=
                of_decide_eq_true accepted
              simpa [form, subst, subst.substList] using atomic
          | var name => simp [canFlatten] at accepted
          | grounded value => rfl
          | expression inner => rfl

/-- A whole-query variable can denote even the nullary conjunction. -/
theorem variable_can_become_conjunction (name : String) :
    ∃ σ : Subst, form (subst σ (.var name)) = .conjunction := by
  exact ⟨fun _ => some (.expression [.symbol ","]), rfl⟩

/-- A variable-headed query needs the same protection as a whole-query
variable, regardless of how its argument patterns are shaped. -/
theorem variable_head_can_become_conjunction (name : String) (tail : List Atom) :
    ∃ σ : Subst, form (subst σ (.expression (.var name :: tail))) = .conjunction := by
  exact ⟨fun _ => some (.symbol ","), rfl⟩

/-- No larger syntactic admission predicate can promise atomic interpretation
under arbitrary later substitutions. This is maximality for classification,
not a claim that every admitted join is safe to reorder or fuse. -/
theorem canFlatten_iff (query : Atom) :
    canFlatten query = true ↔ ∀ σ : Subst, form (subst σ query) = .atomic := by
  constructor
  · exact canFlatten_sound query
  · intro stable
    cases query with
    | symbol name => rfl
    | grounded value => rfl
    | var name =>
        obtain ⟨σ, changes⟩ := variable_can_become_conjunction name
        have impossible := (stable σ).symm.trans changes
        contradiction
    | expression atoms =>
        cases atoms with
        | nil => rfl
        | cons head tail =>
            cases head with
            | symbol name =>
                have same := stable empty
                rw [subst_empty] at same
                simpa [canFlatten] using same
            | var name =>
                obtain ⟨σ, changes⟩ := variable_head_can_become_conjunction name tail
                have impossible := (stable σ).symm.trans changes
                contradiction
            | grounded value => rfl
            | expression inner => rfl

/-- Deferring more than one substitution does not weaken the admission law. -/
theorem canFlatten_after_composition (query : Atom)
    (accepted : canFlatten query = true) (σ τ : Subst) :
    form (subst τ (subst σ query)) = .atomic := by
  rw [subst_subst]
  exact canFlatten_sound query accepted (comp σ τ)

-- Open argument fields are safe; requiring the whole term to be ground
-- would reject the normal pattern-matching use case.
example : canFlatten (.expression [.symbol "edge", .var "x", .var "y"]) = true := rfl

-- A stable compound head stays a compound head even if its children change.
example : canFlatten (.expression [.expression [.var "head"], .var "arg"]) = true := rfl

-- Classification before substitution is observably different for both
-- the conjunction and the disjunction vocabulary.
example : form (.var "query") ≠
    form (subst (fun _ => some (.expression [.symbol ","])) (.var "query")) := by decide

example : form (.expression [.var "head", .symbol "a"]) ≠
    form (subst (fun _ => some (.symbol "|"))
      (.expression [.var "head", .symbol "a"])) := by decide

end Mettapedia.Languages.MeTTa.QueryRootStability
