import Mettapedia.Machines.FreshFrameNoninterference

/-!
# Constructor selection followed by field constraints

The root constructor test precedes the same ordered field constraints. The
existing total first-order unifier gives exact substitution equality, including
already aliased pattern variables. Ground fields contain no occurrence of a
variable being bound. This is not a C instruction or whole-matcher optimality
theorem.

Native representation checks, logical-list equivalence, slot trails, comparator
semantics and C conformance remain separate obligations. This model describes
the admitted ordinary constructor fragment, not every native grounded value.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FlatConstructorMatching

open Mettapedia.Logic.LP
open FreshFrameNoninterference

abbrev Signature (Tag Constant Variable : Type) : LPSignature where
  constants := Constant
  vars := Variable
  functionSymbols := Tag
  functionArity _ := 2
  relationSymbols := Empty
  relationArity := Empty.elim

variable {Tag Constant Variable : Type}
  [DecidableEq Tag] [DecidableEq Constant] [DecidableEq Variable]

abbrev Value := Term (Signature Tag Constant Variable)

def node (tag : Tag) (left right : Value (Tag := Tag) (Constant := Constant)
    (Variable := Variable)) : Value (Tag := Tag) (Constant := Constant) (Variable := Variable) :=
  .app tag (fun index => if index.val = 0 then left else right)

omit [DecidableEq Tag] [DecidableEq Constant] [DecidableEq Variable] in
theorem field_pairs (left right one two : Value (Tag := Tag)
    (Constant := Constant) (Variable := Variable)) :
    finPairsToList (fun i : Fin 2 => if i.val = 0 then left else right)
      (fun i : Fin 2 => if i.val = 0 then one else two) = [(left, one), (right, two)] := by
  simp [finPairsToList, List.finRange]

/-- Removing the matching root leaves precisely the same ordered solve,
not merely the same satisfiability verdict. -/
theorem constructor_fields_exact (store : Subst (Signature Tag Constant Variable))
    (tag : Tag) (left right one two : Value (Tag := Tag)
      (Constant := Constant) (Variable := Variable)) :
    solveStep store [(node tag left right, node tag one two)] =
      solveStep store [(left, one), (right, two)] := by
  unfold solveStep
  simp only [Subst.applyEqs, List.map_cons, List.map_nil, node, Subst.applyTerm_app]
  rw [unifyTotal]
  simp only [↓reduceDIte, List.append_nil]
  congr 2

theorem different_constructor_rejects (store : Subst (Signature Tag Constant Variable))
    (expected actual : Tag) (different : expected ≠ actual)
    (left right one two : Value (Tag := Tag) (Constant := Constant) (Variable := Variable)) :
    solveStep store [(node expected left right, node actual one two)] = none := by
  unfold solveStep
  simp only [Subst.applyEqs, List.map_cons, List.map_nil, node, Subst.applyTerm_app]
  rw [unifyTotal]
  simp only [dif_neg different, Option.map_none]

theorem ground_field_has_no_occurrence {σ : LPSignature} [DecidableEq σ.vars]
    (field : Term σ) (ground : field.isGround) (cell : σ.vars) :
    field.occursIn cell = false := by
  have empty := (Term.isGround_iff_freeVars_empty field).mp ground
  cases found : field.occursIn cell with
  | false => rfl
  | true =>
      have member := (Term.occursIn_iff_mem_freeVars cell field).mp found
      rw [empty] at member
      exact (Finset.notMem_empty _ member).elim

namespace Controls

abbrev Sig := Signature Bool Nat Nat
def start : Subst Sig := Subst.id Sig
def aliased : Subst Sig := Subst.single 1 (.var 0)

theorem accepted_alias :
    (solveStep aliased [(node true (.var 0) (.var 1),
      node true (.const 7) (.const 7))]).map (fun store => (store 0, store 1)) =
      some (.const 7, .const 7) := by
  rw [constructor_fields_exact]
  simp [solveStep, aliased, Subst.applyEqs, Subst.applyTerm, Subst.single,
    unifyTotal, Subst.id, Subst.comp, Term.occursIn]

/-- Distinct source slots can already alias; that equality cannot be erased. -/
theorem rejected_alias :
    solveStep aliased [(node true (.var 0) (.var 1),
      node true (.const 7) (.const 9))] = none := by
  rw [constructor_fields_exact]
  simp [solveStep, aliased, Subst.applyEqs, Subst.applyTerm, Subst.single,
    unifyTotal, Term.occursIn]

theorem wrong_tag_rejects :
    solveStep start [(node true (.var 0) (.var 1),
      node false (.const 7) (.const 7))] = none :=
  different_constructor_rejects _ _ _ (by decide) _ _ _ _

end Controls
end Mettapedia.Machines.FlatConstructorMatching
