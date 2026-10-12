import Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction
import Mettapedia.OSLF.MeTTaIL.GeneralAuthoredExecutionControls
import Mettapedia.OSLF.MeTTaIL.GeneralRhoBinding

open Mettapedia.OSLF.Framework

/-!
# The specified right-hand side retains hidden matched variables

The generated root modality for Successor(X) to X has no rely variables.
Its right-hand side nevertheless depends on the matched value of X. The
actual scoped instantiator demonstrates this for every ambient context and
every scoped body. Two sorted instances show that the RHS and dependent
continuation cannot be recovered from rely observations alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.HiddenAssignments

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules

abbrev carrier := GeneralAuthoredExecutionControls.term
abbrev language := GeneralAuthoredExecutionControls.language
abbrev snapshot := GeneralAuthoredExecutionControls.snapshot []
abbrev runtimePlan := GeneralAuthoredExecutionControls.plan []
abbrev declaration := GeneralAuthoredExecutionControls.declaration 0 GeneralAuthoredExecutionControls.child

def successor (body : Pattern) : Pattern := .apply "Successor" [body]

def schema (bound : List TypeExpr) : Schema runtimePlan where
  ordinal := 0
  declaration := declaration
  declared := by
    rw [GeneralAuthoredExecutionControls.compiled_rules]
    exact List.mem_cons_self
  position := (RedexPosition.positions declaration.rule.left).head!
  bound := bound
  programCarrier := carrier
  focusBound := bound
  focusCarrier := carrier

theorem schema_position (bound : List TypeExpr) : (schema bound).position = [] := rfl

theorem generated_names (bound : List TypeExpr) :
    (schema bound).relyNames = [] ∧ (schema bound).matchedNames = ["X"] ∧
      RedexPosition.hiddenVars declaration.rule.left (schema bound).position = ["X"] := by cbv

def value (bound : List TypeExpr) (body : Pattern) : ContextualValue := ⟨[], bound.length, body⟩
def assignment (bound : List TypeExpr) (body : Pattern) : Assignment := [("X", value bound body)]

theorem assignment_lookup (bound : List TypeExpr) (body : Pattern) :
    lookup (assignment bound body) "X" = some (value bound body) := by
  simp only [assignment, lookup, List.find?_cons, beq_self_eq_true, Option.map_some]

private theorem left_arguments : arguments? declaration.rule declaration.binding.spec "X" .left [0] = some [] := by cbv
private theorem right_arguments : arguments? declaration.rule declaration.binding.spec "X" .right [] = some [] := by cbv

theorem source_instance {bound : List TypeExpr} {body : Pattern}
    (safe : body.isWellScopedAt bound.length = true) :
    instantiateWith? (schema bound).operation declaration.rule declaration.binding.spec bound.length
      .left [] 0 (assignment bound body) declaration.rule.left = some (successor body) := by
  have authored : declaration.rule.left = successor (.fvar "X") := rfl
  have bodyInstance : instantiateValue? (value bound body) bound.length 0 [] = some body :=
    GeneralRho.instantiate_root safe
  rw [authored]
  simp only [successor, instantiateWith?, instantiateArgsWith?, List.nil_append,
    assignment_lookup, left_arguments, Option.bind_eq_bind, Option.bind_some, bodyInstance]

/-- The RHS uses the matched assignment on every ambient context, including
contextual values whose bodies contain properly scoped binders. -/
theorem rhs_instance {bound : List TypeExpr} {body : Pattern}
    (safe : body.isWellScopedAt bound.length = true) :
    (schema bound).rhs? (assignment bound body) = some body := by
  have authored : declaration.rule.right = .fvar "X" := rfl
  have bodyInstance : instantiateValue? (value bound body) bound.length 0 [] = some body :=
    GeneralRho.instantiate_root safe
  simp only [Schema.rhs?, schema, reductWith?, authored, instantiateWith?, assignment_lookup,
    right_arguments, Option.bind_eq_bind, Option.bind_some, bodyInstance]

def relyReadout (bound : List TypeExpr) (supplied : Assignment) : List (Option ContextualValue) :=
  (schema bound).relyNames.map (lookup supplied)

theorem rely_readout_empty (bound : List TypeExpr) (supplied : Assignment) :
    relyReadout bound supplied = [] := by rw [relyReadout, (generated_names bound).1]; rfl

def first : Pattern := GeneralAuthoredExecutionControls.zero
def second : Pattern := successor first

theorem first_proper : OpenPatternWellSorted language snapshot.free [] carrier first := by
  apply checkOpenPatternWellSorted_sound
  cbv

theorem second_proper : OpenPatternWellSorted language snapshot.free [] carrier second := by
  apply checkOpenPatternWellSorted_sound
  cbv

theorem actual_contracta_distinct :
    (schema []).rhs? (assignment [] first) = some first ∧
      (schema []).rhs? (assignment [] second) = some second ∧ first ≠ second :=
  ⟨rhs_instance first_proper.2.2.2, rhs_instance second_proper.2.2.2, by decide +kernel⟩

/-- Suppressing the chosen inhabitant's matched variables is not a valid
functional interpretation of the displayed R(u) notation. -/
theorem no_rely_only_contractum :
    ¬ ∃ readout : List (Option ContextualValue) → Option Pattern,
      ∀ body, OpenPatternWellSorted language snapshot.free [] carrier body →
        readout (relyReadout [] (assignment [] body)) = (schema []).rhs? (assignment [] body) := by
  rintro ⟨readout, computes⟩
  have left := computes first first_proper
  have right := computes second second_proper
  rw [rely_readout_empty, actual_contracta_distinct.1] at left
  rw [rely_readout_empty, actual_contracta_distinct.2.1] at right
  exact actual_contracta_distinct.2.2 (Option.some.inj (left.symm.trans right))

def dependentContinuation : Continuation := fun supplied target =>
  PLift ((schema []).rhs? supplied = some target)

/-- The substituted continuation itself must retain the same full assignment
as the operational RHS, even when all rely answers coincide. -/
theorem continuation_needs_matched_assignment :
    relyReadout [] (assignment [] first) = relyReadout [] (assignment [] second) ∧
      Nonempty (substituteContinuation dependentContinuation (assignment [] first) first) ∧
      ¬ Nonempty (substituteContinuation dependentContinuation (assignment [] second) first) := by
  refine ⟨by rw [rely_readout_empty, rely_readout_empty], ⟨⟨actual_contracta_distinct.1⟩⟩, ?_⟩
  rintro ⟨certificate⟩
  exact actual_contracta_distinct.2.2
    (Option.some.inj (certificate.down.symm.trans actual_contracta_distinct.2.1))

end Mettapedia.OSLF.NativeTypes.Modal.HiddenAssignments
