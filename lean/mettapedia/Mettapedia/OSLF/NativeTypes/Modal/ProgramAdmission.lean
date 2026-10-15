import Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers
import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Checker

open Mettapedia.OSLF.Framework

/-!
# Executable classifying program-source admission

The schematic typing checker retains REST metadata. Its finite input
carriers are computed from the authored program sorts; successful admission
is proved equivalent to the independent typing judgments in this family.
Unsupported explicit substitutions and unclassified root carriers remain
separate diagnostics rather than exhaustive empty catalogues.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

def typedProgramCarriers (language : LanguageDef) (rule : RewriteRule) : List TypeExpr :=
  (programCandidates language).filter fun carrier =>
    schemaCheckHasType language (ruleFree rule) [] rule.left carrier

inductive ProgramCarrierStatus where
  | unclassifiedSource
  | unsupportedSubstitution
  | noDeclaredProgramTyping
  | classified (carriers : List TypeExpr)
  deriving DecidableEq, Repr

def programCarrierStatus (language : LanguageDef) (rule : RewriteRule) : ProgramCarrierStatus :=
  if classifyingProgramSource? language rule then
    if substitutionFree rule.left then
      let carriers := typedProgramCarriers language rule
      if carriers.isEmpty then .noDeclaredProgramTyping else .classified carriers
    else .unsupportedSubstitution
  else .unclassifiedSource

theorem typed_program_carriers_sound {language : LanguageDef} {rule : RewriteRule}
    {carrier : TypeExpr} (member : carrier ∈ typedProgramCarriers language rule) :
    carrier ∈ programCandidates language ∧
      HasType language (ruleFree rule) [] rule.left carrier := by
  have checked := List.mem_filter.mp member
  exact ⟨checked.1, schemaCheckHasType_sound checked.2⟩

/-- Completeness is relative to the source's authored program-result
classification. The caller supplies a typing derivation, not candidate
membership or a list of source sites. -/
theorem classified_program_carriers_complete {language : LanguageDef} {rule : RewriteRule}
    {category : String} (classified : classifyingProgramSource? language rule = true)
    (supported : substitutionFree rule.left = true)
    (typed : HasType language (ruleFree rule) [] rule.left (.base category)) :
    TypeExpr.base category ∈ typedProgramCarriers language rule :=
  List.mem_filter.mpr ⟨classified_program_type_candidate classified typed,
    schemaCheckHasType_complete typed supported⟩

/-- At every declared program sort, the finite readout has exactly the
independent source typing alternatives of the substitution-free schema. -/
theorem declared_program_carriers_exact {language : LanguageDef} {rule : RewriteRule}
    (supported : substitutionFree rule.left = true) (type : TypeDecl)
    (declared : List.Mem type language.types) :
    TypeExpr.base type.name ∈ typedProgramCarriers language rule ↔
      HasType language (ruleFree rule) [] rule.left (.base type.name) := by
  constructor
  · intro member
    exact (typed_program_carriers_sound member).2
  · intro typed
    exact List.mem_filter.mpr ⟨declared_program_candidate declared,
      schemaCheckHasType_complete typed supported⟩

theorem program_status_complete {language : LanguageDef} {rule : RewriteRule}
    {category : String} (classified : classifyingProgramSource? language rule = true)
    (supported : substitutionFree rule.left = true)
    (typed : HasType language (ruleFree rule) [] rule.left (.base category)) :
    programCarrierStatus language rule = .classified (typedProgramCarriers language rule) ∧
      TypeExpr.base category ∈ typedProgramCarriers language rule := by
  have member := classified_program_carriers_complete classified supported typed
  have nonempty : (typedProgramCarriers language rule).isEmpty = false := by
    cases present : typedProgramCarriers language rule with
    | nil => rw [present] at member; exact False.elim (List.not_mem_nil member)
    | cons first rest => rfl
  exact ⟨by simp [programCarrierStatus, classified, supported, nonempty], member⟩

theorem program_status_sound {language : LanguageDef} {rule : RewriteRule}
    {carriers : List TypeExpr}
    (accepted : programCarrierStatus language rule = .classified carriers) :
    classifyingProgramSource? language rule = true ∧
      substitutionFree rule.left = true ∧ carriers ≠ [] ∧
      ∀ carrier ∈ carriers, carrier ∈ programCandidates language ∧
        HasType language (ruleFree rule) [] rule.left carrier := by
  unfold programCarrierStatus at accepted
  split at accepted
  · rename_i classified
    split at accepted
    · rename_i supported
      dsimp only at accepted
      split at accepted
      · contradiction
      · rename_i populated
        cases accepted
        refine ⟨classified, supported, ?_, fun _ member => typed_program_carriers_sound member⟩
        intro empty
        rw [empty] at populated
        contradiction
    · contradiction
  · contradiction

/-- This finite negative readout excludes only declared program-result
typing. It says nothing about arbitrary arrow or collection-expression
carriers, execution successors, or modal failure. -/
theorem no_declared_program_typing {language : LanguageDef} {rule : RewriteRule}
    (empty : programCarrierStatus language rule = .noDeclaredProgramTyping) :
    ∀ type : TypeDecl, List.Mem type language.types →
      ¬ HasType language (ruleFree rule) [] rule.left (.base type.name) := by
  unfold programCarrierStatus at empty
  split at empty
  · split at empty
    · rename_i supported
      dsimp only at empty
      split at empty
      · rename_i missing
        intro type declared typed
        have member := (declared_program_carriers_exact supported type declared).mpr typed
        have actualEmpty : typedProgramCarriers language rule = [] := by
          cases actual : typedProgramCarriers language rule with
          | nil => rfl
          | cons head tail => simp [actual] at missing
        rw [actualEmpty] at member
        exact List.not_mem_nil member
      · contradiction
    · contradiction
  · contradiction

end Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers
