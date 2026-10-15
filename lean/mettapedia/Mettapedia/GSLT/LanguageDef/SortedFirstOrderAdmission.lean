import Mettapedia.GSLT.LanguageDef.SortedFirstOrderCertificates

/-!
# Executable admission of typed first-order rule declarations

All formal sorts and every premise schema are checked. The statement checks
reuse the existing source typing evaluator. Schema scope is checked before
numbering formals, so a missing name cannot turn into an unchecked default
variable. This admission boundary is independent of MM0 or any other backend.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted

def checkBaseType (language : LanguageDef) : TypeExpr → Bool
  | .base name => language.typeNames.contains name
  | _ => false

theorem checkBaseType_iff (language : LanguageDef) (type : TypeExpr) :
    checkBaseType language type = true ↔
      ∃ name, type = .base name ∧ name ∈ language.typeNames := by
  cases type <;> simp [checkBaseType]

def checkStatement (language : LanguageDef) (judgments : List String) (context : List TypeExpr)
    (pattern : Pattern) : Bool :=
  judgments.any (fun name => checkHasType language FreeTypeContext.empty context pattern (.base name))

theorem checkStatement_iff (language : LanguageDef) (judgments : List String) (context : List TypeExpr)
    (pattern : Pattern) (fragment : isMatchCorrectAux pattern = true) :
    checkStatement language judgments context pattern = true ↔
      Statement language judgments context pattern := by
  simp only [checkStatement, List.any_eq_true, Statement]
  constructor
  · rintro ⟨name, member, checked⟩
    exact ⟨name, member, checkHasType_sound checked⟩
  · rintro ⟨name, member, typed⟩
    exact ⟨name, member, checkHasType_complete_of_object typed (firstOrder_object fragment)⟩

def Rule.check (language : LanguageDef) (judgments : List String) (rule : Rule) : Bool :=
  decide rule.row.vars.Nodup && decide (rule.variableTypes.length = rule.row.vars.length) &&
    rule.variableTypes.all (checkBaseType language) &&
    checkSchemas rule.row.vars rule.row.premises && checkSchema rule.row.vars rule.row.conclusion &&
    rule.row.premises.all (fun pattern =>
      checkStatement language judgments rule.variableTypes (numbered rule.row.vars pattern)) &&
    checkStatement language judgments rule.variableTypes (numbered rule.row.vars rule.row.conclusion)

theorem Rule.check_iff (language : LanguageDef) (judgments : List String) (rule : Rule) :
    rule.check language judgments = true ↔ rule.WellFormed language judgments := by
  simp only [Rule.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    checkBaseType_iff, checkSchemas_iff, checkSchema_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨distinct, arity⟩, declared⟩, premises⟩, conclusion⟩, hypotheses⟩, result⟩
    refine ⟨distinct, arity, declared, premises, conclusion, ?_, ?_⟩
    · intro pattern member
      exact (checkStatement_iff _ _ _ _ ((premises.member member).numbered_firstOrder distinct)).mp
        (hypotheses pattern member)
    · exact (checkStatement_iff _ _ _ _ (conclusion.numbered_firstOrder distinct)).mp result
  · intro formed
    refine ⟨⟨⟨⟨⟨⟨formed.distinctNames, formed.arity⟩, formed.declaredTypes⟩,
      formed.premiseSchemas⟩, formed.conclusionSchema⟩, ?_⟩, ?_⟩
    · intro pattern member
      exact (checkStatement_iff _ _ _ _
        ((formed.premiseSchemas.member member).numbered_firstOrder formed.distinctNames)).mpr
        (formed.hypotheses pattern member)
    · exact (checkStatement_iff _ _ _ _
        (formed.conclusionSchema.numbered_firstOrder formed.distinctNames)).mpr formed.conclusion

end Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
