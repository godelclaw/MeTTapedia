import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-!
# Typing transport through selected operational declarations

Selecting equations and reductions changes the operational presentation.
Object typing continues to use the same authored grammar and contexts.
The transport applies to arbitrary patterns, binding depths and typing
alternatives, independently of the execution algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralLanguageTyping

open Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
theorem type_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType first free bound pattern type) : HasType second free bound pattern type :=
  match typed with
  | .bvar found => .bvar found
  | .fvar found => .fvar found
  | .constructor declared ordinary arguments =>
      .constructor (same ▸ declared) ordinary (arguments_transport same arguments)
  | .lambda body => .lambda (type_transport same body)
  | .multiLambda body => .multiLambda (type_transport same body)
  | .subst body replacement => .subst (type_transport same body) (type_transport same replacement)
  | .collection elements => .collection (elements_transport same elements)
  | .collectionConstructor declared shape elements =>
      .collectionConstructor (same ▸ declared) shape (elements_transport same elements)

theorem arguments_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes first free bound arguments parameters) :
    ArgumentsHaveTypes second free bound arguments parameters :=
  match typed with
  | .nil => .nil
  | .cons representation parameterType head tail =>
      .cons representation parameterType (type_transport same head) (arguments_transport same tail)

theorem elements_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType first free bound elements type) :
    ElementsHaveType second free bound elements type :=
  match typed with
  | .nil _ _ => .nil _ _
  | .cons head tail => .cons (type_transport same head) (elements_transport same tail)
end

theorem open_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : OpenPatternWellSorted first free bound type pattern) :
    OpenPatternWellSorted second free bound type pattern :=
  ⟨type_transport same typed.1, typed.2⟩

theorem selected_grammar {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} :
    (GeneralExecutionAdmission.executionLanguage snapshot permissions).terms = snapshot.language.terms := rfl

theorem selected_typing_iff (snapshot : GeneralExecutionAdmission.Snapshot)
    (permissions : GeneralExecutionAdmission.Permissions) (bound : List TypeExpr)
    (pattern : Pattern) (type : TypeExpr) :
    OpenPatternWellSorted (GeneralExecutionAdmission.executionLanguage snapshot permissions)
      snapshot.free bound type pattern ↔ OpenPatternWellSorted snapshot.language snapshot.free bound type pattern :=
  ⟨open_transport selected_grammar, open_transport selected_grammar.symm⟩

end Mettapedia.OSLF.MeTTaIL.GeneralLanguageTyping
