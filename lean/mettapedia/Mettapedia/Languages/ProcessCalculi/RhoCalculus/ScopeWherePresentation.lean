import Mettapedia.GSLT.Examples.ScopedRhoBinding
import Mettapedia.OSLF.Syntax.RhoGuardRelationQueries

/-!
# Scoped rho reception with an explicit complementary where clause

The guarded receiver is a new constructor carrying its branch and an
ordinary name-bound continuation. The original scoped COMM and parallel
rules remain in the language. They cannot match this guarded constructor.
Two additional conditional rules consult the payload-sensitive relation
interpreter and use the same scoped continuation substitution as COMM.

This is an explicit guarded extension. Its table interpreter admits closed
payloads of the intrinsic core signature; the new receiver is not silently
recognized as an unguarded input. No native machine or external provider is
supplied by this presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWherePresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.Examples.RestAwareTyping
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding.RhoGuardRelationQueries
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)

def polarityLabel : Verdict → String
  | .confirm => "ConfirmGuard"
  | .refute => "RefuteGuard"

def polarityDeclaration (branch : Verdict) : GrammarRule where
  label := polarityLabel branch
  category := "Guard"
  params := []
  syntaxPattern := [.terminal (polarityLabel branch)]

def receiverDeclaration : GrammarRule where
  label := "PWhereInput"
  category := "Proc"
  params := [.simple "channel" TypeExpr.name,
    .simple "polarity" (.base "Guard"),
    .abstraction "body" (TypeExpr.funType TypeExpr.name TypeExpr.proc)]
  syntaxPattern := [.terminal "PWhereInput"]

def receiver (branch : Verdict) (channel body : Pattern) : Pattern :=
  .apply "PWhereInput" [channel, .apply (polarityLabel branch) [], .lambda none body]

def bindingSpec : RuleBindingSpec :=
  { scopedCommBindingSpec with
    occurrences :=
      [{ «name» := "p", site := .left, path := [0, 2, 0], arguments := [.bvar 0] },
       { «name» := "p", site := .right, path := [0, 0], arguments := [.bvar 0] }] }

def guardedComm (branch : Verdict) : RewriteRule :=
  { scopedCommRewrite with
    name := match branch with | .confirm => "WhereCommConfirm" | .refute => "WhereCommRefute"
    «bindings» := some bindingSpec
    premises := [.relationQuery (relationName branch) [.fvar "q"]]
    left := .collection .hashBag
      [receiver branch (.fvar "n") (.fvar "p"),
       .apply "POutput" [.fvar "n", .fvar "q"]] (some "rest") }

def language : LanguageDef :=
  { rhoCalcWithScopedSchemas with
    name := "RhoScopeWhere"
    types := rhoCalcWithScopedSchemas.types ++ [TypeDecl.plain "Guard"]
    terms := rhoCalcWithScopedSchemas.terms ++
      [polarityDeclaration .confirm, polarityDeclaration .refute, receiverDeclaration]
    rewrites := rhoCalcWithScopedSchemas.rewrites ++ [guardedComm .confirm, guardedComm .refute] }

def modes : RelationModeTable :=
  [{ relation := relationName .confirm, args := [.input] },
   { relation := relationName .refute, args := [.input] }]

def signatures : List LogicRelationDecl :=
  [{ name := relationName .confirm, argTypes := [TypeExpr.proc] },
   { name := relationName .refute, argTypes := [TypeExpr.proc] }]

theorem validated : language.validate = [] := by
  simp [LanguageDef.validate, language, rhoCalcWithScopedSchemas,
    rhoCalcWithDeclaredSchemas, receiverDeclaration, polarityDeclaration,
    guardedComm, receiver, polarityLabel, relationName, scopedCommRewrite,
    scopedParCongRewrite, declaredCommRewrite, declaredParCongRewrite,
    communicationContextWithRest, communicationContext,
    rhoCalc, rhoCommRewrite, rhoParCongRewrite,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateEquation, LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseType,
    TypeExpr.proc, TypeExpr.name, TypeExpr.funType, TypeExpr.bag,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]
  all_goals
    repeat' apply And.intro
  all_goals
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    simp [TypeExpr.baseNames]

theorem bindings_valid : bindingDeclarationsValid language = true := by
  unfold bindingDeclarationsValid
  rw [validated]
  decide +kernel

theorem scoped_execution_admitted : scopedRewritesExecutable language = true := by
  unfold scopedRewritesExecutable
  rw [bindings_valid]
  decide +kernel

theorem relation_flow_admitted : language.executionAdmissionErrors modes signatures = [] :=
  by
    have keysDistinct :
        s!"scopeConfirm/{(1 : Nat)}" ≠ s!"scopeRefute/{(1 : Nat)}" := by
      change "scopeConfirm/" ++ toString (1 : Nat) ≠ "scopeRefute/" ++ toString (1 : Nat)
      intro same
      have prefixes := (String.append_left_inj (toString (1 : Nat))).mp same
      exact (by decide : "scopeConfirm/" ≠ "scopeRefute/") prefixes
    unfold LanguageDef.executionAdmissionErrors
    rw [validated]
    change [] ++ (LanguageDef.duplicateErrors "RhoScopeWhere" "relation mode"
      [s!"scopeConfirm/{(1 : Nat)}", s!"scopeRefute/{(1 : Nat)}"] ++ []) ++
        language.executionFlowErrors modes = []
    rw [LanguageDef.duplicateErrors_eq_nil_of_nodup _ _ _
      (List.nodup_cons.mpr ⟨by simpa only [List.mem_singleton] using keysDistinct,
        List.nodup_singleton _⟩)]
    simp only [List.nil_append]
    cbv

theorem all_rewrites_sorted :
    ∀ rule ∈ language.rewrites,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType language rule = true := by
  intro rule present
  change rule ∈ [scopedCommRewrite, scopedParCongRewrite, guardedComm .confirm, guardedComm .refute] at present
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
  rcases present with first | second | third | last <;> subst rule <;> decide +kernel

theorem received_payload_is_guard_argument (branch : Verdict) :
    (guardedComm branch).premises = [.relationQuery (relationName branch) [.fvar "q"]] := rfl

theorem ordinary_and_guarded_receivers_differ (branch : Verdict) (channel body : Pattern) :
    receiver branch channel body ≠ .apply "PInput" [channel, .lambda none body] := by
  intro same
  have labels := Pattern.apply.inj same
  have impossible : "PWhereInput" = "PInput" := labels.1
  exact (by decide : "PWhereInput" ≠ "PInput") impossible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWherePresentation
