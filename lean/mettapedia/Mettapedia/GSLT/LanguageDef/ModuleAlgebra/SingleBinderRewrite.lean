import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.BindingDeclarationElaboration
import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# The module single-binder rewrite example in the existing core semantics

The example introduces an inner binder while retaining the matched body's
original dependencies. Its result is calculated with the existing authored
rule interpreter, not a second evaluator. The required index shift is also
the erasure of intrinsic, declaration-derived weakening.

This establishes the meaning and scope obligation of the example. Native
qualification checks that implementation against concrete controls; this
file does not prove the C implementation or source parser adequate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SingleBinderRewrite

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted

def wrap (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]

def weakenRule : RewriteRule where
  name := "Weaken"
  typeContext := [("body", .base "Expr")]
  premises := []
  left := wrap (.fvar "body")
  right := wrap (wrap (.fvar "body"))

def language : LanguageDef :=
  { BindingDeclarationElaboration.bindingLanguage with rewrites := [weakenRule] }

theorem weaken_operational (body : Pattern) :
    reducts language 1 (wrap body) = [wrap (wrap (liftBVars 0 1 body))] := by
  simp [reducts, reductsUsing, rewriteAt, language, applyRuleUsing,
    weakenRule, wrap, matchPatternForRule_eq_syntactic,
    applyBindingsForRule_eq_syntactic, matchPattern, matchArgs, mergeBindings,
    premisesUsing, applyRuleBindings, applyBindingsScoped, captureDepth,
    captureDepthList]

/-- Inward transport preserves scope, including references through binders
internal to the captured body. -/
theorem weaken_scope (body : Pattern) (inScope : body.isWellScopedAt 1 = true) :
    (wrap (wrap (liftBVars 0 1 body))).isWellScopedAt 0 = true := by
  have lifted := liftBVars_isWellScopedAt (ambient := 1) (cutoff := 0) (shift := 1) inScope
  simpa [wrap, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using lifted

/-- The native profile's shift has a typed meaning in the declaration-derived
binding signature. The new binder has an arbitrary declared domain. -/
theorem typed_weakening {core : LanguageDef} {bound : List TypeExpr}
    {sort added : TypeExpr}
    (body : Mettapedia.OSLF.Binding.Term
      (BindingSyntax.signatureOf core) bound sort) :
    ∃ target : Mettapedia.OSLF.Binding.Term
      (BindingSyntax.signatureOf core) (added :: bound) sort,
      BindingSyntax.erase target = liftBVars 0 1 (BindingSyntax.erase body) := by
  exact ⟨Mettapedia.OSLF.Binding.weaken body, BindingSyntax.erase_weaken body⟩

def reference (index : Nat) : Pattern := .apply "Ref" [.bvar index]

/-- Both the intended result and a captured result pass sorting. Therefore
checking the result type alone cannot replace capture-avoiding substitution. -/
theorem sorting_alone_does_not_detect_capture :
    checkClosedTerm language ⟨"Expr", by decide⟩ (wrap (wrap (reference 1))) = true ∧
    checkClosedTerm language ⟨"Expr", by decide⟩ (wrap (wrap (reference 0))) = true ∧
    wrap (wrap (reference 1)) ≠ wrap (wrap (reference 0)) := by decide +kernel

theorem outer_reference_preserved :
    reducts language 1 (wrap (reference 0)) = [wrap (wrap (reference 1))] := by
  simpa [reference, liftBVars] using weaken_operational (reference 0)

/-- The old binder internal to a matched value is not shifted. -/
theorem internal_reference_preserved :
    reducts language 1 (wrap (wrap (reference 0))) =
      [wrap (wrap (wrap (reference 0)))] := by
  simpa [wrap, reference, liftBVars] using weaken_operational (wrap (reference 0))

#print axioms weaken_operational
#print axioms weaken_scope
#print axioms typed_weakening
#print axioms sorting_alone_does_not_detect_capture

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SingleBinderRewrite
