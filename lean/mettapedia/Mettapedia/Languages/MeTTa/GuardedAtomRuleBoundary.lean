import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

/-!
# Literal guarded atom-rule and unextended dialect boundaries

Guarded declarations are source forms of the explicit Atom calculus. The
unextended HE equation query recognizes ordinary equations, and the flat PeTTa
Pattern lowerer rejects scoped or quantified premises and local bindings.
These are precise comparisons of those interfaces, not impossibility claims
about extended dialects or compiler routes. Literal binder display erasure is
separate from alpha-equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.GuardedAtomRuleBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.OSLF.MeTTaIL.Syntax

def guardedDeclaration (head : String) (arguments : List Atom) (body : Atom) (guards : List Atom) : Atom :=
  .expression (.symbol "rule!" :: .expression (.symbol head :: arguments) :: body :: guards)

def ordinaryDeclaration (head : String) (arguments : List Atom) (body : Atom) : Atom :=
  .expression [.symbol "=", .expression (.symbol head :: arguments), body]

theorem guarded_is_original_declaration (head : String) (arguments : List Atom)
    (body : Atom) (guards : List Atom) :
    RuleDeclaration (guardedDeclaration head arguments body guards) ⟨head, arguments, body⟩ guards :=
  .guarded head arguments body guards

theorem guarded_read_original (head : String) (arguments : List Atom) (body : Atom) (guards : List Atom) :
    readRule? (guardedDeclaration head arguments body guards) = some (⟨head, arguments, body⟩, guards) :=
  (readRule?_exact _ _ _).mpr (guarded_is_original_declaration head arguments body guards)

theorem ordinary_is_common_equation (head : String) (arguments : List Atom) (body : Atom) :
    RuleDeclaration (ordinaryDeclaration head arguments body) ⟨head, arguments, body⟩ [] ∧
      HE.Space.isEquation (ordinaryDeclaration head arguments body) = true ∧
      HE.Space.getEquationLhs (ordinaryDeclaration head arguments body) =
        some (.expression (.symbol head :: arguments)) ∧
      HE.Space.getEquationRhs (ordinaryDeclaration head arguments body) = some body :=
  ⟨.equation head arguments body, rfl, rfl, rfl⟩

theorem guarded_is_not_HE_equation (head : String) (arguments : List Atom)
    (body : Atom) (guards : List Atom) :
    HE.Space.isEquation (guardedDeclaration head arguments body guards) = false ∧
      HE.Space.getEquationLhs (guardedDeclaration head arguments body guards) = none ∧
      HE.Space.getEquationRhs (guardedDeclaration head arguments body guards) = none := by
  cases guards <;> exact ⟨rfl, rfl, rfl⟩

theorem guarded_has_no_HE_equation_hits (head : String) (arguments : List Atom)
    (body query : Atom) (guards : List Atom) (fuel : Nat) :
    HE.queryEquations ⟨[guardedDeclaration head arguments body guards]⟩ query fuel = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => cases guards <;> simp [HE.queryEquations, guardedDeclaration]

theorem no_identity_equation_coverage :
    ¬ (∀ atom equation guards, RuleDeclaration atom equation guards → HE.Space.isEquation atom = true) := by
  intro covered
  have impossible := covered _ _ _ (guarded_is_original_declaration "f" [] (.symbol "passed") [])
  have refused := (guarded_is_not_HE_equation "f" [] (.symbol "passed") []).1
  rw [refused] at impossible
  cases impossible

theorem lowerer_rejects_scoped_step (condition : ScopedStepPremise) :
    ProfileBridge.specToCorePremise (.scopedStep condition) =
      .error "Cannot lower a scoped step premise to PeTTa core; core has no scoped premise form." := rfl

theorem lowerer_rejects_forall (collection parameter : String) (body : Premise) :
    ProfileBridge.specToCorePremise (.forAll collection parameter body) =
      .error s!"Cannot lower forAll premise over collection `{collection}` to PeTTa core; core has no quantified premise form." := rfl

theorem lowerer_success_has_no_local_bindings (rule : RewriteRule)
    (lowered : ProfileBridge.CRewriteRule)
    (successful : ProfileBridge.specToCoreRewriteRule rule = .ok lowered) : rule.bindings = none := by
  cases binding : rule.bindings with
  | none => rfl
  | some value =>
      unfold ProfileBridge.specToCoreRewriteRule at successful
      rw [binding] at successful
      change (Except.error s!"Cannot lower rewrite `{rule.name}` with rule-local bindings to core; core has no binding declaration." : Except String ProfileBridge.CRewriteRule) = .ok lowered at successful
      cases successful

theorem literal_binder_metadata_erased (left right : String) (body : Pattern) :
    ProfileBridge.specToCorePattern (.lambda (some left) body) =
      ProfileBridge.specToCorePattern (.lambda (some right) body) := by
  simp only [ProfileBridge.specToCorePattern]

theorem literal_lowerer_not_injective : ¬ Function.Injective ProfileBridge.specToCorePattern := by
  intro injective
  have same := injective (literal_binder_metadata_erased "x" "y" (.bvar 0))
  simp only [Pattern.lambda.injEq, Option.some.injEq] at same
  simp at same

#guard HE.Space.isEquation (ordinaryDeclaration "ordinary" [] (.symbol "passed"))
#guard !HE.Space.isEquation (guardedDeclaration "guarded" [] (.symbol "passed") [])
#guard (readRule? (guardedDeclaration "guarded" [] (.symbol "passed") [])).isSome
#guard HE.queryEquations ⟨[guardedDeclaration "guarded" [] (.symbol "passed") []]⟩
  (.expression [.symbol "guarded"]) 10 == []

#print axioms no_identity_equation_coverage
#print axioms guarded_has_no_HE_equation_hits
#print axioms lowerer_success_has_no_local_bindings
#print axioms literal_lowerer_not_injective

end Mettapedia.Languages.MeTTa.GuardedAtomRuleBoundary
