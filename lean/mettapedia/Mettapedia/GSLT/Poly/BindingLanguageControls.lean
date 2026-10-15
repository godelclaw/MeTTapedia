import Mettapedia.GSLT.Poly.BindingLanguage
import Mettapedia.GSLT.Poly.FirstOrderLanguageControls

/-!
# Controls for the binder fragment

The identity of the lambda language is the print of one binding term, and the
language's own `HasType` judgment accepts it. A bound variable with no binder
in scope is neither typed nor printed. Two constructors that share a label
print to one pattern. A constructor whose parameter is a collection does not
belong to the fragment, so it is not a head of the polynomial. A base-sort
multi-binder prints as one unnamed `multiLambda`. A multi-binder whose type
is an arrow of base sorts stays outside the fragment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.BindingLanguageControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Poly.BindingLanguage
open Mettapedia.GSLT.Poly.BindingSignature
open Mettapedia.GSLT.Poly.FirstOrderLanguageControls
open IPFunctor

/-! ## The lambda identity is the print of one tree -/

theorem lambda_fragment : ∀ rule ∈ lambdaLanguage.terms, BinderRule rule := by
  intro rule member
  simp only [lambdaLanguage, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · intro parameter member
    simp only [lamRule, List.mem_cons, List.mem_nil_iff, or_false] at member
    subst member
    simp [bindingDecl?]
  · intro parameter member
    simp only [appRule, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> simp [bindingDecl?]

theorem lambda_labels : (lambdaLanguage.terms.map (·.label)).Nodup := by
  simp [lambdaLanguage, lamRule, appRule]

def lamOperator : (signature lambdaLanguage).Op "Term" :=
  ⟨⟨lamRule, by simp [lambdaLanguage], by
      intro parameter member
      simp only [lamRule, List.mem_singleton] at member
      subst member
      simp [bindingDecl?], rfl⟩,
    plainOccurrence lamRule.params (by
      intro parameter member
      simp only [lamRule, List.mem_singleton] at member
      subst member
      simp [multiBase?])⟩

def identityTerm : Term (signature lambdaLanguage) [] "Term" :=
  .op lamOperator <|
    @Args.cons (signature lambdaLanguage) ["Term"] "Term" [] []
      (.var (Var.zero (Γ := []) (s := "Term")))
      (@Args.nil (signature lambdaLanguage) [])

theorem identity_reachable : toPattern identityTerm = identityPattern := by
  dsimp [identityTerm, toPattern, identityPattern, lamOperator, lamRule, slots, patternsOfDecl,
    printArgument, slotBinders, wrapBinders, varIndex]
  rfl

theorem identity_typed_here :
    HasType lambdaLanguage FreeTypeContext.empty [] identityPattern (.base "Term") :=
  identity_reachable ▸ toPattern_hasType identityTerm

/-- Closed object patterns of the lambda language are the polynomial's trees. -/
noncomputable example :
    {pattern : Pattern //
      HasType lambdaLanguage FreeTypeContext.empty [] pattern (.base "Term") ∧
        isObjectPattern pattern = true} ≃
      IFreeM (polynomial (signature lambdaLanguage))
        (Vars (signature lambdaLanguage)) ([], "Term") :=
  closedPatternFreeEquiv lambda_fragment lambda_labels "Term"

/-! ## An out-of-scope bound variable is neither typed nor printed -/

theorem outOfScope_not_typed :
    ¬ HasType lambdaLanguage FreeTypeContext.empty [] (.bvar 0) (.base "Term") := by
  intro typed
  cases typed with
  | bvar found => simp at found

theorem outOfScope_not_printed (term : Term (signature lambdaLanguage) [] "Term") :
    toPattern term ≠ .bvar 0 := by
  intro printed
  cases term with
  | var variable_ => cases variable_
  | op _ _ =>
      unfold toPattern at printed
      cases printed

/-! ## A shared label breaks injectivity at one sort -/

def sharedLeft : GrammarRule :=
  { label := "C", category := "A", params := [.simple "x" (.base "A")], syntaxPattern := [] }

def sharedRight : GrammarRule :=
  { label := "C", category := "A", params := [.simple "y" (.base "A")], syntaxPattern := [] }

def sharedUnit : GrammarRule :=
  { label := "U", category := "A", params := [], syntaxPattern := [] }

def sharedLanguage : LanguageDef :=
  { name := "SharedLabel", types := [{ name := "A" }],
    terms := [sharedLeft, sharedRight, sharedUnit], equations := [], rewrites := [] }

theorem shared_labels_not_distinct : ¬ (sharedLanguage.terms.map (·.label)).Nodup := by
  simp [sharedLanguage, sharedLeft, sharedRight, sharedUnit]

def sharedUnitOperator : (signature sharedLanguage).Op "A" :=
  ⟨⟨sharedUnit, by simp [sharedLanguage], by simp [BinderRule, sharedUnit, bindingDecl?], rfl⟩,
    plainOccurrence sharedUnit.params (by simp [sharedUnit, multiBase?])⟩

def sharedLeftOperator : (signature sharedLanguage).Op "A" :=
  ⟨⟨sharedLeft, by simp [sharedLanguage], by
      intro parameter member
      simp only [sharedLeft, List.mem_singleton] at member
      subst member
      simp [bindingDecl?], rfl⟩,
    plainOccurrence sharedLeft.params (by
      intro parameter member
      simp only [sharedLeft, List.mem_singleton] at member
      subst member
      simp [multiBase?])⟩

def sharedRightOperator : (signature sharedLanguage).Op "A" :=
  ⟨⟨sharedRight, by simp [sharedLanguage], by
      intro parameter member
      simp only [sharedRight, List.mem_singleton] at member
      subst member
      simp [bindingDecl?], rfl⟩,
    plainOccurrence sharedRight.params (by
      intro parameter member
      simp only [sharedRight, List.mem_singleton] at member
      subst member
      simp [multiBase?])⟩

def sharedUnitTerm : Term (signature sharedLanguage) [] "A" :=
  .op sharedUnitOperator .nil

def sharedLeftTerm : Term (signature sharedLanguage) [] "A" :=
  .op sharedLeftOperator <|
    @Args.cons (signature sharedLanguage) [] "A" [] [] sharedUnitTerm
      (@Args.nil (signature sharedLanguage) [])

def sharedRightTerm : Term (signature sharedLanguage) [] "A" :=
  .op sharedRightOperator <|
    @Args.cons (signature sharedLanguage) [] "A" [] [] sharedUnitTerm
      (@Args.nil (signature sharedLanguage) [])

theorem shared_same_pattern : toPattern sharedLeftTerm = toPattern sharedRightTerm := by
  dsimp [sharedLeftTerm, sharedRightTerm, toPattern, sharedLeftOperator, sharedRightOperator,
    sharedLeft, sharedRight, slots, patternsOfDecl, printArgument, slotBinders, wrapBinders]
  rfl

def headParam {Γ : List String} {sort : String} :
    Term (signature sharedLanguage) Γ sort → String
  | .var _ => ""
  | .op operator _ =>
      match operator.1.1.params with
      | [.simple name _] => name
      | _ => ""

theorem sharedLeft_param : headParam sharedLeftTerm = "x" := by
  simp [headParam, sharedLeftTerm, sharedLeftOperator, sharedLeft]

theorem sharedRight_param : headParam sharedRightTerm = "y" := by
  simp [headParam, sharedRightTerm, sharedRightOperator, sharedRight]

theorem shared_terms_differ : sharedLeftTerm ≠ sharedRightTerm := by
  intro same
  have := congrArg headParam same
  rw [sharedLeft_param, sharedRight_param] at this
  exact absurd this (by decide)

/-! ## A collection parameter stays outside the fragment -/

def bagRule : GrammarRule :=
  { label := "Bag", category := "A",
    params := [.simple "xs" (.collection .hashBag (.base "A"))], syntaxPattern := [] }

def bagLanguage : LanguageDef :=
  { name := "Bag", types := [{ name := "A" }], terms := [bagRule],
    equations := [], rewrites := [] }

theorem collection_outside : ¬ BinderRule bagRule := by
  intro bound
  have ok := bound _ (List.mem_singleton_self _)
  simp [bindingDecl?] at ok

theorem collection_not_head (operator : (signature bagLanguage).Op "A") : False := by
  have member : operator.1.1 = bagRule := by
    have belongs := operator.1.2.1
    simp only [bagLanguage, List.mem_cons, List.mem_nil_iff, or_false] at belongs
    exact belongs
  exact collection_outside (by simpa [member] using operator.1.2.2.1)

/-! ## A base-sort multi-binder is a head together with its count -/

/-- The same-sort multi-binder shorthand belongs to the fragment. -/
theorem multi_base_inside :
    bindingDecl? (.multiAbstractionNamed [] "body" (.base "A")) = some (["A"], "A") := rfl

/-- A multi-binder whose stored type is an arrow of base sorts, rather than a
`multiBinder` of a base sort, stays outside the fragment. -/
theorem multi_nonbase_outside :
    bindingDecl? (.multiAbstractionNamed [] "body" (.arrow (.base "A") (.base "B"))) = none := rfl

def multiRule : GrammarRule :=
  { label := "M", category := "A",
    params := [.multiAbstractionNamed [] "body" (.base "A")], syntaxPattern := [] }

def multiLanguage : LanguageDef :=
  { name := "Multi", types := [{ name := "A" }], terms := [multiRule],
    equations := [], rewrites := [] }

def multiOccurrence : Occurrence multiRule.params where
  counts := [1]
  length_eq := rfl
  fixed := by
    intro index premise
    cases index with
    | zero =>
        simp [multiRule, multiBase?, List.getD, missingParameter] at premise
    | succ index =>
        simp [List.getD]

def multiOperator : (signature multiLanguage).Op "A" :=
  ⟨⟨multiRule, by simp [multiLanguage], by
      intro parameter member
      simp only [multiRule, List.mem_singleton] at member
      subst member
      simp [bindingDecl?], rfl⟩,
    multiOccurrence⟩

def multiTerm : Term (signature multiLanguage) [] "A" :=
  .op multiOperator <|
    @Args.cons (signature multiLanguage) ["A"] "A" [] []
      (.var (Var.zero (Γ := []) (s := "A")))
      (@Args.nil (signature multiLanguage) [])

theorem multi_prints :
    toPattern multiTerm = .apply "M" [.multiLambda 1 [] (.bvar 0)] := by
  dsimp [multiTerm, toPattern, multiOperator, multiRule, multiOccurrence, slots, patternsOfDecl,
    printArgument, varIndex]
  rfl

theorem multi_typed :
    HasType multiLanguage FreeTypeContext.empty [] (toPattern multiTerm) (.base "A") :=
  multi_prints ▸ toPattern_hasType multiTerm

end Mettapedia.GSLT.Poly.BindingLanguageControls
