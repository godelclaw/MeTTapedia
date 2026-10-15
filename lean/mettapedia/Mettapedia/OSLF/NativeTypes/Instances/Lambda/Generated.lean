import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend
import Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated
import Mettapedia.OSLF.NativeTypes.Decision.Admission

open Mettapedia.OSLF.Framework

/-!
# Generated native structural types on the authored scoped lambda language

The generator receives the original four-rule language. Every structural
former and argument carrier is obtained from its declaration. The checked
intrinsic decoder transports these native predicates to the exact contextual
lambda execution backend.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.GSLT.LanguageDef.WellSorted

def snapshot : Snapshot := ⟨LambdaAuthoredFullRuleProfile.language, [], ⟨[], []⟩⟩
def fragment : LanguageFragment := {operational := {sites := .rootOnly}}
def chosen : Snapshot := selectedSnapshot snapshot fragment
def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language := (fun _ => .star, fun _ => .star)
def generated : Generated := generate snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem generated_snapshot : generated.snapshot = snapshot := by
  change selectedSnapshot snapshot fragment = snapshot
  simp only [selectedSnapshot, fragment, unrestricted_signature]

theorem original_language : generated.snapshot.language = LambdaAuthoredFullRuleProfile.language :=
  congrArg Snapshot.language generated_snapshot

theorem generated_equations : generated.plan.equations = [] := rfl

theorem admitted_cube : generated.equationAdmission = some true := by
  rfl

/-- A semantic sort interpretation accepting all values of each declared
carrier. More restrictive masks can be supplied to `testWithMask`. -/
def carrierMask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool :=
  fun _ _ _ _ => true

structure Leaf where
  index : Fin generated.snapshot.language.terms.length
  accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool

def testWithMask (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (Γ : Ctx sig)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) (leaf : Leaf) :
    Test (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory selection Γ) (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ) :=
  let actual := Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localTest generated generated_equations mask
    (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts
  {predicate := ⟨fun source => actual.predicate (encodeTerm source), by
      intro source other related
      change source = other at related
      cases related
      rfl⟩
   evaluate budget source := actual.evaluate budget (encodeTerm source)
   positive budget source read := actual.positive budget (encodeTerm source) read
   negative budget source read := actual.negative budget (encodeTerm source) read
   completionBudget source := actual.completionBudget (encodeTerm source)
   complete_at source _ := actual.complete_at (encodeTerm source)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_object source)
   complete_above source _ budget enough := actual.complete_above (encodeTerm source)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_object source) budget enough}

def tests (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (Γ : Ctx sig) :=
  testWithMask selection Γ carrierMask

theorem leaf_generated_meaning (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (Γ : Ctx sig)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (leaf : Leaf) (source : Term sig Γ .term) :
    (testWithMask selection Γ mask leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel generated mask
          (LambdaAuthoredTypingComparison.contextTypes Γ)) leaf.index
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs generated
          (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts)).meaning (encodeTerm source) :=
  Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.test_generated_comparison
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel_equations generated_equations mask)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localBackend generated
      (LambdaAuthoredTypingComparison.contextTypes Γ) generated_equations)
    leaf.index _
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs_interpreted generated_equations
      (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanEffective generated mask
      (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts) (encodeTerm source)

def formers : List Leaf :=
  (List.finRange generated.snapshot.language.terms.length).map fun index => ⟨index, fun _ _ => true⟩

def former? (label : String) : Option Leaf :=
  formers.find? fun leaf => (structuralDeclaration generated leaf.index).label == label

def run (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (Γ : Ctx sig)
    (formula : Formula Leaf) (source : Term sig Γ .term) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.backend selection Γ)
    (tests selection Γ) formula source budget

def decisionBound (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (Γ : Ctx sig)
    (formula : Formula Leaf) (source : Term sig Γ .term) : Nat :=
  workBound (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.backend selection Γ) (tests selection Γ) formula source

theorem whole_language_complete (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) (Γ : Ctx sig)
    (formula : Formula Leaf) (source : Term sig Γ .term) :
    (run selection Γ formula source (decisionBound selection Γ formula source)).Decided :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.native_fragment_complete selection Γ (tests selection Γ) formula source

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated
