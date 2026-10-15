import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled

open Mettapedia.OSLF.Framework

/-!
# The authored scoped lambda language through the public native interface

The four declaration switches select the original operational rules. The
connective fragment and generated cube are separate inputs. Source decoding
recovers the exact scoped program; structural leaves interpret the actual
generated constructor declarations and their ordered arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Runtime.Description

structure Configuration where
  rules : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection := {}
  logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment := Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
  vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.chosen.language :=
    (fun _ => .star, fun _ => .star)

def selectedIndices (rules : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection) : List Nat :=
  [rules.beta, rules.lamCong, rules.appCongL, rules.appCongR].zipIdx.filterMap
    fun (enabled, index) => if enabled then some index else none

def fragment (configuration : Configuration) : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {operational := {sites := .rootOnly, ruleIndices := some (selectedIndices configuration.rules)}}

def generated (configuration : Configuration) : Mettapedia.OSLF.NativeTypes.Generation.Generated :=
  Mettapedia.OSLF.NativeTypes.Generation.generate Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
    (fragment configuration) configuration.logic configuration.vertex

theorem original_snapshot (configuration : Configuration) :
    (generated configuration).snapshot = Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot := by
  change Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot _ (fragment configuration) = _
  simp only [Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot, fragment,
    Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]

theorem no_equations (configuration : Configuration) :
    (generated configuration).plan.equations = [] := rfl

theorem admitted_cube (configuration : Configuration) :
    (generated configuration).equationAdmission = some true := rfl

/-- An effective interpretation of the two displayed sorts. The native
predicate still checks every declared carrier independently. -/
def syntaxMask (_bound : List TypeExpr) (_carrier : TypeExpr)
    (sort : ModalHypercube.HSort) (source : Pattern) : Bool :=
  decide (sort = match source with | .bvar _ | .fvar _ => .box | _ => .star)

abbrev Leaf := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf

def tests (configuration : Configuration) (Γ : Ctx sig) (leaf : Leaf) :
    Test (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory configuration.rules Γ)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ) :=
  let actual := Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localTest (generated configuration)
    (no_equations configuration) syntaxMask (LambdaAuthoredTypingComparison.contextTypes Γ)
    leaf.index leaf.accepts
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

theorem native_structural_meaning (configuration : Configuration) (Γ : Ctx sig)
    (leaf : Leaf) (source : Term sig Γ .term) :
    (tests configuration Γ leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel (generated configuration) syntaxMask
          (LambdaAuthoredTypingComparison.contextTypes Γ)) leaf.index
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs (generated configuration)
          (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts)).meaning
        (encodeTerm source) :=
  Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.test_generated_comparison
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel_equations (no_equations configuration) syntaxMask)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localBackend (generated configuration)
      (LambdaAuthoredTypingComparison.contextTypes Γ) (no_equations configuration))
    leaf.index _
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs_interpreted (no_equations configuration)
      (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanEffective (generated configuration) syntaxMask
      (LambdaAuthoredTypingComparison.contextTypes Γ) leaf.index leaf.accepts) (encodeTerm source)

def decode (Γ : Ctx sig) (raw : Pattern) : Except SourceIssue
    {source : Term sig Γ .term // Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ source ∧ encodeTerm source = raw} :=
  match Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.decode Γ raw with
  | none => .error .illScopedOrSorted
  | some source => .ok ⟨source.val, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted source.val,
      source.property⟩

theorem decode_complete (Γ : Ctx sig) (raw : Pattern)
    (admitted : ∃ source : Term sig Γ .term,
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ source ∧ encodeTerm source = raw) :
    (decode Γ raw).isOk = true := by
  obtain ⟨source, _, rfl⟩ := admitted
  simp only [decode, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.decode_complete]
  rfl

def driver (configuration : Configuration) (Γ : Ctx sig) : Driver where
  generated := generated configuration
  expected := .base "Term"
  system := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory configuration.rules Γ
  admitted := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ
  render := encodeTerm
  render_injective := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_injective
  decode := decode Γ
  decode_complete := decode_complete Γ
  backend := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.backend configuration.rules Γ
  Leaf := Leaf
  tests := tests configuration Γ
  leafAdmission := rootAdmission (generated configuration) (.base "Term") (fun leaf : Leaf => leaf.index.val)
  lookup := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.former?

theorem driver_original_language (configuration : Configuration) (Γ : Ctx sig) :
    (driver configuration Γ).generated.snapshot.language = LambdaAuthoredFullRuleProfile.language :=
  congrArg Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot.language
    (original_snapshot configuration)

theorem complete (configuration : Configuration) (Γ : Ctx sig)
    (formula : (driver configuration Γ).Formula) (raw : Pattern)
    (admitted : ∃ source : Term sig Γ .term, encodeTerm source = raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed configuration.logic
      (driver configuration Γ).leafAdmission formula) (budget : Nat)
    (enough : ∀ source : (driver configuration Γ).Decoded raw,
      workBound (driver configuration Γ).backend (driver configuration Γ).tests formula source.val ≤ budget) :
    ∃ answer, (search (driver configuration Γ) formula raw budget).readout = .judgment (.decided answer) := by
  apply search_complete
  · obtain ⟨source, same⟩ := admitted
    exact ⟨source, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted source, same⟩
  · exact formed
  · exact admitted_cube configuration
  · exact enough

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver
