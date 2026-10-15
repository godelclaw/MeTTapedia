import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Codes
import Mettapedia.OSLF.NativeTypes.Generation.ModalCodes

open Mettapedia.OSLF.Framework

/-!
# Dependent code syntax for the generated modal former

Rely inputs retain the carrier and complete dependency context of their
authored declarations. Continuations retain one classified code for every
complete scoped assignment. The modal code records those actual expressions;
its universe judgment checks the computed rely slots and continuation slot.

The constructor delegates its meaning to the same generated modal former
used by the specified-contractum rules. Joint law admission is consumed before
that constructor can be returned.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.NativeTypes.Generation (Generated ModalParameters ModalInputs)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema TypeCode)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (RelyCode RelyIndex RelyCodes)
open ModalHypercube (HSort)

structure RelyDeclaration {generated : Generated} (schema : Schema generated.plan) (name : String) where
  carrier : TypeExpr
  dependencies : List TypeExpr
  declaredCarrier : schema.declaration.rule.typeContext.lookup name = some carrier
  declaredDependencies : dependencies? schema.declaration.binding.spec name = some dependencies

def RelyDeclaration.read? {generated : Generated} (schema : Schema generated.plan) (name : String) :
    Option (RelyDeclaration schema name) :=
  match carrierRead : schema.declaration.rule.typeContext.lookup name with
  | none => none
  | some carrier =>
      match dependenciesRead : dependencies? schema.declaration.binding.spec name with
      | none => none
      | some dependencies => some ⟨carrier, dependencies, carrierRead, dependenciesRead⟩

structure ClassifiedRelyCode (generated : Generated) (schema : Schema generated.plan)
    (name : String) (sort : HSort) where
  declaration : RelyDeclaration schema name
  leaves : LeafCodes generated (declaration.dependencies ++ schema.bound)
  input : ClassifiedCode generated (declaration.dependencies ++ schema.bound) leaves declaration.carrier sort

def ClassifiedRelyCode.native {generated : Generated} {schema : Schema generated.plan}
    {name : String} {sort : HSort} (classified : ClassifiedRelyCode generated schema name sort) :
    RelyCode schema name sort where
  carrier := classified.declaration.carrier
  dependencies := classified.declaration.dependencies
  declaredCarrier := classified.declaration.declaredCarrier
  declaredDependencies := classified.declaration.declaredDependencies
  meaning value := value.dependencies = classified.declaration.dependencies ∧
    value.ambient = schema.bound.length ∧ classified.input.code.meaning value.body
  bounded value inhabited :=
    ⟨inhabited.1, inhabited.2.1, classified.input.code.bounded value.body inhabited.2.2⟩

theorem classified_rely_readout {generated : Generated} {schema : Schema generated.plan}
    {name : String} {sort : HSort} (classified : ClassifiedRelyCode generated schema name sort)
    (value : ContextualValue) :
    classified.native.meaning value ↔ value.dependencies = classified.declaration.dependencies ∧
      value.ambient = schema.bound.length ∧
      meaning generated (classified.declaration.dependencies ++ schema.bound)
        classified.leaves classified.input.expression value.body := by
  exact and_congr Iff.rfl (and_congr Iff.rfl (classified.input.meaningComparison value.body))

abbrev ContinuationCode (generated : Generated) (schema : Schema generated.plan) (sort : HSort) :=
  Σ leaves : LeafCodes generated schema.bound,
    ClassifiedCode generated schema.bound leaves schema.programCarrier sort

structure ModalExpression (generated : Generated) (schema : Schema generated.plan) where
  relyExpressions : RelyIndex schema → Code generated.snapshot.language
  relyValuations : RelyIndex schema → Nat → HSort
  continuationExpressions : Assignment → Code generated.snapshot.language
  continuationValuations : Assignment → Nat → HSort

/-- Modal formation reads the actual computed occurrence profile and checks
every rely code and every substituted continuation at its assigned slot. -/
inductive ModalKinded (generated : Generated) (schema : Schema generated.plan) :
    ModalExpression generated schema → HSort → Prop where
  | constructor (parameters : ModalParameters schema)
      (computed : generated.modalParameters? schema = some parameters)
      (expression : ModalExpression generated schema)
      (relies : ∀ name, Kinded generated.vertex.2 (expression.relyValuations name)
        (expression.relyExpressions name) (parameters.inputs name))
      (continuations : ∀ assignment, Kinded generated.vertex.2 (expression.continuationValuations assignment)
        (expression.continuationExpressions assignment) parameters.output) :
      ModalKinded generated schema expression parameters.output

def ModalUniverse (generated : Generated) (schema : Schema generated.plan) (sort : HSort) :
    Set (ModalExpression generated schema) := {expression | ModalKinded generated schema expression sort}

theorem modal_universe_unique {generated : Generated} {schema : Schema generated.plan}
    {expression : ModalExpression generated schema} {first second : HSort}
    (firstFormation : ModalKinded generated schema expression first)
    (secondFormation : ModalKinded generated schema expression second) : first = second := by
  cases firstFormation with
  | constructor firstParameters firstComputed expression relies continuations =>
      cases secondFormation with
      | constructor secondParameters secondComputed expression relies continuations =>
          have equal : firstParameters = secondParameters :=
            Option.some.inj (firstComputed.symm.trans secondComputed)
          exact congrArg ModalParameters.output equal

theorem modal_universes_disjoint (generated : Generated) (schema : Schema generated.plan) :
    Disjoint (ModalUniverse generated schema .star) (ModalUniverse generated schema .box) := by
  rw [Set.disjoint_left]
  intro expression first second
  cases modal_universe_unique first second

def ClassifiedModalInputs (generated : Generated) (schema : Schema generated.plan) :
    Option (ModalParameters schema) → Type
  | none => Unit
  | some parameters =>
      ((name : RelyIndex schema) → ClassifiedRelyCode generated schema name.val (parameters.inputs name)) ×
        (Assignment → ContinuationCode generated schema parameters.output)

def modalExpression {generated : Generated} {schema : Schema generated.plan}
    {parameters : ModalParameters schema} (inputs : ClassifiedModalInputs generated schema (some parameters)) :
    ModalExpression generated schema where
  relyExpressions name := (inputs.1 name).input.expression
  relyValuations name := leafSorts (inputs.1 name).leaves
  continuationExpressions assignment := (inputs.2 assignment).2.expression
  continuationValuations assignment := leafSorts (inputs.2 assignment).1

def nativeModalInputs {generated : Generated} {schema : Schema generated.plan}
    {parameters : ModalParameters schema} (inputs : ClassifiedModalInputs generated schema (some parameters)) :
    ModalInputs schema (some parameters) :=
  ⟨fun name => (inputs.1 name).native, fun assignment => (inputs.2 assignment).2.code⟩

def toNativeInputs {generated : Generated} {schema : Schema generated.plan} :
    {parameters : Option (ModalParameters schema)} →
      ClassifiedModalInputs generated schema parameters → ModalInputs schema parameters
  | none, _ => ()
  | some _, inputs => nativeModalInputs inputs

theorem native_inputs_transport {generated : Generated} {schema : Schema generated.plan}
    {first second : Option (ModalParameters schema)} (equal : first = second)
    (inputs : ClassifiedModalInputs generated schema first) :
    toNativeInputs (equal ▸ inputs) = equal ▸ toNativeInputs inputs := by
  cases equal
  rfl

structure ClassifiedModalCode (generated : Generated) (schema : Schema generated.plan) (sort : HSort) where
  expression : ModalExpression generated schema
  universeFormation : ModalKinded generated schema expression sort
  code : TypeCode generated.plan schema.focusBound schema.focusCarrier sort
  parameters : ModalParameters schema
  computedParameters : generated.modalParameters? schema = some parameters
  resultSlot : sort = parameters.output
  inputs : ClassifiedModalInputs generated schema (some parameters)
  syntaxComparison : expression = modalExpression inputs
  meaningComparison : ∀ term, code.meaning term ↔
    (Mettapedia.OSLF.NativeTypes.Modal.Formation.generatedFormer schema parameters.inputs parameters.output parameters.output
      (nativeModalInputs inputs).1 (nativeModalInputs inputs).2).meaning term

def classifiedModalCode {generated : Generated} {schema : Schema generated.plan}
    (parameters : ModalParameters schema) (computed : generated.modalParameters? schema = some parameters)
    (inputs : ClassifiedModalInputs generated schema (some parameters)) :
    ClassifiedModalCode generated schema parameters.output where
  expression := modalExpression inputs
  universeFormation := .constructor parameters computed _
    (fun name => (inputs.1 name).input.universeFormation)
    (fun assignment => (inputs.2 assignment).2.universeFormation)
  code := Mettapedia.OSLF.NativeTypes.Modal.Formation.generatedFormer schema parameters.inputs parameters.output parameters.output
    (nativeModalInputs inputs).1 (nativeModalInputs inputs).2
  parameters := parameters
  computedParameters := computed
  resultSlot := rfl
  inputs := inputs
  syntaxComparison := rfl
  meaningComparison _ := Iff.rfl

def compileModalNativeCode (generated : Generated) (schema : Schema generated.plan)
    (inputs : ClassifiedModalInputs generated schema (generated.modalParameters? schema)) :
    Option (Σ sort : HSort, ClassifiedModalCode generated schema sort) :=
  if jointAdmission generated = some true ∧ generated.logicFragment.core.modal = true ∧
      generated.schemaAdmitted? schema = true then
    match computed : generated.modalParameters? schema with
    | none => none
    | some parameters =>
        some ⟨parameters.output, classifiedModalCode parameters computed (computed ▸ inputs)⟩
  else none

/-- The modal code-bearing output delegates to the actual generated former,
with exactly the same dependently substituted input families. -/
theorem compiled_modal_code_native_comparison {generated : Generated} {schema : Schema generated.plan}
    (inputs : ClassifiedModalInputs generated schema (generated.modalParameters? schema))
    {result : Σ sort : HSort, ClassifiedModalCode generated schema sort}
    (accepted : compileModalNativeCode generated schema inputs = some result) :
    generated.modalFormer? schema (toNativeInputs inputs) =
        some ⟨result.1, result.2.code⟩ := by
  unfold compileModalNativeCode at accepted
  split at accepted
  · rename_i permitted
    have equationAdmitted := ((joint_admission_exact generated).mp permitted.1).1
    unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.modalFormer?
    rw [if_pos ⟨equationAdmitted, permitted.2⟩]
    split at accepted
    · cases accepted
    · rename_i parameters computed
      cases accepted
      split
      · rename_i absent
        rw [computed] at absent
        cases absent
      · rename_i actualParameters actual
        have equal : actualParameters = parameters := Option.some.inj (actual.symm.trans computed)
        subst actualParameters
        rw [← native_inputs_transport actual inputs]
        rfl
  · cases accepted

theorem compiled_modal_code_consumes_laws {generated : Generated} {schema : Schema generated.plan}
    (inputs : ClassifiedModalInputs generated schema (generated.modalParameters? schema))
    {result : Σ sort : HSort, ClassifiedModalCode generated schema sort}
    (accepted : compileModalNativeCode generated schema inputs = some result) :
    generated.equationAdmission = some true ∧ generated.rewriteAdmission = some true := by
  unfold compileModalNativeCode at accepted
  split at accepted
  · rename_i permitted
    exact (joint_admission_exact generated).mp permitted.1
  · cases accepted

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source
