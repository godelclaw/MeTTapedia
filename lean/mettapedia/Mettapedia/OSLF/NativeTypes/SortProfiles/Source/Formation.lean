import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.ModalCodes
import Mettapedia.OSLF.NativeTypes.Generation.ModalFormation

open Mettapedia.OSLF.Framework

/-!
# Equation-center formation and its stronger directed contract

Equation-only formation and joint equation/directed preservation are named
separately. Scoped operational reduction remains justified by actual native
receipts; an unresolved display interpretation of its directed laws does not
turn a formed modal code into a negative observation.

Supplied native input codes become assumptions in an explicit code context.
The generated modal constructor extends that syntax with the actual authored
occurrence and its dependent continuation family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.NativeTypes.Generation (Generated ModalParameters ModalInputs)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema TypeCode)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (RelyCode)
open ModalHypercube (HSort)

def suppliedLeaves {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr} {sort : HSort}
    (code : TypeCode generated.plan bound carrier sort) : LeafCodes generated bound :=
  fun _ => ⟨carrier, sort, code⟩

/-- A supplied native code is a context assumption, not a newly generated
constructor. The compiler's nontrivial constructors consume those assumptions. -/
def contextCode {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr} {sort : HSort}
    (code : TypeCode generated.plan bound carrier sort) :
    ClassifiedCode generated bound (suppliedLeaves code) carrier sort :=
  classify (.variableCode 0) (.variableCode 0) (.variableCode 0)

theorem context_code_readout {generated : Generated} {bound : List TypeExpr}
    {carrier : TypeExpr} {sort : HSort} (code : TypeCode generated.plan bound carrier sort) (term : Pattern) :
    (contextCode code).code.meaning term ↔ code.meaning term := Iff.rfl

def relyBodyCode {generated : Generated} {schema : Schema generated.plan} {name : String} {sort : HSort}
    (native : RelyCode schema name sort) :
    TypeCode generated.plan (native.dependencies ++ schema.bound) native.carrier sort where
  meaning body := native.meaning ⟨native.dependencies, schema.bound.length, body⟩
  bounded body meaningful :=
    (native.bounded ⟨native.dependencies, schema.bound.length, body⟩ meaningful).2.2

def liftRelyCode {generated : Generated} {schema : Schema generated.plan} {name : String} {sort : HSort}
    (native : RelyCode schema name sort) : ClassifiedRelyCode generated schema name sort where
  declaration := ⟨native.carrier, native.dependencies, native.declaredCarrier, native.declaredDependencies⟩
  leaves := suppliedLeaves (relyBodyCode native)
  input := contextCode (relyBodyCode native)

theorem lifted_rely_readout {generated : Generated} {schema : Schema generated.plan} {name : String}
    {sort : HSort} (native : RelyCode schema name sort) (value : ContextualValue) :
    (liftRelyCode native).native.meaning value ↔ native.meaning value := by
  change (value.dependencies = native.dependencies ∧ value.ambient = schema.bound.length ∧
    native.meaning ⟨native.dependencies, schema.bound.length, value.body⟩) ↔ native.meaning value
  constructor
  · rintro ⟨dependencies, ambient, meaningful⟩
    have same : (⟨native.dependencies, schema.bound.length, value.body⟩ : ContextualValue) = value := by
      cases value
      cases dependencies
      cases ambient
      rfl
    rw [same] at meaningful
    exact meaningful
  · intro meaningful
    have typed := native.bounded value meaningful
    refine ⟨typed.1, typed.2.1, ?_⟩
    have same : (⟨native.dependencies, schema.bound.length, value.body⟩ : ContextualValue) = value := by
      cases value
      cases typed.1
      cases typed.2.1
      rfl
    rw [same]
    exact meaningful

def liftModalInputs {generated : Generated} {schema : Schema generated.plan} :
    {parameters : Option (ModalParameters schema)} → ModalInputs schema parameters →
      ClassifiedModalInputs generated schema parameters
  | none, _ => ()
  | some _, inputs =>
      ⟨fun name => liftRelyCode (inputs.1 name), fun assignment =>
        ⟨suppliedLeaves (inputs.2 assignment), contextCode (inputs.2 assignment)⟩⟩

def compileEquationNativeCode (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (expression : Code generated.snapshot.language) :
    Compilation generated bound leaves :=
  if generated.logicFragment.core.structural then
    match generated.equationAdmission with
    | none => .unresolved
    | some false => .refused .rejectedLawProfile
    | some true =>
        match carrierRead : expression.carrier? (leafCarriers leaves) with
        | none => .refused .malformedCarrier
        | some carrier =>
            match universeRead : expression.kind? generated.vertex.2 (leafSorts leaves) with
            | none => .refused .malformedUniverse
            | some sort => .accepted ⟨carrier, sort, classify expression
                ((carrier_read_exact _ _ _).mp carrierRead)
                ((kind_read_exact _ _ _ _).mp universeRead)⟩
  else .refused .disabledStructuralFragment

theorem equation_native_code_accepts {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {expression : Code generated.snapshot.language}
    {carrier : TypeExpr} {sort : HSort}
    (enabled : generated.logicFragment.core.structural = true)
    (admitted : generated.equationAdmission = some true)
    (carrierFormation : Carries (leafCarriers leaves) expression carrier)
    (universeFormation : Kinded generated.vertex.2 (leafSorts leaves) expression sort) :
    compileEquationNativeCode generated bound leaves expression = .accepted
      ⟨carrier, sort, classify expression carrierFormation universeFormation⟩ := by
  simp only [compileEquationNativeCode, enabled, if_true, admitted]
  split
  · rename_i missing
    have present := carries_read carrierFormation
    rw [missing] at present
    cases present
  · rename_i actualCarrier readCarrier
    have agrees : actualCarrier = carrier := Option.some.inj
      (readCarrier.symm.trans (carries_read carrierFormation))
    subst actualCarrier
    split
    · rename_i missing
      have present := kinded_read universeFormation
      rw [missing] at present
      cases present
    · rename_i actualSort readSort
      have agrees : actualSort = sort := Option.some.inj
        (readSort.symm.trans (kinded_read universeFormation))
      subst actualSort
      rfl

def compileEquationModalNativeCode (generated : Generated) (schema : Schema generated.plan)
    (inputs : ClassifiedModalInputs generated schema (generated.modalParameters? schema)) :
    Option (Σ sort : HSort, ClassifiedModalCode generated schema sort) :=
  if generated.equationAdmission = some true ∧ generated.logicFragment.core.modal = true ∧
      generated.schemaAdmitted? schema = true then
    match computed : generated.modalParameters? schema with
    | none => none
    | some parameters =>
        some ⟨parameters.output, classifiedModalCode parameters computed (computed ▸ inputs)⟩
  else none

theorem equation_modal_code_native_comparison {generated : Generated} {schema : Schema generated.plan}
    (inputs : ClassifiedModalInputs generated schema (generated.modalParameters? schema))
    {result : Σ sort : HSort, ClassifiedModalCode generated schema sort}
    (accepted : compileEquationModalNativeCode generated schema inputs = some result) :
    generated.modalFormer? schema (toNativeInputs inputs) = some ⟨result.1, result.2.code⟩ := by
  unfold compileEquationModalNativeCode at accepted
  split at accepted
  · rename_i permitted
    unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.modalFormer?
    rw [if_pos permitted]
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

/-- Every actual generated schema with checked equation admission forms its
code-bearing output from classified input families. Coordinate completeness is
earned from generation, rather than supplied as an interface assumption. -/
theorem generated_equation_modal_formation_complete
    (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment).language)
    (schema : Schema (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).plan)
    (member : schema ∈ (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).modalCatalogue)
    (admitted : (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).equationAdmission = some true)
    (inputs : ClassifiedModalInputs (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex) schema
      ((Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).modalParameters? schema)) :
    ∃ result, compileEquationModalNativeCode (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex)
      schema inputs = some result ∧ result.2.expression ∈
        ModalUniverse (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex) schema result.1 := by
  have enabled := Mettapedia.OSLF.NativeTypes.Generation.generated_modal_catalogue_enabled snapshot fragment logic vertex schema member
  change (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).logicFragment.core.modal = true at enabled
  obtain ⟨parameters, computed⟩ :=
    Mettapedia.OSLF.NativeTypes.Generation.generated_modal_parameters_complete snapshot fragment logic vertex schema member
  have forms : (compileEquationModalNativeCode (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex)
      schema inputs).isSome = true := by
    unfold compileEquationModalNativeCode
    rw [if_pos ⟨admitted, enabled, Mettapedia.OSLF.NativeTypes.Generation.generated_schema_admitted member⟩]
    split
    · rename_i absent
      rw [computed] at absent
      cases absent
    · rfl
  obtain ⟨result, accepted⟩ := Option.isSome_iff_exists.mp forms
  exact ⟨result, accepted, result.2.universeFormation⟩

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source
