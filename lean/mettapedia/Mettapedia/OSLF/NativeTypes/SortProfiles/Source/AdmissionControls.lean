import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Formation
import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Laws

open Mettapedia.OSLF.Framework

/-!
# Actual generated classifier and law-admission separators

The input grammar has two constants, a positional binary constructor and a
constructor with an arrow-valued binder input. Its authored constant reduction
separates equation-only formation from the stronger directed-law contract.
Changing a constructor slot changes actual kind checking, not just an output
annotation. Adding commutativity constrains those same generated input slots.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source
open ModalHypercube (HSort)

def carrier : TypeExpr := .base "Value"

def first : Pattern := .apply "First" []
def second : Pattern := .apply "Second" []

def rule : RewriteRule where
  name := "FirstToSecond"
  typeContext := []
  premises := []
  left := first
  right := second

def language : LanguageDef where
  name := "ClassifiedConstructors"
  types := [TypeDecl.plain "Value"]
  terms := [
    {label := "First", category := "Value", params := [], syntaxPattern := []},
    {label := "Second", category := "Value", params := [], syntaxPattern := []},
    {label := "Pair", category := "Value", params := [.simple "x" carrier, .simple "y" carrier], syntaxPattern := []},
    {label := "Binder", category := "Value", params := [.simple "body" (.arrow carrier carrier)], syntaxPattern := []}]
  equations := []
  rewrites := [rule]

def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
def fragment : LanguageFragment := {operational := {includeDerivedEquations := false}}
def chosen := selectedSnapshot snapshot fragment
def logic := Mettapedia.OSLF.NativeTypes.Structural.heytingFragment

def starVertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language := (fun _ => .star, fun _ => .star)

def changedResultVertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun slot =>
    if slot.1.val = .constructor "Second" 0 then .box else .star)

def wrongInputVertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun slot =>
    if slot.1.val = .constructor "Pair" 2 ∧ slot.2.val = 0 then .box else .star)

def generated := generate snapshot fragment logic starVertex
def changedResult := generate snapshot fragment logic changedResultVertex
def wrongInput := generate snapshot fragment logic wrongInputVertex

def leafCode (generated : Generated) (type : TypeExpr) :
    Mettapedia.OSLF.NativeTypes.Modal.Rules.TypeCode generated.plan [] type .star where
  meaning term := HasType generated.snapshot.language generated.snapshot.free [] term type
  bounded _ typed := typed

def leaves (generated : Generated) : LeafCodes generated [] := fun index =>
  let type := if index = 1 then .arrow carrier carrier else carrier
  ⟨type, .star, leafCode generated type⟩

def literalFirstCode : Code chosen.language := .constructor ⟨0, by decide +kernel⟩ (fun position => Fin.elim0 position)
def literalSecondCode : Code chosen.language := .constructor ⟨1, by decide +kernel⟩ (fun position => Fin.elim0 position)
def literalPairCode : Code chosen.language := .constructor ⟨2, by decide +kernel⟩ (fun _ => .variableCode 0)
def literalBinderCode : Code chosen.language := .constructor ⟨3, by decide +kernel⟩ (fun _ => .variableCode 1)

theorem first_carrier_formed : Carries (leafCarriers (leaves changedResult)) literalFirstCode carrier :=
  (carrier_read_exact _ _ _).mp (by cbv)

theorem first_universe_formed : Kinded changedResult.vertex.2 (leafSorts (leaves changedResult)) literalFirstCode .star :=
  (kind_read_exact _ _ _ _).mp (by cbv)

theorem first_is_star_and_second_is_box :
    literalFirstCode ∈ Universe changedResult.vertex.2 (leafSorts (leaves changedResult)) .star ∧
      literalSecondCode ∈ Universe changedResult.vertex.2 (leafSorts (leaves changedResult)) .box := by
  constructor <;> apply (kind_read_exact _ _ _ _).mp <;> cbv

theorem actual_equation_admission_accepts : changedResult.equationAdmission = some true := by cbv

theorem actual_directed_admission_rejects : changedResult.rewriteAdmission = some false := by cbv

theorem joint_law_contract_rejects : jointAdmission changedResult = some false := by
  simp [jointAdmission, actual_equation_admission_accepts, actual_directed_admission_rejects]

theorem equation_only_constructor_executes :
    compileEquationNativeCode changedResult [] (leaves changedResult) literalFirstCode =
      .accepted ⟨carrier, .star, classify literalFirstCode first_carrier_formed first_universe_formed⟩ :=
  equation_native_code_accepts rfl actual_equation_admission_accepts first_carrier_formed first_universe_formed

theorem directed_contract_refuses_same_constructor :
    compileNativeCode changedResult [] (leaves changedResult) literalFirstCode = .refused .rejectedLawProfile := by
  simp only [compileNativeCode,
    show changedResult.logicFragment.core.structural = true from rfl, if_true, joint_law_contract_rejects]

theorem no_equations_whole_cube_but_not_joint_admission :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.center language = Finset.univ ∧
      jointAdmission changedResult = some false :=
  ⟨Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.no_equations_whole_cube language rfl, joint_law_contract_rejects⟩

theorem pair_carrier_formed : Carries (leafCarriers (leaves wrongInput)) literalPairCode carrier :=
  (carrier_read_exact _ _ _).mp (by cbv)

theorem changed_input_rejects_code : literalPairCode.kind? wrongInput.vertex.2 (leafSorts (leaves wrongInput)) = none := by
  cbv

theorem wrong_input_laws_are_admitted : jointAdmission wrongInput = some true := by cbv

theorem changed_input_refuses_actual_compilation :
    compileNativeCode wrongInput [] (leaves wrongInput) literalPairCode = .refused .malformedUniverse :=
  wrong_universe_is_refused _ _ rfl wrong_input_laws_are_admitted pair_carrier_formed changed_input_rejects_code

theorem actual_arrow_slot_forms_binder_code :
    ∃ result, compileNativeCode generated [] (leaves generated) literalBinderCode = .accepted result ∧
      result.1 = carrier ∧ result.2.1 = .star := by
  have carrierFormation : Carries (leafCarriers (leaves generated)) literalBinderCode carrier :=
    (carrier_read_exact _ _ _).mp (by cbv)
  have universeFormation : Kinded generated.vertex.2 (leafSorts (leaves generated)) literalBinderCode .star :=
    (kind_read_exact _ _ _ _).mp (by cbv)
  refine ⟨⟨carrier, .star, classify literalBinderCode carrierFormation universeFormation⟩, ?_, rfl, rfl⟩
  exact compile_native_code_accepts rfl (by cbv) carrierFormation universeFormation

def commutativeEquation : Equation where
  name := "PairComm"
  typeContext := [("x", carrier), ("y", carrier)]
  premises := []
  left := .apply "Pair" [.fvar "x", .fvar "y"]
  right := .apply "Pair" [.fvar "y", .fvar "x"]

def commutativeLanguage : LanguageDef := {language with equations := [commutativeEquation]}
def commutativeSnapshot : Snapshot := ⟨commutativeLanguage, [], ⟨[], [], []⟩⟩
def commutativeChosen := selectedSnapshot commutativeSnapshot fragment
def commutativeWrongVertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex commutativeChosen.language :=
  (fun _ => .star, fun slot =>
    if slot.1.val = .constructor "Pair" 2 ∧ slot.2.val = 0 then .box else .star)
def commutativeGenerated := generate commutativeSnapshot fragment logic commutativeWrongVertex

theorem authored_commutativity_rejects_unequal_input_slots :
    commutativeGenerated.equationAdmission = some false := by decide +kernel

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls
