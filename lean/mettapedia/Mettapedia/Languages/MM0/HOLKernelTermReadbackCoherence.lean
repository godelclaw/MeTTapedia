import Mettapedia.Languages.MM0.HOLKernelTermReadback

/-!
# Contextual round trips for the native HOL syntax reader

Every intrinsic term constructor survives encoding and readback when the
constant dictionary is faithful on its parameter indices and binder names
occupy a distinct bounded bank. The hypotheses concern individual dictionary
entries and names; no model or source derivation is supplied.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u}

theorem readType_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) (type : Ty Unit) :
    readType references (encodeType references (fun _ : Unit => Preterm.var 0) type) = some type := by
  induction type with
  | prop => simp [encodeType, applySymbol, readType, readHead_reference references faithful]
  | base name => cases name; rfl
  | arr domain codomain ihDomain ihCodomain =>
      simp [encodeType, applySymbol, Preterm.applyArgs, readType,
        readHead_reference references faithful, ihDomain, ihCodomain]


def InScope {gamma : Ctx Unit} (parameters : Nat) (names : Names gamma) (depth : Nat) : Prop :=
  names.toList.Nodup ∧ ∀ name ∈ names.toList, parameters ≤ name ∧ name < parameters + depth

theorem InScope.fresh {gamma : Ctx Unit} {parameters depth : Nat} {names : Names gamma}
    (scope : InScope parameters names depth) : names.lookup? (parameters + depth) = none := by
  apply BinderNames.lookup?_none_of_not_mem
  intro member
  exact (Nat.lt_irrefl _) (scope.2 _ member).2

theorem InScope.extend {gamma : Ctx Unit} {parameters depth : Nat} {names : Names gamma}
    (scope : InScope parameters names depth) (type : Ty Unit) :
    InScope parameters (BinderNames.cons (type := type) (parameters + depth) names) (depth + 1) := by
  refine ⟨List.nodup_cons.mpr ⟨?_, scope.1⟩, ?_⟩
  · intro member
    exact (Nat.lt_irrefl _) (scope.2 _ member).2
  · intro name member
    simp only [BinderNames.toList, List.mem_cons] at member
    rcases member with rfl | member
    · omega
    · have bounds := scope.2 name member
      omega

theorem InScope.constant_absent {gamma : Ctx Unit} {parameters depth : Nat} {names : Names gamma}
    (scope : InScope parameters names depth) (index : Nat) (bounded : index < parameters) :
    names.lookup? index = none := by
  apply BinderNames.lookup?_none_of_not_mem
  intro member
  have lower := (scope.2 _ member).1
  omega

theorem positions_cons {gamma : Ctx Unit} {type : Ty Unit} (name : Nat) (names : Names gamma) :
    (Positions.extend (domain := type) name names.nameOf : Positions (type :: gamma)) =
      (fun {_} index => (BinderNames.cons (type := type) name names).nameOf index) := by
  funext type index
  cases index <;> rfl

/-- Read every constructor of an intrinsically typed source term. -/
theorem readTermWith_encode
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    {gamma : Ctx Unit} {type : Ty Unit}
    (source : Term Const gamma type) :
    ∀ (names : Names gamma) (depth : Nat), InScope parameters names depth →
      readTermWith extras references constants parameters names
        (encodeTerm references (fun _ : Unit => Preterm.var 0) (fun {_} symbol => Preterm.var (indices symbol))
          (fun value => parameters + value) names.nameOf depth source) = some ⟨type, source⟩ := by
  induction source with
  | var index =>
      intro names depth scope
      simp [encodeTerm, readTermWith, readVariable, BinderNames.lookup?_nameOf names scope.1 index]
  | const symbol =>
      intro names depth scope
      simp [encodeTerm, readTermWith, readVariable,
        scope.constant_absent (indices symbol) (bounded symbol), lookup]
  | app function argument ihFunction ihArgument =>
      intro names depth scope
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, ihFunction names depth scope,
        ihArgument names depth scope, application]
  | lam body ih =>
      intro names depth scope
      have lower : ¬ parameters + depth < parameters := by omega
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, readType_encode references faithful,
        lower, positions_cons,
        ih (BinderNames.cons ((fun value => parameters + value) depth) names) (depth + 1) (scope.extend _)]
  | top =>
      intro names depth scope
      simp [encodeTerm, applySymbol, readTermWith, readHead_reference references faithful]
  | bot =>
      intro names depth scope
      simp [encodeTerm, applySymbol, readTermWith, readHead_reference references faithful]
  | and first second ihFirst ihSecond =>
      intro names depth scope
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, ihFirst names depth scope,
        ihSecond names depth scope, logicalBinary]
  | or first second ihFirst ihSecond =>
      intro names depth scope
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, ihFirst names depth scope,
        ihSecond names depth scope, logicalBinary]
  | imp first second ihFirst ihSecond =>
      intro names depth scope
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, ihFirst names depth scope,
        ihSecond names depth scope, logicalBinary]
  | not body ih =>
      intro names depth scope
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, ih names depth scope]
  | eq first second ihFirst ihSecond =>
      intro names depth scope
      simp only [encodeTerm, applySymbol, Preterm.applyArgs]
      unfold readTermWith
      simp [readHead_reference references faithful, readType_encode references faithful,
        ihFirst names depth scope, ihSecond names depth scope]

  | all body ih =>
      intro names depth scope
      have lower : ¬ parameters + depth < parameters := by omega
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, readType_encode references faithful,
        lower, positions_cons,
        ih (BinderNames.cons ((fun value => parameters + value) depth) names) (depth + 1) (scope.extend _)]
  | ex body ih =>
      intro names depth scope
      have lower : ¬ parameters + depth < parameters := by omega
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, readType_encode references faithful,
        lower, positions_cons,
        ih (BinderNames.cons ((fun value => parameters + value) depth) names) (depth + 1) (scope.extend _)]

/-- The primitive-only reader is the empty auxiliary-dictionary instance. -/
theorem readTerm_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (names : Names gamma) (depth : Nat) (scope : InScope parameters names depth) :
    readTerm references constants parameters names
      (encodeTerm references (fun _ : Unit => Preterm.var 0) (fun {_} symbol => Preterm.var (indices symbol))
        (fun value => parameters + value) names.nameOf depth source) = some ⟨type, source⟩ :=
  readTermWith_encode (fun {_} _ => none) references faithful constants indices parameters
    lookup bounded source names depth scope

#print axioms readType_encode
#print axioms readTerm_encode
end Mettapedia.Languages.MM0.HOLKernelTermReadback
