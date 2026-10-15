import Mettapedia.Languages.MeTTa.HE.HOLContract.Agreement
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Gradual

/-!
# Gradual typing beside the contract

`%Undefined%` is not a type of the contract.  It is the unknown type of
Abstracting Gradual Typing, read beside the contract: a gradual type stands
for the static types it concretizes (`TypeGrounding.Gradual.Concretizes`), and
an expression is gradually typed at a gradual type when the contract types it
at one of them (`GradualTyped`).

* On static types, gradual typing is contract typing
  (`gradualTyped_static_iff`): gradual typing conservatively extends the
  contract.
* An expression is gradually typed at `G` exactly when the contract types it
  at a static type consistent with `G` (`gradualTyped_iff_consistent`); in
  particular a contract typing at a static type `T` is a gradual typing at
  every gradual type consistent with `T` (`gradualTyped_of_consistent`), and
  at `%Undefined%` (`gradualTyped_undefined`).
* An expression whose contract type is unique has no gradual typing at a type
  inconsistent with it (`not_gradualTyped_of_inconsistent`); a gradual
  judgment without a contract typing has no such negative.

The consistent application rule of gradual typing (`GradualApplication`) is
the lifting of the static application rule: an argument type and its
parameter type need only be consistent.  On static types it is the static
rule (`gradualApplication_static_iff`).  Through a first-order type scheme
the rule asks for a first-order valuation of the scheme's variables
(`GradualSchemeApplication`); on a variable-free head that is the rule itself
(`gradualSchemeApplication_iff_of_ground`).  An argument that nothing types
leaves a variable free (`numberIndexedFamily_unknown_argument`); a typed
argument inconsistent with a parameter the valuation does not reach blocks
the rule (`numberIndexedFamily_string_index`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.HE.TypeGrounding.Gradual
  (StaticAtom Concretizes Concretization)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.TheoryModel (Consistent consistent_pair_iff consistent_pair_comm)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement

/-- Gradual typing: the contract types the expression at a static type that
the gradual type concretizes to. -/
def GradualTyped (space : Space) (expression gradual : Atom) : Prop :=
  ∃ type, Concretizes gradual type ∧ Typed space expression type

/-- **Conservative extension.**  At a static type, gradual typing is contract
typing. -/
theorem gradualTyped_static_iff {space : Space} {expression type : Atom}
    (static : StaticAtom type) : GradualTyped space expression type ↔ Typed space expression type := by
  constructor
  · rintro ⟨found, concrete, typed⟩
    rw [Concretizes.eq_of_static static concrete] at typed
    exact typed
  · intro typed
    exact ⟨type, Concretizes.of_static static, typed⟩

/-- An expression is gradually typed at `G` exactly when the contract types
it at a static type consistent with `G`. -/
theorem gradualTyped_iff_consistent {space : Space} {expression gradual : Atom} :
    GradualTyped space expression gradual ↔
      ∃ type, StaticAtom type ∧ Typed space expression type ∧
        Consistent Concretization {type, gradual} := by
  constructor
  · rintro ⟨type, concrete, typed⟩
    have static := concrete.static
    exact ⟨type, static, typed,
      (consistent_pair_iff _).mpr ⟨type, Concretizes.of_static static, concrete⟩⟩
  · rintro ⟨type, static, typed, consistent⟩
    obtain ⟨found, typeConcrete, gradualConcrete⟩ := (consistent_pair_iff _).mp consistent
    rw [Concretizes.eq_of_static static typeConcrete] at gradualConcrete
    exact ⟨type, gradualConcrete, typed⟩

/-- A contract typing at a static type is a gradual typing at every gradual
type consistent with it. -/
theorem gradualTyped_of_consistent {space : Space} {expression type gradual : Atom}
    (typed : Typed space expression type) (static : StaticAtom type)
    (consistent : Consistent Concretization {type, gradual}) :
    GradualTyped space expression gradual :=
  gradualTyped_iff_consistent.mpr ⟨type, static, typed, consistent⟩

/-- Every expression with a static contract type is gradually typed at the
unknown type. -/
theorem gradualTyped_undefined {space : Space} {expression type : Atom}
    (typed : Typed space expression type) (static : StaticAtom type) :
    GradualTyped space expression Atom.undefinedType :=
  ⟨type, .unknown static, typed⟩

/-- **The only gradual negative.**  When the contract types an expression at
exactly one static type, it is not gradually typed at a type inconsistent
with that one. -/
theorem not_gradualTyped_of_inconsistent {space : Space} {expression type gradual : Atom}
    (unique : ∀ other, StaticAtom other → Typed space expression other → other = type)
    (inconsistent : ¬Consistent Concretization {type, gradual}) :
    ¬GradualTyped space expression gradual := by
  intro gradualTyped
  obtain ⟨other, static, typed, consistent⟩ := gradualTyped_iff_consistent.mp gradualTyped
  rw [unique other static typed] at consistent
  exact inconsistent consistent

/-! ## The consistent application rule -/

/-- The consistent application rule: a head of arrow type `(-> P₁ … Pₙ R)`
applied to arguments of (possibly gradual) types `A₁ … Aₙ`, each consistent
with its parameter type, has type `R`. -/
def GradualApplication (headType : Atom) (argumentTypes : List Atom) (returnType : Atom) :
    Prop :=
  ∃ parameterTypes, FunctionTypeRel headType parameterTypes returnType ∧
    List.Forall₂ (fun argumentType parameterType =>
      Consistent Concretization {argumentType, parameterType}) argumentTypes parameterTypes

private theorem forall₂_consistent_static_iff :
    ∀ {arguments parameters : List Atom}, (∀ argument ∈ arguments, StaticAtom argument) →
      (∀ parameter ∈ parameters, StaticAtom parameter) →
      (List.Forall₂ (fun argument parameter => Consistent Concretization {argument, parameter})
        arguments parameters ↔ arguments = parameters)
  | [], [], _, _ => ⟨fun _ => rfl, fun _ => .nil⟩
  | [], _ :: _, _, _ => ⟨fun all => (by cases all), fun equal => (by cases equal)⟩
  | _ :: _, [], _, _ => ⟨fun all => (by cases all), fun equal => (by cases equal)⟩
  | argument :: arguments, parameter :: parameters, argumentsStatic, parametersStatic => by
      rw [List.forall₂_cons, Gradual.agt_static_iff_eq (argumentsStatic argument (by simp))
          (parametersStatic parameter (by simp)),
        forall₂_consistent_static_iff
          (fun other member => argumentsStatic other (List.mem_cons_of_mem _ member))
          (fun other member => parametersStatic other (List.mem_cons_of_mem _ member)),
        List.cons.injEq]

/-- On static types the consistent application rule is the static one:
every argument type is its parameter type. -/
theorem gradualApplication_static_iff {headType returnType : Atom} {argumentTypes : List Atom}
    (argumentsStatic : ∀ argumentType ∈ argumentTypes, StaticAtom argumentType)
    (parameterTypes : List Atom)
    (function : FunctionTypeRel headType parameterTypes returnType)
    (parametersStatic : ∀ parameterType ∈ parameterTypes, StaticAtom parameterType) :
    GradualApplication headType argumentTypes returnType ↔ argumentTypes = parameterTypes := by
  constructor
  · rintro ⟨found, function', consistent⟩
    obtain ⟨rfl, -⟩ := FunctionTypeRel.unique function function'
    exact (forall₂_consistent_static_iff argumentsStatic parametersStatic).mp consistent
  · intro equal
    exact ⟨parameterTypes, function,
      (forall₂_consistent_static_iff argumentsStatic parametersStatic).mpr equal⟩

/-- The unknown type is consistent with every variable-free parameter type:
an argument that nothing types never blocks the consistent application
rule. -/
theorem undefined_consistent {parameterType : Atom}
    (ground : TypeSubst.typeVars parameterType = []) :
    Consistent Concretization {Atom.undefinedType, parameterType} := by
  obtain ⟨static, concrete⟩ := Concretizes.exists ground
  exact (consistent_pair_iff _).mpr ⟨static, .unknown concrete.static, concrete⟩

/-! ## The consistent application rule through a first-order scheme -/

/-- The consistent application rule through a first-order type scheme: some
first-order valuation of the scheme's variables gives an arrow to which the
consistent application rule applies. -/
def GradualSchemeApplication (headType : Atom) (argumentTypes : List Atom)
    (returnType : Atom) : Prop :=
  ∃ valuation, Schematic.FirstOrderValuation valuation ∧
    GradualApplication (applyTypeValuation valuation headType) argumentTypes returnType

/-- Every type variable valued by `Nat`. -/
private def natValuation : String → Atom := fun _ => .symbol "Nat"

private theorem natValuation_firstOrder : Schematic.FirstOrderValuation natValuation :=
  fun _ => ⟨Schematic.reservedFree_symbol_iff.mpr (by decide), rfl⟩

/-- A variable-free head needs no valuation: through it the scheme rule is
the consistent application rule. -/
theorem gradualSchemeApplication_iff_of_ground {headType returnType : Atom}
    {argumentTypes : List Atom} (ground : TypeSubst.typeVars headType = []) :
    GradualSchemeApplication headType argumentTypes returnType ↔
      GradualApplication headType argumentTypes returnType := by
  constructor
  · rintro ⟨valuation, -, application⟩
    rwa [Gradual.applyTypeValuation_of_typeVars_nil valuation headType ground] at application
  · intro application
    refine ⟨natValuation, natValuation_firstOrder, ?_⟩
    rwa [Gradual.applyTypeValuation_of_typeVars_nil natValuation headType ground]

/-- `(-> $t Number Type)`: a family of types indexed by a number, at any
element type. -/
def numberIndexedFamily : Atom :=
  .expression [.symbol "->", .var "t", .symbol "Number", .symbol "Type"]

private theorem number_static : StaticAtom (.symbol "Number") :=
  StaticAtom.symbol (by decide)

/-- **Positive control.**  An argument that nothing types is consistent
with the scheme's variable, so `(-> $t Number Type)` applied to an argument
of unknown type and a number has type `Type`. -/
theorem numberIndexedFamily_unknown_argument :
    GradualSchemeApplication numberIndexedFamily
      [Atom.undefinedType, .symbol "Number"] (.symbol "Type") := by
  refine ⟨natValuation, natValuation_firstOrder, [.symbol "Nat", .symbol "Number"],
    by simp [FunctionTypeRel, numberIndexedFamily, applyTypeValuation, natValuation], ?_⟩
  refine .cons (undefined_consistent rfl) (.cons ?_ .nil)
  exact (consistent_pair_iff _).mpr
    ⟨.symbol "Number", Concretizes.of_static number_static, Concretizes.of_static number_static⟩

/-- **Negative control.**  No valuation reaches the second parameter, so a
`String` there is inconsistent with it whatever the first argument is. -/
theorem numberIndexedFamily_string_index (argumentType : Atom) :
    ¬GradualSchemeApplication numberIndexedFamily
      [argumentType, .symbol "String"] (.symbol "Type") := by
  rintro ⟨valuation, -, parameterTypes, function, consistent⟩
  simp only [numberIndexedFamily, applyTypeValuation, List.map_cons, List.map_nil,
    FunctionTypeRel] at function
  obtain ⟨first, second, rfl⟩ : ∃ first second, parameterTypes = [first, second] := by
    rcases consistent with _ | ⟨_, consistent⟩
    rcases consistent with _ | ⟨_, consistent⟩
    cases consistent
    exact ⟨_, _, rfl⟩
  simp only [List.cons_append, List.nil_append, Atom.expression.injEq, List.cons.injEq,
    and_true] at function
  obtain ⟨-, -, rfl, -⟩ := function
  rcases consistent with _ | ⟨_, consistent⟩
  rcases consistent with _ | ⟨stringConsistent, -⟩
  rw [Gradual.agt_static_iff_eq (StaticAtom.symbol (by decide)) number_static] at stringConsistent
  exact absurd stringConsistent (by decide)

#print axioms gradualTyped_static_iff
#print axioms gradualTyped_iff_consistent
#print axioms not_gradualTyped_of_inconsistent
#print axioms gradualApplication_static_iff
#print axioms gradualSchemeApplication_iff_of_ground
#print axioms numberIndexedFamily_unknown_argument
#print axioms numberIndexedFamily_string_index

end Mettapedia.Languages.MeTTa.HE.HOLContract
