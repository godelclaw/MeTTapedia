import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Tuples
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Schematic
import Mettapedia.Logic.HOL.Syntax.ClosedElaboration

/-!
# The HOL contract of HE type declarations

HE's type declarations `(: name type)` mean a fixed theory of Church-style higher-order logic,
the *contract*.  It does not depend on any particular implementation of MeTTa's type system.
The contract is HE's theory of first-order prenex schemes hosted in HOL, without identifying
any two HE types.

**Types.**  Every HE type is the HOL base type of the atom itself.  The contract types
(`ContractType`) are the type atoms (`TypeAtom`) that are not a reserved name: `%Undefined%` and
the arrow symbol never occur as a leaf, and the components of an arrow are not reserved names.
An arrow `(-> P₁ … Pₙ R)` is the base type of that atom, so arrows of different arities are
different types and an arrow returning an arrow is not an arrow of another arity.  A compound
non-arrow type `(T₀ T₁ … Tₙ)` is the base type of tuples; the models of the contract interpret
it as the product of the component types (`HOLContract.Products`).

**Constants.**  Every declaration is its own constant, `Name.declared constant occurrence
instance`: the `occurrence`-th declared type of an atom, at each instance that substitutes atoms
for its type variables and is a contract type (`Instance`).  A symbol declared twice has two
constants, and an annotated expression `(: expr type)` is a constant too.  The application
constant `Name.apply [P₁, …, Pₙ] R` has type `(-> P₁ … Pₙ R) ⇒ P₁ ⇒ … ⇒ Pₙ ⇒ R`.  The product
types have their pairing, projections and unit.

**Terms.**  A declared atom is one of its constants; an expression `(f a₁ … aₙ)` is the
application constant of an n-ary arrow applied to `f` and the arguments, so a partial or an
over-application has no type; an expression whose head has a non-arrow type is the pairing
`x₀, (x₁, … (xₙ, one))` of its elements.  `Annotates e t` says that `t` is such a term of `e`,
and `Typed space e T` says that some such term elaborates at the base type `T`.

**HE's first-order rule.**  `FirstOrderType` is HE's typing rule without `%Undefined%`,
meta-types or subtypes: a declared atom has every instance of each of its declarations, an
application of an arrow to exactly as many arguments as it has parameters has the arrow's return
type, and an expression whose head has a non-arrow type has the tuple of its elements' types.
`typed_iff_firstOrder`: the contract types an expression at a type exactly when that rule does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-- A valuation fixes a variable-free atom. -/
theorem applyTypeValuation_of_ground (valuation : String → Atom) {atom : Atom}
    (ground : TypeSubst.typeVars atom = []) : applyTypeValuation valuation atom = atom :=
  (applyTypeValuation_congr_of_typeVars (right := fun name => .var name) atom
    (fun name member => by simp [ground] at member)).trans
    (Theory.applyTypeValuation_var_identity atom)

/-! ## Contract types -/

/-- Atoms that are types of the contract or components of one.  A leaf is a type variable,
a literal, or a symbol other than the arrow and `%Undefined%`; an arrow has at least its
return type, and its components are type atoms other than the reserved names; any other
expression has type atoms as elements. -/
inductive TypeAtom : Atom → Prop where
  | symbol {name : String} : name ≠ "->" → name ≠ "%Undefined%" → TypeAtom (.symbol name)
  | var (name : String) : TypeAtom (.var name)
  | grounded (value : GroundedValue) : TypeAtom (.grounded value)
  | arrow {components : List Atom} : components ≠ [] →
      (∀ component ∈ components, TypeAtom component) →
      (∀ component ∈ components, ¬TopReserved component) →
      TypeAtom (.expression (.symbol "->" :: components))
  | compound {elements : List Atom} : ¬ArrowShaped (.expression elements) →
      (∀ element ∈ elements, TypeAtom element) → TypeAtom (.expression elements)

/-- The types of the contract: type atoms that are not a reserved name. -/
def ContractType (type : Atom) : Prop :=
  TypeAtom type ∧ ¬TopReserved type

theorem TypeAtom.not_arrow_symbol {type : Atom} (atomic : TypeAtom type) :
    type ≠ .symbol "->" := by
  rintro rfl
  cases atomic with
  | symbol notArrow _ => exact notArrow rfl

theorem contractType_symbol {name : String} (notReserved : name ∉ reservedTypeNames) :
    ContractType (.symbol name) := by
  refine ⟨.symbol ?_ ?_, ?_⟩
  · rintro rfl
    exact notReserved (by simp [reservedTypeNames])
  · rintro rfl
    exact notReserved (by simp [reservedTypeNames])
  · rintro ⟨reserved, member, equal⟩
    rw [Atom.symbol.injEq] at equal
    subst equal
    exact notReserved member

/-! ## Arrows and their application constants -/

/-- The arrow `(-> P₁ … Pₙ R)`. -/
def arrowAtom (parameters : List Atom) (result : Atom) : Atom :=
  .expression (.symbol "->" :: (parameters ++ [result]))

theorem arrowAtom_injective {parameters parameters' : List Atom} {result result' : Atom}
    (equal : arrowAtom parameters result = arrowAtom parameters' result') :
    parameters = parameters' ∧ result = result' := by
  simp only [arrowAtom, Atom.expression.injEq, List.cons.injEq, true_and] at equal
  exact List.append_inj' equal rfl |>.imp id (fun singleton => by simpa using singleton)

theorem arrowAtom_arrowShaped (parameters : List Atom) (result : Atom) :
    ArrowShaped (arrowAtom parameters result) :=
  ⟨_, rfl⟩

theorem arrowAtom_of_functionType {type result : Atom} {parameters : List Atom}
    (function : FunctionTypeRel type parameters result) : type = arrowAtom parameters result :=
  function

/-- The components of an arrow are contract types. -/
theorem TypeAtom.arrowAtom_components {parameters : List Atom} {result : Atom}
    (atomic : TypeAtom (arrowAtom parameters result)) :
    ∀ component ∈ parameters ++ [result], ContractType component := by
  cases atomic with
  | arrow _ components notReserved =>
      exact fun component member => ⟨components component member, notReserved component member⟩
  | compound notArrow _ => exact absurd ⟨_, rfl⟩ notArrow

theorem contractType_arrowAtom {parameters : List Atom} {result : Atom}
    (all : ∀ component ∈ parameters ++ [result], ContractType component) :
    ContractType (arrowAtom parameters result) := by
  refine ⟨.arrow (by simp) (fun component member => (all component member).1)
    (fun component member => (all component member).2), ?_⟩
  rintro ⟨_, _, equal⟩
  cases equal

/-- The HOL type `P₁ ⇒ … ⇒ Pₙ ⇒ R` of base types. -/
def applyTy (parameters : List Atom) (result : Atom) : Ty Atom :=
  parameters.foldr (fun parameter rest => .arr (.base parameter) rest) (.base result)

theorem applyTy_eq_foldr (parameters : List Atom) (result : Atom) :
    applyTy parameters result = (parameters.map Ty.base).foldr Ty.arr (.base result) := by
  simp [applyTy, List.foldr_map]

/-- A spine of argument types ending in a base type determines its arguments and its
return. -/
theorem foldr_eq_applyTy :
    ∀ {argumentTypes : List (Ty Atom)} {parameters : List Atom} {type result : Atom},
      argumentTypes.foldr Ty.arr (.base type) = applyTy parameters result →
        argumentTypes = parameters.map Ty.base ∧ type = result
  | [], [], _, _, equal => by
      simp only [List.foldr_nil, applyTy, Ty.base.injEq] at equal
      exact ⟨rfl, equal⟩
  | [], _ :: _, _, _, equal => by simp [applyTy] at equal
  | _ :: _, [], _, _, equal => by simp [applyTy] at equal
  | first :: rest, parameter :: parameters, _, _, equal => by
      simp only [List.foldr_cons, applyTy] at equal
      obtain ⟨firstEq, restEq⟩ := Ty.arr.inj equal
      obtain ⟨restArguments, typeEq⟩ := foldr_eq_applyTy (argumentTypes := rest)
        (parameters := parameters) restEq
      exact ⟨by rw [firstEq, restArguments]; rfl, typeEq⟩

/-! ## Declarations and their instances -/

/-- The declared types of an atom, in declaration order: the intrinsic type of a literal, and
every `(: atom type)` of a symbol or of a nonempty expression. -/
def declarations (space : Space) : Atom → List Atom
  | .grounded value => [getGroundedType value]
  | .var _ => []
  | .symbol name => getAnnotatedTypes space (.symbol name)
  | .expression [] => []
  | .expression (head :: rest) => getAnnotatedTypes space (.expression (head :: rest))

/-- A unique declaration is the only one. -/
theorem declarations_of_declared {space : Space} {atom type : Atom}
    (declared : declaredType? space atom = some type) : declarations space atom = [type] := by
  rcases Tuples.declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
  · exact getAnnotatedTypes_of_declared_symbol declared
  · simp only [declaredType?, Option.some.injEq] at declared
    simp [declarations, declared]

/-- `type` is an instance of `scheme`: a contract type that substitutes type atoms for the
scheme's type variables. -/
def TypeInstance (scheme type : Atom) : Prop :=
  ContractType type ∧ ∃ valuation : String → Atom, (∀ name, TypeAtom (valuation name)) ∧
    applyTypeValuation valuation scheme = type

/-- `type` is an instance of the declaration of `constant` at position `occurrence`. -/
def Instance (space : Space) (constant : Atom) (occurrence : Nat) (type : Atom) : Prop :=
  ∃ scheme, (declarations space constant)[occurrence]? = some scheme ∧ TypeInstance scheme type

/-- A variable-free scheme has itself as its only instance. -/
theorem typeInstance_of_ground {scheme type : Atom} (ground : TypeSubst.typeVars scheme = [])
    (instance' : TypeInstance scheme type) : type = scheme := by
  obtain ⟨_, valuation, _, equal⟩ := instance'
  rw [← equal, applyTypeValuation_of_ground valuation ground]

theorem typeInstance_self {scheme : Atom} (contract : ContractType scheme) :
    TypeInstance scheme scheme :=
  ⟨contract, fun name => .var name, fun name => .var name,
    Theory.applyTypeValuation_var_identity scheme⟩

/-! ## The signature -/

/-- Constant names of the contract: a declaration of an atom at one instance, the application
constant of an arrow, and the pairing, projections and unit of tuples. -/
inductive Name where
  | declared (constant : Atom) (occurrence : Nat) (instanceType : Atom)
  | apply (parameters : List Atom) (result : Atom)
  | pair (components : List Atom)
  | fst (components : List Atom)
  | snd (components : List Atom)
  | one
  deriving DecidableEq

open Classical in
/-- The HOL type of a constant name. -/
noncomputable def nameType (space : Space) : Name → Option (Ty Atom)
  | .declared constant occurrence instanceType =>
      if Instance space constant occurrence instanceType then
        some (.base instanceType)
      else none
  | .apply parameters result =>
      if TypeAtom (arrowAtom parameters result) then
        some (.arr (.base (arrowAtom parameters result)) (applyTy parameters result))
      else none
  | .pair [] => none
  | .pair (component :: components) =>
      some (.arr (.base component)
        (.arr (.base (.expression components)) (.base (.expression (component :: components)))))
  | .fst [] => none
  | .fst (component :: components) =>
      some (.arr (.base (.expression (component :: components))) (.base component))
  | .snd [] => none
  | .snd (component :: components) =>
      some (.arr (.base (.expression (component :: components))) (.base (.expression components)))
  | .one => some (.base (.expression []))

theorem nameType_declared_eq_some_iff {space : Space} {constant instanceType : Atom}
    {occurrence : Nat} {type : Ty Atom} :
    nameType space (.declared constant occurrence instanceType) = some type ↔
      Instance space constant occurrence instanceType ∧ type = .base instanceType := by
  simp only [nameType]
  split
  · next isInstance =>
      simp only [Option.some.injEq]
      exact ⟨fun equal => ⟨isInstance, equal.symm⟩, fun both => both.2.symm⟩
  · next notInstance =>
      simp only [reduceCtorEq, false_iff]
      exact fun both => notInstance both.1

theorem nameType_apply_eq_some_iff {space : Space} {parameters : List Atom} {result : Atom}
    {type : Ty Atom} :
    nameType space (.apply parameters result) = some type ↔
      TypeAtom (arrowAtom parameters result) ∧
        type = .arr (.base (arrowAtom parameters result)) (applyTy parameters result) := by
  simp only [nameType]
  split
  · next atomic =>
      simp only [Option.some.injEq]
      exact ⟨fun equal => ⟨atomic, equal.symm⟩, fun both => both.2.symm⟩
  · next notAtomic =>
      simp only [reduceCtorEq, false_iff]
      exact fun both => notAtomic both.1

/-- HOL constants of the contract, indexed by their HOL type. -/
def Const (space : Space) (type : Ty Atom) : Type :=
  { name : Name // nameType space name = some type }

/-- The contract signature of a declaration space. -/
noncomputable def signature (space : Space) : Signature Name (Const space) :=
  fun name =>
    match lookup : nameType space name with
    | some type => some ⟨type, ⟨name, lookup⟩⟩
    | none => none

theorem signatureType_signature (space : Space) (name : Name) :
    signatureType (signature space) name = nameType space name := by
  unfold signatureType signature
  split
  · next type lookup => simp [lookup]
  · next lookup => simp [lookup]

/-! ## Terms -/

/-- Named HOL terms over the contract's constant names. -/
abbrev ContractTerm := NamedTerm Atom String Name

/-- The tuple `x₀, (x₁, … (xₙ, one))` of terms at the given component types. -/
def tupleTerm : List Atom → List ContractTerm → ContractTerm
  | [], _ => .constant .one
  | _ :: _, [] => .constant .one
  | component :: components, term :: terms =>
      .app (.app (.constant (.pair (component :: components))) term)
        (tupleTerm components terms)

mutual

/-- `term` is a HOL term of `expression`: a declared atom is one of its declaration constants
at an instance, an application applies the application constant of an arrow to the head and
the arguments, and a tuple, whose head type is not an arrow, is the pairing of its elements. -/
inductive Annotates : Atom → ContractTerm → Prop where
  | declared (atom : Atom) (occurrence : Nat) (instanceType : Atom) :
      Annotates atom (.constant (.declared atom occurrence instanceType))
  | application {head result : Atom} {arguments parameters : List Atom}
      {headTerm : ContractTerm} {terms : List ContractTerm} :
      Annotates head headTerm → AnnotatesList arguments terms →
      Annotates (.expression (head :: arguments))
        (terms.foldl .app (.app (.constant (.apply parameters result)) headTerm))
  | tuple {head headType : Atom} {arguments argumentTypes : List Atom}
      {headTerm : ContractTerm} {terms : List ContractTerm} :
      ¬ArrowShaped headType → argumentTypes.length = arguments.length →
      Annotates head headTerm → AnnotatesList arguments terms →
      Annotates (.expression (head :: arguments))
        (tupleTerm (headType :: argumentTypes) (headTerm :: terms))

/-- Pointwise annotation of a list of expressions. -/
inductive AnnotatesList : List Atom → List ContractTerm → Prop where
  | nil : AnnotatesList [] []
  | cons {argument : Atom} {arguments : List Atom} {term : ContractTerm} {terms : List ContractTerm} :
      Annotates argument term → AnnotatesList arguments terms →
      AnnotatesList (argument :: arguments) (term :: terms)

end

theorem annotatesList_iff_forall₂ :
    ∀ {arguments : List Atom} {terms : List ContractTerm},
      AnnotatesList arguments terms ↔ List.Forall₂ Annotates arguments terms
  | [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun annotated => (by cases annotated), fun all => (by cases all)⟩
  | _ :: _, [] => ⟨fun annotated => (by cases annotated), fun all => (by cases all)⟩
  | _ :: _, _ :: _ => by
      constructor
      · intro annotated
        cases annotated with
        | cons head tail => exact .cons head (annotatesList_iff_forall₂.mp tail)
      · intro all
        cases all with
        | cons head tail => exact .cons head (annotatesList_iff_forall₂.mpr tail)

theorem annotatesList_length {arguments : List Atom} {terms : List ContractTerm}
    (annotated : AnnotatesList arguments terms) : terms.length = arguments.length :=
  (annotatesList_iff_forall₂.mp annotated).length_eq.symm

/-- HE typing in the contract: some HOL term of the expression elaborates at the base type of
`type`. -/
def Typed (space : Space) (expression type : Atom) : Prop :=
  ∃ term, Annotates expression term ∧ Elaborates (signature space) term (.base type)

theorem applicative_tupleTerm :
    ∀ (components : List Atom) {terms : List ContractTerm},
      (∀ term ∈ terms, Applicative term) → Applicative (tupleTerm components terms)
  | [], _, _ => .constant Name.one
  | _ :: _, [], _ => .constant Name.one
  | component :: components, term :: terms, all =>
      .app (.app (.constant _) (all term (by simp)))
        (applicative_tupleTerm components
          (fun other member => all other (List.mem_cons_of_mem _ member)))

mutual

theorem Annotates.applicative :
    {expression : Atom} → {term : ContractTerm} → Annotates expression term →
      Applicative term
  | _, _, .declared _ _ _ => .constant _
  | _, _, .application head arguments =>
      Applicative.foldl (.app (.constant _) head.applicative)
        (AnnotatesList.applicative arguments)
  | _, _, .tuple _ _ head arguments => by
      apply applicative_tupleTerm
      intro term member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.applicative
      · exact AnnotatesList.applicative arguments term member

theorem AnnotatesList.applicative :
    {arguments : List Atom} → {terms : List ContractTerm} → AnnotatesList arguments terms →
      ∀ term ∈ terms, Applicative term
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
      intro term member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.applicative
      · exact AnnotatesList.applicative tail term member

end

/-- Contract typing, read as applicative typing over the contract's name types. -/
theorem typed_iff (space : Space) (expression type : Atom) :
    Typed space expression type ↔
      ∃ term, Annotates expression term ∧
        ApplicativeTyped (nameType space) term (.base type) := by
  have typeOf : signatureType (signature space) = nameType space :=
    funext (signatureType_signature space)
  constructor
  · rintro ⟨term, annotates, elaborates⟩
    refine ⟨term, annotates, ?_⟩
    rw [← typeOf]
    exact (elaborates_iff_applicativeTyped annotates.applicative).mp elaborates
  · rintro ⟨term, annotates, typed⟩
    refine ⟨term, annotates, ?_⟩
    rw [← typeOf] at typed
    exact (elaborates_iff_applicativeTyped annotates.applicative).mpr typed

/-- A tuple has the base type of its component list exactly when each element has its
component type. -/
theorem applicativeTyped_tupleTerm_iff {space : Space} :
    ∀ {components : List Atom} {terms : List ContractTerm}, components.length = terms.length →
      ∀ {type : Ty Atom},
        ApplicativeTyped (nameType space) (tupleTerm components terms) type ↔
          type = .base (.expression components) ∧
            List.Forall₂ (fun term component =>
              ApplicativeTyped (nameType space) term (.base component)) terms components
  | [], [], _, type => by
      constructor
      · intro typed
        cases typed with
        | constant lookup =>
            simp only [nameType, Option.some.injEq] at lookup
            exact ⟨lookup.symm, .nil⟩
      · rintro ⟨rfl, _⟩
        exact .constant rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | component :: components, term :: terms, lengths, type => by
      have restLengths : components.length = terms.length := by simpa using lengths
      simp only [tupleTerm]
      constructor
      · intro typed
        cases typed with
        | app pairPart restTyped =>
            cases pairPart with
            | app pairTyped termTyped =>
                cases pairTyped with
                | constant lookup =>
                    simp only [nameType, Option.some.injEq] at lookup
                    obtain ⟨domainEq, middle⟩ := Ty.arr.inj lookup
                    obtain ⟨restEq, typeEq⟩ := Ty.arr.inj middle
                    subst domainEq
                    subst restEq
                    subst typeEq
                    obtain ⟨_, all⟩ := (applicativeTyped_tupleTerm_iff restLengths).mp restTyped
                    exact ⟨rfl, .cons termTyped all⟩
      · rintro ⟨rfl, all⟩
        cases all with
        | cons termTyped restAll =>
            exact .app (.app (.constant rfl) termTyped)
              ((applicativeTyped_tupleTerm_iff restLengths).mpr ⟨rfl, restAll⟩)

/-- An application of an application constant to a head and arguments. -/
theorem applicativeTyped_apply_iff {space : Space} {parameters : List Atom} {result : Atom}
    {headTerm : ContractTerm} {terms : List ContractTerm} {type : Atom} :
    ApplicativeTyped (nameType space)
        (terms.foldl .app (.app (.constant (.apply parameters result)) headTerm)) (.base type) ↔
      TypeAtom (arrowAtom parameters result) ∧ type = result ∧
        ApplicativeTyped (nameType space) headTerm (.base (arrowAtom parameters result)) ∧
        List.Forall₂ (fun term parameter =>
          ApplicativeTyped (nameType space) term (.base parameter)) terms parameters := by
  rw [applicativeTyped_foldl_iff]
  constructor
  · rintro ⟨argumentTypes, applied, all⟩
    cases applied with
    | app constantTyped headTyped =>
        cases constantTyped with
        | constant lookup =>
            obtain ⟨atomic, typeEq⟩ := nameType_apply_eq_some_iff.mp lookup
            obtain ⟨domainEq, spineEq⟩ := Ty.arr.inj typeEq
            obtain ⟨argumentsEq, resultEq⟩ := foldr_eq_applyTy spineEq
            subst domainEq argumentsEq
            refine ⟨atomic, resultEq, headTyped, ?_⟩
            rw [List.forall₂_map_right_iff] at all
            exact all
  · rintro ⟨atomic, rfl, headTyped, all⟩
    refine ⟨parameters.map Ty.base, ?_, ?_⟩
    · refine .app (.constant ?_) headTyped
      rw [nameType_apply_eq_some_iff, applyTy_eq_foldr]
      exact ⟨atomic, rfl⟩
    · rw [List.forall₂_map_right_iff]
      exact all

/-! ## HE's first-order rule -/

mutual

/-- HE's first-order typing rule: a declared atom has every instance of each of its
declarations; an application of an arrow to exactly as many arguments as it has parameters
has the arrow's return type; an expression whose head has a non-arrow type has the tuple of
its elements' types. -/
inductive FirstOrderType (space : Space) : Atom → Atom → Prop where
  | declared {atom type : Atom} {occurrence : Nat} :
      Instance space atom occurrence type → FirstOrderType space atom type
  | application {head result : Atom} {arguments parameters : List Atom} :
      FirstOrderType space head (arrowAtom parameters result) →
      FirstOrderTypes space arguments parameters →
      FirstOrderType space (.expression (head :: arguments)) result
  | tuple {head headType : Atom} {arguments argumentTypes : List Atom} :
      FirstOrderType space head headType → ¬ArrowShaped headType →
      FirstOrderTypes space arguments argumentTypes →
      FirstOrderType space (.expression (head :: arguments))
        (.expression (headType :: argumentTypes))

/-- Pointwise first-order typing of a list of expressions. -/
inductive FirstOrderTypes (space : Space) : List Atom → List Atom → Prop where
  | nil : FirstOrderTypes space [] []
  | cons {argument type : Atom} {arguments types : List Atom} :
      FirstOrderType space argument type → FirstOrderTypes space arguments types →
      FirstOrderTypes space (argument :: arguments) (type :: types)

end

theorem firstOrderTypes_iff_forall₂ {space : Space} :
    ∀ {arguments types : List Atom},
      FirstOrderTypes space arguments types ↔
        List.Forall₂ (FirstOrderType space) arguments types
  | [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun typed => (by cases typed), fun all => (by cases all)⟩
  | _ :: _, [] => ⟨fun typed => (by cases typed), fun all => (by cases all)⟩
  | _ :: _, _ :: _ => by
      constructor
      · intro typed
        cases typed with
        | cons head tail => exact .cons head (firstOrderTypes_iff_forall₂.mp tail)
      · intro all
        cases all with
        | cons head tail => exact .cons head (firstOrderTypes_iff_forall₂.mpr tail)

mutual

/-- Every first-order type is a contract type. -/
theorem FirstOrderType.contractType {space : Space} :
    {expression type : Atom} → FirstOrderType space expression type → ContractType type
  | _, _, .declared ⟨_, _, instance'⟩ => instance'.1
  | _, _, @FirstOrderType.application _ _ result _ parameters head _ =>
      (FirstOrderType.contractType head).1.arrowAtom_components result (by simp)
  | _, _, @FirstOrderType.tuple _ _ headType _ argumentTypes head headNotArrow arguments => by
      have headContract := FirstOrderType.contractType head
      refine ⟨.compound ?_ ?_, ?_⟩
      · rintro ⟨components, equal⟩
        simp only [Atom.expression.injEq, List.cons.injEq] at equal
        exact headContract.1.not_arrow_symbol equal.1
      · intro element member
        rcases List.mem_cons.mp member with rfl | member
        · exact headContract.1
        · exact (FirstOrderTypes.contractType arguments element member).1
      · rintro ⟨_, _, equal⟩
        cases equal

theorem FirstOrderTypes.contractType {space : Space} :
    {arguments types : List Atom} → FirstOrderTypes space arguments types →
      ∀ type ∈ types, ContractType type
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
      intro type member
      rcases List.mem_cons.mp member with rfl | member
      · exact FirstOrderType.contractType head
      · exact FirstOrderTypes.contractType tail type member

end

/-! ## The contract is HE's first-order rule -/

mutual

theorem firstOrder_of_annotated {space : Space} :
    {expression : Atom} → {term : ContractTerm} → Annotates expression term →
      ∀ {type : Atom}, ApplicativeTyped (nameType space) term (.base type) →
        FirstOrderType space expression type
  | _, _, .declared atom occurrence instanceType, _, typed => by
      cases typed with
      | constant lookup =>
          obtain ⟨isInstance, typeEq⟩ := nameType_declared_eq_some_iff.mp lookup
          cases typeEq
          exact .declared isInstance
  | _, _, .application head arguments, _, typed => by
      obtain ⟨_, rfl, headTyped, all⟩ := applicativeTyped_apply_iff.mp typed
      exact .application (firstOrder_of_annotated head headTyped)
        (firstOrderList_of_annotated arguments all)
  | _, _, @Annotates.tuple _ headType _ argumentTypes headTerm terms headNotArrow lengths
      head arguments, _, typed => by
      have termLengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
        simp [annotatesList_length arguments, lengths]
      obtain ⟨typeEq, all⟩ := (applicativeTyped_tupleTerm_iff termLengths).mp typed
      cases typeEq
      cases all with
      | cons headTyped rest =>
          exact .tuple (firstOrder_of_annotated head headTyped) headNotArrow
            (firstOrderList_of_annotated arguments rest)

theorem firstOrderList_of_annotated {space : Space} :
    {arguments : List Atom} → {terms : List ContractTerm} → AnnotatesList arguments terms →
      ∀ {types : List Atom},
        List.Forall₂ (fun term type =>
          ApplicativeTyped (nameType space) term (.base type)) terms types →
        FirstOrderTypes space arguments types
  | _, _, .nil, _, all => by
      cases all
      exact .nil
  | _, _, .cons head tail, _, all => by
      cases all with
      | cons headTyped rest =>
          exact .cons (firstOrder_of_annotated head headTyped)
            (firstOrderList_of_annotated tail rest)

end

mutual

theorem annotated_of_firstOrder {space : Space} :
    {expression type : Atom} → FirstOrderType space expression type →
      ∃ term, Annotates expression term ∧
        ApplicativeTyped (nameType space) term (.base type)
  | _, _, @FirstOrderType.declared _ atom type occurrence isInstance =>
      ⟨_, .declared atom occurrence type,
        .constant (nameType_declared_eq_some_iff.mpr ⟨isInstance, rfl⟩)⟩
  | _, _, @FirstOrderType.application _ _ result _ parameters head arguments => by
      obtain ⟨headTerm, headAnnotates, headTyped⟩ := annotated_of_firstOrder head
      obtain ⟨terms, termsAnnotate, all⟩ := annotatedList_of_firstOrder arguments
      exact ⟨_, .application (result := result) (parameters := parameters) headAnnotates
        termsAnnotate, applicativeTyped_apply_iff.mpr
          ⟨(FirstOrderType.contractType head).1, rfl, headTyped, all⟩⟩
  | _, _, @FirstOrderType.tuple _ _ headType _ argumentTypes head headNotArrow arguments => by
      obtain ⟨headTerm, headAnnotates, headTyped⟩ := annotated_of_firstOrder head
      obtain ⟨terms, termsAnnotate, all⟩ := annotatedList_of_firstOrder arguments
      have lengths : argumentTypes.length = _ :=
        ((firstOrderTypes_iff_forall₂.mp arguments).length_eq).symm
      have termLengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
        simp [all.length_eq]
      exact ⟨_, .tuple headNotArrow lengths headAnnotates termsAnnotate,
        (applicativeTyped_tupleTerm_iff termLengths).mpr ⟨rfl, .cons headTyped all⟩⟩

theorem annotatedList_of_firstOrder {space : Space} :
    {arguments types : List Atom} → FirstOrderTypes space arguments types →
      ∃ terms, AnnotatesList arguments terms ∧
        List.Forall₂ (fun term type =>
          ApplicativeTyped (nameType space) term (.base type)) terms types
  | _, _, .nil => ⟨[], .nil, .nil⟩
  | _, _, .cons head tail => by
      obtain ⟨term, annotates, typed⟩ := annotated_of_firstOrder head
      obtain ⟨terms, annotateTail, all⟩ := annotatedList_of_firstOrder tail
      exact ⟨term :: terms, .cons annotates annotateTail, .cons typed all⟩

end

/-- **The contract is HE's first-order rule.**  An expression has a contract term at the base
type of `type` exactly when HE's first-order rule gives it `type`. -/
theorem typed_iff_firstOrder {space : Space} {expression type : Atom} :
    Typed space expression type ↔ FirstOrderType space expression type := by
  rw [typed_iff]
  constructor
  · rintro ⟨term, annotates, typed⟩
    exact firstOrder_of_annotated annotates typed
  · exact annotated_of_firstOrder

/-- A declared atom of a variable-free declaration has only that type. -/
theorem firstOrder_declared_eq {space : Space} {atom declared type : Atom}
    (unique : declaredType? space atom = some declared)
    (ground : TypeSubst.typeVars declared = []) (typed : FirstOrderType space atom type) :
    type = declared := by
  rcases Tuples.declaredType?_symbol_or_grounded unique with ⟨name, rfl⟩ | ⟨value, rfl⟩ <;>
  · cases typed with
    | @declared _ _ occurrence isInstance =>
        obtain ⟨scheme, found, instance'⟩ := isInstance
        rw [declarations_of_declared unique] at found
        cases occurrence with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst found
            exact typeInstance_of_ground ground instance'
        | succ index => simp at found

/-- The first-order typings of a symbol are instances of its declarations. -/
theorem firstOrder_symbol {space : Space} {name : String} {type : Atom}
    (typed : FirstOrderType space (.symbol name) type) :
    ∃ (occurrence : Nat) (scheme : Atom),
      (declarations space (.symbol name))[occurrence]? = some scheme ∧
        TypeInstance scheme type := by
  cases typed with
  | @declared _ _ occurrence isInstance =>
      obtain ⟨scheme, found, instance'⟩ := isInstance
      exact ⟨occurrence, scheme, found, instance'⟩

/-! ## Projections and declared constants -/

/-- The HOL type of the product of the given component types: the base type of the
expression of the components. -/
def productTy (components : List Atom) : Ty Atom := .base (.expression components)

/-- The pairing constant of a product. -/
def pairConst (space : Space) (component : Atom) (components : List Atom) :
    Const space (.arr (.base component)
      (.arr (productTy components) (productTy (component :: components)))) :=
  ⟨.pair (component :: components), rfl⟩

/-- The first projection of a product. -/
def fstConst (space : Space) (component : Atom) (components : List Atom) :
    Const space (.arr (productTy (component :: components)) (.base component)) :=
  ⟨.fst (component :: components), rfl⟩

/-- The second projection of a product: the product of the remaining components. -/
def sndConst (space : Space) (component : Atom) (components : List Atom) :
    Const space (.arr (productTy (component :: components)) (productTy components)) :=
  ⟨.snd (component :: components), rfl⟩

/-- The element of the empty product. -/
def oneConst (space : Space) : Const space (productTy []) := ⟨.one, rfl⟩

/-- The projection of the component at `index` from a term of the product of the given
component types. -/
def projectTerm : List Atom → Nat → ContractTerm → ContractTerm
  | component :: components, 0, term => .app (.constant (.fst (component :: components))) term
  | component :: components, index + 1, term =>
      projectTerm components index (.app (.constant (.snd (component :: components))) term)
  | [], _, term => term

/-- A projection of a term of a product type has the type of its component. -/
theorem applicativeTyped_projectTerm {space : Space} :
    ∀ {components : List Atom} {index : Nat} {component : Atom} {term : ContractTerm},
      components[index]? = some component →
      ApplicativeTyped (nameType space) term (productTy components) →
        ApplicativeTyped (nameType space) (projectTerm components index term) (.base component)
  | [], _, _, _, found, _ => by simp at found
  | first :: rest, 0, component, term, found, typed => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact .app (ApplicativeTyped.constant (typeOf := nameType space)
        (name := .fst (first :: rest)) rfl) typed
  | first :: rest, index + 1, component, term, found, typed => by
      simp only [List.getElem?_cons_succ] at found
      simp only [projectTerm]
      exact applicativeTyped_projectTerm (components := rest) (index := index)
        (term := .app (.constant (.snd (first :: rest))) term) found
        (.app (ApplicativeTyped.constant (typeOf := nameType space)
          (name := .snd (first :: rest)) rfl) typed)

theorem applicativeTyped_declared_iff {space : Space} {constant instanceType : Atom}
    {occurrence : Nat} {type : Ty Atom} :
    ApplicativeTyped (nameType space) (.constant (.declared constant occurrence instanceType)) type ↔
      Instance space constant occurrence instanceType ∧ type = .base instanceType := by
  constructor
  · intro typed
    cases typed with
    | constant lookup => exact nameType_declared_eq_some_iff.mp lookup
  · intro both
    exact .constant (nameType_declared_eq_some_iff.mpr both)

#print axioms typed_iff
#print axioms typed_iff_firstOrder
#print axioms applicativeTyped_tupleTerm_iff
#print axioms applicativeTyped_apply_iff

end Mettapedia.Languages.MeTTa.HE.HOLContract
