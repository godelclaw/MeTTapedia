import Mettapedia.Languages.MeTTa.HE.TypeGrounding.SimpleAgreement
import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
import Mettapedia.Logic.HOL.Syntax.ClosedElaboration

/-!
# The HOL contract of HE type declarations

HE's type declarations `(: name type)` mean a fixed theory of Church-style
higher-order logic, the *contract*.  It does not depend on any particular
implementation of MeTTa's type system.

**Types.**  An HE type reads as the HOL type `toTy`: an arrow
`(-> A₁ … Aₙ R)` is the curried function type, and every other atom is a base
type.  A compound non-arrow type `(T₀ T₁ … Tₙ)` is the base type of tuples
whose components have the types `Tᵢ`; the models of the contract interpret it
as the product of the component types (`HOLContract.Products`).  The atoms
that read *faithfully* (`Faithful`) mention no `%Undefined%` and use the arrow
symbol only as the head of an arrow with at least one argument and a
non-arrow return, at every depth.  On them the reading is injective
(`toTy_injective_of_faithful`): `(-> A (-> B C))` and `(-> A B C)` share one
curried reading but have different HE arities, so neither nested curried
arrows nor `%Undefined%` are contract types.  The contract types
(`ContractType`) are the faithful atoms that are not a reserved type name at
the top.

**Constants.**  A symbol or literal whose only declared type is `D` is a HOL
constant at every contract-type instance of `D` that substitutes faithful
types for its type variables (`Instance`): a type variable of a declaration is
a type variable of a polymorphic constant, and an occurrence of the constant
carries the instance it takes.  The product types
have their pairing, projections and unit (`Name.pair`, `Name.fst`,
`Name.snd`, `Name.one`).

**Terms.**  An expression `(f a₁ … aₙ)` whose head is a symbol reads as the
curried application of the constant `f`; an expression whose head has a
non-arrow type reads as a tuple, the pairing
`x₀, (x₁, … (xₙ, one))` of its elements (`tupleTerm`).  `Annotates e t` says
that `t` is a HOL term of `e` with one instance at every constant occurrence
and one component list at every tuple node; `Typed space e T` says that some
such term elaborates at the HOL type of `T`.
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

/-! ## Faithful types -/

/-- Atoms whose HOL reading is faithful.  A leaf is a type variable, a
literal, or a symbol other than the arrow and `%Undefined%`; an arrow has at
least one argument, faithful argument and return types that are not reserved
type names, and a non-arrow return; any other expression is a product of
faithful elements. -/
inductive Faithful : Atom → Prop where
  | symbol {name : String} : name ≠ "->" → name ≠ "%Undefined%" → Faithful (.symbol name)
  | var (name : String) : Faithful (.var name)
  | grounded (value : GroundedValue) : Faithful (.grounded value)
  | arrow {type returnType : Atom} {argumentTypes : List Atom} :
      FunctionTypeRel type argumentTypes returnType → argumentTypes ≠ [] →
      (∀ argumentType ∈ argumentTypes, Faithful argumentType) →
      (∀ argumentType ∈ argumentTypes, ¬TopReserved argumentType) →
      ¬ArrowShaped returnType → ¬TopReserved returnType → Faithful returnType →
      Faithful type
  | product {elements : List Atom} :
      ¬ArrowShaped (.expression elements) → (∀ element ∈ elements, Faithful element) →
      Faithful (.expression elements)

/-- The types of the contract: faithful atoms that are not a reserved type
name at the top. -/
def ContractType (type : Atom) : Prop :=
  Faithful type ∧ ¬TopReserved type

/-- `%Undefined%` reads faithfully nowhere. -/
theorem Faithful.undefinedFree {type : Atom} (faithful : Faithful type) :
    UndefinedFree type := by
  induction faithful with
  | symbol _ notUndefined =>
      intro occurs
      have equal := occurs.symbol_eq
      simp only [Atom.undefinedType, Atom.symbol.injEq] at equal
      exact notUndefined equal.symm
  | var name =>
      intro occurs
      cases occurs
  | grounded value =>
      intro occurs
      cases occurs
  | @arrow type returnType argumentTypes function _ _ _ _ _ _ argumentIH returnIH =>
      rw [FunctionTypeRel] at function
      subst function
      intro occurs
      rcases occurs.expression_cases with equal | ⟨child, member, inner⟩
      · cases equal
      · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
        rcases member with rfl | member | rfl
        · have equal := inner.symbol_eq
          simp [Atom.undefinedType] at equal
        · exact argumentIH child member inner
        · exact returnIH inner
  | product _ _ elementIH =>
      intro occurs
      rcases occurs.expression_cases with equal | ⟨child, member, inner⟩
      · cases equal
      · exact elementIH child member inner

private theorem spineTy_ne_base {argumentTypes : List Atom} {returnType base : Atom}
    (nonempty : argumentTypes ≠ []) :
    spineTy argumentTypes returnType ≠ .base base := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp

private theorem faithful_spine_injective :
    ∀ {argumentTypes rightArguments : List Atom} {returnType rightReturn : Atom},
      (∀ argumentType ∈ argumentTypes, ∀ {right : Atom}, Faithful right →
        toTy argumentType = toTy right → argumentType = right) →
      (∀ argumentType ∈ rightArguments, Faithful argumentType) →
      ¬ArrowShaped returnType → ¬ArrowShaped rightReturn →
      spineTy argumentTypes returnType = spineTy rightArguments rightReturn →
      argumentTypes = rightArguments ∧ returnType = rightReturn
  | [], [], _, _, _, _, notArrow, rightNotArrow, equal => by
      simp only [spineTy_nil] at equal
      rw [toTy_of_not_arrowShaped notArrow, toTy_of_not_arrowShaped rightNotArrow] at equal
      exact ⟨rfl, Ty.base.inj equal⟩
  | [], _ :: _, _, _, _, _, notArrow, _, equal => by
      simp only [spineTy_nil, spineTy_cons] at equal
      rw [toTy_of_not_arrowShaped notArrow] at equal
      cases equal
  | _ :: _, [], _, _, _, _, _, rightNotArrow, equal => by
      simp only [spineTy_nil, spineTy_cons] at equal
      rw [toTy_of_not_arrowShaped rightNotArrow] at equal
      cases equal
  | first :: rest, rightFirst :: rightRest, _, _, argumentIH, rightFaithful,
      notArrow, rightNotArrow, equal => by
      simp only [spineTy_cons] at equal
      obtain ⟨firstEqual, restEqual⟩ := Ty.arr.inj equal
      have heads : first = rightFirst :=
        argumentIH first (by simp) (rightFaithful rightFirst (by simp)) firstEqual
      have tails := faithful_spine_injective
        (fun argumentType member => argumentIH argumentType
          (List.mem_cons_of_mem _ member))
        (fun argumentType member => rightFaithful argumentType
          (List.mem_cons_of_mem _ member))
        notArrow rightNotArrow restEqual
      exact ⟨by rw [heads, tails.1], tails.2⟩

/-- **The contract reads faithful atoms injectively.** -/
theorem toTy_injective_of_faithful {left right : Atom} (leftFaithful : Faithful left)
    (rightFaithful : Faithful right) (equal : toTy left = toTy right) : left = right := by
  have baseCase : ∀ {left right : Atom}, ¬ArrowShaped left → Faithful right →
      toTy left = toTy right → left = right := by
    intro left right notArrow rightFaithful equal
    rw [toTy_of_not_arrowShaped notArrow] at equal
    cases rightFaithful with
    | arrow function nonempty _ _ _ _ _ =>
        rw [toTy_of_functionType function nonempty] at equal
        exact absurd equal.symm (spineTy_ne_base nonempty)
    | symbol _ _ => exact Ty.base.inj (by simpa [toTy] using equal)
    | var name => exact Ty.base.inj (by simpa [toTy] using equal)
    | grounded value => exact Ty.base.inj (by simpa [toTy] using equal)
    | product rightNotArrow _ =>
        rw [toTy_of_not_arrowShaped rightNotArrow] at equal
        exact Ty.base.inj equal
  induction leftFaithful generalizing right with
  | symbol notArrowName _ =>
      exact baseCase (by rintro ⟨_, equal⟩; cases equal) rightFaithful equal
  | var name =>
      exact baseCase (by rintro ⟨_, equal⟩; cases equal) rightFaithful equal
  | grounded value =>
      exact baseCase (by rintro ⟨_, equal⟩; cases equal) rightFaithful equal
  | product notArrow _ _ =>
      exact baseCase notArrow rightFaithful equal
  | arrow function nonempty argumentsFaithful argumentsNotReserved returnNotArrow
      returnNotReserved returnFaithful argumentIH _ =>
      have leftFaithful : Faithful _ :=
        Faithful.arrow function nonempty argumentsFaithful argumentsNotReserved
          returnNotArrow returnNotReserved returnFaithful
      cases rightFaithful with
      | arrow rightFunction rightNonempty rightArguments _ rightReturnNotArrow _ _ =>
          rw [toTy_of_functionType function nonempty,
            toTy_of_functionType rightFunction rightNonempty] at equal
          obtain ⟨arguments, returns⟩ := faithful_spine_injective
            (fun argumentType member {right} rightFaithful equal =>
              argumentIH argumentType member rightFaithful equal)
            rightArguments returnNotArrow rightReturnNotArrow equal
          rw [FunctionTypeRel] at function rightFunction
          rw [function, rightFunction, arguments, returns]
      | symbol _ _ =>
          exact (baseCase (by rintro ⟨_, equal⟩; cases equal) leftFaithful equal.symm).symm
      | var name =>
          exact (baseCase (by rintro ⟨_, equal⟩; cases equal) leftFaithful equal.symm).symm
      | grounded value =>
          exact (baseCase (by rintro ⟨_, equal⟩; cases equal) leftFaithful equal.symm).symm
      | product rightNotArrow _ =>
          exact (baseCase rightNotArrow leftFaithful equal.symm).symm

/-- The list of an expression has the shape of an arrow with at least one
argument. -/
def ArrowForm (atoms : List Atom) : Prop :=
  ∃ first second rest, atoms = .symbol "->" :: first :: second :: rest

/-- An expression without the shape of an arrow reads as its own base type. -/
theorem expressionTy_of_not_arrowForm {atoms : List Atom} (notArrow : ¬ArrowForm atoms) :
    expressionTy atoms = .base (.expression atoms) := by
  unfold expressionTy
  split
  · exact absurd ⟨_, _, _, rfl⟩ notArrow
  · rfl

/-- The components of a faithful arrow. -/
theorem Faithful.of_functionType {type returnType : Atom} {argumentTypes : List Atom}
    (faithful : Faithful type) (function : FunctionTypeRel type argumentTypes returnType) :
    argumentTypes ≠ [] ∧ (∀ argumentType ∈ argumentTypes, Faithful argumentType) ∧
      (∀ argumentType ∈ argumentTypes, ¬TopReserved argumentType) ∧
      ¬ArrowShaped returnType ∧ ¬TopReserved returnType ∧ Faithful returnType := by
  cases faithful with
  | arrow function' nonempty arguments argumentsNotReserved returnNotArrow
      returnNotReserved returnFaithful =>
      obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique function function'
      exact ⟨nonempty, arguments, argumentsNotReserved, returnNotArrow, returnNotReserved,
        returnFaithful⟩
  | product notArrow _ => exact absurd (ArrowShaped.of_functionType function) notArrow
  | symbol _ _ => simp [FunctionTypeRel] at function
  | var _ => simp [FunctionTypeRel] at function
  | grounded _ => simp [FunctionTypeRel] at function

/-- A variable-free contract type is a static type of the arrow fragment. -/
theorem ContractType.static {type : Atom} (contract : ContractType type)
    (ground : TypeSubst.typeVars type = []) : StaticType type := by
  obtain ⟨faithful, notReserved⟩ := contract
  induction faithful with
  | symbol notArrow notUndefined =>
      exact .base (by rintro ⟨_, equal⟩; cases equal) notReserved
        (Faithful.symbol notArrow notUndefined).undefinedFree ground
  | var name => simp [TypeSubst.typeVars] at ground
  | grounded value =>
      exact .base (by rintro ⟨_, equal⟩; cases equal) notReserved
        (Faithful.grounded value).undefinedFree ground
  | @arrow type returnType argumentTypes function nonempty _
      argumentsNotReserved returnNotArrow returnNotReserved _ argumentIH returnIH =>
      have components : ∀ atom ∈ argumentTypes ++ [returnType],
          TypeSubst.typeVars atom = [] := by
        rw [FunctionTypeRel] at function
        subst function
        simp only [TypeSubst.typeVars] at ground
        rw [typeVarsList_eq_nil_iff] at ground
        intro atom member
        exact ground atom (List.mem_cons_of_mem _ member)
      refine .arrow function nonempty ?_ returnNotArrow
        (returnIH (components returnType (by simp)) returnNotReserved)
      intro argumentType member
      exact argumentIH argumentType member (components argumentType (by simp [member]))
        (argumentsNotReserved argumentType member)
  | @product elements notArrow elementsFaithful _ =>
      exact .base notArrow notReserved (Faithful.product notArrow elementsFaithful).undefinedFree
        ground

/-! ## The contract signature -/

/-- Constant names of the contract: a declared symbol or literal at one
instance of its declared type, and the pairing, projections and unit of the
product types.  The component list `T₀ :: Ts` names the product of `T₀` and
the product of `Ts`. -/
inductive Name where
  | declared (constant instanceType : Atom)
  | pair (components : List Atom)
  | fst (components : List Atom)
  | snd (components : List Atom)
  | one
  deriving DecidableEq

/-- The HOL type of the product of the given component types: the base type
of the expression of the components. -/
def productTy (components : List Atom) : Ty Atom := .base (.expression components)

/-- A compound non-arrow type reads as the product of its components. -/
theorem toTy_eq_productTy {components : List Atom}
    (notArrow : ¬ArrowShaped (.expression components)) :
    toTy (.expression components) = productTy components :=
  toTy_of_not_arrowShaped notArrow

/-- `instanceType` is a contract-type instance of the single declared type of
`constant`: it substitutes faithful types for the type variables. -/
def Instance (space : Space) (constant instanceType : Atom) : Prop :=
  ContractType instanceType ∧
    ∃ scheme, declaredType? space constant = some scheme ∧
      ∃ valuation : String → Atom, (∀ name, Faithful (valuation name)) ∧
        applyTypeValuation valuation scheme = instanceType

open Classical in
/-- The HOL type of a constant name. -/
noncomputable def nameType (space : Space) : Name → Option (Ty Atom)
  | .declared constant instanceType =>
      if Instance space constant instanceType then some (toTy instanceType) else none
  | .pair [] => none
  | .pair (component :: components) =>
      some (.arr (toTy component)
        (.arr (productTy components) (productTy (component :: components))))
  | .fst [] => none
  | .fst (component :: components) =>
      some (.arr (productTy (component :: components)) (toTy component))
  | .snd [] => none
  | .snd (component :: components) =>
      some (.arr (productTy (component :: components)) (productTy components))
  | .one => some (productTy [])

theorem nameType_declared_eq_some_iff {space : Space} {constant instanceType : Atom}
    {type : Ty Atom} :
    nameType space (.declared constant instanceType) = some type ↔
      Instance space constant instanceType ∧ type = toTy instanceType := by
  simp only [nameType]
  split
  · next isInstance =>
      simp only [Option.some.injEq]
      exact ⟨fun equal => ⟨isInstance, equal.symm⟩, fun both => both.2.symm⟩
  · next notInstance =>
      simp only [reduceCtorEq, false_iff]
      exact fun both => notInstance both.1

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

/-- The pairing constant of a product. -/
def pairConst (space : Space) (component : Atom) (components : List Atom) :
    Const space (.arr (toTy component)
      (.arr (productTy components) (productTy (component :: components)))) :=
  ⟨.pair (component :: components), rfl⟩

/-- The first projection of a product. -/
def fstConst (space : Space) (component : Atom) (components : List Atom) :
    Const space (.arr (productTy (component :: components)) (toTy component)) :=
  ⟨.fst (component :: components), rfl⟩

/-- The second projection of a product: the product of the remaining
components. -/
def sndConst (space : Space) (component : Atom) (components : List Atom) :
    Const space (.arr (productTy (component :: components)) (productTy components)) :=
  ⟨.snd (component :: components), rfl⟩

/-- The element of the empty product. -/
def oneConst (space : Space) : Const space (productTy []) := ⟨.one, rfl⟩

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

/-- The projection of the component at `index` from a term of the product of
the given component types. -/
def projectTerm : List Atom → Nat → ContractTerm → ContractTerm
  | component :: components, 0, term => .app (.constant (.fst (component :: components))) term
  | component :: components, index + 1, term =>
      projectTerm components index (.app (.constant (.snd (component :: components))) term)
  | [], _, term => term

mutual

/-- `term` is a HOL term of `expression`: every constant occurrence carries
an instance type, an application of a symbol is a curried application, and a
tuple, whose head type is not an arrow, is the pairing of its elements at
faithful component types. -/
inductive Annotates : Atom → ContractTerm → Prop where
  | symbol (name : String) (instanceType : Atom) :
      Annotates (.symbol name) (.constant (.declared (.symbol name) instanceType))
  | grounded (value : GroundedValue) (instanceType : Atom) :
      Annotates (.grounded value) (.constant (.declared (.grounded value) instanceType))
  | application {name : String} {instanceType : Atom} {arguments : List Atom}
      {terms : List ContractTerm} :
      AnnotatesList arguments terms →
      Annotates (.expression (.symbol name :: arguments))
        (terms.foldl .app (.constant (.declared (.symbol name) instanceType)))
  | tuple {head headType : Atom} {arguments argumentTypes : List Atom}
      {headTerm : ContractTerm} {terms : List ContractTerm} :
      ¬ArrowShaped headType → Faithful headType →
      (∀ argumentType ∈ argumentTypes, Faithful argumentType) →
      Annotates head headTerm → AnnotatesList arguments terms →
      argumentTypes.length = arguments.length →
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

/-- HE typing in the contract: some HOL term of the expression elaborates at
the HOL type of `type`. -/
def Typed (space : Space) (expression type : Atom) : Prop :=
  ∃ term, Annotates expression term ∧ Elaborates (signature space) term (toTy type)

/-! ## Applicative typing of contract terms -/

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
    {expression : Atom} → {term : ContractTerm} → Annotates expression term → Applicative term
  | _, _, .symbol _ _ => .constant _
  | _, _, .grounded _ _ => .constant _
  | _, _, .application arguments =>
      Applicative.foldl (.constant _) (AnnotatesList.applicative arguments)
  | _, _, .tuple _ _ _ head arguments _ => by
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

/-- Contract typing, read as applicative typing over the contract's name
types. -/
theorem typed_iff (space : Space) (expression type : Atom) :
    Typed space expression type ↔
      ∃ term, Annotates expression term ∧
        ApplicativeTyped (nameType space) term (toTy type) := by
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

theorem applicativeTyped_declared_iff {space : Space} {constant instanceType : Atom}
    {type : Ty Atom} :
    ApplicativeTyped (nameType space) (.constant (.declared constant instanceType)) type ↔
      Instance space constant instanceType ∧ type = toTy instanceType := by
  constructor
  · intro typed
    cases typed with
    | constant lookup => exact nameType_declared_eq_some_iff.mp lookup
  · intro both
    exact .constant (nameType_declared_eq_some_iff.mpr both)

/-- A tuple has the product type of its components exactly when each element
has its component type. -/
theorem applicativeTyped_tupleTerm_iff {space : Space} :
    ∀ {components : List Atom} {terms : List ContractTerm}, components.length = terms.length →
      ∀ {type : Ty Atom},
        ApplicativeTyped (nameType space) (tupleTerm components terms) type ↔
          type = productTy components ∧
            List.Forall₂ (fun term component =>
              ApplicativeTyped (nameType space) term (toTy component)) terms components
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

/-- A projection of a term of a product type has the type of its
component. -/
theorem applicativeTyped_projectTerm {space : Space} :
    ∀ {components : List Atom} {index : Nat} {component : Atom} {term : ContractTerm},
      components[index]? = some component →
      ApplicativeTyped (nameType space) term (productTy components) →
        ApplicativeTyped (nameType space) (projectTerm components index term)
          (toTy component)
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

#print axioms toTy_injective_of_faithful
#print axioms typed_iff
#print axioms applicativeTyped_tupleTerm_iff

end Mettapedia.Languages.MeTTa.HE.HOLContract
