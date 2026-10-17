import Mettapedia.Languages.MeTTa.HE.HOLContract.Agreement

/-!
# The curried view of the contract

HOL's function types give HE's arrows a second reading, the *curried view*: an arrow
`(-> A₁ … Aₙ R)` read as the curried function type `A₁ ⇒ … ⇒ Aₙ ⇒ R`, a declared constant at
an instance of its single declaration, and an application `(f a₁ … aₙ)` read as the curried
application of `f`.  The view is not the contract.  It identifies `(-> A (-> B C))` with
`(-> A B C)` and it types partial applications, so it is faithful only on the atoms that read
injectively (`Faithful`) and on saturated terms.

There it agrees with the contract: on the tuple fragment over faithful declarations
(`typed_iff_curried_of_tuple`) and on first-order schemes (`typed_iff_curried_of_schematic`),
an expression has a curried typing at a type exactly when the contract types it.  The view's
own agreements with HE, which these theorems use, are `tuple_iff_reference`,
`static_iff_exact` and `schematic_iff_exact` below.

Off those fragments the view and the contract part (`Separating`): with
`(: sk (-> SA (-> SB SC)))`, `(: sg (-> SA SB SC))` and `(: sapply (-> (-> $a $b) $a $b))`, the
view types the partial application `(sg sA)`, which HE refuses, and types neither
`((sk sA) sB)` nor `(sapply (sk sA) sB)`, which HE types; the contract makes HE's judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.Curried

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.HE.TypeGrounding.Tuples
  (ReferenceType ReferenceTypes TupleTerm staticType_tuple)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

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


/-! ## Faithful declarations -/

/-- Every declaration the expression uses has a faithful type. -/
def DeclarationsFaithful (space : Space) (expression : Atom) : Prop :=
  ∀ sub, Subatom sub expression → ∀ type, declaredType? space sub = some type → Faithful type

theorem DeclarationsFaithful.of_child {space : Space} {atom : Atom} {atoms : List Atom}
    (faithful : DeclarationsFaithful space (.expression atoms)) (member : atom ∈ atoms) :
    DeclarationsFaithful space atom :=
  fun sub occurs => faithful sub (.child member occurs)

theorem DeclarationsFaithful.self {space : Space} {atom type : Atom}
    (faithful : DeclarationsFaithful space atom) (declared : declaredType? space atom = some type) :
    Faithful type :=
  faithful atom .refl type declared

/-- A variable-free declaration has itself as its only instance. -/
theorem instance_iff_of_ground {space : Space} {constant scheme instanceType : Atom}
    (declared : declaredType? space constant = some scheme)
    (ground : TypeSubst.typeVars scheme = []) :
    Instance space constant instanceType ↔ ContractType scheme ∧ instanceType = scheme := by
  constructor
  · rintro ⟨contract, scheme', declared', valuation, _, instanceEq⟩
    rw [declared] at declared'
    cases declared'
    rw [applyTypeValuation_of_ground valuation ground] at instanceEq
    subst instanceEq
    exact ⟨contract, rfl⟩
  · rintro ⟨contract, instanceEq⟩
    subst instanceEq
    exact ⟨contract, _, declared, fun name => .var name, fun name => .var name,
      Theory.applyTypeValuation_var_identity _⟩

/-- A static type is not the arrow symbol. -/
theorem staticType_ne_arrow_symbol {type : Atom} (static : StaticType type) :
    type ≠ .symbol "->" := by
  rintro rfl
  exact static.not_topReserved ⟨"->", by simp [reservedTypeNames], rfl⟩

/-- A tuple of a static head has a non-arrow product type. -/
theorem tuple_not_arrowShaped {headType : Atom} {argumentTypes : List Atom}
    (headStatic : StaticType headType) :
    ¬ArrowShaped (.expression (headType :: argumentTypes)) := by
  rintro ⟨components, equal⟩
  simp only [Atom.expression.injEq, List.cons.injEq] at equal
  exact staticType_ne_arrow_symbol headStatic equal.1

/-! ## Reference types of faithful declarations are faithful -/

mutual

theorem ReferenceType.faithful {space : Space} :
    ∀ {expression type : Atom}, ReferenceType space expression type →
      DeclarationsFaithful space expression → Faithful type
  | _, _, .constant declared _, faithful => faithful.self declared
  | _, _, @ReferenceType.application _ name _ _ type _ _ declared _ function _, faithful =>
      ((faithful (.symbol name) (Subatom.of_mem (by simp)) type declared).of_functionType
        function).2.2.2.2.2
  | _, _, .tuple head headNotArrow arguments, faithful => by
      refine .product (tuple_not_arrowShaped (ReferenceType.static head)) ?_
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · exact ReferenceType.faithful head (faithful.of_child (by simp))
      · exact ReferenceTypes.faithful arguments
          (fun argument argumentMember => faithful.of_child (List.mem_cons_of_mem _ argumentMember))
          element member

theorem ReferenceTypes.faithful {space : Space} :
    ∀ {arguments types : List Atom}, ReferenceTypes space arguments types →
      (∀ argument ∈ arguments, DeclarationsFaithful space argument) →
      ∀ type ∈ types, Faithful type
  | _, _, .nil, _ => by simp
  | _, _, .cons head tail, faithful => by
      intro type member
      rcases List.mem_cons.mp member with rfl | member
      · exact ReferenceType.faithful head (faithful _ (by simp))
      · exact ReferenceTypes.faithful tail
          (fun argument argumentMember => faithful argument (List.mem_cons_of_mem _ argumentMember))
          type member

end

/-! ## Lists of reading-injective types -/

/-- Pointwise reading of two lists of types that the reading separates. -/
theorem map_toTy_injective {property : Atom → Prop}
    (injective : ∀ {left right : Atom}, property left → property right →
      toTy left = toTy right → left = right) :
    ∀ {left right : List Atom}, (∀ type ∈ left, property type) →
      (∀ type ∈ right, property type) → left.map toTy = right.map toTy → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by simp at equal
  | _ :: _, [], _, _, equal => by simp at equal
  | first :: rest, rightFirst :: rightRest, leftAll, rightAll, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      rw [injective (leftAll first (by simp)) (rightAll rightFirst (by simp)) equal.1,
        map_toTy_injective injective
          (fun type member => leftAll type (List.mem_cons_of_mem _ member))
          (fun type member => rightAll type (List.mem_cons_of_mem _ member)) equal.2]

/-! ## From the reference typing to the contract -/

mutual

/-- Every reference typing over faithful declarations is a contract typing. -/
theorem annotated_of_reference {space : Space} :
    ∀ {expression type : Atom}, ReferenceType space expression type →
      DeclarationsFaithful space expression →
      ∃ term, Annotates expression term ∧
        ApplicativeTyped (nameType space) term (toTy type)
  | _, _, @ReferenceType.constant _ atom type declared static, faithful => by
      have isInstance : Instance space atom type :=
        (instance_iff_of_ground declared static.typeVars_nil).mpr
          ⟨⟨faithful.self declared, static.not_topReserved⟩, rfl⟩
      rcases Tuples.declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · exact ⟨_, .symbol name type, applicativeTyped_declared_iff.mpr ⟨isInstance, rfl⟩⟩
      · exact ⟨_, .grounded value type, applicativeTyped_declared_iff.mpr ⟨isInstance, rfl⟩⟩
  | _, _, @ReferenceType.application _ name arguments argumentTypes type returnType _
      declared static function argumentsTyped, faithful => by
      obtain ⟨terms, annotated, typed⟩ := annotatedList_of_references argumentsTyped
        (fun argument member => faithful.of_child (List.mem_cons_of_mem _ member))
      have isInstance : Instance space (.symbol name) type :=
        (instance_iff_of_ground declared static.typeVars_nil).mpr
          ⟨⟨faithful (.symbol name) (Subatom.of_mem (by simp)) type declared,
            static.not_topReserved⟩, rfl⟩
      obtain ⟨nonempty, _, _, _⟩ := static.of_functionType function
      refine ⟨_, .application (instanceType := type) annotated, ?_⟩
      rw [applicativeTyped_foldl_iff]
      refine ⟨argumentTypes.map toTy, ?_, List.forall₂_map_right_iff.mpr typed⟩
      rw [← spineTy_eq_foldr, ← toTy_of_functionType function nonempty]
      exact applicativeTyped_declared_iff.mpr ⟨isInstance, rfl⟩
  | _, _, @ReferenceType.tuple _ head arguments headType argumentTypes headTyped headNotArrow
      argumentsTyped, faithful => by
      have headFaithful : DeclarationsFaithful space head := faithful.of_child (by simp)
      have argumentsFaithful : ∀ argument ∈ arguments, DeclarationsFaithful space argument :=
        fun argument member => faithful.of_child (List.mem_cons_of_mem _ member)
      obtain ⟨headTerm, headAnnotated, headTyping⟩ := annotated_of_reference headTyped headFaithful
      obtain ⟨terms, annotated, typed⟩ := annotatedList_of_references argumentsTyped argumentsFaithful
      refine ⟨_, .tuple headNotArrow (ReferenceType.faithful headTyped headFaithful)
        (ReferenceTypes.faithful argumentsTyped argumentsFaithful) headAnnotated annotated
        (ReferenceTypes.length_eq argumentsTyped).symm, ?_⟩
      rw [toTy_eq_productTy (tuple_not_arrowShaped (ReferenceType.static headTyped)),
        applicativeTyped_tupleTerm_iff (by simp [typed.length_eq])]
      exact ⟨rfl, .cons headTyping typed⟩

/-- Pointwise companion of `annotated_of_reference`. -/
theorem annotatedList_of_references {space : Space} :
    ∀ {arguments types : List Atom}, ReferenceTypes space arguments types →
      (∀ argument ∈ arguments, DeclarationsFaithful space argument) →
      ∃ terms, AnnotatesList arguments terms ∧
        List.Forall₂ (fun term type => ApplicativeTyped (nameType space) term (toTy type))
          terms types
  | _, _, .nil, _ => ⟨[], .nil, .nil⟩
  | _, _, .cons head tail, faithful => by
      obtain ⟨headTerm, headAnnotated, headTyping⟩ :=
        annotated_of_reference head (faithful _ (by simp))
      obtain ⟨terms, annotated, typed⟩ := annotatedList_of_references tail
        (fun argument member => faithful argument (List.mem_cons_of_mem _ member))
      exact ⟨_, .cons headAnnotated annotated, .cons headTyping typed⟩

end

/-! ## From the contract to the reference typing -/

/-- The arguments of an annotated list, typed by the contract, have reference
types that read as their HOL types. -/
private theorem references_of_annotatedList {space : Space} :
    ∀ {arguments : List Atom},
      (∀ argument ∈ arguments, ∀ {term : ContractTerm} {holType : Ty Atom},
        Annotates argument term → ApplicativeTyped (nameType space) term holType →
          ∃ type, StaticType type ∧ Faithful type ∧ holType = toTy type ∧
            ReferenceType space argument type) →
      ∀ {terms : List ContractTerm} {holTypes : List (Ty Atom)},
        AnnotatesList arguments terms →
        List.Forall₂ (ApplicativeTyped (nameType space)) terms holTypes →
          ∃ types, ReferenceTypes space arguments types ∧ holTypes = types.map toTy ∧
            (∀ type ∈ types, StaticType type) ∧ (∀ type ∈ types, Faithful type)
  | [], _, _, _, .nil, .nil => ⟨[], .nil, rfl, by simp, by simp⟩
  | argument :: arguments, argumentIH, _, _, .cons headAnnotated tailAnnotated,
      .cons headTyped tailTyped => by
      obtain ⟨type, static, faithful, rfl, referenceTyped⟩ :=
        argumentIH argument (by simp) headAnnotated headTyped
      obtain ⟨types, references, rfl, allStatic, allFaithful⟩ :=
        references_of_annotatedList
          (fun other member => argumentIH other (List.mem_cons_of_mem _ member))
          tailAnnotated tailTyped
      refine ⟨type :: types, .cons referenceTyped references, rfl, ?_, ?_⟩
      · intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact static
        · exact allStatic other member
      · intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact faithful
        · exact allFaithful other member

/-- A declared constant read at an instance has its declared static type. -/
private theorem declared_typing {space : Space} {atom type instanceType : Atom}
    {holType : Ty Atom} (declared : declaredType? space atom = some type)
    (static : StaticType type)
    (typed : ApplicativeTyped (nameType space) (.constant (.declared atom instanceType)) holType) :
    instanceType = type ∧ ContractType type ∧ holType = toTy type := by
  obtain ⟨isInstance, rfl⟩ := applicativeTyped_declared_iff.mp typed
  obtain ⟨contract, rfl⟩ := (instance_iff_of_ground declared static.typeVars_nil).mp isInstance
  exact ⟨rfl, contract, rfl⟩

/-- Every contract typing of a tuple-fragment expression is the reading of
a static, faithful reference type. -/
theorem reference_of_annotated {space : Space} {expression : Atom}
    (fragment : TupleTerm space expression) :
    ∀ {term : ContractTerm} {holType : Ty Atom},
      Annotates expression term → ApplicativeTyped (nameType space) term holType →
        ∃ type, StaticType type ∧ Faithful type ∧ holType = toTy type ∧
          ReferenceType space expression type := by
  induction fragment with
  | @constant atom type declared static =>
      intro term holType annotates typed
      rcases Tuples.declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · cases annotates
        obtain ⟨_, contract, rfl⟩ := declared_typing declared static typed
        exact ⟨type, static, contract.1, rfl, .constant declared static⟩
      · cases annotates
        obtain ⟨_, contract, rfl⟩ := declared_typing declared static typed
        exact ⟨type, static, contract.1, rfl, .constant declared static⟩
  | @application name arguments argumentTypes type returnType notState _ declared static
      function lengths _ argumentIH =>
      intro term holType annotates typed
      obtain ⟨nonempty, argumentStatic, returnNotArrow, returnStatic⟩ :=
        static.of_functionType function
      cases annotates with
      | application annotated =>
          rw [applicativeTyped_foldl_iff] at typed
          obtain ⟨holTypes, headTyped, argumentsTyped⟩ := typed
          obtain ⟨_, contract, headEq⟩ := declared_typing declared static headTyped
          rw [toTy_of_functionType function nonempty, spineTy_eq_foldr] at headEq
          obtain ⟨types, references, rfl, allStatic, _⟩ :=
            references_of_annotatedList argumentIH annotated argumentsTyped
          have holLength : (types.map toTy).length = (argumentTypes.map toTy).length := by
            rw [List.length_map, List.length_map, ← Tuples.ReferenceTypes.length_eq references,
              lengths]
          obtain ⟨holEq, rfl⟩ := foldr_arr_injective holLength headEq
          have typesEq : types = argumentTypes :=
            map_toTy_injective (property := StaticType)
              (fun leftStatic rightStatic equal => toTy_injective leftStatic rightStatic equal)
              allStatic argumentStatic holEq
          subst typesEq
          exact ⟨returnType, returnStatic,
            (contract.1.of_functionType function).2.2.2.2.2, rfl,
            .application notState declared static function references⟩
      | @tuple _ headType _ tupleTypes headTerm terms headNotArrow _ _ headAnnotated
          annotated argumentLengths =>
          have tupleLengths : (headType :: tupleTypes).length = (headTerm :: terms).length := by
            simp only [List.length_cons, argumentLengths]
            exact congrArg (· + 1) (annotatesList_iff_forall₂.mp annotated).length_eq
          cases headAnnotated
          rw [applicativeTyped_tupleTerm_iff tupleLengths] at typed
          obtain ⟨_, headTyped⟩ := typed
          cases headTyped with
          | cons headTyping _ =>
              obtain ⟨_, _, headEq⟩ := declared_typing declared static headTyping
              rw [toTy_of_functionType function nonempty, toTy_of_not_arrowShaped headNotArrow]
                at headEq
              obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
              simp at headEq
  | @tupleConstant head arguments type _ declared static notArrow nonempty _ argumentIH =>
      intro term holType annotates typed
      cases annotates with
      | application annotated =>
          rw [applicativeTyped_foldl_iff] at typed
          obtain ⟨holTypes, headTyped, argumentsTyped⟩ := typed
          obtain ⟨_, _, headEq⟩ := declared_typing declared static headTyped
          rw [toTy_of_not_arrowShaped notArrow] at headEq
          have holNonempty : holTypes ≠ [] := by
            intro empty
            subst empty
            cases argumentsTyped
            cases annotated
            exact nonempty rfl
          obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil holNonempty
          simp at headEq
      | @tuple _ headType _ argumentTypes headTerm terms headNotArrow headFaithful
          argumentFaithful headAnnotated annotated argumentLengths =>
          have lengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
            simp only [List.length_cons, argumentLengths]
            exact congrArg (· + 1) (annotatesList_iff_forall₂.mp annotated).length_eq
          rw [applicativeTyped_tupleTerm_iff lengths] at typed
          obtain ⟨rfl, componentsTyped⟩ := typed
          cases componentsTyped with
          | cons headTyping argumentsTyping =>
              rcases Tuples.declaredType?_symbol_or_grounded declared with
                ⟨name, rfl⟩ | ⟨value, rfl⟩ <;>
              · cases headAnnotated
                obtain ⟨_, contract, headEq⟩ := declared_typing declared static headTyping
                rw [toTy_of_not_arrowShaped headNotArrow, toTy_of_not_arrowShaped notArrow]
                  at headEq
                cases headEq
                obtain ⟨types, references, holEq, allStatic, allFaithful⟩ :=
                  references_of_annotatedList argumentIH annotated
                    (List.forall₂_map_right_iff.mpr argumentsTyping)
                have typesEq : argumentTypes = types :=
                  map_toTy_injective (property := Faithful)
                    (fun leftFaithful rightFaithful equal =>
                      toTy_injective_of_faithful leftFaithful rightFaithful equal)
                    argumentFaithful allFaithful holEq
                subst typesEq
                refine ⟨_, staticType_tuple static notArrow allStatic,
                  .product (tuple_not_arrowShaped static) ?_,
                  (toTy_eq_productTy (tuple_not_arrowShaped static)).symm,
                  .tuple (.constant declared static) notArrow references⟩
                intro element member
                rcases List.mem_cons.mp member with rfl | member
                · exact contract.1
                · exact allFaithful element member
  | @tupleExpression headAtoms arguments _ headFragment nonempty _ headIH argumentIH =>
      intro term holType annotates typed
      cases annotates with
      | @tuple _ headType _ argumentTypes headTerm terms headNotArrow headFaithful
          argumentFaithful headAnnotated annotated argumentLengths =>
          have lengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
            simp only [List.length_cons, argumentLengths]
            exact congrArg (· + 1) (annotatesList_iff_forall₂.mp annotated).length_eq
          rw [applicativeTyped_tupleTerm_iff lengths] at typed
          obtain ⟨rfl, componentsTyped⟩ := typed
          cases componentsTyped with
          | cons headTyping argumentsTyping =>
              obtain ⟨found, foundStatic, foundFaithful, headEq, headTyped⟩ :=
                headIH headAnnotated headTyping
              have headTypeEq := toTy_injective_of_faithful headFaithful foundFaithful headEq
              subst headTypeEq
              obtain ⟨types, references, holEq, allStatic, allFaithful⟩ :=
                references_of_annotatedList argumentIH annotated
                  (List.forall₂_map_right_iff.mpr argumentsTyping)
              have typesEq : argumentTypes = types :=
                map_toTy_injective (property := Faithful)
                  (fun leftFaithful rightFaithful equal =>
                    toTy_injective_of_faithful leftFaithful rightFaithful equal)
                  argumentFaithful allFaithful holEq
              subst typesEq
              refine ⟨_, staticType_tuple foundStatic headNotArrow allStatic,
                .product (tuple_not_arrowShaped foundStatic) ?_,
                (toTy_eq_productTy (tuple_not_arrowShaped foundStatic)).symm,
                .tuple headTyped headNotArrow references⟩
              intro element member
              rcases List.mem_cons.mp member with rfl | member
              · exact foundFaithful
              · exact allFaithful element member

/-! ## Agreement -/

/-- **HE's tuples are contract products.**  On the tuple fragment over
faithful declarations, the reference runtime assigns a static type exactly
when the contract types the expression at it. -/
theorem tuple_iff_reference {space : Space} {expression type : Atom}
    (fragment : TupleTerm space expression) (faithful : DeclarationsFaithful space expression)
    (static : StaticType type) :
    Typed space expression type ↔ ReferenceType space expression type := by
  rw [typed_iff]
  constructor
  · rintro ⟨term, annotates, typed⟩
    obtain ⟨found, foundStatic, _, holEq, referenceTyped⟩ :=
      reference_of_annotated fragment annotates typed
    rw [toTy_injective static foundStatic holEq]
    exact referenceTyped
  · intro referenceTyped
    exact annotated_of_reference referenceTyped faithful

/-- **Static arrows.**  On tuple-free saturated expressions over faithful
static declarations, contract typing at a static type is HE's specified exact
relation with no `%Undefined%` fallback. -/
theorem static_iff_exact {space : Space} {expression type : Atom}
    (saturated : SaturatedTerm space expression) (faithful : DeclarationsFaithful space expression)
    (static : StaticType type) :
    Typed space expression type ↔
      ExactTypes space expression [type] ∧ NoUndefinedFallback space expression :=
  (tuple_iff_reference (saturatedTerm_tupleTerm saturated) faithful static).trans
    (Tuples.reference_iff_exact_of_saturated saturated static)

/-! ## First-order schemes -/

/-- A type without reserved names at any depth reads faithfully. -/
theorem reservedFree_faithful {atom : Atom} (free : Schematic.ReservedFree atom) :
    Faithful atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, Schematic.ReservedFree atom) → ∀ atom ∈ atoms, Faithful atom) with
  | symbol name =>
      have notReserved := Schematic.reservedFree_symbol_iff.mp free
      exact .symbol (fun equal => notReserved (by simp [equal, reservedTypeNames]))
        (fun equal => notReserved (by simp [equal, reservedTypeNames]))
  | var name => exact .var name
  | grounded value => exact .grounded value
  | expression atoms ih =>
      exact .product free.not_arrowShaped
        (ih (fun atom member => free.of_child member))
  | nil => rename_i member; cases member
  | cons head tail headIH tailIH =>
      rename_i all atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH (all _ (by simp))
      · exact tailIH (fun other otherMember => all other (List.mem_cons_of_mem _ otherMember))
          atom member

theorem groundFirstOrder_contractType {atom : Atom} (ground : Schematic.GroundFirstOrder atom) :
    ContractType atom :=
  ⟨reservedFree_faithful ground.1, ground.1.not_topReserved⟩

/-- A valuation applies to the components of an arrow. -/
theorem functionTypeRel_applyTypeValuation (valuation : String → Atom)
    {scheme returnType : Atom} {argumentTypes : List Atom}
    (function : FunctionTypeRel scheme argumentTypes returnType) :
    FunctionTypeRel (applyTypeValuation valuation scheme)
      (argumentTypes.map (applyTypeValuation valuation))
      (applyTypeValuation valuation returnType) := by
  rw [FunctionTypeRel] at function ⊢
  subst function
  simp [applyTypeValuation, List.map_append]

/-- A first-order instance of an operator scheme is a contract type. -/
theorem operatorScheme_instance_contractType {scheme returnType : Atom}
    {argumentTypes : List Atom} (operator : Schematic.OperatorScheme scheme argumentTypes returnType)
    {valuation : String → Atom} (firstOrder : Schematic.FirstOrderValuation valuation) :
    ContractType (applyTypeValuation valuation scheme) := by
  have function := functionTypeRel_applyTypeValuation valuation operator.function
  have argumentsGround : ∀ argumentType ∈ argumentTypes.map (applyTypeValuation valuation),
      Schematic.GroundFirstOrder argumentType := by
    intro argumentType member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact firstOrder.ground (operator.arguments source sourceMember)
  have returnGround := firstOrder.ground operator.result
  refine ⟨.arrow function (by simpa using operator.nonempty)
    (fun argumentType member => (groundFirstOrder_contractType (argumentsGround _ member)).1)
    (fun argumentType member => (argumentsGround _ member).1.not_topReserved)
    returnGround.1.not_arrowShaped returnGround.1.not_topReserved
    (groundFirstOrder_contractType returnGround).1, ?_⟩
  rw [FunctionTypeRel] at function
  rw [function]
  rintro ⟨_, _, equal⟩
  cases equal

/-- The HOL types of the first-order instance signature, read off names. -/
theorem signatureType_instanceSignature {space : Space} {name : Atom × Atom}
    {type : Ty Atom} :
    signatureType (Schematic.instanceSignature space) name = some type ↔
      Schematic.InstanceOf space name.1 name.2 ∧ type = toTy name.2 := by
  rw [signatureType_eq_some_iff, ← elaborates_constant_iff, Schematic.elaborates_instance_iff]

/-- A contract term of a first-order expression at an instance is the
annotation that `Schematic.Annotates` describes, with the constant names
renamed. -/
private def instanceName : Atom × Atom → Name := fun name => .declared name.1 name.2

/-- Every first-order annotation is a contract annotation with the same
HOL typing. -/
private theorem contract_of_schematic {space : Space} {expression : Atom}
    (fragment : Schematic.SchematicTerm space expression) :
    ∀ {term : Schematic.InstanceTerm} {holType : Ty Atom},
      Schematic.Annotates expression term →
      ApplicativeTyped (signatureType (Schematic.instanceSignature space)) term holType →
        ∃ contractTerm, Annotates expression contractTerm ∧
          ApplicativeTyped (nameType space) contractTerm holType := by
  induction fragment with
  | @constant atom scheme declared free =>
      intro term holType annotates typed
      have constantCase : ∀ {instanceType : Atom},
          ApplicativeTyped (signatureType (Schematic.instanceSignature space))
            (.constant (atom, instanceType)) holType →
          ApplicativeTyped (nameType space) (.constant (.declared atom instanceType)) holType := by
        intro instanceType typedConstant
        cases typedConstant with
        | constant lookup =>
            obtain ⟨instanceOf, rfl⟩ := signatureType_instanceSignature.mp lookup
            obtain ⟨valuation, firstOrder, instanceEq⟩ :=
              (Schematic.instanceOf_iff declared).mp instanceOf
            change applyTypeValuation valuation scheme = instanceType at instanceEq
            refine applicativeTyped_declared_iff.mpr ⟨⟨?_, scheme, declared, valuation,
              fun name => (groundFirstOrder_contractType (firstOrder name)).1, instanceEq⟩, rfl⟩
            rw [← instanceEq]
            exact groundFirstOrder_contractType (firstOrder.ground free)
      rcases Schematic.SchematicTerm.constant_shape declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · cases annotates
        exact ⟨_, .symbol name _, constantCase typed⟩
      · cases annotates
        exact ⟨_, .grounded value _, constantCase typed⟩
  | @application name arguments argumentTypes scheme returnType _ _ declared operator
      lengths _ argumentIH =>
      intro term holType annotates typed
      cases annotates with
      | @application _ instanceType _ terms annotated =>
          rw [applicativeTyped_foldl_iff] at typed
          obtain ⟨holTypes, headTyped, argumentsTyped⟩ := typed
          have converted : ∀ {arguments : List Atom} {terms : List Schematic.InstanceTerm}
              {holTypes : List (Ty Atom)},
              (∀ argument ∈ arguments, ∀ {term : Schematic.InstanceTerm} {holType : Ty Atom},
                Schematic.Annotates argument term →
                ApplicativeTyped (signatureType (Schematic.instanceSignature space)) term
                  holType →
                  ∃ contractTerm, Annotates argument contractTerm ∧
                    ApplicativeTyped (nameType space) contractTerm holType) →
              List.Forall₂ Schematic.Annotates arguments terms →
              List.Forall₂ (ApplicativeTyped
                (signatureType (Schematic.instanceSignature space))) terms holTypes →
              ∃ contractTerms, AnnotatesList arguments contractTerms ∧
                List.Forall₂ (ApplicativeTyped (nameType space)) contractTerms holTypes := by
            intro arguments
            induction arguments with
            | nil =>
                intro terms holTypes _ annotatedAll typedAll
                cases annotatedAll
                cases typedAll
                exact ⟨[], .nil, .nil⟩
            | cons argument rest restIH =>
                intro terms holTypes allIH annotatedAll typedAll
                cases annotatedAll with
                | cons headAnnotated tailAnnotated =>
                    cases typedAll with
                    | cons headTyped tailTyped =>
                        obtain ⟨contractTerm, contractAnnotated, contractTyped⟩ :=
                          allIH argument (by simp) headAnnotated headTyped
                        obtain ⟨contractTerms, restAnnotated, restTyped⟩ := restIH
                          (fun other member => allIH other (List.mem_cons_of_mem _ member))
                          tailAnnotated tailTyped
                        exact ⟨_, .cons contractAnnotated restAnnotated,
                          .cons contractTyped restTyped⟩
          obtain ⟨contractTerms, contractAnnotated, contractTyped⟩ :=
            converted argumentIH annotated argumentsTyped
          refine ⟨_, .application (instanceType := instanceType) contractAnnotated, ?_⟩
          rw [applicativeTyped_foldl_iff]
          refine ⟨holTypes, ?_, contractTyped⟩
          cases headTyped with
          | constant lookup =>
              obtain ⟨instanceOf, typeEq⟩ := signatureType_instanceSignature.mp lookup
              obtain ⟨valuation, firstOrder, instanceEq⟩ :=
                (Schematic.instanceOf_iff declared).mp instanceOf
              change applyTypeValuation valuation scheme = instanceType at instanceEq
              refine applicativeTyped_declared_iff.mpr ⟨⟨?_, scheme, declared, valuation,
                fun name => (groundFirstOrder_contractType (firstOrder name)).1, instanceEq⟩,
                typeEq⟩
              rw [← instanceEq]
              exact operatorScheme_instance_contractType operator firstOrder

/-- The terms of first-order annotations are applicative. -/
theorem schematicAnnotates_applicative {space : Space} {expression : Atom}
    (fragment : Schematic.SchematicTerm space expression) :
    ∀ {term : Schematic.InstanceTerm}, Schematic.Annotates expression term → Applicative term := by
  induction fragment with
  | constant declared _ =>
      intro term annotates
      rcases Schematic.SchematicTerm.constant_shape declared with ⟨name, rfl⟩ | ⟨value, rfl⟩ <;>
      · cases annotates
        exact .constant _
  | @application name arguments _ _ _ _ _ _ _ _ _ argumentIH =>
      intro term annotates
      cases annotates with
      | application annotated =>
          apply Applicative.foldl (.constant _)
          intro instanceTerm member
          obtain ⟨argument, argumentMember, argumentAnnotated⟩ :=
            forall₂_right_mem annotated instanceTerm member
          exact argumentIH argument argumentMember argumentAnnotated

/-- Arguments of a contract typing of a first-order application, read at the
instances of the parameter types, have first-order annotations at the
projected instances. -/
private theorem schematicArguments {space : Space} {valuation : String → Atom} :
    ∀ {arguments : List Atom} {argumentTypes : List Atom} {terms : List ContractTerm},
      (∀ argument ∈ arguments, ∀ {term : ContractTerm} {holType : Ty Atom},
        Annotates argument term → ApplicativeTyped (nameType space) term holType →
          ∃ type, Faithful type ∧ holType = toTy type ∧
            ∃ instanceTerm, Schematic.Annotates argument instanceTerm ∧
              ApplicativeTyped (signatureType (Schematic.instanceSignature space))
                instanceTerm (toTy (Schematic.project type))) →
      (∀ argumentType ∈ argumentTypes, Schematic.ReservedFree argumentType) →
      (∀ argumentType ∈ argumentTypes, Faithful (applyTypeValuation valuation argumentType)) →
      AnnotatesList arguments terms →
      List.Forall₂ (fun term argumentType => ApplicativeTyped (nameType space) term
        (toTy (applyTypeValuation valuation argumentType))) terms argumentTypes →
      ∃ instanceTerms, List.Forall₂ Schematic.Annotates arguments instanceTerms ∧
        List.Forall₂ (fun instanceTerm argumentType =>
          ApplicativeTyped (signatureType (Schematic.instanceSignature space)) instanceTerm
            (toTy (applyTypeValuation (fun name => Schematic.project (valuation name))
              argumentType))) instanceTerms argumentTypes
  | [], _, _, _, _, _, .nil, .nil => ⟨[], .nil, .nil⟩
  | _ :: _, [], _, _, _, _, .cons _ _, typed => by cases typed
  | argument :: arguments, argumentType :: argumentTypes, _ :: _, argumentIH, free,
      faithful, .cons headAnnotated tailAnnotated, .cons headTyped tailTyped => by
      obtain ⟨type, typeFaithful, holEq, instanceTerm, instanceAnnotated, instanceTyped⟩ :=
        argumentIH argument (by simp) headAnnotated headTyped
      have typeEq := toTy_injective_of_faithful (faithful argumentType (by simp)) typeFaithful holEq
      subst typeEq
      rw [Schematic.project_applyTypeValuation valuation (free argumentType (by simp))]
        at instanceTyped
      obtain ⟨instanceTerms, restAnnotated, restTyped⟩ := schematicArguments
        (fun other member => argumentIH other (List.mem_cons_of_mem _ member))
        (fun other member => free other (List.mem_cons_of_mem _ member))
        (fun other member => faithful other (List.mem_cons_of_mem _ member))
        tailAnnotated tailTyped
      exact ⟨_, .cons instanceAnnotated restAnnotated, .cons instanceTyped restTyped⟩

/-- **The first-order shadow of a contract typing.**  Every contract typing
of a first-order expression is the reading of a faithful type `U`, and the
expression has a first-order annotation typed at the reading of the
projection of `U`. -/
private theorem schematic_of_contract {space : Space} {expression : Atom}
    (fragment : Schematic.SchematicTerm space expression) :
    ∀ {term : ContractTerm} {holType : Ty Atom},
      Annotates expression term → ApplicativeTyped (nameType space) term holType →
        ∃ type, Faithful type ∧ holType = toTy type ∧
          ∃ instanceTerm, Schematic.Annotates expression instanceTerm ∧
            ApplicativeTyped (signatureType (Schematic.instanceSignature space)) instanceTerm
              (toTy (Schematic.project type)) := by
  induction fragment with
  | @constant atom scheme declared free =>
      intro term holType annotates typed
      have constantCase : ∀ {instanceType : Atom},
          ApplicativeTyped (nameType space) (.constant (.declared atom instanceType)) holType →
          ∃ type, Faithful type ∧ holType = toTy type ∧
            ApplicativeTyped (signatureType (Schematic.instanceSignature space))
              (.constant (atom, Schematic.project instanceType)) (toTy (Schematic.project type)) ∧
            type = instanceType := by
        intro instanceType typedConstant
        obtain ⟨⟨contract, scheme', declared', valuation, _, instanceEq⟩, rfl⟩ :=
          applicativeTyped_declared_iff.mp typedConstant
        rw [declared] at declared'
        cases declared'
        refine ⟨instanceType, contract.1, rfl, .constant ?_, rfl⟩
        apply signatureType_instanceSignature.mpr
        refine ⟨⟨scheme, declared, _, Schematic.projected_firstOrder valuation, ?_⟩, rfl⟩
        rw [← instanceEq, Schematic.project_applyTypeValuation valuation free]
      rcases Schematic.SchematicTerm.constant_shape declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · cases annotates
        obtain ⟨type, faithful, holEq, instanceTyped, rfl⟩ := constantCase typed
        exact ⟨type, faithful, holEq, _, .symbol name _, instanceTyped⟩
      · cases annotates
        obtain ⟨type, faithful, holEq, instanceTyped, rfl⟩ := constantCase typed
        exact ⟨type, faithful, holEq, _, .grounded value _, instanceTyped⟩
  | @application name arguments argumentTypes scheme returnType _ _ declared operator
      lengths _ argumentIH =>
      intro term holType annotates typed
      cases annotates with
      | @application _ instanceType _ terms annotated =>
          rw [applicativeTyped_foldl_iff] at typed
          obtain ⟨holTypes, headTyped, argumentsTyped⟩ := typed
          obtain ⟨⟨contract, scheme', declared', valuation, _, instanceEq⟩, headEq⟩ :=
            applicativeTyped_declared_iff.mp headTyped
          rw [declared] at declared'
          cases declared'
          subst instanceEq
          have function := functionTypeRel_applyTypeValuation valuation operator.function
          obtain ⟨nonempty, argumentsFaithful, _, _, _, returnFaithful⟩ :=
            contract.1.of_functionType function
          rw [toTy_of_functionType function nonempty, spineTy_eq_foldr] at headEq
          have holLength : holTypes.length =
              ((argumentTypes.map (applyTypeValuation valuation)).map toTy).length := by
            rw [List.length_map, List.length_map, ← lengths, ← argumentsTyped.length_eq]
            exact ((annotatesList_iff_forall₂.mp annotated).length_eq).symm
          obtain ⟨rfl, rfl⟩ := foldr_arr_injective holLength headEq
          have argumentsTyped' := List.forall₂_map_right_iff.mp
            (List.forall₂_map_right_iff.mp argumentsTyped)
          obtain ⟨instanceTerms, instanceAnnotated, instanceTyped⟩ :=
            schematicArguments (valuation := valuation) argumentIH operator.arguments
              (fun argumentType member => argumentsFaithful _ (List.mem_map_of_mem member))
              annotated argumentsTyped'
          have projected := Schematic.projected_firstOrder valuation
          obtain ⟨instanceFunction, _⟩ := operator.instantiate projected
          refine ⟨applyTypeValuation valuation returnType, returnFaithful, rfl, _,
            .application (instanceType := applyTypeValuation
              (fun name => Schematic.project (valuation name)) scheme) instanceAnnotated, ?_⟩
          rw [applicativeTyped_foldl_iff]
          refine ⟨(argumentTypes.map (applyTypeValuation
              (fun name => Schematic.project (valuation name)))).map toTy, ?_,
            List.forall₂_map_right_iff.mpr (List.forall₂_map_right_iff.mpr instanceTyped)⟩
          rw [Schematic.project_applyTypeValuation valuation operator.result,
            ← spineTy_eq_foldr,
            ← toTy_of_functionType instanceFunction (by simpa using operator.nonempty)]
          exact .constant (signatureType_instanceSignature.mpr
            ⟨⟨scheme, declared, _, projected, rfl⟩, rfl⟩)
      | @tuple _ headType _ tupleTypes headTerm terms headNotArrow _ _ headAnnotated
          annotated argumentLengths =>
          have tupleLengths : (headType :: tupleTypes).length = (headTerm :: terms).length := by
            simp only [List.length_cons, argumentLengths]
            exact congrArg (· + 1) (annotatesList_iff_forall₂.mp annotated).length_eq
          cases headAnnotated
          rw [applicativeTyped_tupleTerm_iff tupleLengths] at typed
          obtain ⟨_, componentsTyped⟩ := typed
          cases componentsTyped with
          | cons headTyping _ =>
              obtain ⟨⟨contract, scheme', declared', valuation, _, instanceEq⟩, headEq⟩ :=
                applicativeTyped_declared_iff.mp headTyping
              rw [declared] at declared'
              cases declared'
              subst instanceEq
              have function := functionTypeRel_applyTypeValuation valuation operator.function
              obtain ⟨nonempty, _⟩ := contract.1.of_functionType function
              rw [toTy_of_functionType function nonempty, toTy_of_not_arrowShaped headNotArrow]
                at headEq
              obtain ⟨first, rest, equal⟩ := List.exists_cons_of_ne_nil nonempty
              rw [equal] at headEq
              simp at headEq

/-- On first-order expressions, contract typing at a ground first-order type
is first-order HOL typing over instances. -/
theorem typed_iff_schematicHOLTyped {space : Space} {expression type : Atom}
    (fragment : Schematic.SchematicTerm space expression)
    (ground : Schematic.GroundFirstOrder type) :
    Typed space expression type ↔ Schematic.SchematicHOLTyped space expression type := by
  rw [typed_iff]
  constructor
  · rintro ⟨term, annotates, typed⟩
    obtain ⟨found, foundFaithful, holEq, instanceTerm, instanceAnnotated, instanceTyped⟩ :=
      schematic_of_contract fragment annotates typed
    have typeEq := toTy_injective_of_faithful (groundFirstOrder_contractType ground).1
      foundFaithful holEq
    subst typeEq
    rw [Schematic.project_of_groundFirstOrder ground] at instanceTyped
    exact ⟨instanceTerm, instanceAnnotated,
      (elaborates_iff_applicativeTyped
        (schematicAnnotates_applicative fragment instanceAnnotated)).mpr instanceTyped⟩
  · rintro ⟨instanceTerm, instanceAnnotated, elaborates⟩
    exact contract_of_schematic fragment instanceAnnotated
      ((elaborates_iff_applicativeTyped
        (schematicAnnotates_applicative fragment instanceAnnotated)).mp elaborates)

/-- **Type variables are the contract's polymorphism.**  On first-order
expressions over schematic declarations, the contract types the expression at
a ground first-order type exactly when no subatom falls back to
`%Undefined%` and the type is a first-order instance of HE's single exact
candidate.  Every contract typing at such a type is therefore an instance of
that principal scheme. -/
theorem schematic_iff_exact {space : Space} {expression type : Atom}
    (fragment : Schematic.SchematicTerm space expression)
    (ground : Schematic.GroundFirstOrder type) :
    Typed space expression type ↔
      NoUndefinedFallback space expression ∧
        ∃ principal, ExactTypes space expression [principal] ∧
          ∃ valuation, Schematic.FirstOrderValuation valuation ∧
            applyTypeValuation valuation principal = type :=
  (typed_iff_schematicHOLTyped fragment ground).trans
    (Schematic.schematic_hol_iff_exact fragment ground.static)

/-! ## Boundary examples -/

section Examples

private def truthZ : Atom := .expression [.symbol "Truth", .symbol "Z"]

private def pairType (first second : Atom) : Atom := .expression [first, second]

private theorem truthZ_fragment : TupleTerm SpecBoundary.truthZSpace truthZ := by
  refine .tupleConstant (by decide)
    (by decide : declaredType? SpecBoundary.truthZSpace (.symbol "Truth") = some (.symbol "Bool"))
    (SpecBoundary.staticSymbol "Bool" (by decide)) (by rintro ⟨_, equal⟩; cases equal)
    (by simp) ?_
  intro argument member
  simp only [List.mem_singleton] at member
  subst member
  exact .constant (by decide : declaredType? SpecBoundary.truthZSpace (.symbol "Z") =
    some (.symbol "Nat")) (SpecBoundary.staticSymbol "Nat" (by decide))

private theorem truthZ_faithful : DeclarationsFaithful SpecBoundary.truthZSpace truthZ := by
  intro sub occurs type declared
  rcases occurs.expression_cases with rfl | ⟨child, member, inner⟩
  · simp [declaredType?] at declared
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [inner.symbol_eq] at declared
      have found : declaredType? SpecBoundary.truthZSpace (.symbol "Truth") =
          some (.symbol "Bool") := by decide
      rw [found] at declared
      cases declared
      exact .symbol (by decide) (by decide)
    · rw [inner.symbol_eq] at declared
      have found : declaredType? SpecBoundary.truthZSpace (.symbol "Z") =
          some (.symbol "Nat") := by decide
      rw [found] at declared
      cases declared
      exact .symbol (by decide) (by decide)

private theorem pairType_static {first second : Atom} (firstStatic : StaticType first)
    (firstNotArrow : ¬ArrowShaped first) (secondStatic : StaticType second) :
    StaticType (pairType first second) :=
  staticType_tuple firstStatic firstNotArrow (by
    intro type member
    simp only [List.mem_singleton] at member
    subst member
    exact secondStatic)

private theorem symbol_not_arrowShaped (name : String) : ¬ArrowShaped (.symbol name) := by
  rintro ⟨_, equal⟩
  cases equal

private theorem symbol_not_topReserved {name : String} (notReserved : name ∉ reservedTypeNames) :
    ¬TopReserved (.symbol name) := by
  rintro ⟨reserved, member, equal⟩
  rw [Atom.symbol.injEq] at equal
  subst equal
  exact notReserved member

/-- **The tuple canary.**  With `(: Truth Bool)` and `(: Z Nat)`, the contract
types `(Truth Z)` at the product `(Bool Nat)` and not at the swapped
`(Nat Bool)`. -/
theorem truth_zero_contract :
    Typed SpecBoundary.truthZSpace truthZ (pairType (.symbol "Bool") (.symbol "Nat")) ∧
      ¬Typed SpecBoundary.truthZSpace truthZ (pairType (.symbol "Nat") (.symbol "Bool")) := by
  have boolStatic := SpecBoundary.staticSymbol "Bool" (by decide)
  have natStatic := SpecBoundary.staticSymbol "Nat" (by decide)
  refine ⟨(tuple_iff_reference truthZ_fragment truthZ_faithful
      (pairType_static boolStatic (symbol_not_arrowShaped _) natStatic)).mpr
      Tuples.truth_zero_is_a_pair.1, ?_⟩
  intro typed
  exact Tuples.truth_zero_not_swapped.1 ((tuple_iff_reference truthZ_fragment truthZ_faithful
    (pairType_static natStatic (symbol_not_arrowShaped _) boolStatic)).mp typed)

private def listOf (element : Atom) : Atom := .expression [.symbol "List", element]

private def arrowAB : Atom := .expression [.symbol "->", .symbol "A", .symbol "B"]

/-- **The first-order boundary of schemes.**  With `(: nil (List $t))`, the
contract types `nil` at `(List (-> A B))`, an instance that substitutes an
arrow.  That type is not first-order, so `schematic_iff_exact` does not
decide it, and a refusal there would not be earned. -/
theorem nil_arrow_instance :
    Typed Schematic.listSpace (.symbol "nil") (listOf arrowAB) ∧
      ¬Schematic.GroundFirstOrder (listOf arrowAB) := by
  have symbolFaithful : ∀ name : String, name ≠ "->" → name ≠ "%Undefined%" →
      Faithful (.symbol name) := fun _ notArrow notUndefined => .symbol notArrow notUndefined
  have arrowFaithful : Faithful arrowAB := by
    refine .arrow (argumentTypes := [.symbol "A"]) (returnType := .symbol "B") rfl (by simp)
      ?_ ?_ (symbol_not_arrowShaped _) (symbol_not_topReserved (by decide))
      (symbolFaithful "B" (by decide) (by decide))
    · intro type member
      simp only [List.mem_singleton] at member
      subst member
      exact symbolFaithful "A" (by decide) (by decide)
    · intro type member
      simp only [List.mem_singleton] at member
      subst member
      exact symbol_not_topReserved (by decide)
  have listFaithful : Faithful (listOf arrowAB) := by
    refine .product (by rintro ⟨_, equal⟩; simp at equal) ?_
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact symbolFaithful "List" (by decide) (by decide)
    · exact arrowFaithful
  constructor
  · rw [typed_iff]
    refine ⟨_, .symbol "nil" (listOf arrowAB), applicativeTyped_declared_iff.mpr ⟨⟨⟨listFaithful,
      by rintro ⟨_, _, equal⟩; cases equal⟩, listOf (.var "t"), by decide,
      fun _ => arrowAB, fun _ => arrowFaithful, by simp [applyTypeValuation, listOf]⟩, rfl⟩⟩
  · intro ground
    have arrowOccurs : Subatom (.symbol "->") (listOf arrowAB) :=
      .child (atom := arrowAB) (by simp) (.child (by simp) .refl)
    exact ground.1 _ arrowOccurs ⟨"->", by simp [reservedTypeNames], rfl⟩

end Examples

#print axioms tuple_iff_reference
#print axioms static_iff_exact
#print axioms schematic_iff_exact
#print axioms truth_zero_contract
#print axioms nil_arrow_instance


/-! ## The view agrees with the contract on saturated terms -/

/-- Faithful atoms are type atoms. -/
theorem Faithful.typeAtom {type : Atom} (faithful : Faithful type) : TypeAtom type := by
  induction faithful with
  | symbol notArrow notUndefined => exact .symbol notArrow notUndefined
  | var name => exact .var name
  | grounded value => exact .grounded value
  | @arrow type returnType argumentTypes function nonempty _ argumentsNotReserved _
      returnNotReserved _ argumentIH returnIH =>
      rw [FunctionTypeRel] at function
      subst function
      refine .arrow (by simp) ?_ ?_
      · intro component member
        rcases List.mem_append.mp member with member | member
        · exact argumentIH component member
        · simp only [List.mem_singleton] at member
          subst member
          exact returnIH
      · intro component member
        rcases List.mem_append.mp member with member | member
        · exact argumentsNotReserved component member
        · simp only [List.mem_singleton] at member
          subst member
          exact returnNotReserved
  | product notArrow _ elementIH => exact .compound notArrow elementIH

/-- Faithful declarations are declarations of type atoms. -/
theorem DeclarationsFaithful.formed {space : Space} {expression : Atom}
    (faithful : DeclarationsFaithful space expression) : DeclarationsFormed space expression :=
  fun sub occurs type declared => (faithful sub occurs type declared).typeAtom

/-- **On the tuple fragment the view is the contract.**  Over faithful declarations, the
curried view types an expression at a static type exactly when the contract does. -/
theorem typed_iff_curried_of_tuple {space : Space} {expression type : Atom}
    (fragment : TupleTerm space expression) (faithful : DeclarationsFaithful space expression)
    (static : StaticType type) :
    HOLContract.Typed space expression type ↔ Typed space expression type :=
  (HOLContract.tuple_iff_reference fragment faithful.formed).trans
    (tuple_iff_reference fragment faithful static).symm

/-- **On first-order schemes the view is the contract.**  At a ground first-order type, the
curried view types an expression over schematic declarations exactly when the contract does. -/
theorem typed_iff_curried_of_schematic {space : Space} {expression type : Atom}
    (fragment : Schematic.SchematicTerm space expression) (ground : Schematic.GroundFirstOrder type) :
    HOLContract.Typed space expression type ↔ Typed space expression type :=
  (HOLContract.schematic_iff_exact fragment ground).trans (schematic_iff_exact fragment ground).symm

#print axioms typed_iff_curried_of_tuple
#print axioms typed_iff_curried_of_schematic

end Mettapedia.Languages.MeTTa.HE.HOLContract.Curried

/-! ## The separating judgments -/

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement
namespace Separating

abbrev typeA : Atom := .symbol "SA"
abbrev typeB : Atom := .symbol "SB"
abbrev typeC : Atom := .symbol "SC"
abbrev sA : Atom := .symbol "sA"
abbrev sB : Atom := .symbol "sB"
abbrev sk : Atom := .symbol "sk"
abbrev sg : Atom := .symbol "sg"
abbrev sapply : Atom := .symbol "sapply"

/-- The scheme `(-> (-> $a $b) $a $b)`. -/
abbrev applyScheme : Atom :=
  arrowAtom [arrowAtom [.var "a"] (.var "b"), .var "a"] (.var "b")

/-- `(: sA SA)`, `(: sB SB)`, `(: sk (-> SA (-> SB SC)))`, `(: sg (-> SA SB SC))` and
`(: sapply (-> (-> $a $b) $a $b))`. -/
def separatingSpace : Space :=
  Space.ofList
    [SpecBoundary.annotation "sA" typeA, SpecBoundary.annotation "sB" typeB,
     SpecBoundary.annotation "sk" (arrowAtom [typeA] (arrowAtom [typeB] typeC)),
     SpecBoundary.annotation "sg" (arrowAtom [typeA, typeB] typeC),
     SpecBoundary.annotation "sapply" applyScheme]

theorem declared_sA : declaredType? separatingSpace sA = some typeA := by decide
theorem declared_sB : declaredType? separatingSpace sB = some typeB := by decide
theorem declared_sk :
    declaredType? separatingSpace sk = some (arrowAtom [typeA] (arrowAtom [typeB] typeC)) := by
  decide
theorem declared_sg : declaredType? separatingSpace sg = some (arrowAtom [typeA, typeB] typeC) := by
  decide
theorem declared_sapply : declaredType? separatingSpace sapply = some applyScheme := by decide

private theorem contractA : ContractType typeA := contractType_symbol (by decide)
private theorem contractB : ContractType typeB := contractType_symbol (by decide)
private theorem contractC : ContractType typeC := contractType_symbol (by decide)
private theorem contractBC : ContractType (arrowAtom [typeB] typeC) :=
  contractType_arrowAtom (by simp [contractB, contractC])
private theorem contractK : ContractType (arrowAtom [typeA] (arrowAtom [typeB] typeC)) :=
  contractType_arrowAtom (by simp [contractA, contractBC])

private theorem firstOrder_declared {atom type : Atom}
    (declared : declaredType? separatingSpace atom = some type) (contract : ContractType type) :
    FirstOrderType separatingSpace atom type :=
  .declared (occurrence := 0) ⟨type, by simp [declarations_of_declared declared],
    typeInstance_self contract⟩

private theorem ground_sk : TypeSubst.typeVars (arrowAtom [typeA] (arrowAtom [typeB] typeC)) = [] := by
  decide
private theorem ground_sg : TypeSubst.typeVars (arrowAtom [typeA, typeB] typeC) = [] := by decide

/-- `(sk sA) : (-> SB SC)`. -/
private theorem firstOrder_sk_sA :
    FirstOrderType separatingSpace (.expression [sk, sA]) (arrowAtom [typeB] typeC) :=
  .application (parameters := [typeA]) (firstOrder_declared declared_sk contractK)
    (.cons (firstOrder_declared declared_sA contractA) .nil)

/-- HE types `((sk sA) sB)` at `SC`, and so does the contract. -/
theorem contract_sk_sA_sB : Typed separatingSpace (.expression [.expression [sk, sA], sB]) typeC :=
  typed_iff_firstOrder.mpr
    (.application (parameters := [typeB]) firstOrder_sk_sA
      (.cons (firstOrder_declared declared_sB contractB) .nil))

/-- HE types `(sapply (sk sA) sB)` at `SC`, instantiating `$a` with `SB` and `$b` with
`SC`; so does the contract. -/
theorem contract_sapply_sk_sA_sB :
    Typed separatingSpace (.expression [sapply, .expression [sk, sA], sB]) typeC := by
  refine typed_iff_firstOrder.mpr
    (.application (parameters := [arrowAtom [typeB] typeC, typeB]) ?_
      (.cons firstOrder_sk_sA (.cons (firstOrder_declared declared_sB contractB) .nil)))
  refine .declared (occurrence := 0) ⟨applyScheme, by simp [declarations_of_declared declared_sapply],
    contractType_arrowAtom (by simp [contractB, contractC, contractBC]),
    fun name => if name = "a" then typeB else if name = "b" then typeC else .var name, ?_, ?_⟩
  · intro name
    by_cases isA : name = "a"
    · simp only [if_pos isA]
      exact contractB.1
    · by_cases isB : name = "b"
      · simp only [if_neg isA, if_pos isB]
        exact contractC.1
      · simp only [if_neg isA, if_neg isB]
        exact .var name
  · simp [applyTypeValuation, arrowAtom]

/-- HE types `(sg sA sB)` at `SC`, and so does the contract. -/
theorem contract_sg_sA_sB : Typed separatingSpace (.expression [sg, sA, sB]) typeC :=
  typed_iff_firstOrder.mpr
    (.application (parameters := [typeA, typeB])
      (firstOrder_declared declared_sg
        (contractType_arrowAtom (by simp [contractA, contractB, contractC])))
      (.cons (firstOrder_declared declared_sA contractA)
        (.cons (firstOrder_declared declared_sB contractB) .nil)))

/-- The arrows of a declared variable-free arrow type its applications only at its arity. -/
private theorem no_application_of_arity {head : Atom} {arguments parameters declaredParameters : List Atom}
    {result declaredResult : Atom}
    (declared : declaredType? separatingSpace head = some (arrowAtom declaredParameters declaredResult))
    (ground : TypeSubst.typeVars (arrowAtom declaredParameters declaredResult) = [])
    (arity : arguments.length ≠ declaredParameters.length)
    (headTyped : FirstOrderType separatingSpace head (arrowAtom parameters result))
    (argumentsTyped : FirstOrderTypes separatingSpace arguments parameters) : False := by
  have headEq := firstOrder_declared_eq declared ground headTyped
  obtain ⟨parametersEq, _⟩ := arrowAtom_injective headEq
  subst parametersEq
  exact arity (firstOrderTypes_iff_forall₂.mp argumentsTyped).length_eq

private theorem not_declared_expression {atoms : List Atom} {type : Atom} {occurrence : Nat}
    (none : declarations separatingSpace (.expression atoms) = [])
    (isInstance : Instance separatingSpace (.expression atoms) occurrence type) : False := by
  obtain ⟨_, found, _⟩ := isInstance
  simp [none] at found

/-- HE refuses the partial application `(sg sA)`, and so does the contract. -/
theorem contract_not_sg_sA (type : Atom) :
    ¬Typed separatingSpace (.expression [sg, sA]) type := by
  rw [typed_iff_firstOrder]
  intro typed
  cases typed with
  | declared isInstance => exact not_declared_expression (by decide) isInstance
  | application head arguments =>
      exact no_application_of_arity declared_sg ground_sg (by simp) head arguments
  | tuple head headNotArrow _ =>
      rw [firstOrder_declared_eq declared_sg ground_sg head] at headNotArrow
      exact headNotArrow (arrowAtom_arrowShaped _ _)

/-- HE refuses the over-application `(sk sA sB)`, and so does the contract. -/
theorem contract_not_sk_sA_sB (type : Atom) :
    ¬Typed separatingSpace (.expression [sk, sA, sB]) type := by
  rw [typed_iff_firstOrder]
  intro typed
  cases typed with
  | declared isInstance => exact not_declared_expression (by decide) isInstance
  | application head arguments =>
      exact no_application_of_arity declared_sk ground_sk (by simp) head arguments
  | tuple head headNotArrow _ =>
      rw [firstOrder_declared_eq declared_sk ground_sk head] at headNotArrow
      exact headNotArrow (arrowAtom_arrowShaped _ _)

/-- The instances of `(-> (-> $a $b) $a $b)`. -/
theorem applyScheme_instance (valuation : String → Atom) :
    applyTypeValuation valuation applyScheme =
      arrowAtom [arrowAtom [valuation "a"] (valuation "b"), valuation "a"] (valuation "b") := by
  simp [applyTypeValuation, arrowAtom]

/-- HE refuses `(sapply sg sA)`: `(-> $a $b)` does not match the binary arrow of `sg`.  So
does the contract. -/
theorem contract_not_sapply_sg_sA (type : Atom) :
    ¬Typed separatingSpace (.expression [sapply, sg, sA]) type := by
  rw [typed_iff_firstOrder]
  intro typed
  cases typed with
  | declared isInstance => exact not_declared_expression (by decide) isInstance
  | application head arguments =>
      obtain ⟨occurrence, scheme, found, _, valuation, _, instanceEq⟩ := firstOrder_symbol head
      rw [declarations_of_declared declared_sapply] at found
      cases occurrence with
      | succ _ => simp at found
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          rw [applyScheme_instance] at instanceEq
          obtain ⟨parametersEq, _⟩ := arrowAtom_injective instanceEq
          subst parametersEq
          cases arguments with
          | cons sgTyped _ =>
              have sgEq := firstOrder_declared_eq declared_sg ground_sg sgTyped
              obtain ⟨singleEq, _⟩ := arrowAtom_injective sgEq
              simp at singleEq
  | tuple head headNotArrow _ =>
      obtain ⟨occurrence, scheme, found, _, valuation, _, instanceEq⟩ := firstOrder_symbol head
      rw [declarations_of_declared declared_sapply] at found
      cases occurrence with
      | succ _ => simp at found
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          rw [← instanceEq, applyScheme_instance] at headNotArrow
          exact headNotArrow (arrowAtom_arrowShaped _ _)

/-! ### The curried view on the same judgments -/

private theorem faithful_symbol (name : String) (notReserved : name ∉ reservedTypeNames) :
    Curried.Faithful (.symbol name) ∧ ¬TopReserved (.symbol name) := by
  have contract := contractType_symbol notReserved
  refine ⟨.symbol ?_ ?_, contract.2⟩
  · rintro rfl
    exact notReserved (by simp [reservedTypeNames])
  · rintro rfl
    exact notReserved (by simp [reservedTypeNames])

private theorem faithful_sg : Curried.ContractType (arrowAtom [typeA, typeB] typeC) := by
  have hA := faithful_symbol "SA" (by decide)
  have hB := faithful_symbol "SB" (by decide)
  have hC := faithful_symbol "SC" (by decide)
  refine ⟨.arrow (argumentTypes := [typeA, typeB]) (returnType := typeC) rfl (by simp) ?_ ?_
    (by rintro ⟨_, equal⟩; cases equal) hC.2 hC.1, by rintro ⟨_, _, equal⟩; cases equal⟩
  · intro argumentType member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact hA.1
    · exact hB.1
  · intro argumentType member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact hA.2
    · exact hB.2

private theorem instance_sg : Curried.Instance separatingSpace sg (arrowAtom [typeA, typeB] typeC) :=
  ⟨faithful_sg, _, declared_sg, fun name => .var name, fun name => .var name,
    applyTypeValuation_of_ground _ ground_sg⟩

private theorem instance_sA : Curried.Instance separatingSpace sA typeA :=
  ⟨faithful_symbol "SA" (by decide), _, declared_sA, fun name => .var name, fun name => .var name,
    applyTypeValuation_of_ground _ (by decide)⟩

/-- **The curried view types the partial application `(sg sA)`**, which HE refuses:
the curried `sg` applied to one argument has the curried type of `(-> SB SC)`. -/
theorem curried_sg_sA : Curried.Typed separatingSpace (.expression [sg, sA]) (arrowAtom [typeB] typeC) := by
  rw [Curried.typed_iff]
  refine ⟨[.constant (.declared sA typeA)].foldl .app
      (.constant (.declared sg (arrowAtom [typeA, typeB] typeC))),
    .application (.cons (.symbol "sA" typeA) .nil), ?_⟩
  have sgReading : toTy (arrowAtom [typeA, typeB] typeC) =
      .arr (toTy typeA) (toTy (arrowAtom [typeB] typeC)) := by
    rw [toTy_of_functionType (rfl : FunctionTypeRel (arrowAtom [typeA, typeB] typeC)
        [typeA, typeB] typeC) (by simp),
      toTy_of_functionType (rfl : FunctionTypeRel (arrowAtom [typeB] typeC) [typeB] typeC)
        (by simp)]
    rfl
  refine .app (domain := toTy typeA) (.constant ?_) (.constant ?_)
  · rw [Curried.nameType_declared_eq_some_iff]
    exact ⟨instance_sg, sgReading.symm⟩
  · rw [Curried.nameType_declared_eq_some_iff]
    exact ⟨instance_sA, rfl⟩

/-- `sk`'s declaration returns an arrow, so the curried view has no constant for it. -/
private theorem no_instance_sk (instanceType : Atom) : ¬Curried.Instance separatingSpace sk instanceType := by
  rintro ⟨contract, scheme, declared, valuation, _, instanceEq⟩
  rw [declared_sk] at declared
  cases declared
  rw [applyTypeValuation_of_ground valuation ground_sk] at instanceEq
  subst instanceEq
  exact (contract.1.of_functionType (argumentTypes := [typeA]) rfl).2.2.2.1 ⟨_, rfl⟩

private theorem untyped_sk {term : Curried.ContractTerm} (annotates : Curried.Annotates sk term) {type : Ty Atom} :
    ¬ApplicativeTyped (Curried.nameType separatingSpace) term type := by
  intro typed
  cases annotates with
  | symbol _ instanceType =>
      exact no_instance_sk instanceType (Curried.applicativeTyped_declared_iff.mp typed).1

/-- No contract term of `(sk sA)` is typed. -/
private theorem untyped_sk_sA {term : Curried.ContractTerm} (annotates : Curried.Annotates (.expression [sk, sA]) term)
    {type : Ty Atom} : ¬ApplicativeTyped (Curried.nameType separatingSpace) term type := by
  intro typed
  cases annotates with
  | @application _ instanceType _ terms _ =>
      obtain ⟨_, headTyped, _⟩ := (applicativeTyped_foldl_iff _ _ _).mp typed
      exact no_instance_sk instanceType (Curried.applicativeTyped_declared_iff.mp headTyped).1
  | @tuple _ headType _ argumentTypes headTerm terms _ _ _ head arguments lengths =>
      have termLengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
        simp [(Curried.annotatesList_iff_forall₂.mp arguments).length_eq, lengths]
      obtain ⟨_, all⟩ := (Curried.applicativeTyped_tupleTerm_iff termLengths).mp typed
      cases all with
      | cons headTyped _ => exact untyped_sk head headTyped

/-- **The curried view does not type `((sk sA) sB)`**, which HE types at `SC`. -/
theorem curried_not_sk_sA_sB (type : Atom) :
    ¬Curried.Typed separatingSpace (.expression [.expression [sk, sA], sB]) type := by
  rw [Curried.typed_iff]
  rintro ⟨term, annotates, typed⟩
  cases annotates with
  | @tuple _ headType _ argumentTypes headTerm terms _ _ _ head arguments lengths =>
      have termLengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
        simp [(Curried.annotatesList_iff_forall₂.mp arguments).length_eq, lengths]
      obtain ⟨_, all⟩ := (Curried.applicativeTyped_tupleTerm_iff termLengths).mp typed
      cases all with
      | cons headTyped _ => exact untyped_sk_sA head headTyped

/-- **The curried view does not type `(sapply (sk sA) sB)`**, which HE types at `SC`. -/
theorem curried_not_sapply_sk_sA_sB (type : Atom) :
    ¬Curried.Typed separatingSpace (.expression [sapply, .expression [sk, sA], sB]) type := by
  rw [Curried.typed_iff]
  rintro ⟨term, annotates, typed⟩
  cases annotates with
  | @application _ _ _ terms arguments =>
      obtain ⟨_, _, all⟩ := (applicativeTyped_foldl_iff _ _ _).mp typed
      cases arguments with
      | cons skAnnotates _ =>
          cases all with
          | cons skTyped _ => exact untyped_sk_sA skAnnotates skTyped
  | @tuple _ headType _ argumentTypes headTerm terms _ _ _ head arguments lengths =>
      have termLengths : (headType :: argumentTypes).length = (headTerm :: terms).length := by
        simp [(Curried.annotatesList_iff_forall₂.mp arguments).length_eq, lengths]
      obtain ⟨_, all⟩ := (Curried.applicativeTyped_tupleTerm_iff termLengths).mp typed
      cases arguments with
      | cons skAnnotates _ =>
          cases all with
          | cons _ rest =>
              cases rest with
              | cons skTyped _ => exact untyped_sk_sA skAnnotates skTyped

end Separating

#print axioms Separating.contract_sk_sA_sB
#print axioms Separating.contract_sapply_sk_sA_sB
#print axioms Separating.contract_sg_sA_sB
#print axioms Separating.contract_not_sg_sA
#print axioms Separating.contract_not_sk_sA_sB
#print axioms Separating.contract_not_sapply_sg_sA
#print axioms Separating.curried_sg_sA
#print axioms Separating.curried_not_sk_sA_sB
#print axioms Separating.curried_not_sapply_sk_sA_sB

end Mettapedia.Languages.MeTTa.HE.HOLContract
