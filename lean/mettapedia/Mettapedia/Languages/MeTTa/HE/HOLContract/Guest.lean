import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.HOLLight.MeTTa.TermReading
import Mettapedia.Languages.HOLLight.MeTTa.TermJudgment

/-!
# The hosted HOL Light checker decides the contract

The runtime checks a contract judgment with the hosted HOL Light checker.  It translates the
judgment into the checker's source syntax, which is HOL Light's: an HE leaf type is a nullary
type operator, an arrow `(-> P₁ … Pₙ R)` the (n+1)-ary type operator `he-arrow:n` applied to
the translations of its components, a compound non-arrow type the right-nested pair type ending
in the unit type, a declared constant the constant of its declaration (named with the
declaration's occurrence) at the translation of its declared type, the application constant of
arity n the polymorphic constant `he-apply:n` of type `he-arrow:n A A' … B → A → A' → … → B`, a
tuple the pairing of its elements, and an application `Comb`.

`guestTyped_iff`: on contract terms whose constants are well named, the checker's typing of the
translation (the source term is resolved, its annotations are formed in the checker's
signature, and its type is computed) is exactly contract typing at the translated type.  The
translation of types is injective on the readings of type atoms (`guestTy_injective`), so the
type the checker computes identifies the contract type.

The checker library is modelled in `Languages.HOLLight.MeTTa`: its reader returns the
positional elaboration of every resolved, formed, well-typed source term, and its type judgment
returns that term's type.  Composed with `guestTyped_iff`, every contract typing is one that
the modelled checker reads and types at the translated type (`checker_reads_contract_typing`,
`checker_types_contract_typing`).

A refusal is a refutation: the modelled checker computes one answer, so a reader or type
judgment that returns anything else than the contract typing's answer shows that there is no
such typing (`reader_refusal_refutes`, `type_refusal_refutes`).

What is not proved here is explicit:

* `ReaderSound` states that the modelled reader returns a term only for a resolved, formed and
  typed source term.  The model proves the converse; `checker_acceptance_is_contract_typing`
  takes this statement as a hypothesis.
* The checker signature (`CheckerSignature`) is a hypothesis on the theory the declaration
  commands build: the model has no theorem for the execution of the type declarations.
* `Naming` records that the runtime's printed names separate the atoms they name, which the
  runtime's printer is not proved to do.
* The runtime evaluates the Prime spelling of the checker library; that this evaluation returns
  what the modelled library returns is not stated in Lean.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.Guest

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement

/-- The checker's types and terms. -/
abbrev CheckerTy := Mettapedia.Languages.OpenTheory.Ty
abbrev CheckerName := Mettapedia.Languages.OpenTheory.Name
abbrev CheckerTypeOp := Mettapedia.Languages.OpenTheory.TypeOp
abbrev CheckerConst := Mettapedia.Languages.OpenTheory.Const
abbrev CheckerTerm := Mettapedia.Languages.OpenTheory.SourceTerm

/-- How the runtime names leaves, declaration constants and type variables in the checker: a
leaf by its printed form, a declaration by its constant and occurrence, a type variable by its
spelling.  Leaves and type variables must be separated by their names. -/
structure Naming where
  leaf : Atom → String
  constant : Atom → Nat → String
  typeVariable : String → String
  leaf_injective : ∀ {left right : Atom}, TypeAtom left → TypeAtom right →
    (∀ atoms, left ≠ .expression atoms) → (∀ atoms, right ≠ .expression atoms) →
    (∀ name, left ≠ .var name) → (∀ name, right ≠ .var name) →
    leaf left = leaf right → left = right
  typeVariable_injective : Function.Injective typeVariable

variable (naming : Naming)

/-- A type operator without definition. -/
def typeOperator (name : String) : CheckerTypeOp := .mk (.mk [] name) .undefined

/-- The type operator of an HE leaf type. -/
def leafOperator (leaf : Atom) : CheckerTypeOp := typeOperator ("he:" ++ naming.leaf leaf)

/-- HOL Light's pair type and its unit type. -/
def prodOperator : CheckerTypeOp := typeOperator "prod"
def unitOperator : CheckerTypeOp := typeOperator "1"

/-- The type operator of the arrows with `arity` parameters. -/
def arrowOperator (arity : Nat) : CheckerTypeOp := typeOperator ("he-arrow:" ++ toString arity)

mutual

/-- The checker type of an HE type. -/
def readingType : Atom → CheckerTy
  | .symbol name => .op (leafOperator naming (.symbol name)) []
  | .grounded value => .op (leafOperator naming (.grounded value)) []
  | .var name => .var (.mk [] (naming.typeVariable name))
  | .expression atoms => expressionType atoms

/-- `readingType` of an expression: an arrow operator, or a product. -/
def expressionType : List Atom → CheckerTy
  | .symbol "->" :: first :: rest =>
      .op (arrowOperator rest.length) (readingType first :: readingList rest)
  | [] => .op unitOperator []
  | atom :: atoms => .op prodOperator [readingType atom, productType atoms]

/-- The readings of a list of types. -/
def readingList : List Atom → List CheckerTy
  | [] => []
  | atom :: atoms => readingType atom :: readingList atoms

/-- The right-nested pair type of a list of types, ending in the unit type. -/
def productType : List Atom → CheckerTy
  | [] => .op unitOperator []
  | atom :: atoms => .op prodOperator [readingType atom, productType atoms]

end

/-- The checker type of a HOL type of the contract. -/
def guestTy : Ty Atom → CheckerTy
  | .prop => Mettapedia.Languages.OpenTheory.Ty.bool
  | .base atom => readingType naming atom
  | .arr domain codomain =>
      Mettapedia.Languages.OpenTheory.Ty.function (guestTy domain) (guestTy codomain)

/-! ## The translation of types -/

theorem readingList_eq_map : ∀ atoms : List Atom, readingList naming atoms = atoms.map (readingType naming)
  | [] => rfl
  | atom :: atoms => by simp [readingList, readingList_eq_map atoms]

/-- The curried function type of argument types ending in a return type. -/
def functionChain (arguments : List CheckerTy) (result : CheckerTy) : CheckerTy :=
  arguments.foldr Mettapedia.Languages.OpenTheory.Ty.function result

theorem readingType_arrowAtom (parameters : List Atom) (result : Atom) :
    readingType naming (arrowAtom parameters result) =
      .op (arrowOperator parameters.length) ((parameters ++ [result]).map (readingType naming)) := by
  cases parameters with
  | nil => simp [arrowAtom, readingType, expressionType, readingList]
  | cons first rest =>
      simp [arrowAtom, readingType, expressionType, readingList_eq_map]

theorem readingType_product {elements : List Atom}
    (notArrow : ¬ArrowShaped (.expression elements)) :
    readingType naming (.expression elements) = productType naming elements := by
  simp only [readingType]
  unfold expressionType
  split
  · exact absurd ⟨_, rfl⟩ notArrow
  · simp only [productType]
  · simp only [productType]

theorem guestTy_applyTy (parameters : List Atom) (result : Atom) :
    guestTy naming (applyTy parameters result) =
      functionChain (parameters.map (readingType naming)) (readingType naming result) := by
  induction parameters with
  | nil => rfl
  | cons first rest ih =>
      simp only [applyTy, List.foldr_cons, guestTy, List.map_cons, functionChain] at ih ⊢
      rw [ih]

/-! ## The translation separates type atoms -/

private theorem he_ne_function (name : String) : "he:" ++ name ≠ "->" := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem he_ne_prod (name : String) : "he:" ++ name ≠ "prod" := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem he_ne_unit (name : String) : "he:" ++ name ≠ "1" := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem he_ne_arrow (name other : String) : "he:" ++ name ≠ "he-arrow:" ++ other := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem arrow_ne_function (name : String) : "he-arrow:" ++ name ≠ "->" := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem arrow_ne_prod (name : String) : "he-arrow:" ++ name ≠ "prod" := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem arrow_ne_unit (name : String) : "he-arrow:" ++ name ≠ "1" := by
  intro equal
  have := congrArg String.toList equal
  simp at this

private theorem he_cancel {left right : String} (equal : "he:" ++ left = "he:" ++ right) :
    left = right := by
  have := congrArg String.toList equal
  simp only [String.toList_append, List.append_cancel_left_eq] at this
  exact String.toList_inj.mp this

/-- The head operator of a checker type, when it is an operator type. -/
def headName : CheckerTy → Option CheckerName
  | .op (.mk name _) _ => some name
  | .var _ => none

theorem headName_function (domain codomain : CheckerTy) :
    headName (Mettapedia.Languages.OpenTheory.Ty.function domain codomain) =
      some (.mk [] "->") := rfl

/-- A type atom never reads as a function type: it reads as a leaf operator, a type variable,
an arrow operator, the pair type or the unit type. -/
theorem readingType_not_function {atom : Atom} (atomic : TypeAtom atom) :
    headName (readingType naming atom) ≠ some (.mk [] "->") := by
  cases atomic with
  | symbol _ _ =>
      intro equal
      simp only [readingType, headName, leafOperator, typeOperator, Option.some.injEq] at equal
      exact he_ne_function _ (Mettapedia.Languages.OpenTheory.Name.mk.inj equal).2
  | var name => simp [readingType, headName]
  | grounded value =>
      intro equal
      simp only [readingType, headName, leafOperator, typeOperator, Option.some.injEq] at equal
      exact he_ne_function _ (Mettapedia.Languages.OpenTheory.Name.mk.inj equal).2
  | @arrow components nonempty _ _ =>
      obtain ⟨parameters, result, rfl⟩ : ∃ parameters result, components = parameters ++ [result] :=
        ⟨components.dropLast, components.getLast nonempty, (List.dropLast_append_getLast nonempty).symm⟩
      intro equal
      have equal' := equal
      rw [show Atom.expression (.symbol "->" :: (parameters ++ [result])) =
        arrowAtom parameters result from rfl, readingType_arrowAtom] at equal'
      simp only [headName, arrowOperator, typeOperator, Option.some.injEq] at equal'
      exact arrow_ne_function _ (Mettapedia.Languages.OpenTheory.Name.mk.inj equal').2
  | @compound elements notArrow _ =>
      rw [readingType_product naming notArrow]
      cases elements with
      | nil => simp [productType, headName, unitOperator, typeOperator]
      | cons _ _ => simp [productType, headName, prodOperator, typeOperator]

private theorem productType_ne_leaf (elements : List Atom) (leaf : Atom) :
    productType naming elements ≠ .op (leafOperator naming leaf) [] := by
  intro equal
  cases elements with
  | nil =>
      have operatorEq := (Mettapedia.Languages.OpenTheory.Ty.op.inj equal).1
      have nameEq := (Mettapedia.Languages.OpenTheory.TypeOp.mk.inj operatorEq).1
      exact he_ne_unit _ (Mettapedia.Languages.OpenTheory.Name.mk.inj nameEq).2.symm
  | cons _ _ =>
      have operatorEq := (Mettapedia.Languages.OpenTheory.Ty.op.inj equal).1
      have nameEq := (Mettapedia.Languages.OpenTheory.TypeOp.mk.inj operatorEq).1
      exact he_ne_prod _ (Mettapedia.Languages.OpenTheory.Name.mk.inj nameEq).2.symm

private theorem productType_ne_arrow (elements : List Atom) (arity : Nat)
    (arguments : List CheckerTy) :
    productType naming elements ≠ .op (arrowOperator arity) arguments := by
  intro equal
  cases elements with
  | nil =>
      have operatorEq := (Mettapedia.Languages.OpenTheory.Ty.op.inj equal).1
      have nameEq := (Mettapedia.Languages.OpenTheory.TypeOp.mk.inj operatorEq).1
      exact arrow_ne_unit _ (Mettapedia.Languages.OpenTheory.Name.mk.inj nameEq).2.symm
  | cons _ _ =>
      have operatorEq := (Mettapedia.Languages.OpenTheory.Ty.op.inj equal).1
      have nameEq := (Mettapedia.Languages.OpenTheory.TypeOp.mk.inj operatorEq).1
      exact arrow_ne_prod _ (Mettapedia.Languages.OpenTheory.Name.mk.inj nameEq).2.symm

private theorem leaf_ne_arrow (leaf : Atom) (arity : Nat) (arguments : List CheckerTy) :
    (.op (leafOperator naming leaf) [] : CheckerTy) ≠ .op (arrowOperator arity) arguments := by
  intro equal
  have operatorEq := (Mettapedia.Languages.OpenTheory.Ty.op.inj equal).1
  have nameEq := (Mettapedia.Languages.OpenTheory.TypeOp.mk.inj operatorEq).1
  exact he_ne_arrow _ _ (Mettapedia.Languages.OpenTheory.Name.mk.inj nameEq).2

private theorem productType_injective_of :
    ∀ {left right : List Atom},
      (∀ element ∈ left, ∀ {other : Atom}, TypeAtom other →
        readingType naming element = readingType naming other → element = other) →
      (∀ element ∈ right, TypeAtom element) →
      productType naming left = productType naming right → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by
      simp [productType, unitOperator, prodOperator, typeOperator] at equal
  | _ :: _, [], _, _, equal => by
      simp [productType, unitOperator, prodOperator, typeOperator] at equal
  | first :: rest, rightFirst :: rightRest, ih, rightAtomic, equal => by
      simp only [productType, Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq,
        true_and] at equal
      obtain ⟨heads, tails, -⟩ := equal
      rw [ih first (by simp) (rightAtomic rightFirst (by simp)) heads,
        productType_injective_of
          (fun element member {other} otherAtomic equal =>
            ih element (List.mem_cons_of_mem _ member) otherAtomic equal)
          (fun element member => rightAtomic element (List.mem_cons_of_mem _ member)) tails]

private theorem map_readingType_injective :
    ∀ {left right : List Atom},
      (∀ element ∈ left, ∀ {other : Atom}, TypeAtom other →
        readingType naming element = readingType naming other → element = other) →
      (∀ element ∈ right, TypeAtom element) →
      left.map (readingType naming) = right.map (readingType naming) → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by simp at equal
  | _ :: _, [], _, _, equal => by simp at equal
  | first :: rest, rightFirst :: rightRest, ih, rightAtomic, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      rw [ih first (by simp) (rightAtomic rightFirst (by simp)) equal.1,
        map_readingType_injective
          (fun element member {other} otherAtomic equal =>
            ih element (List.mem_cons_of_mem _ member) otherAtomic equal)
          (fun element member => rightAtomic element (List.mem_cons_of_mem _ member)) equal.2]

/-- Is the atom a leaf symbol or literal? -/
private def IsLeaf (atom : Atom) : Prop :=
  (∀ atoms, atom ≠ .expression atoms) ∧ ∀ name, atom ≠ .var name

/-- The reading of an arrow type atom, by its components. -/
private theorem readingType_arrow_components {components : List Atom} (nonempty : components ≠ []) :
    readingType naming (.expression (.symbol "->" :: components)) =
      .op (arrowOperator (components.length - 1)) (components.map (readingType naming)) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp [readingType, expressionType, readingList_eq_map]

/-- **The checker reads type atoms injectively.** -/
theorem readingType_injective {left right : Atom} (leftAtomic : TypeAtom left)
    (rightAtomic : TypeAtom right)
    (equal : readingType naming left = readingType naming right) : left = right := by
  have leafCase : ∀ {leaf other : Atom}, TypeAtom leaf → IsLeaf leaf → TypeAtom other →
      .op (leafOperator naming leaf) [] = readingType naming other → leaf = other := by
    intro leaf other leafAtomic leafIsLeaf otherAtomic equal
    cases otherAtomic with
    | symbol notArrow notUndefined =>
        simp only [readingType, leafOperator, typeOperator,
          Mettapedia.Languages.OpenTheory.Ty.op.injEq,
          Mettapedia.Languages.OpenTheory.TypeOp.mk.injEq,
          Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and, and_true] at equal
        exact naming.leaf_injective leafAtomic (.symbol notArrow notUndefined)
          leafIsLeaf.1 (fun _ equal => (by cases equal)) leafIsLeaf.2 (fun _ equal => (by cases equal))
          (he_cancel equal)
    | grounded value =>
        simp only [readingType, leafOperator, typeOperator,
          Mettapedia.Languages.OpenTheory.Ty.op.injEq,
          Mettapedia.Languages.OpenTheory.TypeOp.mk.injEq,
          Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and, and_true] at equal
        exact naming.leaf_injective leafAtomic (.grounded value)
          leafIsLeaf.1 (fun _ equal => (by cases equal)) leafIsLeaf.2 (fun _ equal => (by cases equal))
          (he_cancel equal)
    | var name => simp [readingType] at equal
    | arrow nonempty _ _ =>
        rw [readingType_arrow_components naming nonempty] at equal
        exact absurd equal (leaf_ne_arrow naming leaf _ _)
    | compound notArrow _ =>
        rw [readingType_product naming notArrow] at equal
        exact absurd equal.symm (productType_ne_leaf naming _ leaf)
  have productVar : ∀ {elements : List Atom} {name : String},
      productType naming elements ≠ readingType naming (.var name) := by
    intro elements name equal
    cases elements <;> simp [readingType, productType] at equal
  induction leftAtomic generalizing right with
  | symbol notArrow notUndefined =>
      exact leafCase (.symbol notArrow notUndefined)
        ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ rightAtomic equal
  | grounded value =>
      exact leafCase (.grounded value)
        ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ rightAtomic equal
  | var name =>
      cases rightAtomic with
      | var other =>
          simp only [readingType, Mettapedia.Languages.OpenTheory.Ty.var.injEq,
            Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and] at equal
          rw [naming.typeVariable_injective equal]
      | symbol notArrow notUndefined =>
          exact (leafCase (.symbol notArrow notUndefined)
            ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ (.var name)
            equal.symm).symm
      | grounded value =>
          exact (leafCase (.grounded value)
            ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ (.var name)
            equal.symm).symm
      | arrow nonempty _ _ =>
          rw [readingType_arrow_components naming nonempty] at equal
          simp [readingType] at equal
      | compound notArrow _ =>
          rw [readingType_product naming notArrow] at equal
          exact absurd equal.symm productVar
  | @arrow components nonempty componentsAtomic componentsNotReserved componentIH =>
      have leftAtomic : TypeAtom (.expression (.symbol "->" :: components)) :=
        .arrow nonempty componentsAtomic componentsNotReserved
      rw [readingType_arrow_components naming nonempty] at equal
      cases rightAtomic with
      | @arrow rightComponents rightNonempty rightAtomic _ =>
          rw [readingType_arrow_components naming rightNonempty] at equal
          simp only [Mettapedia.Languages.OpenTheory.Ty.op.injEq] at equal
          rw [map_readingType_injective naming
            (fun element member {other} otherAtomic equal =>
              componentIH element member otherAtomic equal)
            rightAtomic equal.2]
      | symbol notArrow notUndefined =>
          exact absurd equal.symm (leaf_ne_arrow naming _ _ _)
      | grounded value =>
          exact absurd equal.symm (leaf_ne_arrow naming _ _ _)
      | var name => simp [readingType] at equal
      | compound notArrow _ =>
          rw [readingType_product naming notArrow] at equal
          exact absurd equal.symm (productType_ne_arrow naming _ _ _)
  | @compound elements notArrow elementsAtomic elementIH =>
      rw [readingType_product naming notArrow] at equal
      cases rightAtomic with
      | compound rightNotArrow rightElementsAtomic =>
          rw [readingType_product naming rightNotArrow] at equal
          rw [productType_injective_of naming
            (fun element member {other} otherAtomic equal =>
              elementIH element member otherAtomic equal)
            rightElementsAtomic equal]
      | symbol notArrowName notUndefined =>
          exact absurd equal (productType_ne_leaf naming _ _)
      | grounded value => exact absurd equal (productType_ne_leaf naming _ _)
      | var name => exact absurd equal productVar
      | arrow nonempty _ _ =>
          rw [readingType_arrow_components naming nonempty] at equal
          exact absurd equal (productType_ne_arrow naming _ _ _)

/-! ## Contract readings -/

/-- HOL types of the contract that the checker reads faithfully: base types of type atoms and
arrows of such types.  The proposition type is not the reading of any HE type. -/
inductive ContractReading : Ty Atom → Prop where
  | base {atom : Atom} : TypeAtom atom → ContractReading (.base atom)
  | arr {domain codomain : Ty Atom} : ContractReading domain → ContractReading codomain →
      ContractReading (.arr domain codomain)

theorem ContractReading.applyTy {parameters : List Atom} {result : Atom}
    (parametersAtomic : ∀ parameter ∈ parameters, TypeAtom parameter) (resultAtomic : TypeAtom result) :
    ContractReading (Mettapedia.Languages.MeTTa.HE.HOLContract.applyTy parameters result) := by
  induction parameters with
  | nil => exact .base resultAtomic
  | cons first rest ih =>
      exact .arr (.base (parametersAtomic first (by simp)))
        (ih (fun parameter member => parametersAtomic parameter (List.mem_cons_of_mem _ member)))

theorem guestTy_ne_function_of_base {atom : Atom} (atomic : TypeAtom atom) (domain codomain : CheckerTy) :
    guestTy naming (.base atom) ≠ Mettapedia.Languages.OpenTheory.Ty.function domain codomain := by
  intro equal
  have heads := congrArg headName equal
  rw [headName_function] at heads
  exact readingType_not_function naming atomic heads

/-- **The checker separates contract readings.** -/
theorem guestTy_injective {left right : Ty Atom} (leftReading : ContractReading left)
    (rightReading : ContractReading right) (equal : guestTy naming left = guestTy naming right) :
    left = right := by
  induction leftReading generalizing right with
  | @base atom atomic =>
      cases rightReading with
      | @base other otherAtomic =>
          rw [readingType_injective naming atomic otherAtomic equal]
      | arr _ _ =>
          exact absurd equal (guestTy_ne_function_of_base naming atomic _ _)
  | arr _ _ domainIH codomainIH =>
      cases rightReading with
      | @base other otherAtomic =>
          exact absurd equal.symm (guestTy_ne_function_of_base naming otherAtomic _ _)
      | arr rightDomain rightCodomain =>
          simp only [guestTy, Mettapedia.Languages.OpenTheory.Ty.function,
            Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq, true_and] at equal
          rw [domainIH rightDomain equal.1, codomainIH rightCodomain equal.2.1]

/-- A checker function type is the reading of an arrow of HOL types. -/
theorem guestTy_eq_function {type : Ty Atom} (reading : ContractReading type)
    {domain codomain : CheckerTy}
    (equal : guestTy naming type = Mettapedia.Languages.OpenTheory.Ty.function domain codomain) :
    ∃ typeDomain typeCodomain, type = .arr typeDomain typeCodomain ∧
      guestTy naming typeDomain = domain ∧ guestTy naming typeCodomain = codomain := by
  cases reading with
  | @base atom atomic =>
      exact absurd equal (guestTy_ne_function_of_base naming atomic _ _)
  | @arr typeDomain typeCodomain _ _ =>
      simp only [guestTy, Mettapedia.Languages.OpenTheory.Ty.function,
        Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq, true_and] at equal
      exact ⟨typeDomain, typeCodomain, rfl, equal.1, equal.2.1⟩

/-! ## Leaves -/

/-- `leaf` is a leaf the checker reads as a type operator in `atom`: a symbol or literal of the
atom other than the head of an arrow. -/
inductive ReadLeaf : Atom → Atom → Prop where
  | symbol (name : String) : ReadLeaf (.symbol name) (.symbol name)
  | grounded (value : GroundedValue) : ReadLeaf (.grounded value) (.grounded value)
  | arrowComponent {leaf component : Atom} {components : List Atom} :
      component ∈ components → ReadLeaf leaf component →
      ReadLeaf leaf (.expression (.symbol "->" :: components))
  | element {leaf element : Atom} {elements : List Atom} :
      ¬ArrowShaped (.expression elements) → element ∈ elements → ReadLeaf leaf element →
      ReadLeaf leaf (.expression elements)

/-- Every leaf the checker reads in the atom is among `leaves`. -/
def LeavesWithin (leaves : Atom → Prop) (atom : Atom) : Prop :=
  ∀ leaf, ReadLeaf leaf atom → leaves leaf

/-- Every base type of a HOL type has its leaves among `leaves`. -/
def TyLeavesWithin (leaves : Atom → Prop) : Ty Atom → Prop
  | .prop => True
  | .base atom => LeavesWithin leaves atom
  | .arr domain codomain => TyLeavesWithin leaves domain ∧ TyLeavesWithin leaves codomain

/-! ## Constants and terms -/

/-- A constant of the checker without definition. -/
def constOf (name : String) : CheckerConst := .mk (.mk [] name) .undefined

/-- The name of the application constant of arrows with `arity` parameters. -/
def applyName (arity : Nat) : String := "he-apply:" ++ toString arity

/-- The checker constant of a contract name. -/
def nameConst : Name → CheckerConst
  | .declared constant occurrence _ => constOf ("he:" ++ naming.constant constant occurrence)
  | .apply parameters _ => constOf (applyName parameters.length)
  | .pair _ => constOf ","
  | .fst _ => constOf "FST"
  | .snd _ => constOf "SND"
  | .one => constOf "one"

/-- The contract type a name is read at, whatever the space. -/
def nameReading : Name → Ty Atom
  | .declared _ _ instanceType => .base instanceType
  | .apply parameters result =>
      .arr (.base (arrowAtom parameters result)) (applyTy parameters result)
  | .pair (component :: components) =>
      .arr (.base component) (.arr (productTy components) (productTy (component :: components)))
  | .fst (component :: components) => .arr (productTy (component :: components)) (.base component)
  | .snd (component :: components) =>
      .arr (productTy (component :: components)) (productTy components)
  | .one => productTy []
  | .pair [] | .fst [] | .snd [] => .prop

theorem nameType_eq_nameReading {space : Space} {name : Name} {type : Ty Atom}
    (lookup : nameType space name = some type) : type = nameReading name := by
  cases name with
  | declared constant occurrence instanceType =>
      exact (nameType_declared_eq_some_iff.mp lookup).2
  | apply parameters result =>
      exact (nameType_apply_eq_some_iff.mp lookup).2
  | pair components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          simp only [nameType, Option.some.injEq] at lookup
          exact lookup.symm
  | fst components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          simp only [nameType, Option.some.injEq] at lookup
          exact lookup.symm
  | snd components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          simp only [nameType, Option.some.injEq] at lookup
          exact lookup.symm
  | one =>
      simp only [nameType, Option.some.injEq] at lookup
      exact lookup.symm

/-- The checker's source term of a contract term: every constant occurrence carries the checker
type of its contract type. -/
def guestTerm : ContractTerm → CheckerTerm
  | .constant name => .const (nameConst naming name) (guestTy naming (nameReading name))
  | .app function argument => .app (guestTerm function) (guestTerm argument)
  | _ => .const (constOf "") (.op unitOperator [])

/-- A product constant whose first component is not the arrow symbol: its components read as
a product.  Every constant of a tuple is one. -/
def NameReadable : Name → Prop
  | .pair (component :: _) | .fst (component :: _) | .snd (component :: _) =>
      component ≠ .symbol "->"
  | _ => True

/-- Every constant of a contract term is readable and has a contract type that the checker reads
faithfully, with its leaves among `leaves`. -/
def WellNamed (space : Space) (leaves : Atom → Prop) : ContractTerm → Prop
  | .constant name => NameReadable name ∧ ∃ type, nameType space name = some type ∧
      ContractReading type ∧ TyLeavesWithin leaves type
  | .app function argument => WellNamed space leaves function ∧ WellNamed space leaves argument
  | _ => False

/-! ## The checker signature of a space -/

/-- A checker type variable. -/
def tyvar (name : String) : CheckerTy := .var (.mk [] name)

/-- The type variables of the parameters of the application constants: `A`, `A'`, `A''`, …. -/
def applyVariable (index : Nat) : String := String.ofList ('A' :: List.replicate index '\'')

theorem applyVariable_injective : Function.Injective applyVariable := by
  intro left right equal
  have := congrArg (fun name => name.toList.length) equal
  simpa [applyVariable] using this

theorem applyVariable_ne_result (index : Nat) : applyVariable index ≠ "B" := by
  intro equal
  have := congrArg String.toList equal
  simp [applyVariable] at this

/-- The parameter variables from position `start`. -/
def applyParameters : Nat → Nat → List CheckerTy
  | _, 0 => []
  | start, count + 1 => tyvar (applyVariable start) :: applyParameters (start + 1) count

/-- The type of the application constant of arrows with `arity` parameters:
`he-arrow:n A A' … B → A → A' → … → B`. -/
def applySchema (arity : Nat) : CheckerTy :=
  Mettapedia.Languages.OpenTheory.Ty.function
    (.op (arrowOperator arity) (applyParameters 0 arity ++ [tyvar "B"]))
    (functionChain (applyParameters 0 arity) (tyvar "B"))

/-- A checker signature for a set of leaves declares those leaf type operators, the pair and
unit types, the function type and the arrow operators at their arities, every declaration of
the space at the reading of its declared type, the application constants and the pair
signature. -/
structure CheckerSignature (space : Space) (leaves : Atom → Prop)
    (signature : Mettapedia.Languages.OpenTheory.SignatureFormation.Signature) : Prop where
  leafArity : ∀ leaf, leaves leaf → signature.typeOperators (leafOperator naming leaf) = some 0
  prodArity : signature.typeOperators prodOperator = some 2
  unitArity : signature.typeOperators unitOperator = some 0
  functionArity :
    signature.typeOperators Mettapedia.Languages.OpenTheory.TypeOp.function = some 2
  arrowArity : ∀ arity, signature.typeOperators (arrowOperator arity) = some (arity + 1)
  declared : ∀ constant occurrence scheme,
    (declarations space constant)[occurrence]? = some scheme →
      signature.constants (constOf ("he:" ++ naming.constant constant occurrence)) =
        some (readingType naming scheme)
  applySchema : ∀ arity, signature.constants (constOf (applyName arity)) = some (applySchema arity)
  pairSchema : signature.constants (constOf ",") =
    some (Mettapedia.Languages.OpenTheory.Ty.function (tyvar "A")
      (Mettapedia.Languages.OpenTheory.Ty.function (tyvar "B")
        (.op prodOperator [tyvar "A", tyvar "B"])))
  fstSchema : signature.constants (constOf "FST") =
    some (Mettapedia.Languages.OpenTheory.Ty.function (.op prodOperator [tyvar "A", tyvar "B"])
      (tyvar "A"))
  sndSchema : signature.constants (constOf "SND") =
    some (Mettapedia.Languages.OpenTheory.Ty.function (.op prodOperator [tyvar "A", tyvar "B"])
      (tyvar "B"))
  oneSchema : signature.constants (constOf "one") = some (.op unitOperator [])

/-! ## Checker types are formed -/

open Mettapedia.Languages.OpenTheory.SignatureFormation (TypeFormed)
open Mettapedia.Languages.HOLLight.MeTTa.TypeFormation (Resolved)

section Formation

variable {naming}
variable {space : Space} {leaves : Atom → Prop}
variable {signature : Mettapedia.Languages.OpenTheory.SignatureFormation.Signature}
variable (checker : CheckerSignature naming space leaves signature)
include checker

omit checker in
private theorem formed_op {operator : CheckerTypeOp} {arguments : List CheckerTy}
    (arity : signature.typeOperators operator = some arguments.length)
    (all : ∀ argument ∈ arguments, TypeFormed signature argument ∧ Resolved signature argument) :
    TypeFormed signature (.op operator arguments) ∧ Resolved signature (.op operator arguments) := by
  constructor
  · rw [TypeFormed]
    exact ⟨arity, fun argument member => (all argument member).1⟩
  · rw [Resolved]
    exact ⟨⟨_, arity⟩, fun argument member => (all argument member).2⟩

private theorem formed_function {domain codomain : CheckerTy}
    (domainFormed : TypeFormed signature domain ∧ Resolved signature domain)
    (codomainFormed : TypeFormed signature codomain ∧ Resolved signature codomain) :
    TypeFormed signature (Mettapedia.Languages.OpenTheory.Ty.function domain codomain) ∧
      Resolved signature (Mettapedia.Languages.OpenTheory.Ty.function domain codomain) := by
  apply formed_op checker.functionArity
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact domainFormed
  · exact codomainFormed

private theorem formed_product :
    ∀ (atoms : List Atom), (∀ atom ∈ atoms,
      TypeFormed signature (readingType naming atom) ∧ Resolved signature (readingType naming atom)) →
      TypeFormed signature (productType naming atoms) ∧ Resolved signature (productType naming atoms)
  | [], _ => by
      simp only [productType]
      exact formed_op checker.unitArity (by simp)
  | atom :: atoms, all => by
      simp only [productType]
      apply formed_op checker.prodArity
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact all atom (by simp)
      · exact formed_product atoms (fun other member => all other (List.mem_cons_of_mem _ member))

/-- The checker type of a type atom whose leaves are declared is resolved and formed. -/
theorem readingType_formed {atom : Atom} (atomic : TypeAtom atom) (within : LeavesWithin leaves atom) :
    TypeFormed signature (readingType naming atom) ∧ Resolved signature (readingType naming atom) := by
  induction atomic with
  | @symbol name _ _ =>
      simp only [readingType]
      exact formed_op (checker.leafArity _ (within _ (.symbol name))) (by simp)
  | grounded value =>
      simp only [readingType]
      exact formed_op (checker.leafArity _ (within _ (.grounded value))) (by simp)
  | var name =>
      simp only [readingType]
      constructor
      · rw [TypeFormed]; trivial
      · rw [Resolved]
  | @arrow components nonempty _ _ componentIH =>
      rw [readingType_arrow_components naming nonempty]
      refine formed_op (by
        rw [checker.arrowArity, List.length_map, Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (by simpa using nonempty))]) ?_
      intro argument member
      obtain ⟨component, componentMember, rfl⟩ := List.mem_map.mp member
      exact componentIH component componentMember
        (fun leaf read => within leaf (.arrowComponent componentMember read))
  | @compound elements notArrow _ elementIH =>
      rw [readingType_product naming notArrow]
      exact formed_product checker elements (fun element member =>
        elementIH element member (fun leaf read => within leaf (.element notArrow member read)))

/-- The checker type of a contract reading with declared leaves is resolved and formed. -/
theorem guestTy_formed {type : Ty Atom} (reading : ContractReading type)
    (within : TyLeavesWithin leaves type) :
    TypeFormed signature (guestTy naming type) ∧ Resolved signature (guestTy naming type) := by
  induction reading with
  | @base atom atomic => exact readingType_formed checker atomic within
  | arr _ _ domainIH codomainIH =>
      exact formed_function checker (domainIH within.1) (codomainIH within.2)

end Formation

/-! ## Instances commute with the checker's type substitution -/

/-- The checker substitution of a valuation on a list of type variables. -/
def checkerSubst (valuation : String → Atom) (names : List String) :
    Mettapedia.Languages.OpenTheory.TypeSubst :=
  ⟨names.map fun name => (.mk [] (naming.typeVariable name), readingType naming (valuation name))⟩

private theorem lookup_checkerSubst (valuation : String → Atom) :
    ∀ (names : List String) {name : String}, name ∈ names →
      (checkerSubst naming valuation names).lookup (.mk [] (naming.typeVariable name)) =
        some (readingType naming (valuation name))
  | [], _, member => by cases member
  | first :: rest, name, member => by
      by_cases same : first = name
      · subst same
        simp [checkerSubst, Mettapedia.Languages.OpenTheory.TypeSubst.lookup]
      · have restMember : name ∈ rest := by
          rcases List.mem_cons.mp member with equal | restMember
          · exact absurd equal.symm same
          · exact restMember
        have different : (Mettapedia.Languages.OpenTheory.Name.mk [] (naming.typeVariable name) ==
            .mk [] (naming.typeVariable first)) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq,
            Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and]
          exact fun equal => same (naming.typeVariable_injective equal).symm
        have restLookup := lookup_checkerSubst valuation rest restMember
        simp only [checkerSubst, Mettapedia.Languages.OpenTheory.TypeSubst.lookup,
          List.map_cons, List.lookup, different] at restLookup ⊢
        exact restLookup

private theorem product_applyTypeValuation (valuation : String → Atom) (names : List String) :
    ∀ (atoms : List Atom),
      (∀ atom ∈ atoms, (checkerSubst naming valuation names).apply (readingType naming atom) =
        readingType naming (applyTypeValuation valuation atom)) →
      (checkerSubst naming valuation names).apply (productType naming atoms) =
        productType naming (atoms.map (applyTypeValuation valuation))
  | [], _ => by simp [productType]
  | atom :: atoms, all => by
      simp only [productType, List.map_cons,
        Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_nil]
      rw [all atom (by simp),
        product_applyTypeValuation valuation names atoms
          (fun other member => all other (List.mem_cons_of_mem _ member))]

private theorem applyTypeValuation_expression (valuation : String → Atom) (atoms : List Atom) :
    applyTypeValuation valuation (.expression atoms) =
      .expression (atoms.map (applyTypeValuation valuation)) := by
  simp [applyTypeValuation]

/-- The checker reading of an expression that is not an arrow with components is its
product. -/
private theorem readingType_of_not_arrowForm {atoms : List Atom}
    (notForm : ¬∃ first rest, atoms = .symbol "->" :: first :: rest) :
    readingType naming (.expression atoms) = productType naming atoms := by
  simp only [readingType]
  unfold expressionType
  split
  · exact absurd ⟨_, _, rfl⟩ notForm
  · simp only [productType]
  · simp only [productType]

/-- **The checker reads an instance as the substituted reading.**  When no type variable takes
the arrow symbol as its value, applying a valuation and reading commute with the checker's
substitution of the valued variables. -/
theorem readingType_applyTypeValuation (valuation : String → Atom)
    (notArrow : ∀ name, valuation name ≠ .symbol "->") (names : List String) :
    ∀ (atom : Atom), (∀ name ∈ TypeSubst.typeVars atom, name ∈ names) →
      (checkerSubst naming valuation names).apply (readingType naming atom) =
        readingType naming (applyTypeValuation valuation atom) := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ name ∈ TypeSubst.typeVarsList atoms, name ∈ names) → ∀ atom ∈ atoms,
        (checkerSubst naming valuation names).apply (readingType naming atom) =
          readingType naming (applyTypeValuation valuation atom)) with
  | symbol name => intro _; simp [readingType, applyTypeValuation]
  | grounded value => intro _; simp [readingType, applyTypeValuation]
  | var name =>
      intro covered
      simp only [readingType, applyTypeValuation,
        Mettapedia.Languages.OpenTheory.TypeSubst.apply_var]
      rw [lookup_checkerSubst naming valuation names (covered name (by simp [TypeSubst.typeVars]))]
      rfl
  | expression atoms ih =>
      intro covered
      have all := ih (by simpa [TypeSubst.typeVars] using covered)
      rw [applyTypeValuation_expression]
      by_cases arrowForm : ∃ first rest, atoms = .symbol "->" :: first :: rest
      · obtain ⟨first, rest, rfl⟩ := arrowForm
        have headEq : applyTypeValuation valuation (.symbol "->") = .symbol "->" := by
          simp [applyTypeValuation]
        simp only [List.map_cons, headEq]
        rw [readingType_arrow_components naming (by simp),
          readingType_arrow_components naming (by simp)]
        simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.length_cons,
          List.length_map, List.map_cons, List.map_map, Mettapedia.Languages.OpenTheory.Ty.op.injEq,
          List.cons.injEq, true_and]
        refine ⟨all first (by simp), List.map_congr_left (fun atom member => ?_)⟩
        exact all atom (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
      · have notArrowMapped : ¬∃ first rest,
            atoms.map (applyTypeValuation valuation) = .symbol "->" :: first :: rest := by
          rintro ⟨first, rest, mapped⟩
          apply arrowForm
          match atoms, mapped with
          | [], mapped => simp at mapped
          | [_], mapped => simp at mapped
          | head :: atom₁ :: tail, mapped =>
              simp only [List.map_cons, List.cons.injEq] at mapped
              refine ⟨atom₁, tail, ?_⟩
              cases head with
              | symbol name =>
                  simp only [applyTypeValuation, Atom.symbol.injEq] at mapped
                  rw [mapped.1]
              | var name =>
                  simp only [applyTypeValuation] at mapped
                  exact absurd mapped.1 (notArrow name)
              | grounded value => simp [applyTypeValuation] at mapped
              | expression inner => simp [applyTypeValuation] at mapped
        rw [readingType_of_not_arrowForm naming arrowForm,
          readingType_of_not_arrowForm naming notArrowMapped]
        exact product_applyTypeValuation naming valuation names atoms all
  | nil => rename_i member; cases member
  | cons head tail headIH tailIH =>
      rename_i covered atom member
      simp only [TypeSubst.typeVarsList, List.mem_append] at covered
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH (fun name inHead => covered name (Or.inl inHead))
      · exact tailIH (fun name inTail => covered name (Or.inr inTail)) atom member

/-! ## The application constants -/

/-- The bindings of an application instance from parameter position `start`. -/
def applyInstanceBindings : Nat → List Atom → List (CheckerName × CheckerTy)
  | _, [] => []
  | start, parameter :: parameters =>
      (.mk [] (applyVariable start), readingType naming parameter) ::
        applyInstanceBindings (start + 1) parameters

/-- The checker substitution of an application instance. -/
def applyInstanceSubst (parameters : List Atom) (result : Atom) :
    Mettapedia.Languages.OpenTheory.TypeSubst :=
  ⟨applyInstanceBindings naming 0 parameters ++ [(.mk [] "B", readingType naming result)]⟩

private theorem lookup_applyBindings_result (result : CheckerTy) :
    ∀ (start : Nat) (parameters : List Atom),
      List.lookup (Mettapedia.Languages.OpenTheory.Name.mk [] "B")
          (applyInstanceBindings naming start parameters ++ [(.mk [] "B", result)]) = some result
  | _, [] => by simp [applyInstanceBindings]
  | start, parameter :: parameters => by
      have different : (Mettapedia.Languages.OpenTheory.Name.mk [] "B" ==
          .mk [] (applyVariable start)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq,
          Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and]
        exact fun equal => applyVariable_ne_result start equal.symm
      simp only [applyInstanceBindings, List.cons_append, List.lookup, different]
      exact lookup_applyBindings_result result (start + 1) parameters

private theorem lookup_applyBindings_parameter (tail : List (CheckerName × CheckerTy)) :
    ∀ (start : Nat) (parameters : List Atom) (offset : Nat) (inRange : offset < parameters.length),
      List.lookup (Mettapedia.Languages.OpenTheory.Name.mk [] (applyVariable (start + offset)))
          (applyInstanceBindings naming start parameters ++ tail) =
        some (readingType naming parameters[offset])
  | _, [], _, inRange => by simp at inRange
  | start, parameter :: parameters, 0, _ => by
      simp [applyInstanceBindings]
  | start, parameter :: parameters, offset + 1, inRange => by
      have different : (Mettapedia.Languages.OpenTheory.Name.mk [] (applyVariable (start + (offset + 1))) ==
          .mk [] (applyVariable start)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq,
          Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and]
        intro equal
        have := applyVariable_injective equal
        omega
      simp only [applyInstanceBindings, List.cons_append, List.lookup, different]
      have rest := lookup_applyBindings_parameter tail (start + 1) parameters offset
        (by simpa using inRange)
      rw [show start + 1 + offset = start + (offset + 1) by omega] at rest
      simpa using rest

private theorem applySubst_parameters (parameters : List Atom) (result : Atom) :
    ∀ (start : Nat) (suffix : List Atom), (∀ offset (inRange : offset < suffix.length),
      (applyInstanceSubst naming parameters result).lookup
          (.mk [] (applyVariable (start + offset))) = some (readingType naming suffix[offset])) →
      (applyParameters start suffix.length).map (applyInstanceSubst naming parameters result).apply =
        suffix.map (readingType naming)
  | _, [], _ => rfl
  | start, first :: rest, found => by
      simp only [List.length_cons, applyParameters, List.map_cons, tyvar,
        Mettapedia.Languages.OpenTheory.TypeSubst.apply_var]
      have headFound := found 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at headFound
      rw [headFound, Option.getD_some,
        applySubst_parameters parameters result (start + 1) rest (fun offset inRange => by
          have := found (offset + 1) (by simpa using inRange)
          rw [show start + (offset + 1) = start + 1 + offset by omega] at this
          simpa using this)]

private theorem apply_functionChain (substitution : Mettapedia.Languages.OpenTheory.TypeSubst) :
    ∀ (arguments : List CheckerTy) (result : CheckerTy),
      substitution.apply (functionChain arguments result) =
        functionChain (arguments.map substitution.apply) (substitution.apply result)
  | [], _ => rfl
  | first :: rest, result => by
      simp only [functionChain, List.foldr_cons, List.map_cons,
        Mettapedia.Languages.OpenTheory.TypeSubst.apply_function] at apply_functionChain ⊢
      rw [apply_functionChain substitution rest result]

/-- The application constant's type at an instance is the reading of the instance. -/
theorem applySchema_instance (parameters : List Atom) (result : Atom) :
    (applyInstanceSubst naming parameters result).apply (applySchema parameters.length) =
      guestTy naming (.arr (.base (arrowAtom parameters result)) (applyTy parameters result)) := by
  have parametersEq : (applyParameters 0 parameters.length).map
      (applyInstanceSubst naming parameters result).apply = parameters.map (readingType naming) :=
    applySubst_parameters naming parameters result 0 parameters (fun offset inRange => by
      simpa [applyInstanceSubst, Mettapedia.Languages.OpenTheory.TypeSubst.lookup] using
        lookup_applyBindings_parameter naming [(.mk [] "B", readingType naming result)] 0
          parameters offset inRange)
  have resultEq : (applyInstanceSubst naming parameters result).apply (tyvar "B") =
      readingType naming result := by
    simp only [tyvar, Mettapedia.Languages.OpenTheory.TypeSubst.apply_var, applyInstanceSubst,
      Mettapedia.Languages.OpenTheory.TypeSubst.lookup,
      lookup_applyBindings_result naming (readingType naming result) 0 parameters, Option.getD_some]
  simp only [applySchema, Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
    Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_append, List.map_cons,
    List.map_nil, apply_functionChain, parametersEq, resultEq, guestTy, readingType_arrowAtom,
    guestTy_applyTy]

/-- An expression whose elements are type atoms reads as the product of its elements. -/
theorem readingType_expression_of_elements {elements : List Atom}
    (all : ∀ element ∈ elements, TypeAtom element) :
    readingType naming (.expression elements) = productType naming elements := by
  refine readingType_of_not_arrowForm naming ?_
  rintro ⟨first, rest, rfl⟩
  exact (all _ (by simp)).not_arrow_symbol rfl

/-- The components of a product type atom whose first component is not the arrow symbol are
type atoms. -/
theorem product_elements {component : Atom} {components : List Atom}
    (notArrow : component ≠ .symbol "->") (atomic : TypeAtom (.expression (component :: components))) :
    ∀ element ∈ component :: components, TypeAtom element := by
  cases atomic with
  | arrow _ _ _ => exact absurd rfl notArrow
  | compound _ all => exact all

/-! ## The checker's typing is contract typing -/

open Mettapedia.Languages.OpenTheory.SignatureFormation (AnnotationsFormed ConstantInstance)
open Mettapedia.Languages.HOLLight.MeTTa.TermReading (SourceResolved)

/-- The checker's typing of a closed source term: it is resolved, its annotations are formed,
and its type is the given one. -/
def GuestTyped (signature : Mettapedia.Languages.OpenTheory.SignatureFormation.Signature)
    (source : CheckerTerm) (type : CheckerTy) : Prop :=
  SourceResolved signature source ∧ AnnotationsFormed signature (source.toDB []) ∧
    source.inferType = some type

section Correspondence

variable {naming}
variable {space : Space} {leaves : Atom → Prop}
variable {signature : Mettapedia.Languages.OpenTheory.SignatureFormation.Signature}

/-- A contract typing is computed by the checker's type inference. -/
theorem inferType_guestTerm_complete :
    ∀ {term : ContractTerm} {type : Ty Atom},
      ApplicativeTyped (nameType space) term type →
        (guestTerm naming term).inferType = some (guestTy naming type)
  | _, _, .constant lookup => by
      rw [nameType_eq_nameReading lookup]
      simp [guestTerm]
  | _, _, .app functionTyped argumentTyped => by
      have functionInferred := inferType_guestTerm_complete functionTyped
      have argumentInferred := inferType_guestTerm_complete argumentTyped
      simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.inferType.eq_3,
        functionInferred, argumentInferred, guestTy, Option.bind_eq_bind, Option.bind_some,
        Mettapedia.Languages.OpenTheory.Ty.destFunction?_function]
      simp

/-- The checker's type inference computes only contract typings. -/
theorem inferType_guestTerm_sound {term : ContractTerm} (applicative : Applicative term) :
    WellNamed space leaves term → ∀ {inferred : CheckerTy},
      (guestTerm naming term).inferType = some inferred →
        ∃ type, ContractReading type ∧ inferred = guestTy naming type ∧
          ApplicativeTyped (nameType space) term type := by
  induction applicative with
  | constant name =>
      intro wellNamed inferred computed
      obtain ⟨_, type, lookup, reading, _⟩ := wellNamed
      have typeEq := nameType_eq_nameReading lookup
      subst typeEq
      simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.inferType.eq_1,
        Option.some.injEq] at computed
      exact ⟨_, reading, computed.symm, .constant lookup⟩
  | @app function argument _ _ functionIH argumentIH =>
      intro wellNamed inferred computed
      obtain ⟨functionNamed, argumentNamed⟩ := wellNamed
      have unfolded : (guestTerm naming (.app function argument)).inferType =
          ((guestTerm naming function).inferType.bind fun functionTy =>
            (guestTerm naming argument).inferType.bind fun argumentTy =>
              functionTy.destFunction?.bind fun pieces =>
                if Mettapedia.Languages.OpenTheory.Ty.same pieces.1 argumentTy then some pieces.2
                else none) := by
        simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.inferType.eq_3]
        rfl
      rw [unfolded] at computed
      cases functionComputed : (guestTerm naming function).inferType with
      | none => simp [functionComputed] at computed
      | some functionTy =>
          cases argumentComputed : (guestTerm naming argument).inferType with
          | none => simp [functionComputed, argumentComputed] at computed
          | some argumentTy =>
              cases split : functionTy.destFunction? with
              | none => simp [functionComputed, argumentComputed, split] at computed
              | some pieces =>
                  obtain ⟨domain, codomain⟩ := pieces
                  simp only [functionComputed, argumentComputed, split, Option.bind_some]
                    at computed
                  by_cases same : Mettapedia.Languages.OpenTheory.Ty.same domain argumentTy = true
                  · rw [if_pos same, Option.some.injEq] at computed
                    subst computed
                    obtain ⟨functionType, functionReading, functionEq, functionTyped⟩ :=
                      functionIH functionNamed functionComputed
                    obtain ⟨argumentType, argumentReading, argumentEq, argumentTyped⟩ :=
                      argumentIH argumentNamed argumentComputed
                    have shape := Mettapedia.Languages.OpenTheory.Ty.eq_function_of_destFunction?
                      split
                    rw [functionEq] at shape
                    obtain ⟨typeDomain, typeCodomain, rfl, domainEq, codomainEq⟩ :=
                      guestTy_eq_function naming functionReading shape
                    have domainSame := (Mettapedia.Languages.OpenTheory.Ty.same_eq_true_iff _ _).mp
                      same
                    rw [← domainEq, argumentEq] at domainSame
                    cases functionReading with
                    | arr domainReading codomainReading =>
                        have typesEq := guestTy_injective naming domainReading argumentReading
                          domainSame
                        subst typesEq
                        exact ⟨typeCodomain, codomainReading, codomainEq.symm,
                          .app functionTyped argumentTyped⟩
                  · rw [if_neg same] at computed
                    cases computed

variable (checker : CheckerSignature naming space leaves signature)
include checker

omit checker in
private theorem tyvar_lookup (first second : CheckerTy) :
    (⟨[(.mk [] "A", first), (.mk [] "B", second)]⟩ :
        Mettapedia.Languages.OpenTheory.TypeSubst).apply (tyvar "A") = first ∧
      (⟨[(.mk [] "A", first), (.mk [] "B", second)]⟩ :
        Mettapedia.Languages.OpenTheory.TypeSubst).apply (tyvar "B") = second := by
  have different : (Mettapedia.Languages.OpenTheory.Name.mk [] "B" ==
      Mettapedia.Languages.OpenTheory.Name.mk [] "A") = false := by decide
  constructor
  · simp [tyvar, Mettapedia.Languages.OpenTheory.TypeSubst.lookup, List.lookup]
  · simp [tyvar, Mettapedia.Languages.OpenTheory.TypeSubst.lookup, List.lookup, different]

/-- The checker admits every contract name read at a contract reading at its contract type. -/
theorem constantInstance_nameConst {name : Name} {type : Ty Atom}
    (lookup : nameType space name = some type) (readable : NameReadable name)
    (reading : ContractReading type) :
    ConstantInstance signature (nameConst naming name) (guestTy naming (nameReading name)) := by
  have typeEq := nameType_eq_nameReading lookup
  subst typeEq
  cases name with
  | declared constant occurrence instanceType =>
      obtain ⟨⟨scheme, declared, _, valuation, valuesAtomic, instanceEq⟩, _⟩ :=
        nameType_declared_eq_some_iff.mp lookup
      refine ⟨readingType naming scheme, checkerSubst naming valuation (TypeSubst.typeVars scheme),
        checker.declared constant occurrence scheme declared, ?_⟩
      rw [readingType_applyTypeValuation naming valuation
          (fun name => (valuesAtomic name).not_arrow_symbol)
          (TypeSubst.typeVars scheme) scheme (fun _ member => member),
        instanceEq]
      rfl
  | apply parameters result =>
      exact ⟨_, applyInstanceSubst naming parameters result, checker.applySchema parameters.length,
        applySchema_instance naming parameters result⟩
  | pair components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          cases reading with
          | arr componentReading restReading =>
              cases componentReading with
              | base componentAtomic =>
                  cases restReading with
                  | arr tailReading productReading =>
                      cases tailReading with
                      | base tailAtomic =>
                          cases productReading with
                          | base productAtomic =>
                              have all := product_elements readable productAtomic
                              refine ⟨_, ⟨[(.mk [] "A", readingType naming component),
                                (.mk [] "B", productType naming components)]⟩, checker.pairSchema, ?_⟩
                              obtain ⟨first, second⟩ := tyvar_lookup (readingType naming component)
                                (productType naming components)
                              simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
                                Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_cons,
                                List.map_nil, first, second, nameReading, guestTy, productTy]
                              rw [readingType_expression_of_elements naming all,
                                readingType_expression_of_elements naming
                                  (fun element member => all element (List.mem_cons_of_mem _ member))]
                              rfl
  | fst components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          cases reading with
          | arr productReading componentReading =>
              cases productReading with
              | base productAtomic =>
                  cases componentReading with
                  | base componentAtomic =>
                      have all := product_elements readable productAtomic
                      refine ⟨_, ⟨[(.mk [] "A", readingType naming component),
                        (.mk [] "B", productType naming components)]⟩, checker.fstSchema, ?_⟩
                      obtain ⟨first, second⟩ := tyvar_lookup (readingType naming component)
                        (productType naming components)
                      simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
                        Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_cons,
                        List.map_nil, first, second, nameReading, guestTy, productTy]
                      rw [readingType_expression_of_elements naming all]
                      rfl
  | snd components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          cases reading with
          | arr productReading tailReading =>
              cases productReading with
              | base productAtomic =>
                  have all := product_elements readable productAtomic
                  refine ⟨_, ⟨[(.mk [] "A", readingType naming component),
                    (.mk [] "B", productType naming components)]⟩, checker.sndSchema, ?_⟩
                  obtain ⟨first, second⟩ := tyvar_lookup (readingType naming component)
                    (productType naming components)
                  simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
                    Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_cons,
                    List.map_nil, first, second, nameReading, guestTy, productTy]
                  rw [readingType_expression_of_elements naming all,
                    readingType_expression_of_elements naming
                      (fun element member => all element (List.mem_cons_of_mem _ member))]
                  rfl
  | one =>
      refine ⟨_, Mettapedia.Languages.OpenTheory.TypeSubst.empty, checker.oneSchema, ?_⟩
      simp [nameReading, guestTy, productTy, readingType, expressionType]

/-- Every well-named contract typing is resolved and formed in the checker. -/
theorem guestTerm_formed :
    ∀ {term : ContractTerm} {type : Ty Atom},
      ApplicativeTyped (nameType space) term type → WellNamed space leaves term →
        SourceResolved signature (guestTerm naming term) ∧
          AnnotationsFormed signature ((guestTerm naming term).toDB [])
  | _, _, .constant lookup, ⟨readable, type, lookup', reading, within⟩ => by
      rw [lookup] at lookup'
      cases lookup'
      have typeEq := nameType_eq_nameReading lookup
      have formed := guestTy_formed checker (typeEq ▸ reading) (typeEq ▸ within)
      constructor
      · simp only [guestTerm]
        rw [SourceResolved]
        exact formed.2
      · simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.toDB.eq_1]
        exact .constant formed.1 (constantInstance_nameConst checker lookup readable reading)
  | _, _, .app functionTyped argumentTyped, ⟨functionNamed, argumentNamed⟩ => by
      obtain ⟨functionResolved, functionFormed⟩ := guestTerm_formed functionTyped functionNamed
      obtain ⟨argumentResolved, argumentFormed⟩ := guestTerm_formed argumentTyped argumentNamed
      constructor
      · simp only [guestTerm]
        rw [SourceResolved]
        exact ⟨functionResolved, argumentResolved⟩
      · simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.toDB.eq_3]
        exact .app functionFormed argumentFormed

/-- **The checker decides contract typing.**  For a well-named contract term and a contract
reading, the checker's typing of the translation at the translated type is contract typing. -/
theorem guestTyped_iff {term : ContractTerm} (applicative : Applicative term)
    (wellNamed : WellNamed space leaves term) {type : Ty Atom} (reading : ContractReading type) :
    ApplicativeTyped (nameType space) term type ↔
      GuestTyped signature (guestTerm naming term) (guestTy naming type) := by
  constructor
  · intro typed
    obtain ⟨resolved, formed⟩ := guestTerm_formed checker typed wellNamed
    exact ⟨resolved, formed, inferType_guestTerm_complete typed⟩
  · rintro ⟨_, _, inferred⟩
    obtain ⟨found, foundReading, typesEq, typed⟩ :=
      inferType_guestTerm_sound applicative wellNamed inferred
    rw [guestTy_injective naming reading foundReading typesEq]
    exact typed

end Correspondence

/-! ## The modelled checker reads and types every contract typing -/

section Model

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.MeTTa

variable {naming}
variable {space : Space} {leaves : Atom → Prop}
variable (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
variable (origins : CheckerTypeOp → Atom) (constants : CheckerConst → Atom)

/-- The source call of the checker's reader on its tables. -/
def readCall (operatorsKey constantsKey contextKey sourceKey : String) : Atom :=
  .expression [.symbol "hol-light:read-term", .var operatorsKey, .var constantsKey,
    .var contextKey, .var sourceKey]

/-- The elaboration the reader returns for a closed source term. -/
def readAnswer (source : CheckerTerm) : Atom :=
  .expression [.symbol "Some", Representation.termAtom Representation.registeredOperatorAtom
    constants [] (source.toDB [])]

/-- **The modelled reader reads every contract typing.**  Called on the
tables of a theory whose signature is a checker signature of the space, the
checker library's reader returns the positional elaboration of the
translation of every well-named contract typing at a contract reading. -/
theorem checker_reads_contract_typing
    (checker : CheckerSignature naming space leaves world.signature)
    {term : ContractTerm} {type : Ty Atom}
    (typed : ApplicativeTyped (nameType space) term type) (wellNamed : WellNamed space leaves term)
    (bindings : Subst) (state : Effects.State)
    (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) =
      OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) =
      DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom [])
    (sourceCaptured : applySubst bindings (.var sourceKey) =
      TermReading.sourceAtom (guestTerm naming term)) :
    Eval.PureReturns program bindings state
      (readCall operatorsKey constantsKey contextKey sourceKey) state
      (readAnswer constants (guestTerm naming term)) := by
  obtain ⟨resolved, formed⟩ := guestTerm_formed checker typed wellNamed
  exact TermReading.authored_read_return world table origins constants (guestTerm naming term)
    resolved [] (by simp) formed (guestTy naming type) (inferType_guestTerm_complete typed)
    bindings state operatorsKey constantsKey contextKey sourceKey operatorsCaptured
    constantsCaptured contextCaptured sourceCaptured

/-- **The modelled type judgment returns the translated contract type.** -/
theorem checker_types_contract_typing {term : ContractTerm} {type : Ty Atom}
    (typed : ApplicativeTyped (nameType space) term type)
    (bindings : Subst) (state : Effects.State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants []
        ((guestTerm naming term).toDB [])) :
    Eval.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) state
      (.expression [.symbol "Some", TypeSubstitution.typeAtom Representation.registeredOperatorAtom
        (guestTy naming type)]) := by
  have checked : ((guestTerm naming term).toDB []).inferType [] = some (guestTy naming type) := by
    have := Mettapedia.Languages.OpenTheory.DBTerm.inferType_toDB [] (guestTerm naming term)
    simpa [inferType_guestTerm_complete typed] using this
  exact TermJudgment.authored_term_type_return constants bindings state []
    ((guestTerm naming term).toDB []) (guestTy naming type) checked termKey captured

/-- A modelled source evaluation returns one answer. -/
theorem pureReturns_unique {bindings : Subst} {before after after' : Effects.State}
    {expression value value' : Atom}
    (first : Eval.PureReturns program bindings before expression after value)
    (second : Eval.PureReturns program bindings before expression after' value') :
    value = value' := by
  obtain ⟨fuel, completed⟩ := Eval.path_has_sufficient_fuel program _ after' [value'] [] [] second
  obtain ⟨_, answers, _, _⟩ :=
    (Eval.path_completed_iff program _ after [value] [] [] first after' [value'] [] []).mp
      ⟨fuel, completed⟩
  simp only [List.cons.injEq, and_true] at answers
  exact answers.symm

/-- **A refusal by the modelled reader refutes.**  If the reader returns
anything but the elaboration, then the well-named contract term has no
contract typing at any contract reading. -/
theorem reader_refusal_refutes
    (checker : CheckerSignature naming space leaves world.signature)
    {term : ContractTerm} (wellNamed : WellNamed space leaves term)
    (bindings : Subst) (state after : Effects.State)
    (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) =
      OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) =
      DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom [])
    (sourceCaptured : applySubst bindings (.var sourceKey) =
      TermReading.sourceAtom (guestTerm naming term))
    {answer : Atom}
    (returned : Eval.PureReturns program bindings state
      (readCall operatorsKey constantsKey contextKey sourceKey) after answer)
    (refused : answer ≠ readAnswer constants (guestTerm naming term)) (type : Ty Atom) :
    ¬ApplicativeTyped (nameType space) term type := by
  intro typed
  exact refused (pureReturns_unique returned
    (checker_reads_contract_typing world table origins constants checker typed wellNamed bindings
      state operatorsKey constantsKey contextKey sourceKey operatorsCaptured constantsCaptured
      contextCaptured sourceCaptured))

/-- **A refusal by the modelled type judgment refutes.**  If the judgment on
the elaboration returns anything but the translated type, the contract term
is not typed at that type. -/
theorem type_refusal_refutes {term : ContractTerm} {type : Ty Atom}
    (bindings : Subst) (state after : Effects.State) (termKey : String)
    (captured : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants []
        ((guestTerm naming term).toDB []))
    {answer : Atom}
    (returned : Eval.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) after answer)
    (refused : answer ≠ .expression [.symbol "Some",
      TypeSubstitution.typeAtom Representation.registeredOperatorAtom (guestTy naming type)]) :
    ¬ApplicativeTyped (nameType space) term type := by
  intro typed
  exact refused (pureReturns_unique returned
    (checker_types_contract_typing constants typed bindings state termKey captured))

/-- **Open statement: the reader is sound.**  Whenever the modelled reader
returns some term for a closed source term on a theory's tables, the source
term is resolved and its annotations are formed in the theory's signature,
and its type is computed.  The model proves the converse
(`TermReading.authored_read_return`); this direction is not proved in this
development, so a positive answer of the runtime relies on it. -/
def ReaderSound : Prop :=
  ∀ (source : CheckerTerm) (bindings : Subst) (state after : Effects.State)
    (operatorsKey constantsKey contextKey sourceKey : String) (value : Atom),
    applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins →
    applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants →
    applySubst bindings (.var contextKey) = ContextLookup.contextAtom [] →
    applySubst bindings (.var sourceKey) = TermReading.sourceAtom source →
    Eval.PureReturns program bindings state
      (readCall operatorsKey constantsKey contextKey sourceKey) after
      (.expression [.symbol "Some", value]) →
    SourceResolved world.signature source ∧ AnnotationsFormed world.signature (source.toDB []) ∧
      ∃ type, source.inferType = some type ∧
        value = Representation.termAtom Representation.registeredOperatorAtom constants []
          (source.toDB [])

/-- Under the open soundness of the reader, an acceptance by the modelled
reader and type judgment at the translated type is a contract typing. -/
theorem checker_acceptance_is_contract_typing (sound : ReaderSound world table origins constants)
    (checker : CheckerSignature naming space leaves world.signature)
    {term : ContractTerm} (applicative : Applicative term)
    (wellNamed : WellNamed space leaves term) {type : Ty Atom} (reading : ContractReading type)
    (typeWithin : TyLeavesWithin leaves type)
    (bindings : Subst) (state after : Effects.State)
    (operatorsKey constantsKey contextKey sourceKey termKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) =
      OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) =
      DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom [])
    (sourceCaptured : applySubst bindings (.var sourceKey) =
      TermReading.sourceAtom (guestTerm naming term))
    {value : Atom}
    (read : Eval.PureReturns program bindings state
      (readCall operatorsKey constantsKey contextKey sourceKey) after
      (.expression [.symbol "Some", value]))
    (termCaptured : applySubst bindings (.var termKey) = value) (afterTerm : Effects.State)
    (typedAnswer : Eval.PureReturns program bindings state
      (.expression [.symbol "hol-light:term-type", .var termKey]) afterTerm
      (.expression [.symbol "Some", TypeSubstitution.typeAtom
        Representation.registeredOperatorAtom (guestTy naming type)])) :
    ApplicativeTyped (nameType space) term type := by
  obtain ⟨_, formed, found, inferred, valueEq⟩ :=
    sound (guestTerm naming term) bindings state after operatorsKey constantsKey contextKey
      sourceKey value operatorsCaptured constantsCaptured contextCaptured sourceCaptured read
  obtain ⟨foundType, foundReading, foundEq, foundTyped⟩ :=
    inferType_guestTerm_sound applicative wellNamed inferred
  subst foundEq
  have judged := checker_types_contract_typing constants foundTyped bindings state termKey
    (termCaptured.trans valueEq)
  have answersEq := pureReturns_unique typedAnswer judged
  simp only [Atom.expression.injEq, List.cons.injEq, and_true, true_and] at answersEq
  have dbTyped : ((guestTerm naming term).toDB []).inferType [] =
      some (guestTy naming foundType) := by
    have := Mettapedia.Languages.OpenTheory.DBTerm.inferType_toDB [] (guestTerm naming term)
    simpa [inferred] using this
  have foundFormed :=
    Mettapedia.Languages.OpenTheory.SignatureFormation.AnnotationsFormed.inferredType
      world.signature checker.functionArity formed (fun _ member => by cases member) dbTyped
  have typesEq := Representation.registered_typeAtom_injective world _ _
    (guestTy_formed checker reading typeWithin).1 foundFormed answersEq
  rw [guestTy_injective naming reading foundReading typesEq]
  exact foundTyped

end Model

#print axioms readingType_injective
#print axioms guestTy_injective
#print axioms guestTyped_iff
#print axioms checker_reads_contract_typing
#print axioms checker_types_contract_typing
#print axioms reader_refusal_refutes
#print axioms type_refusal_refutes
#print axioms checker_acceptance_is_contract_typing

end Mettapedia.Languages.MeTTa.HE.HOLContract.Guest
