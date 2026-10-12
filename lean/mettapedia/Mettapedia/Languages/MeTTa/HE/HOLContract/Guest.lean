import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.HOLLight.MeTTa.TermReading
import Mettapedia.Languages.HOLLight.MeTTa.TermJudgment

/-!
# The hosted HOL Light checker decides the contract

The runtime checks a contract judgment with the hosted HOL Light checker.
It translates the judgment into the checker's source syntax, which is HOL
Light's: an HE leaf type is a nullary type operator, an arrow the curried
function type, a compound non-arrow type the right-nested pair type ending in
the unit type, a declared constant a constant of its translated declared
type, a tuple the pairing of its elements, and an application `Comb`.

`guestTyped_iff`: on contract terms whose constants are well named, the
checker's typing of the translation (the source term is resolved, its
annotations are formed in the checker's signature, and its type is computed)
is exactly contract typing at the translated type.  The translation of types
is injective on faithful readings (`guestTy_injective`), so the type the
checker computes identifies the contract type.

The checker library is modelled in `Languages.HOLLight.MeTTa`: its reader
returns the positional elaboration of every resolved, formed, well-typed
source term, and its type judgment returns that term's type.  Composed with
`guestTyped_iff`, every contract typing is one that the modelled checker
reads and types at the translated type (`checker_reads_contract_typing`,
`checker_types_contract_typing`).

A refusal is a refutation: the modelled checker computes one answer, so a
reader or type judgment that returns anything else than the contract typing's
answer shows that there is no such typing (`reader_refusal_refutes`,
`type_refusal_refutes`).

What is not proved here is explicit:

* `ReaderSound` states that the modelled reader returns a term only for a
  resolved, formed and typed source term.  The model proves the converse;
  `checker_acceptance_is_contract_typing` takes this statement as a
  hypothesis.
* The checker signature (`CheckerSignature`) is a hypothesis on the theory the
  declaration commands build: the model has no theorem for the execution of
  the type declarations.
* `Naming` records that the runtime's printed names separate the atoms they
  name, which the runtime's printer is not proved to do.
* The runtime evaluates the Prime spelling of the checker library; that this
  evaluation returns what the modelled library returns is not stated in Lean.
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

/-- How the runtime names leaves, constants and type variables in the
checker: a leaf by its printed form, a type variable by its spelling.  Both
must separate what they name. -/
structure Naming where
  leaf : Atom → String
  typeVariable : String → String
  leaf_injective : ∀ {left right : Atom}, Faithful left → Faithful right →
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

mutual

/-- The checker type of the HOL reading of an atom. -/
def readingType : Atom → CheckerTy
  | .symbol name => .op (leafOperator naming (.symbol name)) []
  | .grounded value => .op (leafOperator naming (.grounded value)) []
  | .var name => .var (.mk [] (naming.typeVariable name))
  | .expression atoms => expressionType atoms

/-- `readingType` of an expression. -/
def expressionType : List Atom → CheckerTy
  | .symbol "->" :: first :: second :: rest => spineType (first :: second :: rest)
  | [] => .op unitOperator []
  | atom :: atoms => .op prodOperator [readingType atom, productType atoms]

/-- The curried function type of the components of an arrow. -/
def spineType : List Atom → CheckerTy
  | [] => .op prodOperator [.op (leafOperator naming (.symbol "->")) [], .op unitOperator []]
  | [last] => readingType last
  | first :: second :: rest =>
      Mettapedia.Languages.OpenTheory.Ty.function (readingType first)
        (spineType (second :: rest))

/-- The right-nested pair type of a list of types, ending in the unit
type. -/
def productType : List Atom → CheckerTy
  | [] => .op unitOperator []
  | atom :: atoms => .op prodOperator [readingType atom, productType atoms]

end

/-- The checker type of a base type of the contract. -/
def baseType : Atom → CheckerTy
  | .expression atoms => productType naming atoms
  | .symbol name => .op (leafOperator naming (.symbol name)) []
  | .grounded value => .op (leafOperator naming (.grounded value)) []
  | .var name => .var (.mk [] (naming.typeVariable name))

/-- The checker type of a HOL type of the contract. -/
def guestTy : Ty Atom → CheckerTy
  | .prop => Mettapedia.Languages.OpenTheory.Ty.bool
  | .base atom => baseType naming atom
  | .arr domain codomain =>
      Mettapedia.Languages.OpenTheory.Ty.function (guestTy domain) (guestTy codomain)

/-! ## The translation of types -/

theorem guestTy_componentsSpine :
    ∀ (components : List Atom),
      (∀ atom ∈ components, guestTy naming (toTy atom) = readingType naming atom) →
        guestTy naming (componentsSpine components) = spineType naming components
  | [], _ => by
      simp only [componentsSpine, spineType, guestTy, baseType, productType, readingType]
  | [last], all => by
      simp only [componentsSpine, spineType]
      exact all last (by simp)
  | first :: second :: rest, all => by
      simp only [componentsSpine, spineType, guestTy]
      rw [all first (by simp),
        guestTy_componentsSpine (second :: rest)
          (fun atom member => all atom (List.mem_cons_of_mem _ member))]

/-- The checker type of the reading of an atom is the atom's checker type. -/
theorem guestTy_toTy (atom : Atom) : guestTy naming (toTy atom) = readingType naming atom := by
  induction atom using Atom.rec (motive_2 := fun atoms => ∀ atom ∈ atoms,
      guestTy naming (toTy atom) = readingType naming atom) with
  | symbol name => simp only [toTy, guestTy, baseType, readingType]
  | var name => simp only [toTy, guestTy, baseType, readingType]
  | grounded value => simp only [toTy, guestTy, baseType, readingType]
  | expression atoms ih =>
      simp only [toTy, readingType]
      by_cases arrowForm : ∃ first second rest, atoms = .symbol "->" :: first :: second :: rest
      · obtain ⟨first, second, rest, rfl⟩ := arrowForm
        simp only [expressionTy, expressionType]
        exact guestTy_componentsSpine naming (first :: second :: rest)
          (fun atom member => ih atom (List.mem_cons_of_mem _ member))
      · have tyEq : expressionTy atoms = .base (.expression atoms) := by
          unfold expressionTy
          split
          · exact absurd ⟨_, _, _, rfl⟩ arrowForm
          · rfl
        have typeEq : expressionType naming atoms = productType naming atoms := by
          unfold expressionType
          split
          · exact absurd ⟨_, _, _, rfl⟩ arrowForm
          · simp only [productType]
          · simp only [productType]
        rw [tyEq, typeEq]
        simp only [guestTy, baseType]
  | nil => rename_i member; cases member
  | cons head tail headIH tailIH =>
      rename_i atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH
      · exact tailIH atom member

/-! ## The translation separates faithful types -/

private theorem leafName_ne {name other : String}
    (different : ∀ suffix, "he:" ++ suffix ≠ other) : "he:" ++ name ≠ other :=
  different name

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

private theorem he_ne_bool (name : String) : "he:" ++ name ≠ "bool" := by
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

theorem headName_leaf (leaf : Atom) :
    headName (.op (leafOperator naming leaf) []) = some (.mk [] ("he:" ++ naming.leaf leaf)) :=
  rfl

/-- A faithful non-arrow atom reads as a leaf operator, a type variable, the
pair type or the unit type: never a function type. -/
theorem readingType_not_function {atom : Atom} (faithful : Faithful atom)
    (notArrow : ¬ArrowShaped atom) :
    headName (readingType naming atom) ≠ some (.mk [] "->") := by
  cases faithful with
  | symbol _ _ =>
      intro equal
      simp only [readingType, headName, leafOperator, typeOperator, Option.some.injEq] at equal
      exact he_ne_function _ (Mettapedia.Languages.OpenTheory.Name.mk.inj equal).2
  | var name => simp [readingType, headName]
  | grounded value =>
      intro equal
      simp only [readingType, headName, leafOperator, typeOperator, Option.some.injEq] at equal
      exact he_ne_function _ (Mettapedia.Languages.OpenTheory.Name.mk.inj equal).2
  | arrow function _ _ _ _ _ _ => exact absurd (ArrowShaped.of_functionType function) notArrow
  | @product elements productNotArrow _ =>
      have typeEq : expressionType naming elements = productType naming elements := by
        unfold expressionType
        split
        · exact absurd ⟨_, rfl⟩ productNotArrow
        · simp only [productType]
        · simp only [productType]
      simp only [readingType, typeEq]
      cases elements with
      | nil => simp [productType, headName, unitOperator, typeOperator]
      | cons _ _ => simp [productType, headName, prodOperator, typeOperator]

theorem readingType_product {elements : List Atom}
    (notArrow : ¬ArrowShaped (.expression elements)) :
    readingType naming (.expression elements) = productType naming elements := by
  simp only [readingType]
  unfold expressionType
  split
  · exact absurd ⟨_, rfl⟩ notArrow
  · simp only [productType]
  · simp only [productType]

/-- The curried function type of argument types ending in a return type. -/
def functionChain (arguments : List CheckerTy) (result : CheckerTy) : CheckerTy :=
  arguments.foldr Mettapedia.Languages.OpenTheory.Ty.function result

theorem spineType_append :
    ∀ (argumentTypes : List Atom) (returnType : Atom), argumentTypes ≠ [] →
      spineType naming (argumentTypes ++ [returnType]) =
        functionChain (argumentTypes.map (readingType naming)) (readingType naming returnType)
  | [], _, nonempty => absurd rfl nonempty
  | [first], returnType, _ => by
      simp [spineType, functionChain]
  | first :: second :: rest, returnType, _ => by
      have tail := spineType_append (second :: rest) returnType (by simp)
      simp only [List.cons_append] at tail ⊢
      rw [spineType, tail]
      simp [functionChain]

theorem readingType_arrow {type returnType : Atom} {argumentTypes : List Atom}
    (function : FunctionTypeRel type argumentTypes returnType) (nonempty : argumentTypes ≠ []) :
    readingType naming type =
      functionChain (argumentTypes.map (readingType naming)) (readingType naming returnType) := by
  rw [FunctionTypeRel] at function
  subst function
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  obtain ⟨second, tail, split⟩ : ∃ second tail, rest ++ [returnType] = second :: tail := by
    cases rest with
    | nil => exact ⟨returnType, [], rfl⟩
    | cons head rest => exact ⟨head, rest ++ [returnType], rfl⟩
  have spine := spineType_append naming (first :: rest) returnType (by simp)
  simp only [List.cons_append, split] at spine ⊢
  simp only [readingType, expressionType]
  exact spine

/-- A function chain with at least one argument has the function head. -/
private theorem headName_functionChain {arguments : List CheckerTy} {result : CheckerTy}
    (nonempty : arguments ≠ []) :
    headName (functionChain arguments result) = some (.mk [] "->") := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  rfl

private theorem headName_productType_ne_function (elements : List Atom) :
    headName (productType naming elements) ≠ some (.mk [] "->") := by
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

private theorem productType_injective_of :
    ∀ {left right : List Atom},
      (∀ element ∈ left, ∀ {other : Atom}, Faithful other →
        readingType naming element = readingType naming other → element = other) →
      (∀ element ∈ right, Faithful element) →
      productType naming left = productType naming right → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by
      simp [productType, unitOperator, prodOperator, typeOperator] at equal
  | _ :: _, [], _, _, equal => by
      simp [productType, unitOperator, prodOperator, typeOperator] at equal
  | first :: rest, rightFirst :: rightRest, ih, rightFaithful, equal => by
      simp only [productType, Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq,
        true_and] at equal
      obtain ⟨heads, tails, -⟩ := equal
      rw [ih first (by simp) (rightFaithful rightFirst (by simp)) heads,
        productType_injective_of
          (fun element member {other} otherFaithful equal =>
            ih element (List.mem_cons_of_mem _ member) otherFaithful equal)
          (fun element member => rightFaithful element (List.mem_cons_of_mem _ member)) tails]

/-- Function chains whose results are not function types are equal only
componentwise. -/
private theorem functionChain_injective :
    ∀ {left right : List CheckerTy} {leftResult rightResult : CheckerTy},
      headName leftResult ≠ some (.mk [] "->") → headName rightResult ≠ some (.mk [] "->") →
      functionChain left leftResult = functionChain right rightResult →
      left = right ∧ leftResult = rightResult
  | [], [], _, _, _, _, equal => ⟨rfl, equal⟩
  | [], first :: rest, leftResult, rightResult, leftNot, _, equal => by
      exfalso
      apply leftNot
      have resultEq : leftResult = functionChain (first :: rest) rightResult := equal
      rw [resultEq]
      exact headName_functionChain (by simp)
  | first :: rest, [], leftResult, rightResult, _, rightNot, equal => by
      exfalso
      apply rightNot
      have resultEq : rightResult = functionChain (first :: rest) leftResult := equal.symm
      rw [resultEq]
      exact headName_functionChain (by simp)
  | leftHead :: leftTail, rightHead :: rightTail, _, _, leftNot, rightNot, equal => by
      simp only [functionChain, List.foldr_cons, Mettapedia.Languages.OpenTheory.Ty.function,
        Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq, true_and] at equal
      obtain ⟨heads, tails, -⟩ := equal
      obtain ⟨tailsEqual, results⟩ := functionChain_injective leftNot rightNot tails
      exact ⟨by rw [heads, tailsEqual], results⟩

private theorem map_readingType_injective :
    ∀ {left right : List Atom},
      (∀ element ∈ left, ∀ {other : Atom}, Faithful other →
        readingType naming element = readingType naming other → element = other) →
      (∀ element ∈ right, Faithful element) →
      left.map (readingType naming) = right.map (readingType naming) → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by simp at equal
  | _ :: _, [], _, _, equal => by simp at equal
  | first :: rest, rightFirst :: rightRest, ih, rightFaithful, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      rw [ih first (by simp) (rightFaithful rightFirst (by simp)) equal.1,
        map_readingType_injective
          (fun element member {other} otherFaithful equal =>
            ih element (List.mem_cons_of_mem _ member) otherFaithful equal)
          (fun element member => rightFaithful element (List.mem_cons_of_mem _ member)) equal.2]

/-- Is the atom a leaf symbol or literal? -/
private def IsLeaf (atom : Atom) : Prop :=
  (∀ atoms, atom ≠ .expression atoms) ∧ ∀ name, atom ≠ .var name

/-- **The checker reads faithful atoms injectively.** -/
theorem readingType_injective {left right : Atom} (leftFaithful : Faithful left)
    (rightFaithful : Faithful right)
    (equal : readingType naming left = readingType naming right) : left = right := by
  have leafCase : ∀ {leaf other : Atom}, Faithful leaf → IsLeaf leaf → Faithful other →
      .op (leafOperator naming leaf) [] = readingType naming other → leaf = other := by
    intro leaf other leafFaithful leafIsLeaf otherFaithful equal
    cases otherFaithful with
    | symbol notArrow notUndefined =>
        simp only [readingType, leafOperator, typeOperator,
          Mettapedia.Languages.OpenTheory.Ty.op.injEq,
          Mettapedia.Languages.OpenTheory.TypeOp.mk.injEq,
          Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and, and_true] at equal
        exact naming.leaf_injective leafFaithful (.symbol notArrow notUndefined)
          leafIsLeaf.1 (fun _ equal => (by cases equal)) leafIsLeaf.2 (fun _ equal => (by cases equal))
          (he_cancel equal)
    | grounded value =>
        simp only [readingType, leafOperator, typeOperator,
          Mettapedia.Languages.OpenTheory.Ty.op.injEq,
          Mettapedia.Languages.OpenTheory.TypeOp.mk.injEq,
          Mettapedia.Languages.OpenTheory.Name.mk.injEq, true_and, and_true] at equal
        exact naming.leaf_injective leafFaithful (.grounded value)
          leafIsLeaf.1 (fun _ equal => (by cases equal)) leafIsLeaf.2 (fun _ equal => (by cases equal))
          (he_cancel equal)
    | var name => simp [readingType] at equal
    | arrow function nonempty _ _ _ _ _ =>
        rw [readingType_arrow naming function nonempty] at equal
        have heads := congrArg headName equal
        rw [headName_functionChain (by simpa using nonempty), headName_leaf] at heads
        simp only [Option.some.injEq, Mettapedia.Languages.OpenTheory.Name.mk.injEq,
          true_and] at heads
        exact absurd heads (he_ne_function _)
    | product notArrow _ =>
        rw [readingType_product naming notArrow] at equal
        exact absurd equal.symm (productType_ne_leaf naming _ leaf)
  have arrowVar : ∀ {type returnType : Atom} {argumentTypes : List Atom} {name : String},
      FunctionTypeRel type argumentTypes returnType → argumentTypes ≠ [] →
      readingType naming type ≠ readingType naming (.var name) := by
    intro type returnType argumentTypes name function nonempty equal
    rw [readingType_arrow naming function nonempty] at equal
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
    simp [readingType, functionChain, Mettapedia.Languages.OpenTheory.Ty.function] at equal
  have arrowProduct : ∀ {type returnType : Atom} {argumentTypes elements : List Atom},
      FunctionTypeRel type argumentTypes returnType → argumentTypes ≠ [] →
      ¬ArrowShaped (.expression elements) →
      readingType naming type ≠ readingType naming (.expression elements) := by
    intro type returnType argumentTypes elements function nonempty notArrow equal
    rw [readingType_arrow naming function nonempty, readingType_product naming notArrow] at equal
    have heads := congrArg headName equal
    rw [headName_functionChain (by simpa using nonempty)] at heads
    exact headName_productType_ne_function naming elements heads.symm
  have productVar : ∀ {elements : List Atom} {name : String},
      productType naming elements ≠ readingType naming (.var name) := by
    intro elements name equal
    cases elements <;> simp [readingType, productType] at equal
  induction leftFaithful generalizing right with
  | symbol notArrow notUndefined =>
      exact leafCase (.symbol notArrow notUndefined)
        ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ rightFaithful equal
  | grounded value =>
      exact leafCase (.grounded value)
        ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ rightFaithful equal
  | var name =>
      cases rightFaithful with
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
      | arrow function nonempty _ _ _ _ _ => exact absurd equal.symm (arrowVar function nonempty)
      | product notArrow _ =>
          rw [readingType_product naming notArrow] at equal
          exact absurd equal.symm productVar
  | @arrow type returnType argumentTypes function nonempty argumentsFaithful argumentsNotReserved
      returnNotArrow returnNotReserved returnFaithful argumentIH returnIH =>
      have leftFaithful : Faithful type :=
        .arrow function nonempty argumentsFaithful argumentsNotReserved returnNotArrow
          returnNotReserved returnFaithful
      cases rightFaithful with
      | @arrow rightType rightReturn rightArguments rightFunction rightNonempty
          rightArgumentsFaithful _ rightReturnNotArrow _ rightReturnFaithful =>
          rw [readingType_arrow naming function nonempty,
            readingType_arrow naming rightFunction rightNonempty] at equal
          obtain ⟨argumentsEqual, returnsEqual⟩ := functionChain_injective
            (readingType_not_function naming returnFaithful returnNotArrow)
            (readingType_not_function naming rightReturnFaithful rightReturnNotArrow) equal
          have returnEq := returnIH rightReturnFaithful returnsEqual
          have argumentsEq := map_readingType_injective naming
            (fun element member {other} otherFaithful equal =>
              argumentIH element member otherFaithful equal)
            rightArgumentsFaithful argumentsEqual
          rw [FunctionTypeRel] at function rightFunction
          rw [function, rightFunction, argumentsEq, returnEq]
      | symbol notArrow notUndefined =>
          exact (leafCase (.symbol notArrow notUndefined)
            ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ leftFaithful
            equal.symm).symm
      | grounded value =>
          exact (leafCase (.grounded value)
            ⟨fun _ equal => (by cases equal), fun _ equal => (by cases equal)⟩ leftFaithful
            equal.symm).symm
      | var name => exact absurd equal (arrowVar function nonempty)
      | product notArrow _ => exact absurd equal (arrowProduct function nonempty notArrow)
  | @product elements notArrow elementsFaithful elementIH =>
      have leftFaithful : Faithful (.expression elements) := .product notArrow elementsFaithful
      rw [readingType_product naming notArrow] at equal
      cases rightFaithful with
      | product rightNotArrow rightElementsFaithful =>
          rw [readingType_product naming rightNotArrow] at equal
          rw [productType_injective_of naming
            (fun element member {other} otherFaithful equal =>
              elementIH element member otherFaithful equal)
            rightElementsFaithful equal]
      | symbol notArrowName notUndefined =>
          exact absurd equal (productType_ne_leaf naming _ _)
      | grounded value => exact absurd equal (productType_ne_leaf naming _ _)
      | var name => exact absurd equal productVar
      | arrow function nonempty _ _ _ _ _ =>
          rw [← readingType_product naming notArrow] at equal
          exact absurd equal.symm (arrowProduct function nonempty notArrow)

/-! ## Faithful readings -/

/-- HOL types of the contract that the checker reads faithfully: arrows of
such types and base types of faithful non-arrow atoms.  The proposition type
is not the reading of any HE type. -/
inductive FaithfulReading : Ty Atom → Prop where
  | base {atom : Atom} : Faithful atom → ¬ArrowShaped atom → FaithfulReading (.base atom)
  | arr {domain codomain : Ty Atom} : FaithfulReading domain → FaithfulReading codomain →
      FaithfulReading (.arr domain codomain)

theorem guestTy_base {atom : Atom} (notArrow : ¬ArrowShaped atom) :
    guestTy naming (.base atom) = readingType naming atom := by
  cases atom with
  | symbol name => rfl
  | var name => rfl
  | grounded value => rfl
  | expression atoms =>
      simp only [guestTy, baseType]
      exact (readingType_product naming notArrow).symm

theorem FaithfulReading.foldr :
    ∀ (types : List (Ty Atom)) {result : Ty Atom},
      (∀ type ∈ types, FaithfulReading type) → FaithfulReading result →
        FaithfulReading (types.foldr Ty.arr result)
  | [], _, _, result => result
  | first :: rest, _, all, result =>
      .arr (all first (by simp))
        (FaithfulReading.foldr rest (fun other member => all other (List.mem_cons_of_mem _ member))
          result)

/-- The reading of a faithful atom reads faithfully. -/
theorem FaithfulReading.of_toTy {atom : Atom} (faithful : Faithful atom) :
    FaithfulReading (toTy atom) := by
  induction faithful with
  | symbol notArrow notUndefined =>
      rw [toTy_of_not_arrowShaped (by rintro ⟨_, equal⟩; cases equal)]
      exact .base (.symbol notArrow notUndefined) (by rintro ⟨_, equal⟩; cases equal)
  | var name =>
      rw [toTy_of_not_arrowShaped (by rintro ⟨_, equal⟩; cases equal)]
      exact .base (.var name) (by rintro ⟨_, equal⟩; cases equal)
  | grounded value =>
      rw [toTy_of_not_arrowShaped (by rintro ⟨_, equal⟩; cases equal)]
      exact .base (.grounded value) (by rintro ⟨_, equal⟩; cases equal)
  | @arrow type returnType argumentTypes function nonempty _ _ _ _ _ argumentIH returnIH =>
      rw [toTy_of_functionType function nonempty, spineTy_eq_foldr]
      refine FaithfulReading.foldr _ ?_ returnIH
      intro reading member
      obtain ⟨argumentType, argumentMember, rfl⟩ := List.mem_map.mp member
      exact argumentIH argumentType argumentMember
  | product notArrow elementsFaithful _ =>
      rw [toTy_of_not_arrowShaped notArrow]
      exact .base (.product notArrow elementsFaithful) notArrow

theorem guestTy_ne_function_of_base {atom : Atom} (faithful : Faithful atom)
    (notArrow : ¬ArrowShaped atom) (domain codomain : CheckerTy) :
    guestTy naming (.base atom) ≠ Mettapedia.Languages.OpenTheory.Ty.function domain codomain := by
  intro equal
  have heads := congrArg headName equal
  rw [guestTy_base naming notArrow, headName_function] at heads
  exact readingType_not_function naming faithful notArrow heads

/-- **The checker separates faithful readings.** -/
theorem guestTy_injective {left right : Ty Atom} (leftReading : FaithfulReading left)
    (rightReading : FaithfulReading right) (equal : guestTy naming left = guestTy naming right) :
    left = right := by
  induction leftReading generalizing right with
  | @base atom faithful notArrow =>
      cases rightReading with
      | @base other otherFaithful otherNotArrow =>
          rw [guestTy_base naming notArrow, guestTy_base naming otherNotArrow] at equal
          rw [readingType_injective naming faithful otherFaithful equal]
      | arr _ _ =>
          exact absurd equal (guestTy_ne_function_of_base naming faithful notArrow _ _)
  | arr _ _ domainIH codomainIH =>
      cases rightReading with
      | @base other otherFaithful otherNotArrow =>
          exact absurd equal.symm (guestTy_ne_function_of_base naming otherFaithful otherNotArrow _ _)
      | arr rightDomain rightCodomain =>
          simp only [guestTy, Mettapedia.Languages.OpenTheory.Ty.function,
            Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq, true_and] at equal
          rw [domainIH rightDomain equal.1, codomainIH rightCodomain equal.2.1]

/-- A checker function type is the reading of an arrow. -/
theorem guestTy_eq_function {type : Ty Atom} (reading : FaithfulReading type)
    {domain codomain : CheckerTy}
    (equal : guestTy naming type = Mettapedia.Languages.OpenTheory.Ty.function domain codomain) :
    ∃ typeDomain typeCodomain, type = .arr typeDomain typeCodomain ∧
      guestTy naming typeDomain = domain ∧ guestTy naming typeCodomain = codomain := by
  cases reading with
  | @base atom faithful notArrow =>
      exact absurd equal (guestTy_ne_function_of_base naming faithful notArrow _ _)
  | @arr typeDomain typeCodomain _ _ =>
      simp only [guestTy, Mettapedia.Languages.OpenTheory.Ty.function,
        Mettapedia.Languages.OpenTheory.Ty.op.injEq, List.cons.injEq, true_and] at equal
      exact ⟨typeDomain, typeCodomain, rfl, equal.1, equal.2.1⟩

/-! ## Leaves -/

/-- Every symbol and literal occurring in the atom is among `leaves`. -/
def LeavesWithin (leaves : Atom → Prop) (atom : Atom) : Prop :=
  ∀ leaf, Subatom leaf atom → (∀ atoms, leaf ≠ .expression atoms) → (∀ name, leaf ≠ .var name) →
    leaves leaf

theorem LeavesWithin.of_child {leaves : Atom → Prop} {atom : Atom} {atoms : List Atom}
    (within : LeavesWithin leaves (.expression atoms)) (member : atom ∈ atoms) :
    LeavesWithin leaves atom :=
  fun leaf occurs => within leaf (.child member occurs)

/-- Every base type of a HOL type has its leaves among `leaves`. -/
def TyLeavesWithin (leaves : Atom → Prop) : Ty Atom → Prop
  | .prop => True
  | .base atom => LeavesWithin leaves atom
  | .arr domain codomain => TyLeavesWithin leaves domain ∧ TyLeavesWithin leaves codomain

/-! ## Constants and terms -/

/-- A constant of the checker without definition. -/
def constOf (name : String) : CheckerConst := .mk (.mk [] name) .undefined

/-- The checker constant of a contract name. -/
def nameConst : Name → CheckerConst
  | .declared constant _ => constOf ("he:" ++ naming.leaf constant)
  | .pair _ => constOf ","
  | .fst _ => constOf "FST"
  | .snd _ => constOf "SND"
  | .one => constOf "one"

/-- The contract type a name is read at, whatever the space. -/
def nameReading : Name → Ty Atom
  | .declared _ instanceType => toTy instanceType
  | .pair (component :: components) =>
      .arr (toTy component) (.arr (productTy components) (productTy (component :: components)))
  | .fst (component :: components) => .arr (productTy (component :: components)) (toTy component)
  | .snd (component :: components) =>
      .arr (productTy (component :: components)) (productTy components)
  | .one => productTy []
  | .pair [] | .fst [] | .snd [] => .prop

theorem nameType_eq_nameReading {space : Space} {name : Name} {type : Ty Atom}
    (lookup : nameType space name = some type) : type = nameReading name := by
  cases name with
  | declared constant instanceType =>
      exact (nameType_declared_eq_some_iff.mp lookup).2
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

/-- The checker's source term of a contract term: every constant occurrence
carries the checker type of its contract type. -/
def guestTerm : ContractTerm → CheckerTerm
  | .constant name => .const (nameConst naming name) (guestTy naming (nameReading name))
  | .app function argument => .app (guestTerm function) (guestTerm argument)
  | _ => .const (constOf "") (.op unitOperator [])

/-- Every constant of a contract term has a contract type that reads
faithfully, with its leaves among `leaves`. -/
def WellNamed (space : Space) (leaves : Atom → Prop) : ContractTerm → Prop
  | .constant name => ∃ type, nameType space name = some type ∧ FaithfulReading type ∧
      TyLeavesWithin leaves type
  | .app function argument => WellNamed space leaves function ∧ WellNamed space leaves argument
  | _ => False

/-! ## The checker signature of a space -/

/-- A checker type variable. -/
def tyvar (name : String) : CheckerTy := .var (.mk [] name)

/-- A checker signature for a set of leaves declares those leaf type
operators, the pair and unit types and the function type at their arities,
every declared constant of the space at the reading of its declared type, and
the pair signature. -/
structure CheckerSignature (space : Space) (leaves : Atom → Prop)
    (signature : Mettapedia.Languages.OpenTheory.SignatureFormation.Signature) : Prop where
  leafArity : ∀ leaf, leaves leaf → signature.typeOperators (leafOperator naming leaf) = some 0
  prodArity : signature.typeOperators prodOperator = some 2
  unitArity : signature.typeOperators unitOperator = some 0
  functionArity :
    signature.typeOperators Mettapedia.Languages.OpenTheory.TypeOp.function = some 2
  declared : ∀ constant scheme, declaredType? space constant = some scheme →
    signature.constants (constOf ("he:" ++ naming.leaf constant)) =
      some (readingType naming scheme)
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

private theorem formed_spine :
    ∀ (components : List Atom), components ≠ [] → (∀ atom ∈ components,
      TypeFormed signature (readingType naming atom) ∧ Resolved signature (readingType naming atom)) →
      TypeFormed signature (spineType naming components) ∧
        Resolved signature (spineType naming components)
  | [], nonempty, _ => absurd rfl nonempty
  | [last], _, all => by
      simp only [spineType]
      exact all last (by simp)
  | first :: second :: rest, _, all => by
      simp only [spineType]
      exact formed_function checker (all first (by simp))
        (formed_spine (second :: rest) (by simp)
          (fun other member => all other (List.mem_cons_of_mem _ member)))

/-- The checker type of an atom whose leaves are declared is resolved and
formed. -/
theorem readingType_formed (atom : Atom) (within : LeavesWithin leaves atom) :
    TypeFormed signature (readingType naming atom) ∧ Resolved signature (readingType naming atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms => ∀ atom ∈ atoms,
      LeavesWithin leaves atom →
        TypeFormed signature (readingType naming atom) ∧
          Resolved signature (readingType naming atom)) with
  | symbol name =>
      simp only [readingType]
      exact formed_op (checker.leafArity _ (within _ .refl (fun _ equal => by cases equal)
        (fun _ equal => by cases equal))) (by simp)
  | grounded value =>
      simp only [readingType]
      exact formed_op (checker.leafArity _ (within _ .refl (fun _ equal => by cases equal)
        (fun _ equal => by cases equal))) (by simp)
  | var name =>
      simp only [readingType]
      constructor
      · rw [TypeFormed]; trivial
      · rw [Resolved]
  | expression atoms ih =>
      have children : ∀ atom ∈ atoms, TypeFormed signature (readingType naming atom) ∧
          Resolved signature (readingType naming atom) :=
        fun atom member => ih atom member (within.of_child member)
      simp only [readingType]
      by_cases arrowForm : ∃ first second rest, atoms = .symbol "->" :: first :: second :: rest
      · obtain ⟨first, second, rest, rfl⟩ := arrowForm
        simp only [expressionType]
        exact formed_spine checker (first :: second :: rest) (by simp)
          (fun other member => children other (List.mem_cons_of_mem _ member))
      · have typeEq : expressionType naming atoms = productType naming atoms := by
          unfold expressionType
          split
          · exact absurd ⟨_, _, _, rfl⟩ arrowForm
          · simp only [productType]
          · simp only [productType]
        rw [typeEq]
        exact formed_product checker atoms children
  | nil => rename_i member _; cases member
  | cons head tail headIH tailIH =>
      rename_i atom member within'
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH within'
      · exact tailIH atom member within'

/-- The checker type of a faithful reading with declared leaves is resolved
and formed. -/
theorem guestTy_formed {type : Ty Atom} (reading : FaithfulReading type)
    (within : TyLeavesWithin leaves type) :
    TypeFormed signature (guestTy naming type) ∧ Resolved signature (guestTy naming type) := by
  induction reading with
  | @base atom _ notArrow =>
      rw [guestTy_base naming notArrow]
      exact readingType_formed checker atom within
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

private theorem spine_applyTypeValuation (valuation : String → Atom) (names : List String) :
    ∀ (components : List Atom),
      (∀ atom ∈ components, (checkerSubst naming valuation names).apply (readingType naming atom) =
        readingType naming (applyTypeValuation valuation atom)) →
      (checkerSubst naming valuation names).apply (spineType naming components) =
        spineType naming (components.map (applyTypeValuation valuation))
  | [], _ => by simp [spineType, leafOperator]
  | [last], all => by
      simp only [spineType, List.map_cons, List.map_nil]
      exact all last (by simp)
  | first :: second :: rest, all => by
      simp only [spineType, List.map_cons,
        Mettapedia.Languages.OpenTheory.TypeSubst.apply_function]
      rw [all first (by simp)]
      have restEq := spine_applyTypeValuation valuation names (second :: rest)
        (fun atom member => all atom (List.mem_cons_of_mem _ member))
      simp only [List.map_cons] at restEq
      rw [restEq]

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

private theorem readingType_arrowForm (first second : Atom) (rest : List Atom) :
    readingType naming (.expression (.symbol "->" :: first :: second :: rest)) =
      spineType naming (first :: second :: rest) := by
  simp only [readingType, expressionType]

private theorem applyTypeValuation_expression (valuation : String → Atom) (atoms : List Atom) :
    applyTypeValuation valuation (.expression atoms) =
      .expression (atoms.map (applyTypeValuation valuation)) := by
  simp [applyTypeValuation]

/-- **The checker reads an instance as the substituted reading.**  When no
type variable takes the arrow symbol as its value, applying a valuation and
reading commute with the checker's substitution of the valued variables. -/
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
      by_cases arrowForm : ∃ first second rest, atoms = .symbol "->" :: first :: second :: rest
      · obtain ⟨first, second, rest, rfl⟩ := arrowForm
        have headEq : applyTypeValuation valuation (.symbol "->") = .symbol "->" := by
          simp [applyTypeValuation]
        simp only [List.map_cons, headEq]
        rw [readingType_arrowForm, readingType_arrowForm]
        have componentsEq := spine_applyTypeValuation naming valuation names
          (first :: second :: rest) (fun atom member => all atom (List.mem_cons_of_mem _ member))
        simp only [List.map_cons] at componentsEq
        exact componentsEq
      · have notArrowMapped : ¬∃ first second rest,
            atoms.map (applyTypeValuation valuation) = .symbol "->" :: first :: second :: rest := by
          rintro ⟨first, second, rest, mapped⟩
          apply arrowForm
          match atoms, mapped with
          | [], mapped => simp at mapped
          | [_], mapped => simp at mapped
          | [_, _], mapped => simp at mapped
          | head :: atom₁ :: atom₂ :: tail, mapped =>
              simp only [List.map_cons, List.cons.injEq] at mapped
              refine ⟨atom₁, atom₂, tail, ?_⟩
              cases head with
              | symbol name =>
                  simp only [applyTypeValuation, Atom.symbol.injEq] at mapped
                  rw [mapped.1]
              | var name =>
                  simp only [applyTypeValuation] at mapped
                  exact absurd mapped.1 (notArrow name)
              | grounded value => simp [applyTypeValuation] at mapped
              | expression inner => simp [applyTypeValuation] at mapped
        have typeEq : ∀ list : List Atom,
            (¬∃ first second rest, list = .symbol "->" :: first :: second :: rest) →
              readingType naming (.expression list) = productType naming list := by
          intro list notForm
          simp only [readingType]
          unfold expressionType
          split
          · exact absurd ⟨_, _, _, rfl⟩ notForm
          · simp only [productType]
          · simp only [productType]
        rw [typeEq atoms arrowForm, typeEq _ notArrowMapped]
        exact product_applyTypeValuation naming valuation names atoms all
  | nil => rename_i member; cases member
  | cons head tail headIH tailIH =>
      rename_i covered atom member
      simp only [TypeSubst.typeVarsList, List.mem_append] at covered
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH (fun name inHead => covered name (Or.inl inHead))
      · exact tailIH (fun name inTail => covered name (Or.inr inTail)) atom member

/-! ## The checker's typing is contract typing -/

open Mettapedia.Languages.OpenTheory.SignatureFormation (AnnotationsFormed ConstantInstance)
open Mettapedia.Languages.HOLLight.MeTTa.TermReading (SourceResolved)

/-- The checker's typing of a closed source term: it is resolved, its
annotations are formed, and its type is the given one. -/
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
        ∃ type, FaithfulReading type ∧ inferred = guestTy naming type ∧
          ApplicativeTyped (nameType space) term type := by
  induction applicative with
  | constant name =>
      intro wellNamed inferred computed
      obtain ⟨type, lookup, reading, _⟩ := wellNamed
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

/-- The checker admits every contract name at its contract type. -/
theorem constantInstance_nameConst {name : Name} {type : Ty Atom}
    (lookup : nameType space name = some type) :
    ConstantInstance signature (nameConst naming name) (guestTy naming (nameReading name)) := by
  cases name with
  | declared constant instanceType =>
      obtain ⟨⟨contract, scheme, declared, valuation, valuesFaithful, instanceEq⟩, _⟩ :=
        nameType_declared_eq_some_iff.mp lookup
      refine ⟨readingType naming scheme, checkerSubst naming valuation (TypeSubst.typeVars scheme),
        checker.declared constant scheme declared, ?_⟩
      rw [readingType_applyTypeValuation naming valuation
          (fun name equal => by
            have faithful := valuesFaithful name
            rw [equal] at faithful
            cases faithful with
            | symbol notArrow _ => exact notArrow rfl
            | arrow function => simp [FunctionTypeRel] at function)
          (TypeSubst.typeVars scheme) scheme (fun _ member => member),
        instanceEq]
      exact (guestTy_toTy naming instanceType).symm
  | pair components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          refine ⟨_, ⟨[(.mk [] "A", readingType naming component),
            (.mk [] "B", productType naming components)]⟩, checker.pairSchema, ?_⟩
          obtain ⟨first, second⟩ := tyvar_lookup (readingType naming component)
            (productType naming components)
          simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
            Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_cons, List.map_nil,
            first, second, nameReading, guestTy, baseType, productTy, productType,
            guestTy_toTy]
  | fst components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          refine ⟨_, ⟨[(.mk [] "A", readingType naming component),
            (.mk [] "B", productType naming components)]⟩, checker.fstSchema, ?_⟩
          obtain ⟨first, second⟩ := tyvar_lookup (readingType naming component)
            (productType naming components)
          simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
            Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_cons, List.map_nil,
            first, second, nameReading, guestTy, baseType, productTy, productType,
            guestTy_toTy]
  | snd components =>
      cases components with
      | nil => simp [nameType] at lookup
      | cons component components =>
          refine ⟨_, ⟨[(.mk [] "A", readingType naming component),
            (.mk [] "B", productType naming components)]⟩, checker.sndSchema, ?_⟩
          obtain ⟨first, second⟩ := tyvar_lookup (readingType naming component)
            (productType naming components)
          simp only [Mettapedia.Languages.OpenTheory.TypeSubst.apply_function,
            Mettapedia.Languages.OpenTheory.TypeSubst.apply_op, List.map_cons, List.map_nil,
            first, second, nameReading, guestTy, baseType, productTy, productType]
  | one =>
      refine ⟨_, Mettapedia.Languages.OpenTheory.TypeSubst.empty, checker.oneSchema, ?_⟩
      simp [nameReading, guestTy, baseType, productTy, productType]

/-- Every well-named contract typing is resolved and formed in the checker. -/
theorem guestTerm_formed :
    ∀ {term : ContractTerm} {type : Ty Atom},
      ApplicativeTyped (nameType space) term type → WellNamed space leaves term →
        SourceResolved signature (guestTerm naming term) ∧
          AnnotationsFormed signature ((guestTerm naming term).toDB [])
  | _, _, .constant lookup, ⟨type, lookup', reading, within⟩ => by
      rw [lookup] at lookup'
      cases lookup'
      have typeEq := nameType_eq_nameReading lookup
      have formed := guestTy_formed checker (typeEq ▸ reading) (typeEq ▸ within)
      constructor
      · simp only [guestTerm]
        rw [SourceResolved]
        exact formed.2
      · simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.toDB.eq_1]
        exact .constant formed.1 (constantInstance_nameConst checker lookup)
  | _, _, .app functionTyped argumentTyped, ⟨functionNamed, argumentNamed⟩ => by
      obtain ⟨functionResolved, functionFormed⟩ := guestTerm_formed functionTyped functionNamed
      obtain ⟨argumentResolved, argumentFormed⟩ := guestTerm_formed argumentTyped argumentNamed
      constructor
      · simp only [guestTerm]
        rw [SourceResolved]
        exact ⟨functionResolved, argumentResolved⟩
      · simp only [guestTerm, Mettapedia.Languages.OpenTheory.SourceTerm.toDB.eq_3]
        exact .app functionFormed argumentFormed

/-- **The checker decides contract typing.**  For a well-named contract term
and a faithfully read type, the checker's typing of the translation at the
translated type is contract typing. -/
theorem guestTyped_iff {term : ContractTerm} (applicative : Applicative term)
    (wellNamed : WellNamed space leaves term) {type : Ty Atom} (reading : FaithfulReading type) :
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
translation of every well-named contract typing at a faithful reading. -/
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
contract typing at any faithful reading. -/
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
    (wellNamed : WellNamed space leaves term) {type : Ty Atom} (reading : FaithfulReading type)
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
