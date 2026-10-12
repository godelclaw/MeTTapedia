import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
import Mettapedia.Logic.HOL.Syntax.NamedElaboration

/-!
# The static arrow fragment of HE typing and its Church-style HOL image

HE types an atom through its `(: atom type)` declarations, and an
application `(f a₁ … aₙ)` through an arrow `(-> A₁ … Aₙ R)` declared for its
head.  Inside the static arrow fragment this is exactly simply typed
application in Church-style HOL:

* a static type is a ground arrow `(-> A₁ … Aₙ R)` with `n ≥ 1`, static
  argument types and a non-arrow return, or a ground non-arrow atom that is
  not one of the reserved type names and does not mention `%Undefined%`;
* a static type translates to the HOL simple type
  `⟦A₁⟧ ⇒ … ⇒ ⟦Aₙ⟧ ⇒ ⟦R⟧` over the base types `Ty Atom`; a non-arrow atom is
  an opaque base type, so `(List Nat)` is one base;
* a symbol with exactly one declaration, or a grounded literal with its
  intrinsic type, is a HOL constant of the translated type;
* an expression `(f a₁ … aₙ)` translates to the curried HOL application
  `f a₁ … aₙ`, elaborated by `NamedElaboration.infer`.

The fragment requires every application to be saturated: the head's declared
arrow has exactly as many argument types as the expression has arguments.
HE never types a partial application by an arrow, while curried HOL does, so
saturation is a genuine boundary rather than a convenience.  Returns are
non-arrows for the same reason: `(-> A (-> B C))` and `(-> A B C)` have the
same curried HOL type but different HE arities.

This module only states the fragment and the translation.  The agreement
theorems are in `TypeGrounding.SimpleAgreement`.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Spec.Type
open Spec.Type.Presentation

/-! ## Subatoms -/

/-- `Subatom sub atom`: `sub` occurs in `atom`, the atom itself included. -/
inductive Subatom (sub : Atom) : Atom → Prop where
  | refl : Subatom sub sub
  | child {atom : Atom} {atoms : List Atom} :
      atom ∈ atoms → Subatom sub atom → Subatom sub (.expression atoms)

theorem Subatom.trans {first second third : Atom}
    (inner : Subatom first second) (outer : Subatom second third) :
    Subatom first third := by
  induction outer with
  | refl => exact inner
  | child member _ ih => exact .child member ih

theorem Subatom.of_mem {atom : Atom} {atoms : List Atom}
    (member : atom ∈ atoms) : Subatom atom (.expression atoms) :=
  .child member .refl

theorem Subatom.symbol_eq {sub : Atom} {name : String}
    (occurs : Subatom sub (.symbol name)) : sub = .symbol name := by
  cases occurs
  rfl

theorem Subatom.grounded_eq {sub : Atom} {value : GroundedValue}
    (occurs : Subatom sub (.grounded value)) : sub = .grounded value := by
  cases occurs
  rfl

theorem Subatom.expression_cases {sub : Atom} {atoms : List Atom}
    (occurs : Subatom sub (.expression atoms)) :
    sub = .expression atoms ∨ ∃ atom ∈ atoms, Subatom sub atom := by
  cases occurs with
  | refl => exact Or.inl rfl
  | child member inner => exact Or.inr ⟨_, member, inner⟩

/-- No `%Undefined%` occurs anywhere in an atom.  `%Undefined%` is HE's
gradual wildcard at every depth, so it has no place in a static type. -/
def UndefinedFree (atom : Atom) : Prop :=
  ¬Subatom Atom.undefinedType atom

theorem UndefinedFree.of_child {atom : Atom} {atoms : List Atom}
    (free : UndefinedFree (.expression atoms)) (member : atom ∈ atoms) :
    UndefinedFree atom :=
  fun occurs => free (.child member occurs)

theorem UndefinedFree.ne {atom : Atom} (free : UndefinedFree atom) :
    atom ≠ Atom.undefinedType := by
  rintro rfl
  exact free .refl

/-! ## Static types -/

/-- Symbols with a reserved meaning at the top of an HE type: the two gradual
wildcards `%Undefined%` and `Atom`, the meta-types, and the arrow head. -/
def reservedTypeNames : List String :=
  ["%Undefined%", "Atom", "Symbol", "Variable", "Expression", "Grounded", "->"]

/-- The atom is one of the reserved type symbols. -/
def TopReserved (type : Atom) : Prop :=
  ∃ name ∈ reservedTypeNames, type = .symbol name

/-- The atom has the syntactic shape of an arrow, malformed ones included. -/
def ArrowShaped (type : Atom) : Prop :=
  ∃ components, type = .expression (.symbol "->" :: components)

theorem ArrowShaped.of_functionType {type returnType : Atom}
    {argumentTypes : List Atom}
    (function : FunctionTypeRel type argumentTypes returnType) :
    ArrowShaped type :=
  ⟨_, function⟩

/-- Static HE types.  A base is a ground non-arrow atom outside the reserved
names, with no `%Undefined%` at any depth; an arrow has at least one
argument, static components and a non-arrow return. -/
inductive StaticType : Atom → Prop where
  | base {type : Atom} :
      ¬ArrowShaped type → ¬TopReserved type →
      UndefinedFree type → TypeSubst.typeVars type = [] →
      StaticType type
  | arrow {type returnType : Atom} {argumentTypes : List Atom} :
      FunctionTypeRel type argumentTypes returnType →
      argumentTypes ≠ [] →
      (∀ argumentType ∈ argumentTypes, StaticType argumentType) →
      ¬ArrowShaped returnType → StaticType returnType →
      StaticType type

theorem StaticType.not_topReserved {type : Atom} (static : StaticType type) :
    ¬TopReserved type := by
  cases static with
  | base _ notReserved _ _ => exact notReserved
  | arrow function _ _ _ _ =>
      rintro ⟨name, _, rfl⟩
      simp [FunctionTypeRel] at function

theorem StaticType.ne_undefined {type : Atom} (static : StaticType type) :
    type ≠ Atom.undefinedType := by
  intro equal
  exact static.not_topReserved ⟨"%Undefined%", by simp [reservedTypeNames], equal⟩

theorem StaticType.ne_atom {type : Atom} (static : StaticType type) :
    type ≠ Atom.atomType := by
  intro equal
  exact static.not_topReserved ⟨"Atom", by simp [reservedTypeNames], equal⟩

/-- An arrow-shaped static type is a genuine arrow with nonempty arguments. -/
theorem StaticType.arrow_parts {type : Atom} (static : StaticType type)
    (shaped : ArrowShaped type) :
    ∃ argumentTypes returnType,
      FunctionTypeRel type argumentTypes returnType ∧ argumentTypes ≠ [] ∧
        (∀ argumentType ∈ argumentTypes, StaticType argumentType) ∧
        ¬ArrowShaped returnType ∧ StaticType returnType := by
  cases static with
  | base notArrow _ _ _ => exact absurd shaped notArrow
  | arrow function nonempty arguments notArrow returnStatic =>
      exact ⟨_, _, function, nonempty, arguments, notArrow, returnStatic⟩

/-- The argument and return components of a static arrow are the ones its
own constructor recorded. -/
theorem StaticType.of_functionType {type returnType : Atom}
    {argumentTypes : List Atom} (static : StaticType type)
    (function : FunctionTypeRel type argumentTypes returnType) :
    argumentTypes ≠ [] ∧
      (∀ argumentType ∈ argumentTypes, StaticType argumentType) ∧
      ¬ArrowShaped returnType ∧ StaticType returnType := by
  obtain ⟨arguments', return', function', nonempty, arguments, notArrow,
    returnStatic⟩ := static.arrow_parts (.of_functionType function)
  obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique function function'
  exact ⟨nonempty, arguments, notArrow, returnStatic⟩

/-! ## The HOL type of a static type -/

mutual

/-- Translate an HE type to a HOL simple type over the base `Atom`.  An
arrow with at least one argument becomes a curried HOL arrow; every other
atom is an opaque base. -/
def toTy : Atom → Ty Atom
  | .symbol name => .base (.symbol name)
  | .var name => .base (.var name)
  | .grounded value => .base (.grounded value)
  | .expression atoms => expressionTy atoms

/-- The HOL type of the expression with the given elements. -/
def expressionTy : List Atom → Ty Atom
  | .symbol "->" :: components@(_ :: _ :: _) => componentsSpine components
  | atoms => .base (.expression atoms)

/-- The curried arrow of arrow components; the last component is the return
type.  The empty list never arises from `expressionTy`. -/
def componentsSpine : List Atom → Ty Atom
  | [] => .base (.expression [.symbol "->"])
  | [last] => toTy last
  | first :: rest@(_ :: _) => .arr (toTy first) (componentsSpine rest)

end

/-- The curried HOL arrow of argument types ending in a return type. -/
def spineTy (argumentTypes : List Atom) (returnType : Atom) : Ty Atom :=
  argumentTypes.foldr (fun argumentType result => .arr (toTy argumentType) result)
    (toTy returnType)

@[simp] theorem spineTy_nil (returnType : Atom) :
    spineTy [] returnType = toTy returnType := rfl

@[simp] theorem spineTy_cons (argumentType : Atom) (argumentTypes : List Atom)
    (returnType : Atom) :
    spineTy (argumentType :: argumentTypes) returnType =
      .arr (toTy argumentType) (spineTy argumentTypes returnType) := rfl

/-- The spine is the right fold of `Ty.arr` over the translated argument
types. -/
theorem spineTy_eq_foldr (argumentTypes : List Atom) (returnType : Atom) :
    spineTy argumentTypes returnType =
      (argumentTypes.map toTy).foldr Ty.arr (toTy returnType) := by
  induction argumentTypes with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem componentsSpine_append (argumentTypes : List Atom) (returnType : Atom) :
    componentsSpine (argumentTypes ++ [returnType]) = spineTy argumentTypes returnType := by
  induction argumentTypes with
  | nil => simp [componentsSpine]
  | cons first rest ih =>
      cases rest with
      | nil => simp [componentsSpine]
      | cons second rest =>
          simp only [List.cons_append] at ih ⊢
          rw [componentsSpine, ih]
          rfl

/-- A declared arrow with at least one argument translates to its curried
spine. -/
theorem toTy_of_functionType {type returnType : Atom}
    {argumentTypes : List Atom}
    (function : FunctionTypeRel type argumentTypes returnType)
    (nonempty : argumentTypes ≠ []) :
    toTy type = spineTy argumentTypes returnType := by
  rw [FunctionTypeRel] at function
  subst type
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  rw [← componentsSpine_append]
  obtain ⟨second, tail, split⟩ :
      ∃ second tail, rest ++ [returnType] = second :: tail := by
    cases rest with
    | nil => exact ⟨returnType, [], rfl⟩
    | cons head rest => exact ⟨head, rest ++ [returnType], rfl⟩
  simp only [List.cons_append, split]
  simp [toTy, expressionTy]

/-- A non-arrow atom translates to the base type it names. -/
theorem toTy_of_not_arrowShaped {type : Atom} (notArrow : ¬ArrowShaped type) :
    toTy type = .base type := by
  cases type with
  | symbol name => simp [toTy]
  | var name => simp [toTy]
  | grounded value => simp [toTy]
  | expression atoms =>
      simp only [toTy]
      unfold expressionTy
      split
      · exact absurd ⟨_, rfl⟩ notArrow
      · rfl

/-- The HOL spine of a nonempty argument list is an arrow, never a base. -/
private theorem spineTy_ne_base {argumentTypes : List Atom} {returnType base : Atom}
    (nonempty : argumentTypes ≠ []) :
    spineTy argumentTypes returnType ≠ .base base := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp

private theorem spineTy_injective_aux :
    ∀ {argumentTypes rightArguments : List Atom} {returnType rightReturn : Atom},
      (∀ argumentType ∈ argumentTypes, ∀ {right : Atom}, StaticType right →
        toTy argumentType = toTy right → argumentType = right) →
      (∀ argumentType ∈ rightArguments, StaticType argumentType) →
      (∀ {right : Atom}, StaticType right → toTy returnType = toTy right →
        returnType = right) →
      StaticType rightReturn →
      ¬ArrowShaped returnType → ¬ArrowShaped rightReturn →
      spineTy argumentTypes returnType = spineTy rightArguments rightReturn →
      argumentTypes = rightArguments ∧ returnType = rightReturn
  | [], [], _, _, _, _, returnIH, rightReturnStatic, _, _, equal =>
      ⟨rfl, returnIH rightReturnStatic equal⟩
  | [], _ :: _, _, _, _, _, _, _, notArrow, _, equal => by
      simp only [spineTy_nil, spineTy_cons] at equal
      rw [toTy_of_not_arrowShaped notArrow] at equal
      cases equal
  | _ :: _, [], _, _, _, _, _, _, _, rightNotArrow, equal => by
      simp only [spineTy_nil, spineTy_cons] at equal
      rw [toTy_of_not_arrowShaped rightNotArrow] at equal
      cases equal
  | first :: rest, rightFirst :: rightRest, _, _, argumentIH, rightStatic,
      returnIH, rightReturnStatic, notArrow, rightNotArrow, equal => by
      simp only [spineTy_cons] at equal
      obtain ⟨firstEqual, restEqual⟩ := Ty.arr.inj equal
      have heads : first = rightFirst :=
        argumentIH first (by simp) (rightStatic rightFirst (by simp)) firstEqual
      have tails := spineTy_injective_aux
        (fun argumentType member => argumentIH argumentType
          (List.mem_cons_of_mem _ member))
        (fun argumentType member => rightStatic argumentType
          (List.mem_cons_of_mem _ member))
        returnIH rightReturnStatic notArrow rightNotArrow restEqual
      exact ⟨by rw [heads, tails.1], tails.2⟩

/-- Translation is injective on static types: the HOL type of a static type
determines it. -/
theorem toTy_injective {left right : Atom} (leftStatic : StaticType left)
    (rightStatic : StaticType right) (equal : toTy left = toTy right) :
    left = right := by
  induction leftStatic generalizing right with
  | base notArrow _ _ _ =>
      rw [toTy_of_not_arrowShaped notArrow] at equal
      cases rightStatic with
      | base rightNotArrow _ _ _ =>
          rw [toTy_of_not_arrowShaped rightNotArrow] at equal
          exact (Ty.base.inj equal)
      | arrow function nonempty _ _ _ =>
          rw [toTy_of_functionType function nonempty] at equal
          exact absurd equal.symm (spineTy_ne_base nonempty)
  | arrow function nonempty _ notArrow _ argumentIH returnIH =>
      cases rightStatic with
      | base rightNotArrow _ _ _ =>
          rw [toTy_of_functionType function nonempty,
            toTy_of_not_arrowShaped rightNotArrow] at equal
          exact absurd equal (spineTy_ne_base nonempty)
      | arrow rightFunction rightNonempty rightArgumentStatic rightNotArrow
          rightReturnStatic =>
          rw [toTy_of_functionType function nonempty,
            toTy_of_functionType rightFunction rightNonempty] at equal
          obtain ⟨arguments, returns⟩ := spineTy_injective_aux
            argumentIH rightArgumentStatic returnIH rightReturnStatic
            notArrow rightNotArrow equal
          rw [FunctionTypeRel] at function rightFunction
          rw [function, rightFunction, arguments, returns]

/-! ## Declared constants -/

/-- The unique declared type of a symbol, or the intrinsic type of a grounded
literal.  A symbol with no declaration or with several declarations has
none. -/
def declaredType? (space : Space) : Atom → Option Atom
  | .symbol name =>
      match getAnnotatedTypes space (.symbol name) with
      | [type] => some type
      | _ => none
  | .grounded value => some (getGroundedType value)
  | _ => none

/-- HOL constants of a declaration space, indexed by their HOL type. -/
def SpaceConst (space : Space) (type : Ty Atom) : Type :=
  { constant : Atom // (declaredType? space constant).map toTy = some type }

/-- The HOL signature of a declaration space. -/
def spaceSignature (space : Space) :
    NamedElaboration.Signature Atom (SpaceConst space) :=
  fun constant =>
    match lookup : declaredType? space constant with
    | some type => some ⟨toTy type, ⟨constant, by simp [lookup]⟩⟩
    | none => none

theorem spaceSignature_of_declared {space : Space} {constant type : Atom}
    (declared : declaredType? space constant = some type) :
    spaceSignature space constant =
      some ⟨toTy type, ⟨constant, by simp [declared]⟩⟩ := by
  unfold spaceSignature
  split
  · next type' lookup =>
      rw [declared] at lookup
      cases lookup
      rfl
  · next lookup =>
      rw [declared] at lookup
      cases lookup

theorem spaceSignature_of_undeclared {space : Space} {constant : Atom}
    (undeclared : declaredType? space constant = none) :
    spaceSignature space constant = none := by
  unfold spaceSignature
  split
  · next type lookup =>
      rw [undeclared] at lookup
      cases lookup
  · rfl

/-! ## The HOL term of an HE expression -/

/-- Named HOL terms over HE atoms: types are atoms, constants are atoms. -/
abbrev HOLTerm := NamedElaboration.NamedTerm Atom String Atom

mutual

/-- Translate an HE expression to a named HOL term.  An expression is the
curried application of its head to its arguments. -/
def toNamed : Atom → HOLTerm
  | .symbol name => .constant (.symbol name)
  | .var name => .variable name
  | .grounded value => .constant (.grounded value)
  | .expression [] => .constant (.expression [])
  | .expression (head :: arguments) => applySpine (toNamed head) arguments

/-- Apply a translated function to the translations of the arguments. -/
def applySpine (function : HOLTerm) : List Atom → HOLTerm
  | [] => function
  | argument :: arguments => applySpine (.app function (toNamed argument)) arguments

end

/-- Closed HOL elaboration of an HE expression at the HOL image of a type. -/
def HOLTyped (space : Space) (expression type : Atom) : Prop :=
  ∃ term : Term (SpaceConst space) [] (toTy type),
    NamedElaboration.infer (spaceSignature space)
        (NamedElaboration.BinderNames.nil : NamedElaboration.BinderNames Atom String [])
        (toNamed expression) =
      .ok ⟨toTy type, term⟩

/-! ## The fragment -/

/-- Saturated expressions over static declarations.  A constant is a symbol
with exactly one static declaration or a literal with a static intrinsic
type.  An application has a symbol head whose single static declaration is an
arrow with exactly as many argument types as there are arguments, and no
declaration annotates the application itself (HE lets a direct annotation of
an expression override its inferred type).  The `StateValue` head is excluded
because its typing is a separate runtime rule. -/
inductive SaturatedTerm (space : Space) : Atom → Prop where
  | constant {atom type : Atom} :
      declaredType? space atom = some type → StaticType type →
      SaturatedTerm space atom
  | application {name : String} {arguments argumentTypes : List Atom}
      {type returnType : Atom} :
      name ≠ "StateValue" →
      getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [] →
      declaredType? space (.symbol name) = some type →
      StaticType type →
      FunctionTypeRel type argumentTypes returnType →
      arguments.length = argumentTypes.length →
      (∀ argument ∈ arguments, SaturatedTerm space argument) →
      SaturatedTerm space (.expression (.symbol name :: arguments))

/-! ## Prime's primitive kinds -/

/-- Prime's primitive types, which formation reads as types of kind `Type`
when the space declares nothing for them. -/
def primitiveKindNames : List String :=
  ["Atom", "Symbol", "Variable", "Expression", "Grounded", "Number", "Bool",
    "String", "ErrorType"]

/-- The declaration `(: P Type)` of a primitive type `P`. -/
def kindAnnotation (name : String) : Atom :=
  .expression [.symbol ":", .symbol name, .symbol "Type"]

/-- The space extended by `(: P Type)` for every primitive type `P` that it
does not declare. -/
def withPrimitiveKinds (space : Space) : Space :=
  Space.ofList (space.atoms ++
    ((primitiveKindNames.filter fun name =>
        getAnnotatedTypes space (.symbol name) = []).map kindAnnotation))

theorem getAnnotatedTypes_ofList_append (atoms extra : List Atom) (target : Atom) :
    getAnnotatedTypes (Space.ofList (atoms ++ extra)) target =
      getAnnotatedTypes (Space.ofList atoms) target ++
        getAnnotatedTypes (Space.ofList extra) target := by
  simp [getAnnotatedTypes, Space.ofList, List.filterMap_append]

private theorem getAnnotatedTypes_kindAnnotations :
    ∀ (names : List String), names.Nodup → ∀ name : String,
      getAnnotatedTypes (Space.ofList (names.map kindAnnotation)) (.symbol name) =
        if name ∈ names then [.symbol "Type"] else []
  | [], _, name => by simp [getAnnotatedTypes, Space.ofList]
  | first :: rest, nodup, name => by
      have restEq := getAnnotatedTypes_kindAnnotations rest (List.nodup_cons.mp nodup).2 name
      have split := getAnnotatedTypes_ofList_append [kindAnnotation first]
        (rest.map kindAnnotation) (.symbol name)
      simp only [List.singleton_append] at split
      rw [List.map_cons, split, restEq]
      by_cases same : name = first
      · subst same
        have notInRest : name ∉ rest := (List.nodup_cons.mp nodup).1
        simp [getAnnotatedTypes, Space.ofList, kindAnnotation, notInRest]
      · have firstNe : ¬first = name := fun equal => same equal.symm
        by_cases inRest : name ∈ rest <;>
          simp [getAnnotatedTypes, Space.ofList, kindAnnotation, same, inRest, firstNe]

private theorem primitiveKindNames_nodup : primitiveKindNames.Nodup := by
  decide

/-- Formation's reading of a symbol: a primitive type that the space does
not declare is a constant of type `Type`; every other symbol keeps its
declarations. -/
theorem declaredType?_withPrimitiveKinds_symbol (space : Space) (name : String) :
    declaredType? (withPrimitiveKinds space) (.symbol name) =
      if getAnnotatedTypes space (.symbol name) = [] ∧ name ∈ primitiveKindNames
      then some (.symbol "Type") else declaredType? space (.symbol name) := by
  have extended : getAnnotatedTypes (withPrimitiveKinds space) (.symbol name) =
      getAnnotatedTypes space (.symbol name) ++
        (if getAnnotatedTypes space (.symbol name) = [] ∧ name ∈ primitiveKindNames
          then [.symbol "Type"] else []) := by
    unfold withPrimitiveKinds
    rw [getAnnotatedTypes_ofList_append]
    have kinds := getAnnotatedTypes_kindAnnotations
      (primitiveKindNames.filter fun name => getAnnotatedTypes space (.symbol name) = [])
      (primitiveKindNames_nodup.filter _) name
    rw [kinds]
    by_cases condition :
        getAnnotatedTypes space (.symbol name) = [] ∧ name ∈ primitiveKindNames
    · have member : name ∈ primitiveKindNames.filter
          (fun name => getAnnotatedTypes space (.symbol name) = []) :=
        List.mem_filter.mpr ⟨condition.2, by simpa using condition.1⟩
      rw [if_pos member, if_pos condition]
      rfl
    · have notMember : name ∉ primitiveKindNames.filter
          (fun name => getAnnotatedTypes space (.symbol name) = []) := by
        intro member
        obtain ⟨inNames, empty⟩ := List.mem_filter.mp member
        exact condition ⟨by simpa using empty, inNames⟩
      rw [if_neg notMember, if_neg condition]
      rfl
  simp only [declaredType?]
  rw [extended]
  by_cases condition :
      getAnnotatedTypes space (.symbol name) = [] ∧ name ∈ primitiveKindNames
  · rw [if_pos condition, if_pos condition, condition.1]
    rfl
  · rw [if_neg condition, if_neg condition, List.append_nil]

/-- The primitive kind declarations annotate symbols only. -/
theorem getAnnotatedTypes_withPrimitiveKinds_expression (space : Space)
    (atoms : List Atom) :
    getAnnotatedTypes (withPrimitiveKinds space) (.expression atoms) =
      getAnnotatedTypes space (.expression atoms) := by
  unfold withPrimitiveKinds
  rw [getAnnotatedTypes_ofList_append]
  have none : ∀ names : List String,
      getAnnotatedTypes (Space.ofList (names.map kindAnnotation))
        (.expression atoms) = [] := by
    intro names
    induction names with
    | nil => rfl
    | cons first rest _ =>
        simp [getAnnotatedTypes, Space.ofList, kindAnnotation]
  rw [none, List.append_nil]
  rfl

/-! ## Boundary examples -/

/-- `(-> Nat Nat Nat)` is a static binary arrow. -/
theorem static_binary_arrow :
    StaticType (.expression [.symbol "->", .symbol "Nat", .symbol "Nat", .symbol "Nat"]) := by
  have nat : StaticType (.symbol "Nat") := by
    refine .base ?_ ?_ ?_ ?_
    · rintro ⟨_, equal⟩
      cases equal
    · rintro ⟨name, member, equal⟩
      cases equal
      simp [reservedTypeNames] at member
    · intro occurs
      have equal := Subatom.symbol_eq occurs
      simp [Atom.undefinedType] at equal
    · rfl
  refine .arrow (argumentTypes := [.symbol "Nat", .symbol "Nat"])
    (returnType := .symbol "Nat") rfl (by simp) ?_ ?_ nat
  · intro argumentType member
    have equal : argumentType = .symbol "Nat" := by simpa using member
    subst equal
    exact nat
  · rintro ⟨_, equal⟩
    cases equal

/-- `%Undefined%` is not static, nor is any type containing it. -/
theorem undefined_list_not_static :
    ¬StaticType (.expression [.symbol "List", Atom.undefinedType]) := by
  intro static
  cases static with
  | base _ _ free _ => exact free (.child (by simp) .refl)
  | arrow function _ _ _ _ => simp [FunctionTypeRel] at function

/-- A curried arrow return is outside the fragment: `(-> A (-> B C))`. -/
theorem curried_return_not_static :
    ¬StaticType (.expression [.symbol "->", .symbol "A",
      .expression [.symbol "->", .symbol "B", .symbol "C"]]) := by
  intro static
  have function : FunctionTypeRel
      (.expression [.symbol "->", .symbol "A",
        .expression [.symbol "->", .symbol "B", .symbol "C"]])
      [.symbol "A"] (.expression [.symbol "->", .symbol "B", .symbol "C"]) := rfl
  exact (static.of_functionType function).2.2.1 ⟨_, rfl⟩

/-- The HOL image of `(-> A B C)` is the curried `A ⇒ B ⇒ C`. -/
theorem toTy_binary_arrow :
    toTy (.expression [.symbol "->", .symbol "A", .symbol "B", .symbol "C"]) =
      .arr (.base (.symbol "A")) (.arr (.base (.symbol "B")) (.base (.symbol "C"))) := by
  simp [toTy, expressionTy, componentsSpine]

/-- A compound non-arrow type is one opaque HOL base. -/
theorem toTy_compound_base :
    toTy (.expression [.symbol "List", .symbol "Nat"]) =
      .base (.expression [.symbol "List", .symbol "Nat"]) := by
  simp [toTy, expressionTy]

end Mettapedia.Languages.MeTTa.HE.TypeGrounding
