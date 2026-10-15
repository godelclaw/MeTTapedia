import Mettapedia.Languages.MeTTa.HE.TypeGrounding.SpecBoundary

/-!
# HE's tuple rule as HOL product introduction

The reference runtime types an expression whose head has a non-arrow type
as the tuple of the types of its elements: with `(: Truth Bool)` and
`(: Z Nat)`, `(Truth Z)` has type `(Bool Nat)`.  The published specification
has no such rule (`SpecBoundary.spec_tuple_is_undefined`).

`ReferenceType` is the reference runtime's typing of static expressions:
declared constants, saturated applications of declared arrows, and tuples.
On tuple-free saturated expressions it agrees with the specification's exact
relation (`reference_iff_exact_of_saturated`).

The HOL grounding adds product-introduction constants.  For static component
types `T₀ T₁ … Tₙ` whose head `T₀` is not an arrow, the constant
`tuple [T₀, …, Tₙ]` has type `⟦T₀⟧ ⇒ ⟦T₁⟧ ⇒ … ⇒ ⟦Tₙ⟧ ⇒ (T₀ T₁ … Tₙ)`, where
the tuple type is an opaque HOL base.  An expression is translated with an
annotation that marks some of its subexpressions as tuples; the annotation is
part of the HOL term, and `TupleHOLTyped` asks for some annotation under which
HOL elaborates the term.

`reference_iff_tupleHOLTyped`: on the tuple fragment the reference typing
holds exactly when some annotated HOL term elaborates at the image of the
type.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding.Tuples

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation

/-! ## The reference typing of static expressions -/

mutual

/-- The reference runtime's types of static expressions: declared constants,
saturated applications of declared arrows, and tuples of a non-arrow head. -/
inductive ReferenceType (space : Space) : Atom → Atom → Prop where
  | constant {atom type : Atom} :
      declaredType? space atom = some type → StaticType type →
      ReferenceType space atom type
  | application {name : String} {arguments argumentTypes : List Atom}
      {type returnType : Atom} :
      name ≠ "StateValue" →
      declaredType? space (.symbol name) = some type → StaticType type →
      FunctionTypeRel type argumentTypes returnType →
      ReferenceTypes space arguments argumentTypes →
      ReferenceType space (.expression (.symbol name :: arguments)) returnType
  | tuple {head : Atom} {arguments : List Atom} {headType : Atom}
      {argumentTypes : List Atom} :
      ReferenceType space head headType → ¬ArrowShaped headType →
      ReferenceTypes space arguments argumentTypes →
      ReferenceType space (.expression (head :: arguments))
        (.expression (headType :: argumentTypes))

/-- Pointwise reference typing of a list of expressions. -/
inductive ReferenceTypes (space : Space) : List Atom → List Atom → Prop where
  | nil : ReferenceTypes space [] []
  | cons {argument type : Atom} {arguments types : List Atom} :
      ReferenceType space argument type → ReferenceTypes space arguments types →
      ReferenceTypes space (argument :: arguments) (type :: types)

end

/-- The tuple fragment: static constants, saturated applications of declared
static arrows, and tuples with at least one element after a head that is a
non-arrow constant or an expression.  No declaration annotates an expression
of the fragment. -/
inductive TupleTerm (space : Space) : Atom → Prop where
  | constant {atom type : Atom} :
      declaredType? space atom = some type → StaticType type →
      TupleTerm space atom
  | application {name : String} {arguments argumentTypes : List Atom}
      {type returnType : Atom} :
      name ≠ "StateValue" →
      getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [] →
      declaredType? space (.symbol name) = some type → StaticType type →
      FunctionTypeRel type argumentTypes returnType →
      arguments.length = argumentTypes.length →
      (∀ argument ∈ arguments, TupleTerm space argument) →
      TupleTerm space (.expression (.symbol name :: arguments))
  | tupleConstant {head : Atom} {arguments : List Atom} {type : Atom} :
      getAnnotatedTypes space (.expression (head :: arguments)) = [] →
      declaredType? space head = some type → StaticType type → ¬ArrowShaped type →
      arguments ≠ [] →
      (∀ argument ∈ arguments, TupleTerm space argument) →
      TupleTerm space (.expression (head :: arguments))
  | tupleExpression {headAtoms arguments : List Atom} :
      getAnnotatedTypes space (.expression (.expression headAtoms :: arguments)) = [] →
      TupleTerm space (.expression headAtoms) →
      arguments ≠ [] →
      (∀ argument ∈ arguments, TupleTerm space argument) →
      TupleTerm space (.expression (.expression headAtoms :: arguments))

/-! ## The HOL signature with product constructors -/

/-- HOL constant names: declared atoms and product constructors at given
component types. -/
inductive TupleConstName where
  | atom (constant : Atom)
  | tuple (componentTypes : List Atom)

/-- The product type of the given component types. -/
def tupleType (componentTypes : List Atom) : Atom := .expression componentTypes

open Classical in
/-- The HOL type of a constant name.  Product constructors exist for
nonempty lists of static component types whose head is not an arrow. -/
noncomputable def tupleConstType (space : Space) : TupleConstName → Option (Ty Atom)
  | .atom constant => (declaredType? space constant).map toTy
  | .tuple componentTypes =>
      if (∃ headType rest, componentTypes = headType :: rest ∧ ¬ArrowShaped headType) ∧
          ∀ type ∈ componentTypes, StaticType type
      then some (spineTy componentTypes (tupleType componentTypes))
      else none

/-- HOL constants of the tuple signature, indexed by their HOL type. -/
def TupleConst (space : Space) (type : Ty Atom) : Type :=
  { name : TupleConstName // tupleConstType space name = some type }

/-- The HOL signature of a declaration space with product constructors. -/
noncomputable def tupleSignature (space : Space) : Signature TupleConstName (TupleConst space) :=
  fun name =>
    match lookup : tupleConstType space name with
    | some type => some ⟨type, ⟨name, lookup⟩⟩
    | none => none

theorem tupleSignature_some {space : Space} {name : TupleConstName} {type : Ty Atom}
    (lookup : tupleConstType space name = some type) :
    tupleSignature space name = some ⟨type, ⟨name, lookup⟩⟩ := by
  unfold tupleSignature
  split
  · next type' lookup' =>
      rw [lookup] at lookup'
      cases lookup'
      rfl
  · next lookup' =>
      rw [lookup] at lookup'
      cases lookup'

theorem tupleSignature_none {space : Space} {name : TupleConstName}
    (lookup : tupleConstType space name = none) : tupleSignature space name = none := by
  unfold tupleSignature
  split
  · next type lookup' =>
      rw [lookup] at lookup'
      cases lookup'
  · rfl

/-- A constant name elaborates exactly at its HOL type. -/
theorem elaborates_tupleConst_iff {space : Space} {name : TupleConstName}
    {type : Ty Atom} :
    Elaborates (tupleSignature space) (.constant name) type ↔
      tupleConstType space name = some type := by
  rw [elaborates_constant_iff]
  constructor
  · rintro ⟨constant, lookup⟩
    cases constantType : tupleConstType space name with
    | none =>
        rw [tupleSignature_none constantType] at lookup
        cases lookup
    | some found =>
        rw [tupleSignature_some constantType] at lookup
        simp only [Option.some.injEq] at lookup
        exact congrArg some (congrArg Sigma.fst lookup)
  · intro lookup
    exact ⟨_, tupleSignature_some lookup⟩

/-! ## Annotated translation -/

/-- Named HOL terms over the tuple signature. -/
abbrev TupleHOLTerm := NamedTerm Atom String TupleConstName

mutual

/-- Translate an expression, reading a subexpression as a tuple when the
annotation gives it one component type per element. -/
def toNamedTuple (annotation : Atom → Option (List Atom)) : Atom → TupleHOLTerm
  | .symbol name => .constant (.atom (.symbol name))
  | .var name => .variable name
  | .grounded value => .constant (.atom (.grounded value))
  | .expression [] => .constant (.atom (.expression []))
  | .expression (head :: arguments) =>
      tupleSpine annotation
        (match annotation (.expression (head :: arguments)) with
          | some componentTypes =>
              if componentTypes.length = arguments.length + 1 then
                .app (.constant (.tuple componentTypes)) (toNamedTuple annotation head)
              else toNamedTuple annotation head
          | none => toNamedTuple annotation head)
        arguments

/-- Apply a translated function to translated arguments. -/
def tupleSpine (annotation : Atom → Option (List Atom)) (function : TupleHOLTerm) :
    List Atom → TupleHOLTerm
  | [] => function
  | argument :: arguments =>
      tupleSpine annotation (.app function (toNamedTuple annotation argument)) arguments

end

theorem tupleSpine_eq_foldl (annotation : Atom → Option (List Atom)) :
    ∀ (function : TupleHOLTerm) (arguments : List Atom),
      tupleSpine annotation function arguments =
        arguments.foldl (fun accumulated argument =>
          .app accumulated (toNamedTuple annotation argument)) function
  | _, [] => rfl
  | function, argument :: arguments => by
      rw [tupleSpine, tupleSpine_eq_foldl]
      rfl

/-- Some annotated HOL term of the expression elaborates at the image of the
type. -/
def TupleHOLTyped (space : Space) (expression type : Atom) : Prop :=
  ∃ annotation : Atom → Option (List Atom),
    Elaborates (tupleSignature space) (toNamedTuple annotation expression) (toTy type)

/-! ## Static and functional reference types -/

theorem staticType_tuple {headType : Atom} {argumentTypes : List Atom}
    (headStatic : StaticType headType) (headNotArrow : ¬ArrowShaped headType)
    (argumentStatic : ∀ type ∈ argumentTypes, StaticType type) :
    StaticType (.expression (headType :: argumentTypes)) := by
  refine .base ?_ ?_ ?_ ?_
  · rintro ⟨components, equal⟩
    simp only [Atom.expression.injEq, List.cons.injEq] at equal
    exact headStatic.not_topReserved
      ⟨"->", by simp [reservedTypeNames], equal.1⟩
  · rintro ⟨_, _, equal⟩
    cases equal
  · intro occurs
    rcases occurs.expression_cases with equal | ⟨child, member, inner⟩
    · cases equal
    · simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headStatic.undefinedFree inner
      · exact (argumentStatic child member).undefinedFree inner
  · simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, headStatic.typeVars_nil,
      List.nil_append]
    rw [typeVarsList_eq_nil_iff]
    intro type member
    exact (argumentStatic type member).typeVars_nil

mutual

theorem ReferenceType.static {space : Space} {expression type : Atom} :
    ReferenceType space expression type → StaticType type
  | .constant _ static => static
  | .application _ _ static function _ =>
      (static.of_functionType function).2.2.2
  | .tuple head headNotArrow arguments =>
      staticType_tuple (ReferenceType.static head) headNotArrow
        (ReferenceTypes.static arguments)

theorem ReferenceTypes.static {space : Space} {arguments types : List Atom} :
    ReferenceTypes space arguments types → ∀ type ∈ types, StaticType type
  | .nil => by simp
  | .cons head tail => by
      intro type member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ReferenceType.static head
      · exact ReferenceTypes.static tail type member

end

theorem declaredType?_symbol_or_grounded {space : Space} {atom type : Atom}
    (declared : declaredType? space atom = some type) :
    (∃ name, atom = .symbol name) ∨ (∃ value, atom = .grounded value) := by
  cases atom with
  | symbol name => exact Or.inl ⟨name, rfl⟩
  | grounded value => exact Or.inr ⟨value, rfl⟩
  | var name => simp [declaredType?] at declared
  | expression atoms => simp [declaredType?] at declared

/-- A declared constant has only its declared reference type. -/
theorem ReferenceType.constant_eq {space : Space} {atom type found : Atom}
    (declared : declaredType? space atom = some type)
    (typed : ReferenceType space atom found) : found = type := by
  rcases declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩ <;>
  · cases typed with
    | constant declared' _ =>
        rw [declared] at declared'
        cases declared'
        rfl

mutual

/-- The reference typing is functional. -/
theorem ReferenceType.unique {space : Space} {expression left right : Atom} :
    ReferenceType space expression left → ReferenceType space expression right →
      left = right
  | .constant declared _, typed => (ReferenceType.constant_eq declared typed).symm
  | .application notState declared static function arguments, typed => by
      cases typed with
      | constant declared' _ => simp [declaredType?] at declared'
      | application _ declared' _ function' arguments' =>
          rw [declared] at declared'
          cases declared'
          obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique function function'
          rfl
      | tuple head headNotArrow _ =>
          have headType := ReferenceType.constant_eq declared head
          subst headType
          exact absurd (ArrowShaped.of_functionType function) headNotArrow
  | .tuple head headNotArrow arguments, typed => by
      cases typed with
      | constant declared' _ => simp [declaredType?] at declared'
      | application _ declared' _ function' _ =>
          have headType := ReferenceType.constant_eq declared' head
          subst headType
          exact absurd (ArrowShaped.of_functionType function') headNotArrow
      | tuple head' _ arguments' =>
          rw [ReferenceType.unique head head', ReferenceTypes.unique arguments arguments']

theorem ReferenceTypes.unique {space : Space} {arguments left right : List Atom} :
    ReferenceTypes space arguments left → ReferenceTypes space arguments right →
      left = right
  | .nil, .nil => rfl
  | .cons head tail, .cons head' tail' => by
      rw [ReferenceType.unique head head', ReferenceTypes.unique tail tail']

end

theorem ReferenceTypes.forall₂_iff {space : Space} :
    ∀ {arguments types : List Atom},
      ReferenceTypes space arguments types ↔
        List.Forall₂ (ReferenceType space) arguments types
  | [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun typed => (by cases typed), fun all => (by cases all)⟩
  | _ :: _, [] => ⟨fun typed => (by cases typed), fun all => (by cases all)⟩
  | argument :: arguments, type :: types => by
      constructor
      · intro typed
        cases typed with
        | cons head tail => exact .cons head (ReferenceTypes.forall₂_iff.mp tail)
      · intro all
        cases all with
        | cons head tail => exact .cons head (ReferenceTypes.forall₂_iff.mpr tail)

theorem ReferenceTypes.length_eq {space : Space} {arguments types : List Atom}
    (typed : ReferenceTypes space arguments types) : arguments.length = types.length :=
  (ReferenceTypes.forall₂_iff.mp typed).length_eq

/-- The reference type of an expression is never an arrow. -/
theorem ReferenceType.expression_not_arrow {space : Space} {atoms : List Atom}
    {type : Atom} (typed : ReferenceType space (.expression atoms) type) :
    ¬ArrowShaped type := by
  cases typed with
  | constant declared _ => simp [declaredType?] at declared
  | application _ _ static function _ =>
      exact (static.of_functionType function).2.2.1
  | tuple head headNotArrow _ =>
      rintro ⟨components, equal⟩
      simp only [Atom.expression.injEq, List.cons.injEq] at equal
      exact (ReferenceType.static head).not_topReserved
        ⟨"->", by simp [reservedTypeNames], equal.1⟩

theorem toNamedTuple_of_declared {annotation : Atom → Option (List Atom)}
    {space : Space} {atom type : Atom} (declared : declaredType? space atom = some type) :
    toNamedTuple annotation atom = .constant (.atom atom) := by
  rcases declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩ <;> rfl

theorem elaborates_declared_atom_iff {space : Space} {atom : Atom} {type : Ty Atom} :
    Elaborates (tupleSignature space) (.constant (.atom atom)) type ↔
      ∃ declared, declaredType? space atom = some declared ∧ type = toTy declared := by
  rw [elaborates_tupleConst_iff]
  simp only [tupleConstType, Option.map_eq_some_iff]
  constructor
  · rintro ⟨declared, lookup, rfl⟩
    exact ⟨declared, lookup, rfl⟩
  · rintro ⟨declared, lookup, rfl⟩
    exact ⟨declared, lookup, rfl⟩

/-- The tuple constructor elaborates exactly at its product type. -/
theorem elaborates_tuple_iff {space : Space} {componentTypes : List Atom} {type : Ty Atom} :
    Elaborates (tupleSignature space) (.constant (.tuple componentTypes)) type ↔
      (∃ headType rest, componentTypes = headType :: rest ∧ ¬ArrowShaped headType) ∧
        (∀ component ∈ componentTypes, StaticType component) ∧
        type = spineTy componentTypes (tupleType componentTypes) := by
  rw [elaborates_tupleConst_iff]
  by_cases condition : (∃ headType rest, componentTypes = headType :: rest ∧
      ¬ArrowShaped headType) ∧ ∀ type ∈ componentTypes, StaticType type
  · have lookup : tupleConstType space (.tuple componentTypes) =
        some (spineTy componentTypes (tupleType componentTypes)) := if_pos condition
    rw [lookup, Option.some.injEq]
    exact ⟨fun equal => ⟨condition.1, condition.2, equal.symm⟩,
      fun ⟨_, _, equal⟩ => equal.symm⟩
  · have lookup : tupleConstType space (.tuple componentTypes) = none := if_neg condition
    rw [lookup]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨shape, static, _⟩
    exact condition ⟨shape, static⟩

/-! ## From HOL to the reference typing -/

/-- The tuple branch of an annotated tuple node. -/
private theorem tuple_branch {space : Space} {head : Atom}
    {arguments componentTypes : List Atom} {annotation : Atom → Option (List Atom)}
    {holTypes : List (Ty Atom)} {holType : Ty Atom}
    (lengthOk : componentTypes.length = arguments.length + 1)
    (start : Elaborates (tupleSignature space)
      (.app (.constant (.tuple componentTypes)) (toNamedTuple annotation head))
      (holTypes.foldr Ty.arr holType))
    (all : List.Forall₂ (fun argument type =>
      Elaborates (tupleSignature space) (toNamedTuple annotation argument) type)
      arguments holTypes)
    (headSound : ∀ {holType : Ty Atom},
      Elaborates (tupleSignature space) (toNamedTuple annotation head) holType →
        ∃ type, StaticType type ∧ holType = toTy type ∧ ReferenceType space head type)
    (argumentSound : ∀ argument ∈ arguments, ∀ {holType : Ty Atom},
      Elaborates (tupleSignature space) (toNamedTuple annotation argument) holType →
        ∃ type, StaticType type ∧ holType = toTy type ∧ ReferenceType space argument type) :
    ∃ type, StaticType type ∧ holType = toTy type ∧
      ReferenceType space (.expression (head :: arguments)) type := by
  obtain ⟨domain, tupleElaborates, headElaborates⟩ := elaborates_app_iff.mp start
  obtain ⟨⟨headType, rest, rfl, headNotArrow⟩, componentStatic, tupleTypeEq⟩ :=
    elaborates_tuple_iff.mp tupleElaborates
  simp only [spineTy_cons] at tupleTypeEq
  obtain ⟨domainEq, spineEq⟩ := Ty.arr.inj tupleTypeEq
  obtain ⟨foundHead, foundHeadStatic, headHolEq, headTyped⟩ := headSound headElaborates
  have headEq : headType = foundHead :=
    toTy_injective (componentStatic headType (by simp)) foundHeadStatic
      (domainEq.symm.trans headHolEq)
  subst headEq
  have restLength : holTypes.length = (rest.map toTy).length := by
    simp only [List.length_cons, add_left_inj] at lengthOk
    rw [List.length_map, lengthOk]
    exact all.length_eq.symm
  rw [spineTy_eq_foldr] at spineEq
  obtain ⟨holEq, resultEq⟩ := foldr_arr_injective restLength spineEq
  subst holEq
  have restStatic : ∀ type ∈ rest, StaticType type :=
    fun type member => componentStatic type (List.mem_cons_of_mem _ member)
  have typed : List.Forall₂ (ReferenceType space) arguments rest := by
    have mapped := List.forall₂_map_right_iff.mp all
    refine forall₂_imp_of_mem₂ mapped ?_
    intro argument member type typeMember elaborated
    obtain ⟨found, foundStatic, holEq, foundTyped⟩ := argumentSound argument member elaborated
    rw [toTy_injective (restStatic type typeMember) foundStatic holEq]
    exact foundTyped
  exact ⟨_, staticType_tuple foundHeadStatic headNotArrow restStatic, resultEq,
    .tuple headTyped headNotArrow (ReferenceTypes.forall₂_iff.mpr typed)⟩

/-- The application reading of a tuple node elaborates nowhere: its head has
a non-arrow HOL type. -/
private theorem application_branch_impossible {space : Space} {head : Atom}
    {annotation : Atom → Option (List Atom)} {holTypes : List (Ty Atom)} {holType : Ty Atom}
    (nonempty : holTypes ≠ [])
    (start : Elaborates (tupleSignature space) (toNamedTuple annotation head)
      (holTypes.foldr Ty.arr holType))
    (headBase : ∀ {holType : Ty Atom},
      Elaborates (tupleSignature space) (toNamedTuple annotation head) holType →
        ∃ type, ¬ArrowShaped type ∧ holType = toTy type) : False := by
  obtain ⟨type, notArrow, holEq⟩ := headBase start
  rw [toTy_of_not_arrowShaped notArrow] at holEq
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp at holEq

/-- Every HOL elaboration of an annotated tuple-fragment term is the image of
a static type that the reference typing assigns to the expression. -/
theorem reference_of_elaborates {space : Space} {expression : Atom}
    (fragment : TupleTerm space expression) :
    ∀ {annotation : Atom → Option (List Atom)} {holType : Ty Atom},
      Elaborates (tupleSignature space) (toNamedTuple annotation expression) holType →
        ∃ type, StaticType type ∧ holType = toTy type ∧ ReferenceType space expression type := by
  induction fragment with
  | constant declared static =>
      intro annotation holType elaborated
      rw [toNamedTuple_of_declared declared] at elaborated
      obtain ⟨declared', lookup, rfl⟩ := elaborates_declared_atom_iff.mp elaborated
      rw [declared] at lookup
      cases lookup
      exact ⟨_, static, rfl, .constant declared static⟩
  | @application name arguments argumentTypes type returnType notState _ declared static
      function lengths _ argumentIH =>
      intro annotation holType elaborated
      obtain ⟨nonempty, argumentStatic, _, returnStatic⟩ := static.of_functionType function
      have argumentsFrom : ∀ (holTypes : List (Ty Atom)),
          (Elaborates (tupleSignature space) (.constant (.atom (.symbol name)))
            (holTypes.foldr Ty.arr holType)) →
          List.Forall₂ (fun argument type =>
            Elaborates (tupleSignature space) (toNamedTuple annotation argument) type)
            arguments holTypes →
          ∃ found, StaticType found ∧ holType = toTy found ∧
            ReferenceType space (.expression (.symbol name :: arguments)) found := by
        intro holTypes functionElaborates all
        obtain ⟨declared', lookup, typeEq⟩ :=
          elaborates_declared_atom_iff.mp functionElaborates
        rw [declared] at lookup
        cases lookup
        rw [toTy_of_functionType function nonempty, spineTy_eq_foldr] at typeEq
        have holLength : (argumentTypes.map toTy).length = holTypes.length := by
          rw [List.length_map, ← lengths]
          exact all.length_eq
        obtain ⟨holEq, resultEq⟩ := foldr_arr_injective holLength.symm typeEq
        subst holEq
        have typed : List.Forall₂ (ReferenceType space) arguments argumentTypes := by
          have mapped := List.forall₂_map_right_iff.mp all
          refine (List.forall₂_iff_get.mpr ⟨by simpa using lengths, ?_⟩)
          intro index first second
          have elaboratedArgument := (List.forall₂_iff_get.mp mapped).2 index first second
          obtain ⟨found, foundStatic, holEq, foundTyped⟩ :=
            argumentIH _ (List.get_mem _ _) elaboratedArgument
          rw [toTy_injective (argumentStatic _ (List.get_mem _ _)) foundStatic holEq]
          exact foundTyped
        exact ⟨returnType, returnStatic, resultEq, .application notState declared static
          function (ReferenceTypes.forall₂_iff.mpr typed)⟩
      simp only [toNamedTuple] at elaborated
      rw [tupleSpine_eq_foldl, elaborates_foldl_app_iff] at elaborated
      obtain ⟨holTypes, startElaborates, all⟩ := elaborated
      split at startElaborates
      · next componentTypes _ =>
          split at startElaborates
          · obtain ⟨domain, tupleElaborates, headElaborates⟩ :=
              elaborates_app_iff.mp startElaborates
            obtain ⟨⟨headType, rest, rfl, headNotArrow⟩, componentStatic, tupleTypeEq⟩ :=
              elaborates_tuple_iff.mp tupleElaborates
            simp only [spineTy_cons] at tupleTypeEq
            obtain ⟨domainEq, _⟩ := Ty.arr.inj tupleTypeEq
            obtain ⟨declared', lookup, headTypeEq⟩ :=
              elaborates_declared_atom_iff.mp headElaborates
            rw [declared] at lookup
            cases lookup
            have equal := toTy_injective static (componentStatic headType (by simp))
              (headTypeEq.symm.trans domainEq)
            subst equal
            exact absurd (ArrowShaped.of_functionType function) headNotArrow
          · exact argumentsFrom holTypes startElaborates all
      · exact argumentsFrom holTypes startElaborates all
  | @tupleConstant head arguments headType _ declared static notArrow nonempty _ argumentIH =>
      intro annotation holType elaborated
      have headSound : ∀ {holType : Ty Atom},
          Elaborates (tupleSignature space) (toNamedTuple annotation head) holType →
            ∃ type, StaticType type ∧ holType = toTy type ∧ ReferenceType space head type := by
        intro holType headElaborates
        rw [toNamedTuple_of_declared declared] at headElaborates
        obtain ⟨declared', lookup, rfl⟩ := elaborates_declared_atom_iff.mp headElaborates
        rw [declared] at lookup
        cases lookup
        exact ⟨_, static, rfl, .constant declared static⟩
      have headBase : ∀ {holType : Ty Atom},
          Elaborates (tupleSignature space) (toNamedTuple annotation head) holType →
            ∃ type, ¬ArrowShaped type ∧ holType = toTy type := by
        intro holType headElaborates
        obtain ⟨type, _, holEq, typed⟩ := headSound headElaborates
        have typeEq := ReferenceType.constant_eq declared typed
        subst typeEq
        exact ⟨type, notArrow, holEq⟩
      simp only [toNamedTuple] at elaborated
      rw [tupleSpine_eq_foldl, elaborates_foldl_app_iff] at elaborated
      obtain ⟨holTypes, startElaborates, all⟩ := elaborated
      have holNonempty : holTypes ≠ [] := by
        intro empty
        subst empty
        cases all
        exact nonempty rfl
      split at startElaborates
      · split at startElaborates
        · next lengthOk =>
            exact tuple_branch lengthOk startElaborates all headSound
              (fun argument member => argumentIH argument member)
        · exact (application_branch_impossible holNonempty startElaborates headBase).elim
      · exact (application_branch_impossible holNonempty startElaborates headBase).elim
  | @tupleExpression headAtoms arguments _ headFragment nonempty _ headIH argumentIH =>
      intro annotation holType elaborated
      have headBase : ∀ {holType : Ty Atom},
          Elaborates (tupleSignature space)
              (toNamedTuple annotation (.expression headAtoms)) holType →
            ∃ type, ¬ArrowShaped type ∧ holType = toTy type := by
        intro holType headElaborates
        obtain ⟨type, _, holEq, typed⟩ := headIH headElaborates
        exact ⟨type, typed.expression_not_arrow, holEq⟩
      simp only [toNamedTuple] at elaborated
      rw [tupleSpine_eq_foldl, elaborates_foldl_app_iff] at elaborated
      obtain ⟨holTypes, startElaborates, all⟩ := elaborated
      have holNonempty : holTypes ≠ [] := by
        intro empty
        subst empty
        cases all
        exact nonempty rfl
      split at startElaborates
      · split at startElaborates
        · next lengthOk =>
            exact tuple_branch lengthOk startElaborates all headIH
              (fun argument member => argumentIH argument member)
        · exact (application_branch_impossible holNonempty startElaborates headBase).elim
      · exact (application_branch_impossible holNonempty startElaborates headBase).elim

/-! ## From the reference typing to HOL -/

open Classical in
/-- The annotation read off the reference typing: an expression is a tuple
exactly when its head has a non-arrow reference type. -/
noncomputable def referenceAnnotation (space : Space) : Atom → Option (List Atom)
  | .expression (head :: arguments) =>
      if tupleNode : ∃ headType argumentTypes, ReferenceType space head headType ∧
          ¬ArrowShaped headType ∧ ReferenceTypes space arguments argumentTypes
      then some (tupleNode.choose :: tupleNode.choose_spec.choose)
      else none
  | _ => none

theorem referenceAnnotation_tuple {space : Space} {head : Atom} {arguments : List Atom}
    {headType : Atom} {argumentTypes : List Atom}
    (headTyped : ReferenceType space head headType) (headNotArrow : ¬ArrowShaped headType)
    (argumentsTyped : ReferenceTypes space arguments argumentTypes) :
    referenceAnnotation space (.expression (head :: arguments)) =
      some (headType :: argumentTypes) := by
  have tupleNode : ∃ headType argumentTypes, ReferenceType space head headType ∧
      ¬ArrowShaped headType ∧ ReferenceTypes space arguments argumentTypes :=
    ⟨headType, argumentTypes, headTyped, headNotArrow, argumentsTyped⟩
  simp only [referenceAnnotation, dif_pos tupleNode, Option.some.injEq, List.cons.injEq]
  have spec := tupleNode.choose_spec.choose_spec
  exact ⟨ReferenceType.unique spec.1 headTyped, ReferenceTypes.unique spec.2.2 argumentsTyped⟩

theorem referenceAnnotation_application {space : Space} {name : String}
    {arguments argumentTypes : List Atom} {type returnType : Atom}
    (declared : declaredType? space (.symbol name) = some type)
    (function : FunctionTypeRel type argumentTypes returnType) :
    referenceAnnotation space (.expression (.symbol name :: arguments)) = none := by
  have notTuple : ¬∃ headType argumentTypes, ReferenceType space (.symbol name) headType ∧
      ¬ArrowShaped headType ∧ ReferenceTypes space arguments argumentTypes := by
    rintro ⟨headType, _, headTyped, headNotArrow, _⟩
    rw [ReferenceType.constant_eq declared headTyped] at headNotArrow
    exact headNotArrow (ArrowShaped.of_functionType function)
  simp only [referenceAnnotation, dif_neg notTuple]

mutual

/-- Every reference typing is a HOL elaboration of the annotated term. -/
theorem elaborates_of_reference {space : Space} :
    ∀ {expression type : Atom}, ReferenceType space expression type →
      Elaborates (tupleSignature space)
        (toNamedTuple (referenceAnnotation space) expression) (toTy type)
  | _, _, .constant declared _ => by
      rw [toNamedTuple_of_declared declared]
      exact elaborates_declared_atom_iff.mpr ⟨_, declared, rfl⟩
  | _, _, @ReferenceType.application _ name arguments argumentTypes type returnType
      _ declared static function argumentsTyped => by
      obtain ⟨nonempty, _, _, _⟩ := static.of_functionType function
      simp only [toNamedTuple]
      rw [referenceAnnotation_application declared function, tupleSpine_eq_foldl,
        elaborates_foldl_app_iff]
      refine ⟨argumentTypes.map toTy, ?_,
        List.forall₂_map_right_iff.mpr (elaborates_of_references argumentsTyped)⟩
      rw [← spineTy_eq_foldr, ← toTy_of_functionType function nonempty]
      exact elaborates_declared_atom_iff.mpr ⟨_, declared, rfl⟩
  | _, _, @ReferenceType.tuple _ head arguments headType argumentTypes
      headTyped headNotArrow argumentsTyped => by
      have lengthOk : (headType :: argumentTypes).length = arguments.length + 1 := by
        simp [argumentsTyped.length_eq]
      simp only [toNamedTuple]
      rw [referenceAnnotation_tuple headTyped headNotArrow argumentsTyped]
      simp only [lengthOk, if_true]
      rw [tupleSpine_eq_foldl, elaborates_foldl_app_iff]
      refine ⟨argumentTypes.map toTy, ?_,
        List.forall₂_map_right_iff.mpr (elaborates_of_references argumentsTyped)⟩
      apply elaborates_app_iff.mpr
      refine ⟨toTy headType, ?_, elaborates_of_reference headTyped⟩
      apply elaborates_tuple_iff.mpr
      refine ⟨⟨headType, argumentTypes, rfl, headNotArrow⟩, ?_, ?_⟩
      · intro component member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ReferenceType.static headTyped
        · exact ReferenceTypes.static argumentsTyped component member
      · simp [spineTy_eq_foldr, tupleType]

/-- Pointwise companion of `elaborates_of_reference`. -/
theorem elaborates_of_references {space : Space} :
    ∀ {arguments types : List Atom}, ReferenceTypes space arguments types →
      List.Forall₂ (fun argument type => Elaborates (tupleSignature space)
        (toNamedTuple (referenceAnnotation space) argument) (toTy type)) arguments types
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (elaborates_of_reference head) (elaborates_of_references tail)

end

/-! ## Agreement -/

/-- **HE's tuple rule is HOL product introduction.**  On the tuple fragment,
the reference runtime's typing assigns a static type exactly when some
annotated HOL term, with product constructors at tuple nodes, elaborates at
the image of that type. -/
theorem reference_iff_tupleHOLTyped {space : Space} {expression type : Atom}
    (fragment : TupleTerm space expression) (static : StaticType type) :
    ReferenceType space expression type ↔ TupleHOLTyped space expression type := by
  constructor
  · intro typed
    exact ⟨referenceAnnotation space, elaborates_of_reference typed⟩
  · rintro ⟨annotation, elaborated⟩
    obtain ⟨found, foundStatic, holEq, typed⟩ := reference_of_elaborates fragment elaborated
    rw [toTy_injective static foundStatic holEq]
    exact typed

/-- On tuple-free saturated expressions the reference typing is HOL
elaboration over the plain declaration signature. -/
theorem reference_iff_holTyped_of_saturated {space : Space} {expression : Atom}
    (saturated : SaturatedTerm space expression) :
    ∀ {type : Atom}, StaticType type →
      (ReferenceType space expression type ↔ HOLTyped space expression type) := by
  induction saturated with
  | constant declared static =>
      intro type typeStatic
      constructor
      · intro typed
        rw [ReferenceType.constant_eq declared typed, holTyped_iff_elaborates,
          toNamed_of_declared declared]
        exact elaborates_declared_iff.mpr ⟨_, declared, rfl⟩
      · intro typed
        rw [holTyped_iff_elaborates, toNamed_of_declared declared] at typed
        obtain ⟨found, lookup, holEq⟩ := elaborates_declared_iff.mp typed
        rw [declared] at lookup
        cases lookup
        rw [toTy_injective typeStatic static holEq]
        exact .constant declared static
  | @application name arguments argumentTypes type returnType notState _ declared static
      function lengths _ argumentIH =>
      intro resultType resultStatic
      obtain ⟨nonempty, argumentStatic, _, returnStatic⟩ := static.of_functionType function
      have argumentsIff : ReferenceTypes space arguments argumentTypes ↔
          List.Forall₂ (fun argument argumentType =>
            Elaborates (spaceSignature space) (toNamed argument) (toTy argumentType))
            arguments argumentTypes := by
        rw [ReferenceTypes.forall₂_iff]
        constructor
        · intro all
          exact forall₂_imp_of_mem₂ all (fun argument member argumentType typeMember typed =>
            (argumentIH argument member (argumentStatic argumentType typeMember)).mp typed)
        · intro all
          exact forall₂_imp_of_mem₂ all (fun argument member argumentType typeMember typed =>
            (argumentIH argument member (argumentStatic argumentType typeMember)).mpr typed)
      rw [holTyped_iff_elaborates,
        elaborates_application_iff declared function nonempty lengths]
      constructor
      · intro typed
        cases typed with
        | constant declared' _ => simp [declaredType?] at declared'
        | application _ declared' _ function' argumentsTyped =>
            rw [declared] at declared'
            cases declared'
            obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique function function'
            exact ⟨rfl, argumentsIff.mp argumentsTyped⟩
        | tuple headTyped headNotArrow _ =>
            rw [ReferenceType.constant_eq declared headTyped] at headNotArrow
            exact absurd (ArrowShaped.of_functionType function) headNotArrow
      · rintro ⟨holEq, all⟩
        rw [toTy_injective resultStatic returnStatic holEq]
        exact .application notState declared static function (argumentsIff.mpr all)

/-- Where both are defined, the reference typing agrees with the
specification's exact relation. -/
theorem reference_iff_exact_of_saturated {space : Space} {expression type : Atom}
    (saturated : SaturatedTerm space expression) (static : StaticType type) :
    ReferenceType space expression type ↔
      ExactTypes space expression [type] ∧ NoUndefinedFallback space expression :=
  (reference_iff_holTyped_of_saturated saturated static).trans
    (hol_iff_exact saturated static)

/-! ## The tuple canary -/

private def truth : Atom := .symbol "Truth"
private def zero : Atom := .symbol "Z"

/-- With `(: Truth Bool)` and `(: Z Nat)` the reference typing gives
`(Truth Z)` the tuple type `(Bool Nat)`, HOL agrees through the product
constructor, and the specification gives only `%Undefined%`. -/
theorem truth_zero_is_a_pair :
    ReferenceType SpecBoundary.truthZSpace (.expression [truth, zero])
        (.expression [.symbol "Bool", .symbol "Nat"]) ∧
      TupleHOLTyped SpecBoundary.truthZSpace (.expression [truth, zero])
        (.expression [.symbol "Bool", .symbol "Nat"]) ∧
      ExactTypes SpecBoundary.truthZSpace (.expression [truth, zero]) [Atom.undefinedType] := by
  have boolStatic := SpecBoundary.staticSymbol "Bool" (by decide)
  have natStatic := SpecBoundary.staticSymbol "Nat" (by decide)
  have truthDeclared : declaredType? SpecBoundary.truthZSpace truth = some (.symbol "Bool") := by
    decide
  have zeroDeclared : declaredType? SpecBoundary.truthZSpace zero = some (.symbol "Nat") := by
    decide
  have typed : ReferenceType SpecBoundary.truthZSpace (.expression [truth, zero])
      (.expression [.symbol "Bool", .symbol "Nat"]) :=
    .tuple (.constant truthDeclared boolStatic) (by rintro ⟨_, equal⟩; cases equal)
      (.cons (.constant zeroDeclared natStatic) .nil)
  refine ⟨typed, ⟨referenceAnnotation _, elaborates_of_reference typed⟩, ?_⟩
  exact SpecBoundary.spec_tuple_is_undefined

/-- Negative: `(Truth Z)` does not have the swapped tuple type `(Nat Bool)`,
in the reference typing or in HOL. -/
theorem truth_zero_not_swapped :
    ¬ReferenceType SpecBoundary.truthZSpace (.expression [truth, zero])
        (.expression [.symbol "Nat", .symbol "Bool"]) ∧
      ¬TupleHOLTyped SpecBoundary.truthZSpace (.expression [truth, zero])
        (.expression [.symbol "Nat", .symbol "Bool"]) := by
  have boolStatic := SpecBoundary.staticSymbol "Bool" (by decide)
  have natStatic := SpecBoundary.staticSymbol "Nat" (by decide)
  have truthDeclared : declaredType? SpecBoundary.truthZSpace truth = some (.symbol "Bool") := by
    decide
  have zeroDeclared : declaredType? SpecBoundary.truthZSpace zero = some (.symbol "Nat") := by
    decide
  have notReference : ¬ReferenceType SpecBoundary.truthZSpace (.expression [truth, zero])
      (.expression [.symbol "Nat", .symbol "Bool"]) := by
    intro swapped
    have equal := ReferenceType.unique truth_zero_is_a_pair.1 swapped
    simp at equal
  have fragment : TupleTerm SpecBoundary.truthZSpace (.expression [truth, zero]) := by
    refine .tupleConstant (by decide) truthDeclared boolStatic
      (by rintro ⟨_, equal⟩; cases equal) (by simp) ?_
    intro argument member
    simp only [List.mem_singleton] at member
    subst member
    exact .constant zeroDeclared natStatic
  have swappedStatic : StaticType (.expression [.symbol "Nat", .symbol "Bool"]) :=
    staticType_tuple (headType := .symbol "Nat") (argumentTypes := [.symbol "Bool"])
      natStatic (by rintro ⟨_, equal⟩; cases equal)
      (by
        intro argumentType member
        simp only [List.mem_singleton] at member
        subst member
        exact boolStatic)
  exact ⟨notReference, fun typed =>
    notReference ((reference_iff_tupleHOLTyped fragment swappedStatic).mpr typed)⟩

#print axioms reference_iff_tupleHOLTyped
#print axioms reference_iff_exact_of_saturated
#print axioms truth_zero_is_a_pair
#print axioms truth_zero_not_swapped

end Mettapedia.Languages.MeTTa.HE.TypeGrounding.Tuples
