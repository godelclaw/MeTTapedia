import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Tuples
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Schematic

/-!
# HE typing agrees with the contract on its fragments

Inside each grounded fragment, an HE typing judgment holds exactly when the
contract types the expression (`Typed`):

* `tuple_iff_reference`: on static constants, saturated applications of
  declared static arrows and tuples, the reference runtime's typing
  (`Tuples.ReferenceType`) is contract typing, with tuples read as products;
* `static_iff_exact`: on tuple-free saturated expressions, contract typing is
  HE's specified exact relation together with the absence of an
  `%Undefined%` fallback;
* `schematic_iff_exact`: on first-order expressions over schematic
  declarations, contract typing at a ground first-order type is exactly a
  first-order instance of HE's single exact candidate, its principal type
  scheme.

The fragments ask the declarations they use to read faithfully
(`DeclarationsFaithful`), and the type to be a faithful one.  A declaration
like `(: x (List (-> A (-> B C))))` is static for HE but has no faithful
HOL reading: a nested curried arrow and its uncurried form read alike.

The agreements make a refusal by the contract a genuine negative: inside a
fragment, a judgment the contract rejects is one that HE rejects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

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

/-- A valuation fixes a variable-free atom. -/
theorem applyTypeValuation_of_ground (valuation : String → Atom) {atom : Atom}
    (ground : TypeSubst.typeVars atom = []) : applyTypeValuation valuation atom = atom :=
  (applyTypeValuation_congr_of_typeVars (right := fun name => .var name) atom
    (fun name member => by simp [ground] at member)).trans
    (Theory.applyTypeValuation_var_identity atom)

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

/-- The tuple-free saturated fragment is part of the tuple fragment. -/
theorem saturatedTerm_tupleTerm {space : Space} {expression : Atom}
    (saturated : SaturatedTerm space expression) : TupleTerm space expression := by
  induction saturated with
  | constant declared static => exact .constant declared static
  | application notState annotationFree declared static function lengths _ argumentIH =>
      exact .application notState annotationFree declared static function lengths argumentIH

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

end Mettapedia.Languages.MeTTa.HE.HOLContract
