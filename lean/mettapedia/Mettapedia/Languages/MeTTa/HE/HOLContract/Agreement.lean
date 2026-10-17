import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature

/-!
# HE typing agrees with the contract

The contract is HE's first-order rule (`typed_iff_firstOrder`).  On the fragments where HE's
reference runtime and its specification are known, the contract agrees with them:

* `tuple_iff_reference`: on static constants, saturated applications of declared static arrows
  and tuples, over declarations whose types are type atoms, the reference runtime's typing
  (`Tuples.ReferenceType`) is contract typing, at every type;
* `static_iff_exact`: on tuple-free saturated expressions, contract typing at a static type is
  HE's specified exact relation together with the absence of an `%Undefined%` fallback;
* `schematic_iff_exact`: on first-order expressions over schematic declarations, contract
  typing at a ground first-order type is exactly a first-order instance of HE's single exact
  candidate, its principal type scheme.

The agreements make a refusal by the contract a genuine negative: inside a fragment, a
judgment that the contract rejects is one that HE rejects.
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

/-! ## Declarations whose types are type atoms -/

/-- Every declaration the expression uses has a type atom as its type. -/
def DeclarationsFormed (space : Space) (expression : Atom) : Prop :=
  ∀ sub, Subatom sub expression → ∀ type, declaredType? space sub = some type → TypeAtom type

theorem DeclarationsFormed.of_child {space : Space} {atom : Atom} {atoms : List Atom}
    (formed : DeclarationsFormed space (.expression atoms)) (member : atom ∈ atoms) :
    DeclarationsFormed space atom :=
  fun sub occurs => formed sub (.child member occurs)

theorem DeclarationsFormed.self {space : Space} {atom type : Atom}
    (formed : DeclarationsFormed space atom) (declared : declaredType? space atom = some type) :
    TypeAtom type :=
  formed atom .refl type declared

/-- The tuple-free saturated fragment is part of the tuple fragment. -/
theorem saturatedTerm_tupleTerm {space : Space} {expression : Atom}
    (saturated : SaturatedTerm space expression) : TupleTerm space expression := by
  induction saturated with
  | constant declared static => exact .constant declared static
  | application notState annotationFree declared static function lengths _ argumentIH =>
      exact .application notState annotationFree declared static function lengths argumentIH

/-! ## The reference runtime -/

mutual

/-- Reference typings over declarations of type atoms are first-order typings. -/
theorem firstOrder_of_reference {space : Space} :
    ∀ {expression type : Atom}, ReferenceType space expression type →
      DeclarationsFormed space expression → FirstOrderType space expression type
  | _, _, @ReferenceType.constant _ atom type declared static, formed =>
      .declared (occurrence := 0) ⟨type, by simp [declarations_of_declared declared],
        typeInstance_self ⟨formed.self declared, static.not_topReserved⟩⟩
  | _, _, @ReferenceType.application _ name arguments argumentTypes type returnType
      _ declared static function arguments', formed => by
      have headFormed : TypeAtom type :=
        formed (.symbol name) (Subatom.of_mem (by simp)) type declared
      have headType : FirstOrderType space (.symbol name) type :=
        .declared (occurrence := 0) ⟨type, by simp [declarations_of_declared declared],
          typeInstance_self ⟨headFormed, static.not_topReserved⟩⟩
      rw [arrowAtom_of_functionType function] at headType
      exact .application headType (firstOrderList_of_reference arguments'
        (fun argument member => formed.of_child (List.mem_cons_of_mem _ member)))
  | _, _, .tuple head headNotArrow arguments, formed =>
      .tuple (firstOrder_of_reference head (formed.of_child (by simp))) headNotArrow
        (firstOrderList_of_reference arguments
          (fun argument member => formed.of_child (List.mem_cons_of_mem _ member)))

theorem firstOrderList_of_reference {space : Space} :
    ∀ {arguments types : List Atom}, ReferenceTypes space arguments types →
      (∀ argument ∈ arguments, DeclarationsFormed space argument) →
      FirstOrderTypes space arguments types
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, formed =>
      .cons (firstOrder_of_reference head (formed _ (by simp)))
        (firstOrderList_of_reference tail
          (fun argument member => formed argument (List.mem_cons_of_mem _ member)))

end

/-- Pointwise: first-order typings of arguments whose own typings are reference typings. -/
theorem referenceTypes_of_firstOrderTypes {space : Space} :
    ∀ {arguments types : List Atom},
      (∀ argument ∈ arguments, ∀ {type : Atom},
        FirstOrderType space argument type → ReferenceType space argument type) →
      FirstOrderTypes space arguments types → ReferenceTypes space arguments types
  | [], _, _, typed => by
      cases typed
      exact .nil
  | head :: tail, _, argumentIH, typed => by
      cases typed with
      | cons headTyped tailTyped =>
          exact .cons (argumentIH head (by simp) headTyped)
            (referenceTypes_of_firstOrderTypes
              (fun argument member => argumentIH argument (List.mem_cons_of_mem _ member))
              tailTyped)

/-- On the tuple fragment, first-order typings are reference typings. -/
theorem reference_of_firstOrder {space : Space} {expression : Atom}
    (fragment : TupleTerm space expression) :
    ∀ {type : Atom}, FirstOrderType space expression type → ReferenceType space expression type := by
  induction fragment with
  | constant declared static =>
      intro type typed
      rw [firstOrder_declared_eq declared static.typeVars_nil typed]
      exact .constant declared static
  | @application name arguments argumentTypes declaredType returnType notState noAnnotation
      declared static function lengths _ argumentIH =>
      intro type typed
      cases typed with
      | declared isInstance =>
          obtain ⟨_, found, _⟩ := isInstance
          simp [declarations, noAnnotation] at found
      | application head arguments' =>
          have headEq := firstOrder_declared_eq declared static.typeVars_nil head
          rw [arrowAtom_of_functionType function] at headEq
          obtain ⟨parametersEq, resultEq⟩ := arrowAtom_injective headEq
          subst parametersEq resultEq
          exact .application notState declared static function
            (referenceTypes_of_firstOrderTypes argumentIH arguments')
      | tuple head headNotArrow _ =>
          have headEq := firstOrder_declared_eq declared static.typeVars_nil head
          subst headEq
          exact absurd (ArrowShaped.of_functionType function) headNotArrow
  | @tupleConstant head arguments declaredType noAnnotation declared static notArrow nonempty _
      argumentIH =>
      intro type typed
      cases typed with
      | declared isInstance =>
          obtain ⟨_, found, _⟩ := isInstance
          simp [declarations, noAnnotation] at found
      | application head' _ =>
          have headEq := firstOrder_declared_eq declared static.typeVars_nil head'
          rw [← headEq] at notArrow
          exact absurd (arrowAtom_arrowShaped _ _) notArrow
      | tuple head' headNotArrow arguments' =>
          have headEq := firstOrder_declared_eq declared static.typeVars_nil head'
          subst headEq
          exact .tuple (.constant declared static) headNotArrow
            (referenceTypes_of_firstOrderTypes argumentIH arguments')
  | @tupleExpression headAtoms arguments noAnnotation _ nonempty _ headIH argumentIH =>
      intro type typed
      cases typed with
      | declared isInstance =>
          obtain ⟨_, found, _⟩ := isInstance
          simp [declarations, noAnnotation] at found
      | application head' _ =>
          exact absurd (arrowAtom_arrowShaped _ _)
            (Tuples.ReferenceType.expression_not_arrow (headIH head'))
      | tuple head' headNotArrow arguments' =>
          exact .tuple (headIH head') headNotArrow
            (referenceTypes_of_firstOrderTypes argumentIH arguments')

/-- **HE's tuples are contract products.**  On the tuple fragment over declarations of type
atoms, the reference runtime assigns a type exactly when the contract types the expression
at it. -/
theorem tuple_iff_reference {space : Space} {expression type : Atom}
    (fragment : TupleTerm space expression) (formed : DeclarationsFormed space expression) :
    Typed space expression type ↔ ReferenceType space expression type := by
  rw [typed_iff_firstOrder]
  exact ⟨reference_of_firstOrder fragment, fun typed => firstOrder_of_reference typed formed⟩

/-- **Static arrows.**  On tuple-free saturated expressions over declarations of type atoms,
contract typing at a static type is HE's specified exact relation with no `%Undefined%`
fallback. -/
theorem static_iff_exact {space : Space} {expression type : Atom}
    (saturated : SaturatedTerm space expression) (formed : DeclarationsFormed space expression)
    (static : StaticType type) :
    Typed space expression type ↔
      ExactTypes space expression [type] ∧ NoUndefinedFallback space expression :=
  (tuple_iff_reference (saturatedTerm_tupleTerm saturated) formed).trans
    (Tuples.reference_iff_exact_of_saturated saturated static)

/-! ## First-order schemes -/

theorem applyTypeValuation_arrowAtom (valuation : String → Atom) (parameters : List Atom)
    (result : Atom) :
    applyTypeValuation valuation (arrowAtom parameters result) =
      arrowAtom (parameters.map (applyTypeValuation valuation)) (applyTypeValuation valuation result) := by
  simp [applyTypeValuation, arrowAtom, List.map_append]

/-- An atom without reserved names is a type atom. -/
theorem typeAtom_of_reservedFree {atom : Atom} (free : Schematic.ReservedFree atom) : TypeAtom atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, Schematic.ReservedFree atom) → ∀ atom ∈ atoms, TypeAtom atom) with
  | symbol name =>
      have notReserved := Schematic.reservedFree_symbol_iff.mp free
      refine .symbol ?_ ?_
      · rintro rfl
        exact notReserved (by simp [reservedTypeNames])
      · rintro rfl
        exact notReserved (by simp [reservedTypeNames])
  | var name => exact .var name
  | grounded value => exact .grounded value
  | expression atoms ih =>
      exact .compound free.not_arrowShaped
        (ih (fun _ member => free.of_child member))
  | nil =>
      rename_i _ atom member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i allFree atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH (allFree _ (by simp))
      · exact tailIH (fun other member' => allFree other (List.mem_cons_of_mem _ member')) atom
          member

/-- A ground first-order type is a contract type. -/
theorem contractType_of_groundFirstOrder {atom : Atom} (ground : Schematic.GroundFirstOrder atom) :
    ContractType atom :=
  ⟨typeAtom_of_reservedFree ground.1, ground.1.not_topReserved⟩

/-- Pointwise: the projected instance typings of arguments whose own typings project. -/
theorem elaborated_of_firstOrderTypes {space : Space} :
    ∀ {arguments types : List Atom},
      (∀ argument ∈ arguments, ∀ {type : Atom}, FirstOrderType space argument type →
        Schematic.SchematicHOLTyped space argument (Schematic.project type)) →
      FirstOrderTypes space arguments types →
      ∃ terms, List.Forall₂ Schematic.Annotates arguments terms ∧
        List.Forall₂ (fun term type =>
          Elaborates (Schematic.instanceSignature space) term (toTy type)) terms
          (types.map Schematic.project)
  | [], _, _, typed => by
      cases typed
      exact ⟨[], .nil, .nil⟩
  | argument :: arguments, _, argumentIH, typed => by
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨term, annotates, elaborates⟩ := argumentIH argument (by simp) headTyped
          obtain ⟨terms, restAnnotate, restElaborate⟩ := elaborated_of_firstOrderTypes
            (fun other member {_} typed' => argumentIH other (List.mem_cons_of_mem _ member) typed')
            tailTyped
          exact ⟨term :: terms, .cons annotates restAnnotate, .cons elaborates restElaborate⟩

/-- Pointwise: first-order typings of arguments from their instance typings in HOL. -/
theorem firstOrderTypes_of_elaborated {space : Space} :
    ∀ {arguments : List Atom} {terms : List Schematic.InstanceTerm} {types : List Atom},
      (∀ argument ∈ arguments, ∀ {type : Atom}, Schematic.GroundFirstOrder type →
        Schematic.SchematicHOLTyped space argument type → FirstOrderType space argument type) →
      List.Forall₂ Schematic.Annotates arguments terms →
      List.Forall₂ (fun term type =>
        Elaborates (Schematic.instanceSignature space) term (toTy type)) terms types →
      (∀ type ∈ types, Schematic.GroundFirstOrder type) →
      FirstOrderTypes space arguments types
  | [], _, _, _, annotate, elaborate, _ => by
      cases annotate
      cases elaborate
      exact .nil
  | argument :: arguments, _, _, argumentIH, annotate, elaborate, ground => by
      cases annotate with
      | cons headAnnotates restAnnotate =>
          cases elaborate with
          | cons headElaborates restElaborate =>
              exact .cons (argumentIH argument (by simp) (ground _ (by simp))
                  ⟨_, headAnnotates, headElaborates⟩)
                (firstOrderTypes_of_elaborated
                  (fun other member {_} ground' typed' => argumentIH other
                    (List.mem_cons_of_mem _ member) ground' typed')
                  restAnnotate restElaborate
                  (fun type member => ground type (List.mem_cons_of_mem _ member)))

/-- Every contract typing of a first-order expression over schematic declarations projects
to an instance typing in HOL. -/
theorem schematicHOL_of_firstOrder {space : Space} {expression : Atom}
    (fragment : Schematic.SchematicTerm space expression) :
    ∀ {type : Atom}, FirstOrderType space expression type →
      Schematic.SchematicHOLTyped space expression (Schematic.project type) := by
  induction fragment with
  | @constant atom scheme declared free =>
      intro type typed
      have instanceOf : Schematic.InstanceOf space atom (Schematic.project type) := by
        rcases Tuples.declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩ <;>
        · cases typed with
          | @declared _ _ occurrence isInstance =>
              obtain ⟨scheme', found, _, valuation, _, instanceEq⟩ := isInstance
              rw [declarations_of_declared declared] at found
              cases occurrence with
              | succ _ => simp at found
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                  subst found
                  refine ⟨scheme, declared, _, Schematic.projected_firstOrder valuation, ?_⟩
                  rw [← instanceEq, Schematic.project_applyTypeValuation valuation free]
      rcases Tuples.declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · exact ⟨_, .symbol name (Schematic.project type),
          Schematic.elaborates_instance_iff.mpr ⟨instanceOf, rfl⟩⟩
      · exact ⟨_, .grounded value (Schematic.project type),
          Schematic.elaborates_instance_iff.mpr ⟨instanceOf, rfl⟩⟩
  | @application name arguments argumentTypes scheme returnType notState noAnnotation declared
      operator lengths _ argumentIH =>
      intro type typed
      cases typed with
      | declared isInstance =>
          obtain ⟨_, found, _⟩ := isInstance
          simp [declarations, noAnnotation] at found
      | @application _ result _ parameters head arguments' =>
          obtain ⟨occurrence, scheme', found, _, valuation, _, instanceEq⟩ := firstOrder_symbol head
          rw [declarations_of_declared declared] at found
          cases occurrence with
          | succ _ => simp at found
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst found
              rw [arrowAtom_of_functionType operator.function, applyTypeValuation_arrowAtom]
                at instanceEq
              obtain ⟨parametersEq, resultEq⟩ := arrowAtom_injective instanceEq
              subst parametersEq resultEq
              -- The projected instance of the head.
              let projected : String → Atom := fun name => Schematic.project (valuation name)
              have argumentsEq : argumentTypes.map (applyTypeValuation projected) =
                  (argumentTypes.map (applyTypeValuation valuation)).map Schematic.project := by
                rw [List.map_map]
                refine List.map_congr_left (fun argumentType member => ?_)
                exact (Schematic.project_applyTypeValuation valuation
                  (operator.arguments argumentType member)).symm
              have returnEq : applyTypeValuation projected returnType =
                  Schematic.project (applyTypeValuation valuation returnType) :=
                (Schematic.project_applyTypeValuation valuation operator.result).symm
              have instanceOf : Schematic.InstanceOf space (.symbol name)
                  (applyTypeValuation projected scheme) :=
                ⟨scheme, declared, projected, Schematic.projected_firstOrder valuation, rfl⟩
              have function : FunctionTypeRel (applyTypeValuation projected scheme)
                  (argumentTypes.map (applyTypeValuation projected))
                  (applyTypeValuation projected returnType) := by
                rw [arrowAtom_of_functionType operator.function, applyTypeValuation_arrowAtom]
                rfl
              have argumentTerms := elaborated_of_firstOrderTypes argumentIH arguments'
              obtain ⟨terms, annotate, elaborate⟩ := argumentTerms
              refine ⟨terms.foldl .app (.constant (.symbol name, applyTypeValuation projected scheme)),
                .application annotate, ?_⟩
              rw [← argumentsEq] at elaborate
              rw [Schematic.elaborates_application_instance_iff function
                (by simpa using operator.nonempty)
                (by rw [List.length_map]; exact (elaborate.length_eq).trans (by simp))]
              exact ⟨instanceOf, by rw [returnEq], elaborate⟩
      | tuple head headNotArrow _ =>
          obtain ⟨occurrence, scheme', found, _, valuation, _, instanceEq⟩ := firstOrder_symbol head
          rw [declarations_of_declared declared] at found
          cases occurrence with
          | succ _ => simp at found
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst found
              rw [arrowAtom_of_functionType operator.function, applyTypeValuation_arrowAtom]
                at instanceEq
              rw [← instanceEq] at headNotArrow
              exact absurd (arrowAtom_arrowShaped _ _) headNotArrow

/-- Every instance typing in HOL of a first-order expression over schematic declarations is a
contract typing. -/
theorem firstOrder_of_schematicHOL {space : Space} {expression : Atom}
    (fragment : Schematic.SchematicTerm space expression) :
    ∀ {type : Atom}, Schematic.GroundFirstOrder type →
      Schematic.SchematicHOLTyped space expression type → FirstOrderType space expression type := by
  induction fragment with
  | @constant atom scheme declared free =>
      intro type ground typed
      obtain ⟨term, annotates, elaborates⟩ := typed
      have constantCase : ∀ {name : Atom × Atom},
          Elaborates (Schematic.instanceSignature space) (.constant name) (toTy type) →
          name.1 = atom → FirstOrderType space atom type := by
        intro name elaborated nameEq
        obtain ⟨instanceOf, typeEq⟩ := Schematic.elaborates_instance_iff.mp elaborated
        obtain ⟨valuation, firstOrder, instanceEq⟩ :=
          (Schematic.instanceOf_iff (by rw [nameEq]; exact declared)).mp instanceOf
        have instanceGround : Schematic.GroundFirstOrder name.2 := by
          rw [← instanceEq]
          exact firstOrder.ground free
        have equal := toTy_injective ground.static instanceGround.static typeEq
        subst equal
        exact .declared (occurrence := 0) ⟨scheme, by simp [declarations_of_declared declared],
          contractType_of_groundFirstOrder ground, valuation,
          fun name => typeAtom_of_reservedFree (firstOrder name).1, instanceEq⟩
      rcases Tuples.declaredType?_symbol_or_grounded declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · cases annotates with
        | symbol _ instanceType => exact constantCase elaborates rfl
      · cases annotates with
        | grounded _ instanceType => exact constantCase elaborates rfl
  | @application name arguments argumentTypes scheme returnType notState noAnnotation declared
      operator lengths _ argumentIH =>
      intro type ground typed
      obtain ⟨term, annotates, elaborates⟩ := typed
      cases annotates with
      | @application _ instanceType _ terms all =>
          rw [Schematic.elaborates_foldl_iff] at elaborates
          obtain ⟨holArguments, headElaborates, argumentsElaborate⟩ := elaborates
          obtain ⟨instanceOf, headTypeEq⟩ := Schematic.elaborates_instance_iff.mp headElaborates
          obtain ⟨valuation, firstOrder, instanceEq⟩ :=
            (Schematic.instanceOf_iff declared).mp instanceOf
          dsimp only at instanceEq
          have instanceArrow : instanceType =
              arrowAtom (argumentTypes.map (applyTypeValuation valuation))
                (applyTypeValuation valuation returnType) := by
            rw [← instanceEq, arrowAtom_of_functionType operator.function,
              applyTypeValuation_arrowAtom]
          have function : FunctionTypeRel instanceType
              (argumentTypes.map (applyTypeValuation valuation))
              (applyTypeValuation valuation returnType) := instanceArrow
          have elaborated : Elaborates (Schematic.instanceSignature space)
              (terms.foldl .app (.constant (.symbol name, instanceType))) (toTy type) :=
            (Schematic.elaborates_foldl_iff _ _ _).mpr
              ⟨holArguments, headElaborates, argumentsElaborate⟩
          have termLengths : terms.length = (argumentTypes.map (applyTypeValuation valuation)).length := by
            rw [List.length_map, ← lengths]
            exact all.length_eq.symm
          obtain ⟨_, resultEq, argumentsTyped⟩ :=
            (Schematic.elaborates_application_instance_iff function
              (by simpa using operator.nonempty) termLengths).mp elaborated
          have resultGround := firstOrder.ground operator.result
          have typeEq := toTy_injective ground.static resultGround.static resultEq
          subst typeEq
          have headGround : ∀ argumentType ∈ argumentTypes,
              Schematic.GroundFirstOrder (applyTypeValuation valuation argumentType) :=
            fun argumentType member => firstOrder.ground (operator.arguments argumentType member)
          refine .application (parameters := argumentTypes.map (applyTypeValuation valuation)) ?_ ?_
          · rw [← instanceArrow]
            refine .declared (occurrence := 0) ⟨scheme, by simp [declarations_of_declared declared],
              ?_, valuation, fun name => typeAtom_of_reservedFree (firstOrder name).1, instanceEq⟩
            rw [instanceArrow]
            refine contractType_arrowAtom (fun component member => ?_)
            rcases List.mem_append.mp member with member | member
            · obtain ⟨argumentType, argumentMember, rfl⟩ := List.mem_map.mp member
              exact contractType_of_groundFirstOrder (headGround argumentType argumentMember)
            · simp only [List.mem_singleton] at member
              subst member
              exact contractType_of_groundFirstOrder resultGround
          · refine firstOrderTypes_of_elaborated argumentIH all argumentsTyped ?_
            intro parameter member
            obtain ⟨argumentType, argumentMember, rfl⟩ := List.mem_map.mp member
            exact headGround argumentType argumentMember

/-- **First-order schemes.**  On first-order expressions over schematic declarations, contract
typing at a ground first-order type is exactly a first-order instance of HE's single exact
candidate, its principal type scheme. -/
theorem schematic_iff_exact {space : Space} {expression type : Atom}
    (fragment : Schematic.SchematicTerm space expression)
    (ground : Schematic.GroundFirstOrder type) :
    Typed space expression type ↔
      NoUndefinedFallback space expression ∧
        ∃ principal, ExactTypes space expression [principal] ∧
          ∃ valuation, Schematic.FirstOrderValuation valuation ∧
            applyTypeValuation valuation principal = type := by
  rw [typed_iff_firstOrder]
  refine Iff.trans ?_ (Schematic.schematic_hol_iff_exact fragment ground.static)
  constructor
  · intro typed
    have projected := schematicHOL_of_firstOrder fragment typed
    rwa [Schematic.project_of_groundFirstOrder ground] at projected
  · exact firstOrder_of_schematicHOL fragment ground

end Mettapedia.Languages.MeTTa.HE.HOLContract
