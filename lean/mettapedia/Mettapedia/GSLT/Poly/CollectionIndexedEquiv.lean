import Mettapedia.GSLT.Poly.CollectionIndexed
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn

/-!
# Closed object patterns as indexed trees

A language in the collection fragment has distinct constructor labels. At every
base sort, its closed object patterns are the free-monad trees of the indexed
polynomial. `vec` parameters contribute no quotient. Bags and sets are then
quotiented by the tree congruence: permutation of one bag or set parameter,
and deletion of a duplicate set child.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedEquiv

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Poly.BindingLanguage
open Mettapedia.GSLT.Poly.BindingSignature
open Mettapedia.GSLT.Poly.CollectionIndexed
open IPFunctor

variable {language : LanguageDef}

theorem baseCollection_shape {parameter : TermParam} {kind : CollType} {element : String}
    (shape : baseCollection? parameter = some (kind, element)) :
    ∃ name : String, parameter = .simple name (.collection kind (.base element)) := by
  cases parameter with
  | simple name type =>
      cases type with
      | collection collectionKind elementType =>
          cases elementType with
          | base elementSort =>
              simp only [baseCollection?, Option.some.injEq, Prod.mk.injEq] at shape
              obtain ⟨rfl, rfl⟩ := shape
              exact ⟨name, rfl⟩
          | arrow _ _ => simp [baseCollection?] at shape
          | multiBinder _ => simp [baseCollection?] at shape
          | collection _ _ => simp [baseCollection?] at shape
      | base _ => simp [baseCollection?] at shape
      | arrow _ _ => simp [baseCollection?] at shape
      | multiBinder _ => simp [baseCollection?] at shape
  | abstractionNamed _ _ _ => simp [baseCollection?] at shape
  | multiAbstractionNamed _ _ _ => simp [baseCollection?] at shape

theorem ofFn_elements_typed {Γ : List String} {element : String} {count : Nat}
    (children : Fin count → Pattern)
    (typed : ∀ index, HasType language FreeTypeContext.empty (typeContext Γ)
      (children index) (.base element)) :
    ElementsHaveType language FreeTypeContext.empty (typeContext Γ)
      (List.ofFn children) (.base element) := by
  induction count with
  | zero =>
      simp [List.ofFn_zero]
      exact ElementsHaveType.nil (typeContext Γ) (.base element)
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ]
      exact ElementsHaveType.cons (typed 0)
        (inductionHypothesis (fun index => children index.succ) fun index => typed index.succ)

theorem ofFn_elements_object {count : Nat} (children : Fin count → Pattern)
    (objects : ∀ index, isObjectPattern (children index) = true) :
    isObjectPatternList (List.ofFn children) = true := by
  induction count with
  | zero => simp [List.ofFn_zero, isObjectPatternList]
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ]
      simp [isObjectPatternList, objects 0,
        inductionHypothesis (fun index => children index.succ) fun index => objects index.succ]

/-- A bare collection's directions are `n` copies of the element sort, with no
binders of their own. -/
theorem bare_arity {sort : String} {kind : CollType} {element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element)) :
    (indexedSignature language).arity operator =
      List.replicate (operator.2.lengths.headD 0) ([], element) := by
  cases operator with
  | mk packed data =>
      cases packed with
      | mk rule _property =>
          cases rule with
          | mk label categoryName parameters syntaxPattern evalPolicy algebra representation =>
              cases parameters with
              | nil => simp [bareCollection?] at shape
              | cons parameter parameters =>
                  cases parameters with
                  | cons _ _ => simp [bareCollection?] at shape
                  | nil =>
                      cases parameter with
                      | abstractionNamed _ _ _ => simp [bareCollection?] at shape
                      | multiAbstractionNamed _ _ _ => simp [bareCollection?] at shape
                      | simple name type =>
                          cases type with
                          | base _ => simp [bareCollection?] at shape
                          | arrow _ _ => simp [bareCollection?] at shape
                          | multiBinder _ => simp [bareCollection?] at shape
                          | collection collectionKind elementType =>
                              cases elementType with
                              | arrow _ _ => simp [bareCollection?] at shape
                              | multiBinder _ => simp [bareCollection?] at shape
                              | collection _ _ => simp [bareCollection?] at shape
                              | base elementSort =>
                                  have mode : representation = .bare := by
                                    cases representation <;> simp_all [bareCollection?]
                                  subst mode
                                  simp only [bareCollection?, Option.some.injEq,
                                    Prod.mk.injEq] at shape
                                  obtain ⟨kindEq, elementEq⟩ := shape
                                  subst kindEq
                                  subst elementEq
                                  cases dataLengths : data.lengths with
                                  | nil =>
                                      have lengthEq := data.lengths_length
                                      rw [dataLengths] at lengthEq
                                      simp at lengthEq
                                  | cons length tail =>
                                      cases tail with
                                      | nil =>
                                          cases dataCounts : data.counts with
                                          | nil =>
                                              have countEq := data.counts_length
                                              rw [dataCounts] at countEq
                                              simp at countEq
                                          | cons count countsTail =>
                                              cases countsTail with
                                              | nil =>
                                                  simp [indexedSignature, dataLengths, dataCounts,
                                                    expandSlots, expandParam, baseCollection?]
                                              | cons _ _ =>
                                                  have countEq := data.counts_length
                                                  rw [dataCounts] at countEq
                                                  simp at countEq
                                      | cons _ _ =>
                                          have lengthEq := data.lengths_length
                                          rw [dataLengths] at lengthEq
                                          simp at lengthEq

theorem printArgument_hasType {Γ : List String} {parameter : TermParam} {count : Nat}
    {binders : List String} {result : String} {body : Pattern}
    (fragment : (bindingDecl? parameter).isSome)
    (declaration : slotBinders parameter count = (binders, result))
    (bodyTyped : HasType language FreeTypeContext.empty (typeContext (binders ++ Γ)) body
      (.base result)) :
    ∃ expected : TypeExpr, parameterType? parameter = some expected ∧
      HasType language FreeTypeContext.empty (typeContext Γ)
        (printArgument parameter count body) expected ∧
      MatchesParameterRepresentation parameter (printArgument parameter count body) := by
  cases inFragment_of_isSome fragment with
  | simple name sort =>
      simp only [slotBinders, Prod.mk.injEq] at declaration
      obtain ⟨bindersEq, resultEq⟩ := declaration
      subst bindersEq
      subst resultEq
      refine ⟨.base sort, rfl, ?_, trivial⟩
      simpa [printArgument, slotBinders, wrapBinders] using bodyTyped
  | abstraction binderName bodyName domain bodySort =>
      simp only [slotBinders, Prod.mk.injEq] at declaration
      obtain ⟨bindersEq, resultEq⟩ := declaration
      subst bindersEq
      subst resultEq
      refine ⟨.arrow (.base domain) (.base bodySort), rfl, ?_, ?_⟩
      · simpa [printArgument, slotBinders, wrapBinders, typeContext] using
          HasType.lambda bodyTyped
      · simp [MatchesParameterRepresentation, printArgument, slotBinders, wrapBinders]
  | shorthand binderName bodyName sort =>
      simp only [slotBinders, Prod.mk.injEq] at declaration
      obtain ⟨bindersEq, resultEq⟩ := declaration
      subst bindersEq
      subst resultEq
      refine ⟨.arrow (.base sort) (.base sort), rfl, ?_, ?_⟩
      · simpa [printArgument, slotBinders, wrapBinders, typeContext] using
          HasType.lambda bodyTyped
      · simp [MatchesParameterRepresentation, printArgument, slotBinders, wrapBinders]
  | multiShorthand binderNames bodyName sort =>
      simp only [slotBinders, Prod.mk.injEq] at declaration
      obtain ⟨bindersEq, resultEq⟩ := declaration
      subst bindersEq
      subst resultEq
      refine ⟨.arrow (.multiBinder (.base sort)) (.base sort), rfl, ?_, ?_⟩
      · have retyped :
            HasType language FreeTypeContext.empty
              (List.replicate count (.base sort) ++ typeContext Γ) body (.base sort) := by
          simpa [typeContext, List.map_append, List.map_replicate] using bodyTyped
        simpa [printArgument] using HasType.multiLambda retyped
      · simp [MatchesParameterRepresentation, printArgument]
  | multi binderNames bodyName domain bodySort =>
      simp only [slotBinders, Prod.mk.injEq] at declaration
      obtain ⟨bindersEq, resultEq⟩ := declaration
      subst bindersEq
      subst resultEq
      refine ⟨.arrow (.multiBinder (.base domain)) (.base bodySort), rfl, ?_, ?_⟩
      · have retyped :
            HasType language FreeTypeContext.empty
              (List.replicate count (.base domain) ++ typeContext Γ) body (.base bodySort) := by
          simpa [typeContext, List.map_append, List.map_replicate] using bodyTyped
        simpa [printArgument] using HasType.multiLambda retyped
      · simp [MatchesParameterRepresentation, printArgument]

theorem bare_rule_params {rule : GrammarRule} {kind : CollType} {element : String}
    (shape : bareCollection? rule = some (kind, element)) :
    ∃ name : String, rule.params = [.simple name (.collection kind (.base element))] := by
  have used := bareCollection_uses shape
  rcases used with ⟨name, collectionKind, elementType, bareEq⟩
  obtain ⟨mode, paramsEq⟩ := (GrammarRule.bareParams_cons_iff _ _ _).mp bareEq
  cases elementType with
  | base elementSort =>
      have bare : bareCollection? rule = some (collectionKind, elementSort) := by
        simp [bareCollection?, paramsEq, mode]
      simp only [shape, Option.some.injEq, Prod.mk.injEq] at bare
      obtain ⟨rfl, rfl⟩ := bare
      exact ⟨name, paramsEq⟩
  | arrow _ _ => simp [bareCollection?, paramsEq] at shape
  | multiBinder _ => simp [bareCollection?, paramsEq] at shape
  | collection _ _ => simp [bareCollection?, paramsEq] at shape

/-- The same parameter as the bare-collection typing rule sees it. -/
theorem bare_rule_bareParams {rule : GrammarRule} {kind : CollType} {element : String}
    (shape : bareCollection? rule = some (kind, element)) :
    ∃ name : String, rule.bareParams = [.simple name (.collection kind (.base element))] := by
  obtain ⟨name, paramsEq⟩ := bare_rule_params shape
  have mode : rule.collectionRepresentation = .bare := by
    cases representation : rule.collectionRepresentation
    · rfl
    · simp [bareCollection?, paramsEq, representation] at shape
  exact ⟨name, (GrammarRule.bareParams_of_bare _ mode).trans paramsEq⟩

def slotFin' (parameters : List TermParam) (counts lengths : List Nat)
    (index : Fin (slotCount parameters counts lengths)) :
    Fin (expandSlots parameters counts lengths).length :=
  ⟨index.val, (expandSlots_length parameters counts lengths).symm ▸ index.isLt⟩

theorem getElem_of_list_eq {α : Type} {left right : List α} (equal : left = right) {index : Nat}
    (bound : index < left.length) :
    left[index] = right[index]'(equal ▸ bound) := by
  subst equal
  rfl

theorem toPattern_direction_eq {Γ : List String} {sort : String}
    {operator : (indexedSignature language).Op sort}
    (children : Child language Γ sort operator)
    {left right : Fin ((indexedSignature language).arity operator).length}
    (equal : left = right) :
    toPattern (children left) = toPattern (children right) := by
  subst equal
  rfl

theorem assemblePrinted_hasType {Γ : List String} {total : Nat}
    (printed : Fin total → Pattern) (offset : Nat) (parameters : List TermParam)
    (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (fit : offset + slotCount parameters counts lengths ≤ total)
    (fragment : ∀ parameter ∈ parameters,
      (bindingDecl? parameter).isSome ∨ (baseCollection? parameter).isSome)
    (typed : ∀ index : Fin (slotCount parameters counts lengths),
      HasType language FreeTypeContext.empty
        (typeContext
          (((expandSlots parameters counts lengths).get
              (slotFin' parameters counts lengths index)).1 ++ Γ))
        (nthPrinted printed (offset + index.val))
        (.base ((expandSlots parameters counts lengths).get
          (slotFin' parameters counts lengths index)).2)) :
    ArgumentsHaveTypes language FreeTypeContext.empty (typeContext Γ)
      (assemblePrinted printed offset parameters counts lengths) parameters := by
  induction parameters generalizing counts lengths offset with
  | nil =>
      simp [assemblePrinted]
      exact ArgumentsHaveTypes.nil (bound := typeContext Γ)
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp only [List.length_cons] at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp only [List.length_cons] at lengthsLength
                omega
              have tailFragment : ∀ item ∈ parameters,
                  (bindingDecl? item).isSome ∨ (baseCollection? item).isSome :=
                fun item member => fragment item (List.mem_cons_of_mem _ member)
              cases reading : baseCollection? parameter with
              | some packed =>
                  obtain ⟨kind, element⟩ := packed
                  obtain ⟨name, parameterEq⟩ := baseCollection_shape reading
                  subst parameterEq
                  simp only [assemblePrinted, baseCollection?]
                  have headSlot : ∀ index : Fin length,
                      index.val <
                        slotCount
                          (.simple name (.collection kind (.base element)) :: parameters)
                          (count :: counts) (length :: lengths) := by
                    intro index
                    have indexBound := index.isLt
                    simp [slotCount, directionsOf, baseCollection?]
                    omega
                  refine ArgumentsHaveTypes.cons trivial rfl ?collectionHead ?collectionTail
                  · apply HasType.collection
                    refine ofFn_elements_typed
                      (fun index : Fin length => nthPrinted printed (offset + index.val)) ?_
                    intro index
                    let slotIndex : Fin (slotCount
                        (.simple name (.collection kind (.base element)) :: parameters)
                        (count :: counts) (length :: lengths)) :=
                      ⟨index.val, headSlot index⟩
                    have raw := typed slotIndex
                    have declaration :
                        (expandSlots
                            (.simple name (.collection kind (.base element)) :: parameters)
                            (count :: counts) (length :: lengths)).get
                          (slotFin'
                            (.simple name (.collection kind (.base element)) :: parameters)
                            (count :: counts) (length :: lengths) slotIndex) =
                          ([], element) := by
                      simp only [slotFin', expandSlots, expandParam, baseCollection?,
                        List.get_eq_getElem]
                      have low : slotIndex.val <
                          (List.replicate length (([] : List String), element)).length := by
                        rw [List.length_replicate]
                        simp [slotIndex]
                      rw [List.getElem_append_left low]
                      simp [List.getElem_replicate]
                    rw [declaration] at raw
                    simpa [typeContext] using raw
                  · have width :
                        slotCount
                            (.simple name (.collection kind (.base element)) :: parameters)
                            (count :: counts) (length :: lengths) =
                          length + slotCount parameters counts lengths := by
                      simp [slotCount, directionsOf, baseCollection?]
                    have tailFit :
                        offset + length + slotCount parameters counts lengths ≤ total := by
                      omega
                    have tailTyped :
                        ∀ index : Fin (slotCount parameters counts lengths),
                          HasType language FreeTypeContext.empty
                            (typeContext
                              (((expandSlots parameters counts lengths).get
                                  (slotFin' parameters counts lengths index)).1 ++ Γ))
                            (nthPrinted printed (offset + length + index.val))
                            (.base ((expandSlots parameters counts lengths).get
                              (slotFin' parameters counts lengths index)).2) := by
                      intro index
                      have slotBound :
                          length + index.val <
                            slotCount
                              (.simple name (.collection kind (.base element)) :: parameters)
                              (count :: counts) (length :: lengths) := by
                        have indexBound := index.isLt
                        have widthBound :
                            slotCount
                                (.simple name (.collection kind (.base element)) :: parameters)
                                (count :: counts) (length :: lengths) =
                              length + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, baseCollection?]
                        omega
                      let slotIndex :
                          Fin (slotCount
                            (.simple name (.collection kind (.base element)) :: parameters)
                            (count :: counts) (length :: lengths)) :=
                        ⟨length + index.val, slotBound⟩
                      have raw := typed slotIndex
                      have sameGet :
                          (expandSlots
                              (.simple name (.collection kind (.base element)) :: parameters)
                              (count :: counts) (length :: lengths)).get
                            (slotFin'
                              (.simple name (.collection kind (.base element)) :: parameters)
                              (count :: counts) (length :: lengths) slotIndex) =
                            (expandSlots parameters counts lengths).get
                              (slotFin' parameters counts lengths index) := by
                        simp only [slotFin', expandSlots, expandParam, baseCollection?,
                          List.get_eq_getElem]
                        have high : (List.replicate length (([] : List String), element)).length ≤
                            slotIndex.val := by
                          rw [List.length_replicate]
                          simp [slotIndex]
                        rw [List.getElem_append_right high]
                        simp [slotIndex, List.length_replicate]
                      have patternEq :
                          nthPrinted printed (offset + slotIndex.val) =
                            nthPrinted printed (offset + length + index.val) := by
                        have valEq : slotIndex.val = length + index.val := by simp [slotIndex]
                        rw [valEq]
                        exact congrArg (nthPrinted printed) (Nat.add_assoc offset length index.val).symm
                      rw [sameGet] at raw
                      rw [patternEq] at raw
                      exact raw
                    exact inductionHypothesis (offset + length) counts lengths tailCounts
                      tailLengths tailFit tailFragment tailTyped
              | none =>
                  have binder : (bindingDecl? parameter).isSome := by
                    have member := fragment parameter List.mem_cons_self
                    simpa [reading] using member
                  simp only [assemblePrinted, reading]
                  have slotBound :
                      0 < slotCount (parameter :: parameters) (count :: counts)
                        (length :: lengths) := by
                    simp [slotCount, directionsOf, reading]
                  let slotIndex :
                      Fin (slotCount (parameter :: parameters) (count :: counts)
                        (length :: lengths)) :=
                    ⟨0, slotBound⟩
                  have raw := typed slotIndex
                  have declaration :
                      (expandSlots (parameter :: parameters) (count :: counts)
                          (length :: lengths)).get
                        (slotFin' (parameter :: parameters) (count :: counts)
                          (length :: lengths) slotIndex) =
                        slotBinders parameter count := by
                    simp only [slotFin', expandSlots, expandParam, reading, List.get_eq_getElem,
                      slotIndex]
                    exact List.getElem_cons_zero _ _ _
                  have patternEq :
                      nthPrinted printed (offset + slotIndex.val) = nthPrinted printed offset := by
                    have valEq : slotIndex.val = 0 := by simp [slotIndex]
                    rw [valEq, Nat.add_zero]
                  have bodyAt :
                      HasType language FreeTypeContext.empty
                        (typeContext ((slotBinders parameter count).1 ++ Γ))
                        (nthPrinted printed offset)
                        (.base (slotBinders parameter count).2) := by
                    rw [declaration] at raw
                    rw [patternEq] at raw
                    simpa [typeContext] using raw
                  obtain ⟨expected, expectedEq, argumentTyped, representation⟩ :=
                    printArgument_hasType binder rfl bodyAt
                  refine ArgumentsHaveTypes.cons representation expectedEq argumentTyped ?binderTail
                  · have width :
                        slotCount (parameter :: parameters) (count :: counts)
                            (length :: lengths) =
                          1 + slotCount parameters counts lengths := by
                      simp [slotCount, directionsOf, reading]
                    have tailFit :
                        offset + 1 + slotCount parameters counts lengths ≤ total := by
                      omega
                    have tailTyped :
                        ∀ index : Fin (slotCount parameters counts lengths),
                          HasType language FreeTypeContext.empty
                            (typeContext
                              (((expandSlots parameters counts lengths).get
                                  (slotFin' parameters counts lengths index)).1 ++ Γ))
                            (nthPrinted printed (offset + 1 + index.val))
                            (.base ((expandSlots parameters counts lengths).get
                              (slotFin' parameters counts lengths index)).2) := by
                      intro index
                      have slotBound :
                          1 + index.val <
                            slotCount (parameter :: parameters) (count :: counts)
                              (length :: lengths) := by
                        have indexBound := index.isLt
                        have widthBound :
                            slotCount (parameter :: parameters) (count :: counts)
                                (length :: lengths) =
                              1 + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, reading]
                        omega
                      let slotIndex :
                          Fin (slotCount (parameter :: parameters) (count :: counts)
                            (length :: lengths)) :=
                        ⟨1 + index.val, slotBound⟩
                      have raw := typed slotIndex
                      have sameGet :
                          (expandSlots (parameter :: parameters) (count :: counts)
                              (length :: lengths)).get
                            (slotFin' (parameter :: parameters) (count :: counts)
                              (length :: lengths) slotIndex) =
                            (expandSlots parameters counts lengths).get
                              (slotFin' parameters counts lengths index) := by
                        simp only [slotFin', expandSlots, expandParam, reading, List.get_eq_getElem,
                          slotIndex, List.singleton_append, Nat.add_comm, List.getElem_cons_succ]
                      have patternEq :
                          nthPrinted printed (offset + slotIndex.val) =
                            nthPrinted printed (offset + 1 + index.val) := by
                        have valEq : slotIndex.val = 1 + index.val := by simp [slotIndex]
                        rw [valEq]
                        exact congrArg (nthPrinted printed) (Nat.add_assoc offset 1 index.val).symm
                      rw [sameGet] at raw
                      rw [patternEq] at raw
                      exact raw
                    exact inductionHypothesis (offset + 1) counts lengths tailCounts tailLengths
                      tailFit tailFragment tailTyped

theorem toPattern_hasType {index : List String × String} (tree : Tree language index) :
    HasType language FreeTypeContext.empty (typeContext index.1) (toPattern tree)
      (.base index.2) := by
  induction tree using IFreeM.inductionOn with
  | pure index variable_ =>
      rw [toPattern_pure]
      exact HasType.bvar (varIndex_lookup variable_)
  | liftBind index operator children childTyped =>
      cases index with
      | mk Γ sort =>
          rw [toPattern_liftBind]
          cases shape : bareCollection? operator.1.1 with
          | some packed =>
              obtain ⟨kind, element⟩ := packed
              obtain ⟨parameterName, paramsEq⟩ := bare_rule_params shape
              obtain ⟨_, bareParamsEq⟩ := bare_rule_bareParams shape
              simp only [nodeOf, shape]
              have elementsTyped :
                  ElementsHaveType language FreeTypeContext.empty (typeContext Γ)
                    (List.ofFn fun direction => toPattern (children direction))
                    (.base element) :=
                ofFn_elements_typed _ fun direction => by
                  have raw := childTyped direction
                  have declaration :
                      ((indexedSignature language).arity operator).get direction =
                        ([], element) := by
                    have arityEq := bare_arity operator shape
                    have casted := getElem_of_list_eq arityEq direction.isLt
                    simpa [List.get_eq_getElem, List.getElem_replicate] using casted
                  simp only [declaration, typeContext] at raw
                  exact raw
              have typed :=
                HasType.collectionConstructor (rule := operator.1.1) (rest := none)
                  operator.1.2.1 bareParamsEq elementsTyped
              simpa [operator.1.2.2.2] using typed
          | none =>
              simp only [nodeOf, shape]
              have fitDir :
                  0 + slotCount operator.1.1.params operator.2.counts operator.2.lengths ≤
                    ((indexedSignature language).arity operator).length := by
                rw [Nat.zero_add]
                simp only [indexedSignature, expandSlots_length]
                exact Nat.le_refl _
              have argsTyped :=
                assemblePrinted_hasType
                  (fun direction => toPattern (children direction)) 0
                  operator.1.1.params operator.2.counts operator.2.lengths
                  operator.2.counts_length operator.2.lengths_length fitDir
                  (fun parameter member => operator.1.2.2.1 parameter member)
                  (fun index => by
                    let direction :=
                      slotFin' operator.1.1.params operator.2.counts operator.2.lengths index
                    have raw := childTyped direction
                    have bound : 0 + index.val <
                        ((indexedSignature language).arity operator).length := by
                      rw [Nat.zero_add]
                      have valEq : direction.val = index.val := by
                        simp [direction, slotFin']
                      rw [← valEq]
                      exact direction.isLt
                    have finEq :
                        (⟨0 + index.val, bound⟩ :
                          Fin ((indexedSignature language).arity operator).length) =
                          direction := by
                      apply Fin.ext
                      simp [Fin.val_mk, direction, slotFin']
                    have patternEq :
                        nthPrinted (fun child => toPattern (children child)) (0 + index.val) =
                          toPattern (children direction) := by
                      rw [nthPrinted_of_lt _ bound]
                      exact toPattern_direction_eq children finEq
                    rw [← patternEq] at raw
                    exact raw)
              have typed :=
                HasType.constructor (rule := operator.1.1) operator.1.2.1
                  (not_bare_of_fragment operator.1.2.2.1 shape) argsTyped
              simpa [operator.1.2.2.2] using typed

theorem assemblePrinted_isObject {total : Nat}
    (printed : Fin total → Pattern) (offset : Nat) (parameters : List TermParam)
    (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (objects : ∀ index : Fin (slotCount parameters counts lengths),
      isObjectPattern (nthPrinted printed (offset + index.val)) = true) :
    ∀ pattern ∈ assemblePrinted printed offset parameters counts lengths,
      isObjectPattern pattern = true := by
  induction parameters generalizing counts lengths offset with
  | nil => simp [assemblePrinted]
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp only [List.length_cons] at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp only [List.length_cons] at lengthsLength
                omega
              cases reading : baseCollection? parameter with
              | some packed =>
                  obtain ⟨kind, element⟩ := packed
                  obtain ⟨name, parameterEq⟩ := baseCollection_shape reading
                  subst parameterEq
                  simp only [assemblePrinted, baseCollection?, List.mem_cons, forall_eq_or_imp]
                  refine ⟨?_, ?_⟩
                  · simp only [isObjectPattern, Option.isNone, Bool.true_and]
                    refine ofFn_elements_object _ ?_
                    intro index
                    have slotBound : index.val <
                        slotCount
                          (.simple name (.collection kind (.base element)) :: parameters)
                          (count :: counts) (length :: lengths) := by
                      have indexBound := index.isLt
                      simp [slotCount, directionsOf, baseCollection?]
                      omega
                    let slotIndex : Fin (slotCount
                        (.simple name (.collection kind (.base element)) :: parameters)
                        (count :: counts) (length :: lengths)) :=
                      ⟨index.val, slotBound⟩
                    have raw := objects slotIndex
                    have valEq : slotIndex.val = index.val := by simp [slotIndex]
                    rw [valEq] at raw
                    exact raw
                  · have tailObjects :
                        ∀ index : Fin (slotCount parameters counts lengths),
                          isObjectPattern
                            (nthPrinted printed (offset + length + index.val)) = true := by
                      intro index
                      have slotBound : length + index.val <
                          slotCount
                            (.simple name (.collection kind (.base element)) :: parameters)
                            (count :: counts) (length :: lengths) := by
                        have indexBound := index.isLt
                        have widthBound :
                            slotCount
                                (.simple name (.collection kind (.base element)) :: parameters)
                                (count :: counts) (length :: lengths) =
                              length + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, baseCollection?]
                        omega
                      let slotIndex : Fin _ := ⟨length + index.val, slotBound⟩
                      have raw := objects slotIndex
                      have patternEq :
                          nthPrinted printed (offset + slotIndex.val) =
                            nthPrinted printed (offset + length + index.val) := by
                        have valEq : slotIndex.val = length + index.val := by simp [slotIndex]
                        rw [valEq]
                        exact congrArg (nthPrinted printed)
                          (Nat.add_assoc offset length index.val).symm
                      rw [patternEq] at raw
                      exact raw
                    exact inductionHypothesis (offset + length) counts lengths tailCounts
                      tailLengths tailObjects
              | none =>
                  simp only [assemblePrinted, reading, List.mem_cons, forall_eq_or_imp]
                  refine ⟨?_, ?_⟩
                  · have slotBound : 0 <
                        slotCount (parameter :: parameters) (count :: counts)
                          (length :: lengths) := by
                      simp [slotCount, directionsOf, reading]
                    let slotIndex : Fin (slotCount (parameter :: parameters) (count :: counts)
                        (length :: lengths)) := ⟨0, slotBound⟩
                    have raw := objects slotIndex
                    have patternEq :
                        nthPrinted printed (offset + slotIndex.val) =
                          nthPrinted printed offset := by
                      have valEq : slotIndex.val = 0 := by simp [slotIndex]
                      rw [valEq, Nat.add_zero]
                    rw [patternEq] at raw
                    exact printArgument_isObject parameter count raw
                  · have tailObjects :
                        ∀ index : Fin (slotCount parameters counts lengths),
                          isObjectPattern (nthPrinted printed (offset + 1 + index.val)) = true := by
                      intro index
                      have slotBound : 1 + index.val <
                          slotCount (parameter :: parameters) (count :: counts)
                            (length :: lengths) := by
                        have indexBound := index.isLt
                        have widthBound :
                            slotCount (parameter :: parameters) (count :: counts)
                                (length :: lengths) =
                              1 + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, reading]
                        omega
                      let slotIndex : Fin _ := ⟨1 + index.val, slotBound⟩
                      have raw := objects slotIndex
                      have patternEq :
                          nthPrinted printed (offset + slotIndex.val) =
                            nthPrinted printed (offset + 1 + index.val) := by
                        have valEq : slotIndex.val = 1 + index.val := by simp [slotIndex]
                        rw [valEq]
                        exact congrArg (nthPrinted printed) (Nat.add_assoc offset 1 index.val).symm
                      rw [patternEq] at raw
                      exact raw
                    exact inductionHypothesis (offset + 1) counts lengths tailCounts tailLengths
                      tailObjects

theorem toPattern_isObject {index : List String × String} (tree : Tree language index) :
    isObjectPattern (toPattern tree) = true := by
  induction tree using IFreeM.inductionOn with
  | pure _ _ =>
      rw [toPattern_pure]
      rfl
  | liftBind index operator children childObject =>
      cases index with
      | mk Γ sort =>
          rw [toPattern_liftBind]
          cases shape : bareCollection? operator.1.1 with
          | some _ =>
              simp only [nodeOf, shape, isObjectPattern, Option.isNone, Bool.true_and]
              exact ofFn_elements_object _ childObject
          | none =>
              simp only [nodeOf, shape, isObjectPattern]
              rw [isObjectPatternList_eq_true_iff]
              refine assemblePrinted_isObject
                (fun direction => toPattern (children direction)) 0
                operator.1.1.params operator.2.counts operator.2.lengths
                operator.2.counts_length operator.2.lengths_length ?_
              intro index
              let direction :=
                slotFin' operator.1.1.params operator.2.counts operator.2.lengths index
              have bound : 0 + index.val <
                  ((indexedSignature language).arity operator).length := by
                rw [Nat.zero_add]
                have valEq : direction.val = index.val := by simp [direction, slotFin']
                rw [← valEq]
                exact direction.isLt
              have finEq :
                  (⟨0 + index.val, bound⟩ :
                    Fin ((indexedSignature language).arity operator).length) = direction := by
                apply Fin.ext
                simp [Fin.val_mk, direction, slotFin']
              have patternEq :
                  nthPrinted (fun child => toPattern (children child)) (0 + index.val) =
                    toPattern (children direction) := by
                rw [nthPrinted_of_lt _ bound]
                exact toPattern_direction_eq children finEq
              rw [patternEq]
              exact childObject direction

/-- Patterns modulo permutation of one bag or set, and deletion of one duplicate
set child. -/
def patternSetoid (sort : String) : Setoid (ClosedObject language sort) where
  r left right := PatternCong left.1 right.1
  iseqv :=
    ⟨fun pattern => PatternCong.refl pattern.1,
      fun related => PatternCong.symm related,
      fun first second => PatternCong.trans first second⟩

/-- Trees modulo the indexed tree congruence. -/
def treeSetoid (sort : String) : Setoid (Tree language ([], sort)) where
  r := TreeCong language
  iseqv :=
    ⟨fun tree => TreeCong.refl tree,
      fun related => TreeCong.symm related,
      fun first second => TreeCong.trans first second⟩

/-- At most one bare collection rule of a given kind at a given sort.

A bare collection is printed without its label, so distinct labels do not
separate two such rules. The element sort is part of the rule, and the
equation forces it to agree as well. -/
def UniqueBare (language : LanguageDef) : Prop :=
  ∀ {rule₁ rule₂ : GrammarRule} {kind : CollType} {element₁ element₂ : String},
    rule₁ ∈ language.terms →
    rule₂ ∈ language.terms →
    rule₁.category = rule₂.category →
    bareCollection? rule₁ = some (kind, element₁) →
    bareCollection? rule₂ = some (kind, element₂) →
    rule₁ = rule₂

theorem toPattern_cast {index index' : List String × String} (equal : index = index')
    (tree : Tree language index) :
    toPattern (cast (congrArg (Tree language) equal) tree) = toPattern tree := by
  subst equal
  rfl

theorem ofFn_pointwise {α : Type*} {n : Nat} {left right : Fin n → α}
    (agree : ∀ index, left index = right index) :
    List.ofFn left = List.ofFn right := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.cons_eq_cons.mpr
        ⟨agree 0, inductionHypothesis (fun index => agree index.succ)⟩

/-- Assembled arguments depend only on the children actually read. -/
theorem assemblePrinted_congr {total total' : Nat}
    (printed : Fin total → Pattern) (printed' : Fin total' → Pattern)
    (offset : Nat) (parameters : List TermParam) (counts lengths : List Nat)
    (agree : ∀ index : Nat, offset ≤ index →
      index < offset + slotCount parameters counts lengths →
      nthPrinted printed index = nthPrinted printed' index) :
    assemblePrinted printed offset parameters counts lengths =
      assemblePrinted printed' offset parameters counts lengths := by
  induction parameters generalizing counts lengths offset with
  | nil => simp [assemblePrinted]
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp [assemblePrinted]
      | cons count counts =>
          cases lengths with
          | nil => simp [assemblePrinted]
          | cons length lengths =>
              cases reading : baseCollection? parameter with
              | some packed =>
                  simp only [assemblePrinted, reading]
                  have childrenEq :
                      List.ofFn (fun index : Fin length =>
                          nthPrinted printed (offset + index.val)) =
                        List.ofFn (fun index : Fin length =>
                          nthPrinted printed' (offset + index.val)) :=
                    ofFn_pointwise fun index =>
                      agree (offset + index.val) (Nat.le_add_right _ _) <| by
                        have indexBound := index.isLt
                        have width :
                            slotCount (parameter :: parameters) (count :: counts)
                                (length :: lengths) =
                              length + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, reading]
                        omega
                  have tailEq :=
                    inductionHypothesis (offset + length) counts lengths fun index lower upper =>
                      agree index (Nat.le_trans (Nat.le_add_right offset length) lower) <| by
                        have width :
                            slotCount (parameter :: parameters) (count :: counts)
                                (length :: lengths) =
                              length + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, reading]
                        omega
                  simp [childrenEq, tailEq]
              | none =>
                  simp only [assemblePrinted, reading]
                  have headEq : nthPrinted printed offset = nthPrinted printed' offset :=
                    agree offset (Nat.le_refl _) <| by
                      have width :
                          0 < slotCount (parameter :: parameters) (count :: counts)
                            (length :: lengths) := by
                        simp [slotCount, directionsOf, reading]
                      omega
                  have tailEq :=
                    inductionHypothesis (offset + 1) counts lengths fun index lower upper =>
                      agree index (Nat.le_trans (Nat.le_add_right offset 1) lower) <| by
                        have width :
                            slotCount (parameter :: parameters) (count :: counts)
                                (length :: lengths) =
                              1 + slotCount parameters counts lengths := by
                          simp [slotCount, directionsOf, reading]
                        omega
                  simp [headEq, tailEq]

/-- Element patterns of one collection, read as trees at that element sort. -/
theorem exists_list_trees {bound : Nat}
    (recurse :
      ∀ {Γ : List String} {sort : String} (pattern : Pattern),
        sizeOf pattern < bound →
        HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
        isObjectPattern pattern = true →
        ∃ tree : Tree language (Γ, sort), CollectionIndexed.toPattern tree = pattern)
    {Γ : List String} {element : String} (elements : List Pattern)
    (typed : ElementsHaveType language FreeTypeContext.empty (typeContext Γ) elements
      (.base element))
    (objects : ∀ pattern ∈ elements, isObjectPattern pattern = true)
    (smaller : ∀ pattern ∈ elements, sizeOf pattern < bound) :
    ∃ trees : List (Tree language (Γ, element)),
      trees.map CollectionIndexed.toPattern = elements := by
  induction elements with
  | nil =>
      cases typed
      exact ⟨[], rfl⟩
  | cons head tail inductionHypothesis =>
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨headTree, headPrinted⟩ :=
            recurse head (smaller head List.mem_cons_self) headTyped
              (objects head List.mem_cons_self)
          obtain ⟨tailTrees, tailPrinted⟩ :=
            inductionHypothesis tailTyped
              (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
              (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
          exact ⟨headTree :: tailTrees, by simp [List.map_cons, headPrinted, tailPrinted]⟩

theorem map_eq_ofFn_get {α β : Type*} (function : α → β) (values : List α) :
    List.ofFn (fun index : Fin values.length => function (values.get index)) =
      values.map function := by
  induction values with
  | nil => simp [List.ofFn_zero]
  | cons head tail inductionHypothesis =>
      rw [List.ofFn_succ, List.map_cons, List.get_cons_zero]
      have tailEq :
          List.ofFn (fun index : Fin tail.length =>
              function ((head :: tail).get index.succ)) =
            List.ofFn (fun index : Fin tail.length => function (tail.get index)) :=
        ofFn_pointwise fun index => by simp
      rw [tailEq, inductionHypothesis]

theorem element_base_of_fragment {rule : GrammarRule} {name : String} {kind : CollType}
    {elementType : TypeExpr}
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (member : rule ∈ language.terms)
    (paramsEq : rule.params = [.simple name (.collection kind elementType)]) :
    ∃ element : String, elementType = .base element := by
  have ok :=
    fragment rule member (.simple name (.collection kind elementType)) (by simp [paramsEq])
  cases elementType with
  | base element => exact ⟨element, rfl⟩
  | arrow _ _ => simp [bindingDecl?, baseCollection?] at ok
  | multiBinder _ => simp [bindingDecl?, baseCollection?] at ok
  | collection _ _ => simp [bindingDecl?, baseCollection?] at ok

/-- A bare collection object is the indexed tree of its element trees. -/
theorem exists_collection_tree
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule) {bound : Nat}
    (recurse :
      ∀ {Γ : List String} {sort : String} (pattern : Pattern),
        sizeOf pattern < bound →
        HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
        isObjectPattern pattern = true →
        ∃ tree : Tree language (Γ, sort), CollectionIndexed.toPattern tree = pattern)
    {Γ : List String} {sort : String} {kind : CollType} {elements : List Pattern}
    (typed : HasType language FreeTypeContext.empty (typeContext Γ)
      (.collection kind elements none) (.base sort))
    (objects : ∀ pattern ∈ elements, isObjectPattern pattern = true)
    (smaller : ∀ pattern ∈ elements, sizeOf pattern < bound) :
    ∃ tree : Tree language (Γ, sort),
      CollectionIndexed.toPattern tree = .collection kind elements none := by
  cases typed with
  | collectionConstructor member paramsEq elementsTyped =>
      rename_i rule parameterName elementType
      obtain ⟨mode, paramsEq⟩ := (GrammarRule.bareParams_cons_iff _ _ _).mp paramsEq
      obtain ⟨element, elementEq⟩ :=
        element_base_of_fragment fragment member paramsEq
      subst elementEq
      obtain ⟨trees, treesPrinted⟩ :=
        exists_list_trees recurse elements elementsTyped objects smaller
      let data : HeadData rule.params :=
        { counts := [0]
          lengths := [elements.length]
          counts_length := by simp [paramsEq]
          lengths_length := by simp [paramsEq]
          counts_fixed := by
            intro index _
            cases index <;> simp [List.getD]
          lengths_fixed := by
            intro index premise
            cases index with
            | zero => simp [paramsEq, List.getD, baseCollection?] at premise
            | succ _ => simp [List.getD] }
      let operator : (indexedSignature language).Op rule.category :=
        ⟨⟨rule, member, fragment rule member, rfl⟩, data⟩
      have shape : bareCollection? operator.1.1 = some (kind, element) := by
        simp [operator, bareCollection?, paramsEq, mode]
      have arityEq := bare_arity operator shape
      have treeLength : trees.length = elements.length := by
        simpa using congrArg List.length treesPrinted
      have width : ((indexedSignature language).arity operator).length = elements.length := by
        rw [arityEq]
        simp [operator, data, List.length_replicate, List.headD]
      have directionDecl (direction : Fin ((indexedSignature language).arity operator).length) :
          ((indexedSignature language).arity operator).get direction = ([], element) := by
        have casted := getElem_of_list_eq arityEq direction.isLt
        simpa [List.get_eq_getElem, List.getElem_replicate] using casted
      let children : Child language Γ rule.category operator :=
        fun direction =>
          cast (congrArg (Tree language)
              (collection_direction_lands (Γ := Γ) operator direction
                (directionDecl direction)).symm)
            (trees.get (Fin.cast (width.trans treeLength.symm) direction))
      refine ⟨IFreeM.liftBind (P := polynomial (indexedSignature language))
        (s := (Γ, rule.category)) operator children, ?_⟩
      rw [toPattern_liftBind]
      simp only [nodeOf, shape]
      simp only [Pattern.collection.injEq, true_and]
      have childPrinted :
          List.ofFn (fun direction => CollectionIndexed.toPattern (children direction)) =
            List.ofFn (fun direction =>
              CollectionIndexed.toPattern
                (trees.get (Fin.cast (width.trans treeLength.symm) direction))) := by
        refine ofFn_pointwise ?_
        intro direction
        unfold children
        exact toPattern_cast
          (collection_direction_lands (Γ := Γ) operator direction (directionDecl direction)).symm
          (trees.get (Fin.cast (width.trans treeLength.symm) direction))
      have transported :=
        List.ofFn_congr (width.trans treeLength.symm).symm
          (fun index : Fin trees.length => CollectionIndexed.toPattern (trees.get index))
      have asElements :
          List.ofFn (fun index : Fin trees.length =>
              CollectionIndexed.toPattern (trees.get index)) = elements :=
        (map_eq_ofFn_get CollectionIndexed.toPattern trees).trans treesPrinted
      rw [childPrinted, ← transported, asElements]
      exact ⟨rfl, trivial⟩

/-- One child of a parameter, in the context that child opens. -/
structure Opened (language : LanguageDef) (Γ : List String) where
  binders : List String
  sort : String
  tree : Tree language (binders ++ Γ, sort)

/-- Binder count, collection length, and child trees of one argument. -/
structure ParamOpening (language : LanguageDef) (Γ : List String)
    (parameter : TermParam) (argument : Pattern) where
  count : Nat
  length : Nat
  countOk : (multiBase? parameter).isNone → count = 0
  lengthOk : (baseCollection? parameter).isNone → length = 0
  opened : List (Opened language Γ)
  lengthEq : opened.length = directionsOf parameter count length
  declsEq :
    opened.map (fun slot => (slot.binders, slot.sort)) = expandParam parameter count length
  patternsEq :
    argument =
      match baseCollection? parameter with
      | some (kind, _) =>
          .collection kind
            (opened.map fun slot => CollectionIndexed.toPattern slot.tree) none
      | none =>
          printArgument parameter count
            ((opened.map fun slot => CollectionIndexed.toPattern slot.tree).headD (.bvar 0))

theorem opened_decls_replicate {Γ : List String} {element : String}
    (trees : List (Tree language (Γ, element))) :
    ((trees.map fun tree => (⟨[], element, tree⟩ : Opened language Γ)).map
        fun slot => (slot.binders, slot.sort)) =
      List.replicate trees.length ([], element) := by
  induction trees with
  | nil => simp
  | cons _ tail inductionHypothesis =>
      simp only [List.map_cons]
      exact congrArg (List.cons ([], element)) inductionHypothesis

theorem exists_param_opening {bound : Nat}
    (recurse :
      ∀ {Γ : List String} {sort : String} (pattern : Pattern),
        sizeOf pattern < bound →
        HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
        isObjectPattern pattern = true →
        ∃ tree : Tree language (Γ, sort), CollectionIndexed.toPattern tree = pattern)
    {Γ : List String} (parameter : TermParam)
    (fragmentParam : (bindingDecl? parameter).isSome ∨ (baseCollection? parameter).isSome)
    (argument : Pattern)
    (representation : MatchesParameterRepresentation parameter argument)
    (expected : TypeExpr)
    (expectedEq : parameterType? parameter = some expected)
    (typed : HasType language FreeTypeContext.empty (typeContext Γ) argument expected)
    (object : isObjectPattern argument = true)
    (small : sizeOf argument < bound) :
    Nonempty (ParamOpening language Γ parameter argument) := by
  cases fragmentParam with
  | inl boundParam =>
      cases inFragment_of_isSome boundParam with
      | simple name sort =>
          simp only [parameterType?, Option.some.injEq] at expectedEq
          subst expectedEq
          obtain ⟨tree, printed⟩ := recurse argument small typed object
          refine ⟨{
            count := 0
            length := 0
            countOk := fun _ => rfl
            lengthOk := fun _ => rfl
            opened := [{ binders := [], sort := sort, tree := tree }]
            lengthEq := by simp [directionsOf, baseCollection?]
            declsEq := by simp [expandParam, baseCollection?, slotBinders]
            patternsEq := by
              simp [baseCollection?, printArgument, slotBinders, wrapBinders, printed]
          }⟩
      | abstraction binderName bodyName domain bodySort =>
          simp only [parameterType?, Option.some.injEq] at expectedEq
          subst expectedEq
          obtain ⟨body, argumentEq⟩ :=
            (matchesParameterRepresentation_abstractionNamed_iff _ _ _ argument).mp
              representation
          subst argumentEq
          cases typed with
          | lambda bodyTyped =>
              have bodySmall : sizeOf body < bound := by
                simp only [Pattern.lambda.sizeOf_spec] at small
                omega
              have bodyObject : isObjectPattern body = true := by
                simpa [isObjectPattern] using object
              have bodyTyped' :
                  HasType language FreeTypeContext.empty (typeContext (domain :: Γ)) body
                    (.base bodySort) := by
                simpa [typeContext] using bodyTyped
              obtain ⟨tree, printed⟩ :=
                recurse (Γ := domain :: Γ) (sort := bodySort) body bodySmall bodyTyped' bodyObject
              refine ⟨{
                count := 0
                length := 0
                countOk := fun _ => rfl
                lengthOk := fun _ => rfl
                opened := [{ binders := [domain], sort := bodySort, tree := tree }]
                lengthEq := by simp [directionsOf, baseCollection?]
                declsEq := by simp [expandParam, baseCollection?, slotBinders]
                patternsEq := by
                  simp [baseCollection?, printArgument, slotBinders, wrapBinders, printed]
              }⟩
      | shorthand binderName bodyName sort =>
          simp only [parameterType?, Option.some.injEq] at expectedEq
          subst expectedEq
          obtain ⟨body, argumentEq⟩ :=
            (matchesParameterRepresentation_abstractionNamed_iff _ _ _ argument).mp
              representation
          subst argumentEq
          cases typed with
          | lambda bodyTyped =>
              have bodySmall : sizeOf body < bound := by
                simp only [Pattern.lambda.sizeOf_spec] at small
                omega
              have bodyObject : isObjectPattern body = true := by
                simpa [isObjectPattern] using object
              have bodyTyped' :
                  HasType language FreeTypeContext.empty (typeContext (sort :: Γ)) body
                    (.base sort) := by
                simpa [typeContext] using bodyTyped
              obtain ⟨tree, printed⟩ :=
                recurse (Γ := sort :: Γ) (sort := sort) body bodySmall bodyTyped' bodyObject
              refine ⟨{
                count := 0
                length := 0
                countOk := fun _ => rfl
                lengthOk := fun _ => rfl
                opened := [{ binders := [sort], sort := sort, tree := tree }]
                lengthEq := by simp [directionsOf, baseCollection?]
                declsEq := by simp [expandParam, baseCollection?, slotBinders]
                patternsEq := by
                  simp [baseCollection?, printArgument, slotBinders, wrapBinders, printed]
              }⟩
      | multiShorthand binderNames bodyName sort =>
          simp only [parameterType?, Option.some.injEq] at expectedEq
          subst expectedEq
          obtain ⟨arity, body, argumentEq⟩ :=
            (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ argument).mp
              representation
          subst argumentEq
          cases typed with
          | multiLambda bodyTyped =>
              have bodySmall : sizeOf body < bound := by
                simp only [Pattern.multiLambda.sizeOf_spec] at small
                omega
              have bodyObject : isObjectPattern body = true := by
                simpa [isObjectPattern] using object
              have bodyTyped' :
                  HasType language FreeTypeContext.empty
                    (typeContext (List.replicate arity sort ++ Γ)) body (.base sort) := by
                simpa [typeContext, List.map_append, List.map_replicate] using bodyTyped
              obtain ⟨tree, printed⟩ :=
                recurse (Γ := List.replicate arity sort ++ Γ) (sort := sort) body bodySmall
                  bodyTyped' bodyObject
              refine ⟨{
                count := arity
                length := 0
                countOk := by
                  intro bad
                  simp [multiBase?] at bad
                lengthOk := fun _ => rfl
                opened := [{
                  binders := List.replicate arity sort, sort := sort, tree := tree }]
                lengthEq := by simp [directionsOf, baseCollection?]
                declsEq := by simp [expandParam, baseCollection?, slotBinders]
                patternsEq := by
                  simp [baseCollection?, printArgument, printed]
              }⟩
      | multi binderNames bodyName domain bodySort =>
          simp only [parameterType?, Option.some.injEq] at expectedEq
          subst expectedEq
          obtain ⟨arity, body, argumentEq⟩ :=
            (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ argument).mp
              representation
          subst argumentEq
          cases typed with
          | multiLambda bodyTyped =>
              have bodySmall : sizeOf body < bound := by
                simp only [Pattern.multiLambda.sizeOf_spec] at small
                omega
              have bodyObject : isObjectPattern body = true := by
                simpa [isObjectPattern] using object
              have bodyTyped' :
                  HasType language FreeTypeContext.empty
                    (typeContext (List.replicate arity domain ++ Γ)) body (.base bodySort) := by
                simpa [typeContext, List.map_append, List.map_replicate] using bodyTyped
              obtain ⟨tree, printed⟩ :=
                recurse (Γ := List.replicate arity domain ++ Γ) (sort := bodySort) body bodySmall
                  bodyTyped' bodyObject
              refine ⟨{
                count := arity
                length := 0
                countOk := by
                  intro bad
                  simp [multiBase?] at bad
                lengthOk := fun _ => rfl
                opened := [{
                  binders := List.replicate arity domain, sort := bodySort, tree := tree }]
                lengthEq := by simp [directionsOf, baseCollection?]
                declsEq := by simp [expandParam, baseCollection?, slotBinders]
                patternsEq := by
                  simp [baseCollection?, printArgument, printed]
              }⟩
  | inr collected =>
      cases shape : baseCollection? parameter with
      | none => simp [shape] at collected
      | some packed =>
          obtain ⟨kind, element⟩ := packed
          obtain ⟨name, parameterEq⟩ := baseCollection_shape shape
          subst parameterEq
          simp only [parameterType?, Option.some.injEq] at expectedEq
          subst expectedEq
          cases typed with
          | bvar found => simp [typeContext] at found
          | fvar found => simp [FreeTypeContext.empty] at found
          | subst _ _ => simp [isObjectPattern] at object
          | collection elementsTyped =>
              rename_i argumentElements rest
              cases rest with
              | some _ => simp [isObjectPattern, Option.isNone] at object
              | none =>
                  have elementObjects :
                      ∀ pattern ∈ argumentElements, isObjectPattern pattern = true := by
                    have listObject : isObjectPatternList argumentElements = true := by
                      simpa [isObjectPattern, Option.isNone] using object
                    exact (isObjectPatternList_eq_true_iff argumentElements).mp listObject
                  have elementSmaller :
                      ∀ pattern ∈ argumentElements, sizeOf pattern < bound := by
                    intro pattern member
                    have memSmall := List.sizeOf_lt_of_mem member
                    simp only [Pattern.collection.sizeOf_spec] at small
                    omega
                  obtain ⟨trees, treesPrinted⟩ :=
                    exists_list_trees recurse argumentElements elementsTyped elementObjects
                      elementSmaller
                  refine ⟨{
                    count := 0
                    length := argumentElements.length
                    countOk := fun _ => rfl
                    lengthOk := by
                      intro bad
                      simp [baseCollection?] at bad
                    opened := trees.map fun tree =>
                      (⟨[], element, tree⟩ : Opened language Γ)
                    lengthEq := by
                      have treeLength : trees.length = argumentElements.length := by
                        simpa using congrArg List.length treesPrinted
                      simp [directionsOf, baseCollection?, treeLength]
                    declsEq := by
                      simp only [expandParam, baseCollection?]
                      have treeLength : trees.length = argumentElements.length := by
                        simpa using congrArg List.length treesPrinted
                      rw [← treeLength]
                      exact opened_decls_replicate trees
                    patternsEq := by
                      simp only [baseCollection?]
                      have mapped :
                          ((trees.map fun tree => (⟨[], element, tree⟩ : Opened language Γ)).map
                              fun slot => CollectionIndexed.toPattern slot.tree) =
                            argumentElements := by
                        rw [List.map_map]
                        exact treesPrinted
                      rw [← mapped]
                  }⟩

/-- One opened argument prints as that argument. -/
theorem opening_assembles {Γ : List String} {parameter : TermParam} {argument : Pattern}
    (opening : ParamOpening language Γ parameter argument) :
    assemblePrinted
        (fun index : Fin opening.opened.length =>
          CollectionIndexed.toPattern (opening.opened.get index).tree)
        0 [parameter] [opening.count] [opening.length] = [argument] := by
  cases reading : baseCollection? parameter with
  | some packed =>
      simp only [assemblePrinted, reading]
      have lengthEq : opening.length = opening.opened.length := by
        have counted := opening.lengthEq
        simp [directionsOf, reading] at counted
        exact counted.symm
      have nthEq :
          List.ofFn (fun index : Fin opening.length =>
              nthPrinted
                (fun slot : Fin opening.opened.length =>
                  CollectionIndexed.toPattern (opening.opened.get slot).tree)
                (0 + index.val)) =
            List.ofFn (fun index : Fin opening.length =>
              CollectionIndexed.toPattern
                (opening.opened.get (Fin.cast lengthEq index)).tree) := by
        refine ofFn_pointwise ?_
        intro index
        have bound : 0 + index.val < opening.opened.length := by
          rw [Nat.zero_add, ← lengthEq]
          exact index.isLt
        rw [nthPrinted_of_lt _ bound]
        apply congrArg fun slot : Opened language Γ => CollectionIndexed.toPattern slot.tree
        apply congrArg (opening.opened.get : Fin opening.opened.length → Opened language Γ)
        apply Fin.ext
        simp [Fin.val_cast]
      have shifted :
          List.ofFn (fun index : Fin opening.opened.length =>
              CollectionIndexed.toPattern (opening.opened.get index).tree) =
            List.ofFn (fun index : Fin opening.length =>
              CollectionIndexed.toPattern
                (opening.opened.get (Fin.cast lengthEq index)).tree) :=
        List.ofFn_congr lengthEq.symm
          (fun index : Fin opening.opened.length =>
            CollectionIndexed.toPattern (opening.opened.get index).tree)
      have asMap :=
        map_eq_ofFn_get (fun slot : Opened language Γ => CollectionIndexed.toPattern slot.tree)
          opening.opened
      rw [nthEq, ← shifted, asMap]
      have argumentEq := opening.patternsEq
      simp only [reading] at argumentEq
      rw [← argumentEq]
  | none =>
      simp only [assemblePrinted, reading]
      have counted := opening.lengthEq
      simp [directionsOf, reading] at counted
      have zeroBound : 0 < opening.opened.length := by omega
      rw [nthPrinted_of_lt _ zeroBound]
      obtain ⟨slot, slots⟩ := List.length_eq_one_iff.mp counted
      have lookup : opening.opened[0]? = some slot := by
        simp [slots]
      have atIndex : opening.opened.get ⟨0, zeroBound⟩ = slot := by
        have element : opening.opened[0] = slot := (List.getElem_eq_iff zeroBound).mpr lookup
        simpa [List.get_eq_getElem] using element
      rw [atIndex]
      have argumentEq := opening.patternsEq
      simp only [reading, slots, List.map_cons, List.map_nil, List.headD] at argumentEq
      rw [← argumentEq]

/-- No parameters, so no binder counts and no collection lengths. -/
def headEmpty : HeadData [] where
  counts := []
  lengths := []
  counts_length := rfl
  lengths_length := rfl
  counts_fixed := by
    intro _ _
    simp [List.getD]
  lengths_fixed := by
    intro _ _
    simp [List.getD]

/-- One parameter in front of an existing head. -/
def headCons {parameter : TermParam} {parameters : List TermParam}
    (count length : Nat)
    (countOk : (multiBase? parameter).isNone → count = 0)
    (lengthOk : (baseCollection? parameter).isNone → length = 0)
    (tail : HeadData parameters) : HeadData (parameter :: parameters) where
  counts := count :: tail.counts
  lengths := length :: tail.lengths
  counts_length := by simp [tail.counts_length]
  lengths_length := by simp [tail.lengths_length]
  counts_fixed := by
    intro index hypothesis
    cases index with
    | zero =>
        simpa [List.getD] using countOk (by simpa [List.getD] using hypothesis)
    | succ index =>
        simpa [List.getD] using
          tail.counts_fixed index (by simpa [List.getD] using hypothesis)
  lengths_fixed := by
    intro index hypothesis
    cases index with
    | zero =>
        simpa [List.getD] using lengthOk (by simpa [List.getD] using hypothesis)
    | succ index =>
        simpa [List.getD] using
          tail.lengths_fixed index (by simpa [List.getD] using hypothesis)

/-- Moving the read window by a fixed start leaves the assembled arguments unchanged. -/
theorem assemblePrinted_shift {total total' : Nat}
    (printed : Fin total → Pattern) (printed' : Fin total' → Pattern)
    (start offset : Nat) (parameters : List TermParam) (counts lengths : List Nat)
    (agree : ∀ index : Nat, offset ≤ index →
      index < offset + slotCount parameters counts lengths →
      nthPrinted printed (start + index) = nthPrinted printed' index) :
    assemblePrinted printed (start + offset) parameters counts lengths =
      assemblePrinted printed' offset parameters counts lengths := by
  induction parameters generalizing counts lengths start offset with
  | nil => simp [assemblePrinted]
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp [assemblePrinted]
      | cons count counts =>
          cases lengths with
          | nil => simp [assemblePrinted]
          | cons length lengths =>
              cases reading : baseCollection? parameter with
              | some _ =>
                  simp only [assemblePrinted, reading]
                  have width :
                      slotCount (parameter :: parameters) (count :: counts) (length :: lengths) =
                        length + slotCount parameters counts lengths := by
                    simp [slotCount, directionsOf, reading]
                  have childrenEq :
                      List.ofFn (fun index : Fin length =>
                          nthPrinted printed ((start + offset) + index.val)) =
                        List.ofFn (fun index : Fin length =>
                          nthPrinted printed' (offset + index.val)) :=
                    ofFn_pointwise fun index => by
                      have reassoc :
                          (start + offset) + index.val = start + (offset + index.val) :=
                        Nat.add_assoc _ _ _
                      rw [reassoc]
                      exact agree (offset + index.val) (Nat.le_add_right _ _) <| by
                        have indexBound := index.isLt
                        omega
                  have tailEq :=
                    inductionHypothesis start (offset + length) counts lengths
                      fun index lower upper =>
                        agree index (Nat.le_trans (Nat.le_add_right offset length) lower) <| by
                          omega
                  have reassocTail : (start + offset) + length = start + (offset + length) :=
                    Nat.add_assoc _ _ _
                  simp [childrenEq, tailEq, reassocTail]
              | none =>
                  simp only [assemblePrinted, reading]
                  have headEq :
                      nthPrinted printed (start + offset) = nthPrinted printed' offset :=
                    agree offset (Nat.le_refl _) <| by
                      have width :
                          0 <
                            slotCount (parameter :: parameters) (count :: counts)
                              (length :: lengths) := by
                        simp [slotCount, directionsOf, reading]
                      omega
                  have tailEq :=
                    inductionHypothesis start (offset + 1) counts lengths
                      fun index lower upper =>
                        agree index (Nat.le_trans (Nat.le_add_right offset 1) lower) <| by
                          have width :
                              slotCount (parameter :: parameters) (count :: counts)
                                  (length :: lengths) =
                                1 + slotCount parameters counts lengths := by
                            simp [slotCount, directionsOf, reading]
                          omega
                  have reassocTail : (start + offset) + 1 = start + (offset + 1) :=
                    Nat.add_assoc _ _ _
                  simp [headEq, tailEq, reassocTail]

/-- The same assembly, read from a window that begins at `start`. -/
theorem assemblePrinted_drop {total total' : Nat}
    (printed : Fin total → Pattern) (printed' : Fin total' → Pattern)
    (start : Nat) (parameters : List TermParam) (counts lengths : List Nat)
    (agree : ∀ index : Nat, index < slotCount parameters counts lengths →
      nthPrinted printed (start + index) = nthPrinted printed' index) :
    assemblePrinted printed start parameters counts lengths =
      assemblePrinted printed' 0 parameters counts lengths := by
  have shifted :=
    assemblePrinted_shift printed printed' start 0 parameters counts lengths fun index _ upper => by
      rw [Nat.zero_add] at upper
      exact agree index upper
  simpa [Nat.add_zero] using shifted

/-- Opened arguments of a whole parameter list, in direction order. -/
structure ArgumentsOpening (language : LanguageDef) (Γ : List String)
    (parameters : List TermParam) (arguments : List Pattern) where
  data : HeadData parameters
  opened : List (Opened language Γ)
  lengthEq : opened.length = slotCount parameters data.counts data.lengths
  declsEq :
    opened.map (fun slot => (slot.binders, slot.sort)) =
      expandSlots parameters data.counts data.lengths
  assembled :
    assemblePrinted
      (fun index : Fin opened.length =>
        CollectionIndexed.toPattern (opened.get index).tree)
      0 parameters data.counts data.lengths = arguments

/-- The head argument, then the remaining arguments, is one assembled list. -/
theorem assemble_append {Γ : List String} {parameter : TermParam} {parameters : List TermParam}
    {argument : Pattern} {arguments : List Pattern}
    (head : ParamOpening language Γ parameter argument)
    (tailOpened : List (Opened language Γ)) (tailCounts tailLengths : List Nat)
    (tailLengthEq : tailOpened.length = slotCount parameters tailCounts tailLengths)
    (tailAssembled :
      assemblePrinted
        (fun index : Fin tailOpened.length =>
          CollectionIndexed.toPattern (tailOpened.get index).tree)
        0 parameters tailCounts tailLengths = arguments) :
    assemblePrinted
        (fun index : Fin (head.opened ++ tailOpened).length =>
          CollectionIndexed.toPattern ((head.opened ++ tailOpened).get index).tree)
        0 (parameter :: parameters) (head.count :: tailCounts) (head.length :: tailLengths) =
      argument :: arguments := by
  let combined := head.opened ++ tailOpened
  let full : Fin combined.length → Pattern :=
    fun index => CollectionIndexed.toPattern (combined.get index).tree
  let headFun : Fin head.opened.length → Pattern :=
    fun index => CollectionIndexed.toPattern (head.opened.get index).tree
  let tailFun : Fin tailOpened.length → Pattern :=
    fun index => CollectionIndexed.toPattern (tailOpened.get index).tree
  have headNth : ∀ {index : Nat}, index < head.opened.length →
      nthPrinted full index = nthPrinted headFun index := by
    intro index bound
    have fullBound : index < combined.length := by
      simp [combined, List.length_append]
      omega
    rw [nthPrinted_of_lt full fullBound, nthPrinted_of_lt headFun bound]
    apply congrArg fun slot : Opened language Γ => CollectionIndexed.toPattern slot.tree
    simpa [combined, List.get_eq_getElem] using
      List.getElem_append_left (as := head.opened) (bs := tailOpened) (i := index) bound
  have tailNth : ∀ {index : Nat}, index < tailOpened.length →
      nthPrinted full (head.opened.length + index) = nthPrinted tailFun index := by
    intro index bound
    have fullBound : head.opened.length + index < combined.length := by
      simp [combined, List.length_append]
      omega
    rw [nthPrinted_of_lt full fullBound, nthPrinted_of_lt tailFun bound]
    apply congrArg fun slot : Opened language Γ => CollectionIndexed.toPattern slot.tree
    have erased :=
      List.getElem_append_right (as := head.opened) (bs := tailOpened)
        (i := head.opened.length + index) (Nat.le_add_right _ _) (h₂ := fullBound)
    simp [combined, List.get_eq_getElem, erased]
  have counted := head.lengthEq
  show assemblePrinted full 0 (parameter :: parameters) (head.count :: tailCounts)
      (head.length :: tailLengths) = argument :: arguments
  cases reading : baseCollection? parameter with
  | some _ =>
      simp [directionsOf, reading] at counted
      simp only [assemblePrinted, reading]
      have cells :
          List.ofFn (fun index : Fin head.length => nthPrinted full (0 + index.val)) =
            List.ofFn (fun index : Fin head.length => nthPrinted headFun (0 + index.val)) := by
        refine ofFn_pointwise ?_
        intro index
        have bound : 0 + index.val < head.opened.length := by
          rw [Nat.zero_add, counted]
          exact index.isLt
        exact headNth bound
      have fromHead := opening_assembles head
      simp only [assemblePrinted, reading] at fromHead
      have headFunEq :
          (fun index : Fin head.opened.length =>
              CollectionIndexed.toPattern (head.opened.get index).tree) =
            headFun := rfl
      rw [headFunEq] at fromHead
      rw [← cells] at fromHead
      simp only [List.cons.injEq, and_true] at fromHead
      have tailList :
          assemblePrinted full (0 + head.length) parameters tailCounts tailLengths = arguments := by
        have dropped :=
          assemblePrinted_drop full tailFun head.opened.length parameters tailCounts tailLengths
            fun index upper =>
              tailNth <| by
                rw [tailLengthEq]
                exact upper
        have offsetEq : 0 + head.length = head.opened.length := by
          rw [Nat.zero_add]
          exact counted.symm
        rw [offsetEq, dropped]
        have tailFunEq :
            (fun index : Fin tailOpened.length =>
                CollectionIndexed.toPattern (tailOpened.get index).tree) =
              tailFun := rfl
        rw [tailFunEq] at tailAssembled
        exact tailAssembled
      simp only [List.cons.injEq]
      refine ⟨?_, ?_⟩
      · simpa [Nat.zero_add] using fromHead
      · simpa [Nat.zero_add] using tailList
  | none =>
      simp [directionsOf, reading] at counted
      simp only [assemblePrinted, reading]
      have fromHead := opening_assembles head
      simp only [assemblePrinted, reading] at fromHead
      have atZero : nthPrinted full 0 = nthPrinted headFun 0 :=
        headNth (by omega)
      have headFunEq :
          (fun index : Fin head.opened.length =>
              CollectionIndexed.toPattern (head.opened.get index).tree) =
            headFun := rfl
      rw [headFunEq] at fromHead
      rw [← atZero] at fromHead
      simp only [List.cons.injEq, and_true] at fromHead
      have tailList :
          assemblePrinted full (0 + 1) parameters tailCounts tailLengths = arguments := by
        have dropped :=
          assemblePrinted_drop full tailFun head.opened.length parameters tailCounts tailLengths
            fun index upper =>
              tailNth <| by
                rw [tailLengthEq]
                exact upper
        have offsetEq : 0 + 1 = head.opened.length := by
          rw [Nat.zero_add]
          exact counted.symm
        rw [offsetEq, dropped]
        have tailFunEq :
            (fun index : Fin tailOpened.length =>
                CollectionIndexed.toPattern (tailOpened.get index).tree) =
              tailFun := rfl
        rw [tailFunEq] at tailAssembled
        exact tailAssembled
      simp only [List.cons.injEq]
      refine ⟨fromHead, ?_⟩
      simpa [Nat.zero_add] using tailList

/-- Every typed object argument list opens as head data and child trees. -/
theorem exists_arguments_opening {bound : Nat}
    (recurse :
      ∀ {Γ : List String} {sort : String} (pattern : Pattern),
        sizeOf pattern < bound →
        HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
        isObjectPattern pattern = true →
        ∃ tree : Tree language (Γ, sort), CollectionIndexed.toPattern tree = pattern) :
    (parameters : List TermParam) →
    (fragmentParams : ∀ parameter ∈ parameters,
      (bindingDecl? parameter).isSome ∨ (baseCollection? parameter).isSome) →
    {Γ : List String} →
    (arguments : List Pattern) →
    (typed : ArgumentsHaveTypes language FreeTypeContext.empty (typeContext Γ)
      arguments parameters) →
    (smaller : ∀ pattern ∈ arguments, sizeOf pattern < bound) →
    (objects : ∀ pattern ∈ arguments, isObjectPattern pattern = true) →
    Nonempty (ArgumentsOpening language Γ parameters arguments)
  | [], _, _, _, typed, _, _ => by
      cases typed
      exact ⟨{
        data := headEmpty
        opened := []
        lengthEq := by simp [slotCount]
        declsEq := by simp [expandSlots]
        assembled := by simp [assemblePrinted]
      }⟩
  | parameter :: parameters, fragmentParams, Γ, _, typed, smaller, objects => by
      cases typed with
      | cons representation expectedEq argumentTyped restTyped =>
          rename_i argument arguments _
          obtain ⟨head⟩ :=
            exists_param_opening recurse parameter
              (fragmentParams parameter (List.mem_cons_self)) argument representation _
              expectedEq argumentTyped
              (objects argument (List.mem_cons_self))
              (smaller argument (List.mem_cons_self))
          obtain ⟨tail⟩ :=
            exists_arguments_opening recurse parameters
              (fun parameter member =>
                fragmentParams parameter (List.mem_cons_of_mem _ member))
              arguments restTyped
              (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
              (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
          exact ⟨{
            data := headCons head.count head.length head.countOk head.lengthOk tail.data
            opened := head.opened ++ tail.opened
            lengthEq := by
              simp [headCons, slotCount, List.length_append, head.lengthEq, tail.lengthEq]
            declsEq := by
              simp [headCons, expandSlots, List.map_append, head.declsEq, tail.declsEq]
            assembled :=
              assemble_append head tail.opened tail.data.counts tail.data.lengths tail.lengthEq
                tail.assembled
          }⟩

/-- An application of a non-bare rule is the indexed tree of its opened arguments. -/
theorem exists_apply_tree {Γ : List String} {rule : GrammarRule} {arguments : List Pattern}
    (member : rule ∈ language.terms) (fragmentRule : FragmentRule rule)
    (notBare : ¬ UsesBareCollection rule)
    (opening : ArgumentsOpening language Γ rule.params arguments) :
    ∃ tree : Tree language (Γ, rule.category),
      CollectionIndexed.toPattern tree = .apply rule.label arguments := by
  let operator : (indexedSignature language).Op rule.category :=
    ⟨⟨rule, member, fragmentRule, rfl⟩, opening.data⟩
  have bareNone : bareCollection? operator.1.1 = none := by
    cases reading : bareCollection? operator.1.1 with
    | none => rfl
    | some _ =>
        exact absurd (bareCollection_uses reading) notBare
  have arityLen :
      ((indexedSignature language).arity operator).length = opening.opened.length := by
    simpa [operator, expandSlots_length] using opening.lengthEq.symm
  have sourceEq (direction : Fin ((indexedSignature language).arity operator).length) :
      (polynomial (indexedSignature language)).src (Γ, rule.category) operator direction =
        ((opening.opened.get (Fin.cast arityLen direction)).binders ++ Γ,
          (opening.opened.get (Fin.cast arityLen direction)).sort) := by
    have openedBound : direction.val < opening.opened.length := by
      rw [← arityLen]
      exact direction.isLt
    have same :
        (indexedSignature language).arity operator =
          opening.opened.map fun slot => (slot.binders, slot.sort) := by
      simpa [operator] using opening.declsEq.symm
    have lookup :=
      congrArg (fun list : List (List String × String) => list[direction.val]?) same
    rw [List.getElem?_eq_getElem direction.isLt, List.getElem?_map,
      List.getElem?_eq_getElem openedBound] at lookup
    have pair :
        ((indexedSignature language).arity operator)[direction.val] =
          ((opening.opened[direction.val]'openedBound).binders,
            (opening.opened[direction.val]'openedBound).sort) :=
      Option.some.inj lookup
    rw [polynomial_direction, List.get_eq_getElem, pair]
    simp [List.get_eq_getElem]
  let children : Child language Γ rule.category operator :=
    fun direction =>
      cast (congrArg (Tree language) (sourceEq direction).symm)
        (opening.opened.get (Fin.cast arityLen direction)).tree
  have printed :
      assemblePrinted (fun direction => CollectionIndexed.toPattern (children direction)) 0
        rule.params opening.data.counts opening.data.lengths =
        assemblePrinted
          (fun index : Fin opening.opened.length =>
            CollectionIndexed.toPattern (opening.opened.get index).tree)
          0 rule.params opening.data.counts opening.data.lengths := by
    refine assemblePrinted_congr _ _ 0 rule.params opening.data.counts opening.data.lengths ?_
    intro index _lower upper
    have rightBound : index < opening.opened.length := by
      rw [Nat.zero_add] at upper
      rwa [opening.lengthEq]
    have leftBound : index < ((indexedSignature language).arity operator).length := by
      rw [arityLen]
      exact rightBound
    rw [nthPrinted_of_lt _ leftBound, nthPrinted_of_lt _ rightBound]
    unfold children
    rw [toPattern_cast (sourceEq ⟨index, leftBound⟩).symm]
    apply congrArg fun slot : Opened language Γ => CollectionIndexed.toPattern slot.tree
    apply congrArg opening.opened.get
    apply Fin.ext
    rfl
  refine ⟨
    IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, rule.category))
      operator children, ?_⟩
  rw [CollectionIndexed.toPattern_liftBind]
  have assembled := printed.trans opening.assembled
  simp only [nodeOf, bareNone]
  simpa [operator] using assembled

/-- Every typed object pattern at a base sort is an indexed tree. -/
theorem exists_toPattern_of_size
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule) :
    (bound : Nat) → (Γ : List String) → (pattern : Pattern) → sizeOf pattern < bound →
      (sort : String) →
      HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
      isObjectPattern pattern = true →
      ∃ tree : Tree language (Γ, sort), CollectionIndexed.toPattern tree = pattern
  | 0, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, Γ, pattern, small, sort, typed, object => by
      cases pattern with
      | bvar index =>
          cases typed with
          | bvar found =>
              obtain ⟨variable_, printed⟩ := exists_var_of_get (lookup_base found)
              exact ⟨IFreeM.pure (P := polynomial (indexedSignature language)) variable_, by
                rw [CollectionIndexed.toPattern_pure, printed]⟩
      | fvar _ =>
          cases typed with
          | fvar found => simp [FreeTypeContext.empty] at found
      | apply _label arguments =>
          cases typed with
          | constructor member notBare argumentsTyped =>
              rename_i rule
              have smaller : ∀ pattern ∈ arguments, sizeOf pattern < bound := by
                intro pattern memberPattern
                have memSmall := List.sizeOf_lt_of_mem memberPattern
                simp only [Pattern.apply.sizeOf_spec] at small
                omega
              have argumentObjects :
                  ∀ pattern ∈ arguments, isObjectPattern pattern = true := by
                simpa [isObjectPattern, isObjectPatternList_eq_true_iff] using object
              obtain ⟨opening⟩ :=
                exists_arguments_opening
                  (fun {Δ} {argumentSort} pattern smallPattern typedPattern objectPattern =>
                    exists_toPattern_of_size fragment bound Δ pattern smallPattern
                      argumentSort typedPattern objectPattern)
                  rule.params (fragment rule member) arguments argumentsTyped smaller
                  argumentObjects
              simpa using
                exists_apply_tree member (fragment rule member) notBare opening
      | lambda _ _ => cases typed
      | multiLambda _ _ _ => cases typed
      | subst _ _ => simp [isObjectPattern] at object
      | collection kind elements rest =>
          cases typed with
          | collectionConstructor member paramsEq elementsTyped =>
              cases rest with
              | some _ => simp [isObjectPattern, Option.isNone] at object
              | none =>
                  have elementObjects :
                      ∀ pattern ∈ elements, isObjectPattern pattern = true := by
                    have listObject : isObjectPatternList elements = true := by
                      simpa [isObjectPattern, Option.isNone] using object
                    exact (isObjectPatternList_eq_true_iff elements).mp listObject
                  have elementSmaller : ∀ pattern ∈ elements, sizeOf pattern < bound := by
                    intro pattern memberPattern
                    have memSmall := List.sizeOf_lt_of_mem memberPattern
                    simp only [Pattern.collection.sizeOf_spec] at small
                    omega
                  simpa using
                    exists_collection_tree fragment
                      (fun {Δ} {argumentSort} pattern smallPattern typedPattern objectPattern =>
                        exists_toPattern_of_size fragment bound Δ pattern smallPattern
                          argumentSort typedPattern objectPattern)
                      (HasType.collectionConstructor member paramsEq elementsTyped)
                      elementObjects elementSmaller

/-! ## Printing is injective -/

theorem multiBase_of_collection {parameter : TermParam} {kind : CollType} {element : String}
    (shape : baseCollection? parameter = some (kind, element)) :
    multiBase? parameter = none := by
  cases parameter with
  | simple _ type =>
      cases type with
      | collection _ elementType =>
          cases elementType with
          | base _ => rfl
          | arrow _ _ => simp [baseCollection?] at shape
          | multiBinder _ => simp [baseCollection?] at shape
          | collection _ _ => simp [baseCollection?] at shape
      | base _ => simp [baseCollection?] at shape
      | arrow _ _ => simp [baseCollection?] at shape
      | multiBinder _ => simp [baseCollection?] at shape
  | abstractionNamed _ _ _ => simp [baseCollection?] at shape
  | multiAbstractionNamed _ _ _ => simp [baseCollection?] at shape

theorem nodeOf_ne_bvar {sort : String}
    (operator : (indexedSignature language).Op sort)
    (printed : Fin ((indexedSignature language).arity operator).length → Pattern)
    (index : Nat) : nodeOf operator printed ≠ .bvar index := by
  intro same
  cases reading : bareCollection? operator.1.1 with
  | some _ => simp [nodeOf, reading] at same
  | none => simp [nodeOf, reading] at same

/-- A bare collection stores the count zero and a single length, the number of
directions. -/
theorem bare_head {sort : String} {kind : CollType} {element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element)) :
    operator.2.counts = [0] ∧
      operator.2.lengths = [((indexedSignature language).arity operator).length] := by
  obtain ⟨_name, paramsEq⟩ := bare_rule_params shape
  have counted : operator.2.counts.length = 1 := by
    simpa [paramsEq] using operator.2.counts_length
  have lengthed : operator.2.lengths.length = 1 := by
    simpa [paramsEq] using operator.2.lengths_length
  obtain ⟨count, countsShape⟩ := List.length_eq_one_iff.mp counted
  obtain ⟨length, lengthsShape⟩ := List.length_eq_one_iff.mp lengthed
  have countZero : count = 0 := by
    have fixed :=
      operator.2.counts_fixed 0 (by simp [paramsEq, List.getD, multiBase?])
    rw [countsShape] at fixed
    simpa [List.getD] using fixed
  have lengthValue : length = ((indexedSignature language).arity operator).length := by
    have slots := bare_slot_length operator shape
    rw [lengthsShape] at slots
    simpa [List.headD] using slots.symm
  refine ⟨?_, ?_⟩
  · rw [countsShape, countZero]
  · rw [lengthsShape, lengthValue]

theorem headData_ext {parameters : List TermParam} {left right : HeadData parameters}
    (countsEq : left.counts = right.counts) (lengthsEq : left.lengths = right.lengths) :
    left = right := by
  cases left with
  | mk countsL lengthsL _ _ _ _ =>
      cases right with
      | mk countsR lengthsR _ _ _ _ =>
          cases countsEq
          cases lengthsEq
          rfl

theorem ofFn_length_eq {m n : Nat} {f : Fin m → Pattern} {g : Fin n → Pattern}
    (same : List.ofFn f = List.ofFn g) : m = n := by
  have lengths := congrArg List.length same
  simpa [List.length_ofFn] using lengths

theorem ofFn_point_of_eq {m n : Nat} {f : Fin m → Pattern} {g : Fin n → Pattern}
    (same : List.ofFn f = List.ofFn g) (index : Fin m) :
    f index = g (index.cast (ofFn_length_eq same)) := by
  have lengthEq := ofFn_length_eq same
  have rewritten :
      List.ofFn f =
        List.ofFn (fun index : Fin m => g (index.cast lengthEq)) :=
    same.trans (List.ofFn_congr lengthEq.symm g)
  exact congrFun (List.ofFn_inj.mp rewritten) index

/-- Assembled arguments determine the binder counts, the collection lengths,
and every printed direction. Each parameter contributes one argument, so the
split between parameters is the parameter list itself. -/
theorem assemblePrinted_recover {total total' : Nat}
    (printed : Fin total → Pattern) (printed' : Fin total' → Pattern)
    (offset : Nat) (parameters : List TermParam)
    (counts lengths counts' lengths' : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (countsLength' : counts'.length = parameters.length)
    (lengthsLength' : lengths'.length = parameters.length)
    (countsFixed : ∀ index : Nat,
      (multiBase? (parameters.getD index missingParameter)).isNone →
        counts.getD index 0 = 0)
    (countsFixed' : ∀ index : Nat,
      (multiBase? (parameters.getD index missingParameter)).isNone →
        counts'.getD index 0 = 0)
    (lengthsFixed : ∀ index : Nat,
      (baseCollection? (parameters.getD index missingParameter)).isNone →
        lengths.getD index 0 = 0)
    (lengthsFixed' : ∀ index : Nat,
      (baseCollection? (parameters.getD index missingParameter)).isNone →
        lengths'.getD index 0 = 0)
    (same : assemblePrinted printed offset parameters counts lengths =
      assemblePrinted printed' offset parameters counts' lengths') :
    counts = counts' ∧ lengths = lengths' ∧
      ∀ index : Nat, index < slotCount parameters counts lengths →
        nthPrinted printed (offset + index) = nthPrinted printed' (offset + index) := by
  induction parameters generalizing counts lengths counts' lengths' offset with
  | nil =>
      cases counts with
      | cons _ _ => simp at countsLength
      | nil =>
          cases lengths with
          | cons _ _ => simp at lengthsLength
          | nil =>
              cases counts' with
              | cons _ _ => simp at countsLength'
              | nil =>
                  cases lengths' with
                  | cons _ _ => simp at lengthsLength'
                  | nil =>
                      refine ⟨rfl, rfl, ?_⟩
                      intro index bound
                      simp [slotCount] at bound
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              cases counts' with
              | nil => simp at countsLength'
              | cons count' counts' =>
                  cases lengths' with
                  | nil => simp at lengthsLength'
                  | cons length' lengths' =>
                      have tailCountsLength : counts.length = parameters.length := by
                        simp only [List.length_cons] at countsLength
                        exact Nat.succ.inj countsLength
                      have tailLengthsLength : lengths.length = parameters.length := by
                        simp only [List.length_cons] at lengthsLength
                        exact Nat.succ.inj lengthsLength
                      have tailCountsLength' : counts'.length = parameters.length := by
                        simp only [List.length_cons] at countsLength'
                        exact Nat.succ.inj countsLength'
                      have tailLengthsLength' : lengths'.length = parameters.length := by
                        simp only [List.length_cons] at lengthsLength'
                        exact Nat.succ.inj lengthsLength'
                      have tailCountsFixed : ∀ index : Nat,
                          (multiBase? (parameters.getD index missingParameter)).isNone →
                            counts.getD index 0 = 0 := by
                        intro index hypothesis
                        have counted :=
                          countsFixed (index + 1) (by simpa [List.getD] using hypothesis)
                        simpa [List.getD] using counted
                      have tailCountsFixed' : ∀ index : Nat,
                          (multiBase? (parameters.getD index missingParameter)).isNone →
                            counts'.getD index 0 = 0 := by
                        intro index hypothesis
                        have counted :=
                          countsFixed' (index + 1) (by simpa [List.getD] using hypothesis)
                        simpa [List.getD] using counted
                      have tailLengthsFixed : ∀ index : Nat,
                          (baseCollection? (parameters.getD index missingParameter)).isNone →
                            lengths.getD index 0 = 0 := by
                        intro index hypothesis
                        have counted :=
                          lengthsFixed (index + 1) (by simpa [List.getD] using hypothesis)
                        simpa [List.getD] using counted
                      have tailLengthsFixed' : ∀ index : Nat,
                          (baseCollection? (parameters.getD index missingParameter)).isNone →
                            lengths'.getD index 0 = 0 := by
                        intro index hypothesis
                        have counted :=
                          lengthsFixed' (index + 1) (by simpa [List.getD] using hypothesis)
                        simpa [List.getD] using counted
                      cases reading : baseCollection? parameter with
                      | some packed =>
                          obtain ⟨kind, _element⟩ := packed
                          simp only [assemblePrinted, reading, List.cons.injEq] at same
                          obtain ⟨headEq, tailEq⟩ := same
                          simp only [Pattern.collection.injEq] at headEq
                          obtain ⟨_kindEq, elementsEq, _restEq⟩ := headEq
                          have lengthEq : length = length' := ofFn_length_eq elementsEq
                          rw [← lengthEq] at tailEq
                          have countEq : count = count' := by
                            have countZero : count = 0 := by
                              have fixed := countsFixed 0
                                (by simp [List.getD, multiBase_of_collection reading])
                              simpa [List.getD] using fixed
                            have countZero' : count' = 0 := by
                              have fixed := countsFixed' 0
                                (by simp [List.getD, multiBase_of_collection reading])
                              simpa [List.getD] using fixed
                            rw [countZero, countZero']
                          obtain ⟨countsTailEq, lengthsTailEq, tailAgree⟩ :=
                            inductionHypothesis (offset + length) counts lengths counts' lengths'
                              tailCountsLength tailLengthsLength tailCountsLength'
                              tailLengthsLength' tailCountsFixed tailCountsFixed' tailLengthsFixed
                              tailLengthsFixed' tailEq
                          refine ⟨?_, ?_, ?_⟩
                          · rw [countEq, countsTailEq]
                          · rw [lengthEq, lengthsTailEq]
                          · intro index indexBound
                            have width :
                                slotCount (parameter :: parameters) (count :: counts)
                                    (length :: lengths) =
                                  length + slotCount parameters counts lengths := by
                              simp [slotCount, directionsOf, reading]
                            rw [width] at indexBound
                            by_cases below : index < length
                            · have point :=
                                ofFn_point_of_eq elementsEq ⟨index, below⟩
                              simpa [Fin.val_cast] using point
                            · have lower : length ≤ index := Nat.le_of_not_lt below
                              have tailBound :
                                  index - length < slotCount parameters counts lengths := by
                                omega
                              have shifted := tailAgree (index - length) tailBound
                              have reassoc :
                                  (offset + length) + (index - length) = offset + index := by
                                omega
                              rw [reassoc] at shifted
                              exact shifted
                      | none =>
                          simp only [assemblePrinted, reading, List.cons.injEq] at same
                          obtain ⟨headEq, tailEq⟩ := same
                          have countCanonical : (multiBase? parameter).isNone → count = 0 := by
                            intro notMulti
                            have fixed := countsFixed 0 (by simpa [List.getD] using notMulti)
                            simpa [List.getD] using fixed
                          have countCanonical' : (multiBase? parameter).isNone → count' = 0 := by
                            intro notMulti
                            have fixed := countsFixed' 0 (by simpa [List.getD] using notMulti)
                            simpa [List.getD] using fixed
                          have countEq : count = count' := by
                            have leftCount :=
                              observableCount_print parameter count
                                (nthPrinted printed offset) countCanonical
                            have rightCount :=
                              observableCount_print parameter count'
                                (nthPrinted printed' offset) countCanonical'
                            have sameCount := congrArg (observableCount parameter) headEq
                            rw [leftCount, rightCount] at sameCount
                            exact sameCount
                          have bodyEq :
                              nthPrinted printed offset = nthPrinted printed' offset := by
                            have rewritten :
                                printArgument parameter count (nthPrinted printed offset) =
                                  printArgument parameter count (nthPrinted printed' offset) := by
                              simpa [countEq] using headEq
                            exact printArgument_injective parameter count rewritten
                          have lengthEq : length = length' := by
                            have lengthZero : length = 0 := by
                              have fixed := lengthsFixed 0 (by simp [List.getD, reading])
                              simpa [List.getD] using fixed
                            have lengthZero' : length' = 0 := by
                              have fixed := lengthsFixed' 0 (by simp [List.getD, reading])
                              simpa [List.getD] using fixed
                            rw [lengthZero, lengthZero']
                          obtain ⟨countsTailEq, lengthsTailEq, tailAgree⟩ :=
                            inductionHypothesis (offset + 1) counts lengths counts' lengths'
                              tailCountsLength tailLengthsLength tailCountsLength'
                              tailLengthsLength' tailCountsFixed tailCountsFixed' tailLengthsFixed
                              tailLengthsFixed' tailEq
                          refine ⟨?_, ?_, ?_⟩
                          · rw [countEq, countsTailEq]
                          · rw [lengthEq, lengthsTailEq]
                          · intro index indexBound
                            have width :
                                slotCount (parameter :: parameters) (count :: counts)
                                    (length :: lengths) =
                                  1 + slotCount parameters counts lengths := by
                              simp [slotCount, directionsOf, reading]
                            rw [width] at indexBound
                            cases index with
                            | zero => simpa [Nat.zero_add] using bodyEq
                            | succ index =>
                                have tailBound :
                                    index < slotCount parameters counts lengths := by
                                  omega
                                have shifted := tailAgree index tailBound
                                have reassoc : (offset + 1) + index = offset + index.succ := by
                                  omega
                                rw [reassoc] at shifted
                                exact shifted

/-- Distinct labels and at most one bare rule of each kind make printing
injective. A bare collection does not print its label, so labels alone do not
separate two bare rules. -/
theorem toPattern_injective
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {index : List String × String} (left : Tree language index) :
    ∀ right : Tree language index,
      CollectionIndexed.toPattern left = CollectionIndexed.toPattern right → left = right := by
  induction left with
  | pure variable_ =>
      intro right printed
      cases right with
      | pure variable' =>
          rw [CollectionIndexed.toPattern_pure, CollectionIndexed.toPattern_pure] at printed
          simp only [Pattern.bvar.injEq] at printed
          exact congrArg (IFreeM.pure (P := polynomial (indexedSignature language)))
            (varIndex_injective variable_ variable' printed)
      | liftBind operator _children =>
          rw [CollectionIndexed.toPattern_pure, CollectionIndexed.toPattern_liftBind] at printed
          exact absurd printed (nodeOf_ne_bvar operator _ _).symm
  | liftBind operator children inductionHypothesis =>
      intro right printed
      cases right with
      | pure variable_ =>
          rw [CollectionIndexed.toPattern_liftBind, CollectionIndexed.toPattern_pure] at printed
          exact absurd printed (nodeOf_ne_bvar operator _ _)
      | liftBind operator' children' =>
          rcases operator with ⟨packed, data⟩
          rcases operator' with ⟨packed', data'⟩
          rw [CollectionIndexed.toPattern_liftBind, CollectionIndexed.toPattern_liftBind] at printed
          cases reading : bareCollection? packed.1 with
          | some pair =>
              obtain ⟨kind, element⟩ := pair
              cases reading' : bareCollection? packed'.1 with
              | some pair' =>
                  obtain ⟨kind', element'⟩ := pair'
                  simp only [nodeOf, reading, reading'] at printed
                  simp only [Pattern.collection.injEq] at printed
                  obtain ⟨kindEq, elementsEq, _restEq⟩ := printed
                  subst kindEq
                  have sameRule : packed.1 = packed'.1 :=
                    uniqueBare packed.2.1 packed'.2.1
                      (packed.2.2.2.trans packed'.2.2.2.symm) reading reading'
                  have packedEq : packed = packed' := Subtype.ext sameRule
                  subst packedEq
                  obtain ⟨countsL, lengthsL⟩ := bare_head ⟨packed, data⟩ reading
                  obtain ⟨countsR, lengthsR⟩ := bare_head ⟨packed, data'⟩ reading'
                  have lengthEq :
                      ((indexedSignature language).arity ⟨packed, data⟩).length =
                        ((indexedSignature language).arity ⟨packed, data'⟩).length :=
                    ofFn_length_eq elementsEq
                  have dataEq : data = data' :=
                    headData_ext (by rw [countsL, countsR]) (by rw [lengthsL, lengthsR, lengthEq])
                  subst dataEq
                  refine congrArg
                    (fun continuation =>
                      IFreeM.liftBind (P := polynomial (indexedSignature language))
                        ⟨packed, data⟩ continuation) ?_
                  funext direction
                  exact inductionHypothesis direction (children' direction)
                    (ofFn_point_of_eq elementsEq direction)
              | none => simp [nodeOf, reading, reading'] at printed
          | none =>
              cases reading' : bareCollection? packed'.1 with
              | some _ => simp [nodeOf, reading, reading'] at printed
              | none =>
                  simp only [nodeOf, reading, reading', Pattern.apply.injEq] at printed
                  obtain ⟨sameLabel, sameArgs⟩ := printed
                  have sameRule : packed.1 = packed'.1 :=
                    List.inj_on_of_nodup_map labels packed.2.1 packed'.2.1 sameLabel
                  have packedEq : packed = packed' := Subtype.ext sameRule
                  subst packedEq
                  obtain ⟨countsEq, lengthsEq, agree⟩ :=
                    assemblePrinted_recover
                      (fun direction => CollectionIndexed.toPattern (children direction))
                      (fun direction => CollectionIndexed.toPattern (children' direction))
                      0 packed.1.params data.counts data.lengths data'.counts data'.lengths
                      data.counts_length data.lengths_length data'.counts_length
                      data'.lengths_length data.counts_fixed data'.counts_fixed data.lengths_fixed
                      data'.lengths_fixed sameArgs
                  have dataEq : data = data' := headData_ext countsEq lengthsEq
                  subst dataEq
                  refine congrArg
                    (fun continuation =>
                      IFreeM.liftBind (P := polynomial (indexedSignature language))
                        ⟨packed, data⟩ continuation) ?_
                  funext direction
                  have bound : direction.val <
                      slotCount packed.1.params data.counts data.lengths := by
                    simpa [indexedSignature, expandSlots_length] using direction.isLt
                  have agreed := agree direction.val bound
                  rw [Nat.zero_add] at agreed
                  rw [nthPrinted_of_lt _ direction.isLt, nthPrinted_of_lt _ direction.isLt] at agreed
                  exact inductionHypothesis direction (children' direction) agreed

/-- Closed object patterns at a base sort are the indexed trees there.

`UniqueBare` is required because a bare collection is printed without its
label. Distinct labels do not separate two bare rules of one kind. -/
noncomputable def closedIndexedEquiv
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language) (sort : String) :
    Tree language ([], sort) ≃ ClosedObject language sort :=
  Equiv.ofBijective
    (fun tree =>
      ⟨CollectionIndexed.toPattern tree,
        ⟨toPattern_hasType tree, toPattern_isObject tree⟩⟩)
    ⟨fun left right same =>
      toPattern_injective labels uniqueBare left right (congrArg Subtype.val same),
      fun object => by
        obtain ⟨tree, printed⟩ :=
          exists_toPattern_of_size fragment (sizeOf object.1 + 1) [] object.1
            (Nat.lt_succ_self _) sort object.2.1 object.2.2
        exact ⟨tree, Subtype.ext printed⟩⟩

/-- Every collection node is a `vec`. -/
def VecShaped : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply _ arguments => ∀ argument ∈ arguments, VecShaped argument
  | .lambda _ body => VecShaped body
  | .multiLambda _ _ body => VecShaped body
  | .subst body replacement => VecShaped body ∧ VecShaped replacement
  | .collection kind elements _ => kind = .vec ∧ ∀ element ∈ elements, VecShaped element

theorem wrapBinders_vecShaped (binders : List String) {body : Pattern}
    (shaped : VecShaped body) : VecShaped (wrapBinders binders body) := by
  induction binders generalizing body with
  | nil => simpa [wrapBinders] using shaped
  | cons _ binders inductionHypothesis =>
      exact inductionHypothesis (by simpa [wrapBinders, VecShaped] using shaped)

theorem printArgument_vecShaped (parameter : TermParam) (count : Nat) {body : Pattern}
    (shaped : VecShaped body) : VecShaped (printArgument parameter count body) := by
  cases parameter with
  | simple _ type =>
      cases type <;> simpa [printArgument, slotBinders, wrapBinders] using shaped
  | abstractionNamed _ _ type =>
      cases type with
      | base _ => simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
      | arrow domain codomain =>
          cases domain <;> cases codomain <;>
            simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
      | multiBinder _ =>
          simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
      | collection _ _ =>
          simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base _ => simpa [printArgument, VecShaped] using shaped
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              cases inner <;> cases codomain <;>
                simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
          | base _ =>
              simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
          | arrow _ _ =>
              simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
          | collection _ _ =>
              simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
      | multiBinder _ =>
          simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped
      | collection _ _ =>
          simpa [printArgument, slotBinders, wrapBinders, VecShaped] using shaped

theorem nthPrinted_vecShaped {total : Nat} (printed : Fin total → Pattern)
    (shaped : ∀ index, VecShaped (printed index)) (index : Nat) :
    VecShaped (nthPrinted printed index) := by
  rw [nthPrinted]
  split
  · exact shaped _
  · simp [VecShaped]

theorem assemblePrinted_vecShaped
    (vecOnly : VecOnly language) {rule : GrammarRule}
    (member : rule ∈ language.terms)
    {total : Nat} (printed : Fin total → Pattern)
    (shaped : ∀ index, VecShaped (printed index))
    (offset : Nat) (parameters : List TermParam)
    (subset : ∀ parameter ∈ parameters, parameter ∈ rule.params)
    (counts lengths : List Nat) :
    ∀ argument ∈ assemblePrinted printed offset parameters counts lengths,
      VecShaped argument := by
  induction parameters generalizing counts lengths offset with
  | nil =>
      intro argument memberArgument
      simp [assemblePrinted] at memberArgument
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil =>
          intro argument memberArgument
          simp [assemblePrinted] at memberArgument
      | cons count counts =>
          cases lengths with
          | nil =>
              intro argument memberArgument
              simp [assemblePrinted] at memberArgument
          | cons length lengths =>
              cases reading : baseCollection? parameter with
              | some packed =>
                  obtain ⟨kind, element⟩ := packed
                  intro argument memberArgument
                  simp only [assemblePrinted, reading, List.mem_cons] at memberArgument
                  cases memberArgument with
                  | inl head =>
                      subst head
                      have kindVec : kind = .vec :=
                        vecOnly rule member parameter (subset parameter (by simp)) kind element
                          reading
                      simp only [VecShaped]
                      refine ⟨kindVec, ?_⟩
                      intro elementPattern elementMember
                      obtain ⟨index, elementAt⟩ := List.mem_ofFn.mp elementMember
                      rw [← elementAt]
                      exact nthPrinted_vecShaped printed shaped _
                  | inr tail =>
                      exact inductionHypothesis (offset + length)
                        (fun parameter parameterMember =>
                          subset parameter (List.mem_cons_of_mem _ parameterMember))
                        counts lengths argument tail
              | none =>
                  intro argument memberArgument
                  simp only [assemblePrinted, reading, List.mem_cons] at memberArgument
                  cases memberArgument with
                  | inl head =>
                      subst head
                      exact printArgument_vecShaped parameter count
                        (nthPrinted_vecShaped printed shaped offset)
                  | inr tail =>
                      exact inductionHypothesis (offset + 1)
                        (fun parameter parameterMember =>
                          subset parameter (List.mem_cons_of_mem _ parameterMember))
                        counts lengths argument tail

theorem toPattern_vecShaped (vecOnly : VecOnly language)
    {index : List String × String} (tree : Tree language index) :
    VecShaped (CollectionIndexed.toPattern tree) := by
  induction tree using IFreeM.inductionOn with
  | pure _ _ =>
      rw [CollectionIndexed.toPattern_pure]
      simp [VecShaped]
  | liftBind _ operator children inductionHypothesis =>
      rw [CollectionIndexed.toPattern_liftBind]
      cases reading : bareCollection? operator.1.1 with
      | some packed =>
          obtain ⟨kind, element⟩ := packed
          obtain ⟨name, paramsEq⟩ := bare_rule_params reading
          have kindVec : kind = .vec :=
            vecOnly operator.1.1 operator.1.2.1
              (.simple name (.collection kind (.base element))) (by simp [paramsEq]) kind element
              (by simp [baseCollection?])
          simp only [nodeOf, reading, VecShaped]
          refine ⟨kindVec, ?_⟩
          intro elementPattern elementMember
          obtain ⟨direction, elementAt⟩ := List.mem_ofFn.mp elementMember
          rw [← elementAt]
          exact inductionHypothesis direction
      | none =>
          simp only [nodeOf, reading, VecShaped]
          exact assemblePrinted_vecShaped vecOnly operator.1.2.1
            (fun direction => CollectionIndexed.toPattern (children direction))
            inductionHypothesis 0 operator.1.1.params (fun _ parameterMember => parameterMember)
            operator.2.counts operator.2.lengths

/-- On patterns whose collections are vectors, the bag and set generators do
not apply, so the pattern congruence is equality. -/
theorem vec_cong_eq {left right : Pattern} (related : PatternCong left right)
    (shaped : VecShaped left ∨ VecShaped right) : left = right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis shaped.symm).symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl shapedLeft =>
          have leftMid := inductionHypothesis (Or.inl shapedLeft)
          exact leftMid.trans (inductionHypothesis' (Or.inl (leftMid ▸ shapedLeft)))
      | inr shapedRight =>
          have midRight := inductionHypothesis' (Or.inr shapedRight)
          exact (inductionHypothesis (Or.inr (midRight.symm ▸ shapedRight))).trans midRight
  | bagPerm _ =>
      cases shaped with
      | inl shapedLeft =>
          simp only [VecShaped] at shapedLeft
          cases shapedLeft.1
      | inr shapedRight =>
          simp only [VecShaped] at shapedRight
          cases shapedRight.1
  | setPerm _ =>
      cases shaped with
      | inl shapedLeft =>
          simp only [VecShaped] at shapedLeft
          cases shapedLeft.1
      | inr shapedRight =>
          simp only [VecShaped] at shapedRight
          cases shapedRight.1
  | setDup =>
      cases shaped with
      | inl shapedLeft =>
          simp only [VecShaped] at shapedLeft
          cases shapedLeft.1
      | inr shapedRight =>
          simp only [VecShaped] at shapedRight
          cases shapedRight.1
  | applyAt _ inductionHypothesis =>
      expose_names
      cases shaped with
      | inl shapedLeft =>
          have argumentShaped : VecShaped left_1 := by
            simp only [VecShaped] at shapedLeft
            exact shapedLeft left_1
              (List.mem_append_right before (List.mem_cons_self (a := left_1)))
          rw [inductionHypothesis (Or.inl argumentShaped)]
      | inr shapedRight =>
          have argumentShaped : VecShaped right_1 := by
            simp only [VecShaped] at shapedRight
            exact shapedRight right_1
              (List.mem_append_right before (List.mem_cons_self (a := right_1)))
          rw [inductionHypothesis (Or.inr argumentShaped)]
  | lambdaAt _ inductionHypothesis =>
      cases shaped with
      | inl shapedLeft =>
          rw [inductionHypothesis (by simpa [VecShaped] using Or.inl shapedLeft)]
      | inr shapedRight =>
          rw [inductionHypothesis (by simpa [VecShaped] using Or.inr shapedRight)]
  | multiLambdaAt _ inductionHypothesis =>
      cases shaped with
      | inl shapedLeft =>
          rw [inductionHypothesis (by simpa [VecShaped] using Or.inl shapedLeft)]
      | inr shapedRight =>
          rw [inductionHypothesis (by simpa [VecShaped] using Or.inr shapedRight)]
  | collectionAt _ inductionHypothesis =>
      expose_names
      cases shaped with
      | inl shapedLeft =>
          have elementShaped : VecShaped left_1 := by
            simp only [VecShaped] at shapedLeft
            exact shapedLeft.2 left_1
              (List.mem_append_right before (List.mem_cons_self (a := left_1)))
          rw [inductionHypothesis (Or.inl elementShaped)]
      | inr shapedRight =>
          have elementShaped : VecShaped right_1 := by
            simp only [VecShaped] at shapedRight
            exact shapedRight.2 right_1
              (List.mem_append_right before (List.mem_cons_self (a := right_1)))
          rw [inductionHypothesis (Or.inr elementShaped)]

theorem closed_vecShaped
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (vecOnly : VecOnly language) {sort : String} (object : ClosedObject language sort) :
    VecShaped object.1 := by
  obtain ⟨tree, printed⟩ :=
    exists_toPattern_of_size fragment (sizeOf object.1 + 1) [] object.1 (Nat.lt_succ_self _)
      sort object.2.1 object.2.2
  rw [← printed]
  exact toPattern_vecShaped vecOnly tree

/-- With only `vec` parameters, pattern congruence does not identify distinct
closed object patterns. -/
theorem vecOnly_patternCong_eq
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (vecOnly : VecOnly language) {sort : String} {left right : ClosedObject language sort}
    (related : PatternCong left.1 right.1) : left = right :=
  Subtype.ext (vec_cong_eq related (Or.inl (closed_vecShaped fragment vecOnly left)))

/-- Closed object patterns, read as indexed trees. The vec hypothesis is not
required for the bijection; `vecOnly_patternCong_eq` says there is nothing
further to quotient. -/
noncomputable def vecIndexedEquiv
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language) (sort : String) :
    ClosedObject language sort ≃ Tree language ([], sort) :=
  (closedIndexedEquiv fragment labels uniqueBare sort).symm

/-- Collapsing a setoid whose relation is equality. -/
noncomputable def quotientCollapse {α : Type} (setoid : Setoid α)
    (trivial : ∀ left right, setoid.r left right → left = right) : Quotient setoid ≃ α where
  toFun := Quotient.lift id trivial
  invFun := Quotient.mk setoid
  left_inv quotient := by
    induction quotient using Quotient.inductionOn with
    | _ element => rfl
  right_inv _ := rfl

/-- For a vec language the pattern quotient is the indexed tree. -/
noncomputable def vecQuotientEquiv
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language) (vecOnly : VecOnly language) (sort : String) :
    Quotient (patternSetoid (language := language) sort) ≃ Tree language ([], sort) :=
  (quotientCollapse (patternSetoid (language := language) sort)
      (fun left right related =>
        vecOnly_patternCong_eq fragment vecOnly (left := left) (right := right) related)).trans
    (vecIndexedEquiv fragment labels uniqueBare sort)

end Mettapedia.GSLT.Poly.CollectionIndexedEquiv
