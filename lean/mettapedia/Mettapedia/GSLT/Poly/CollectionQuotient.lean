import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.Poly.CollectionIndexedQuotient
import Mettapedia.GSLT.Poly.CollectionLanguage
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.QPF.Univariate.Basic

/-!
# Bags as the multiset quotient of the list polynomial

A language whose constructors are nullary or one `hashBag` of their own sort
prints closed object patterns at that sort. Reading each bag as the multiset
of the readings of its elements is the initial algebra of the bag quotient of
the list polynomial. Two patterns denote the same algebra element exactly when
their bag elements agree up to permutation after the same reading. Nesting and
a singleton are not erased: those equations are not this functor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionQuotient

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.CollectionIndexed
open Mettapedia.GSLT.Poly.CollectionIndexedEquiv
open Mettapedia.GSLT.Poly.CollectionLanguage

/-- Nullary atoms and one hash bag of the same sort. -/
def bagLanguage : LanguageDef :=
  { name := "Bags", types := [{ name := "A" }],
    terms := [atomURule, atomWRule, hashBagRule],
    equations := [], rewrites := [] }

/-- A closed object pattern of the bag language, typed at the base sort. -/
abbrev ClosedBag : Type :=
  {pattern : Pattern //
    HasType bagLanguage FreeTypeContext.empty [] pattern (.base "A") ∧
      isObjectPattern pattern = true}

/-- Fuelled reading of a pattern as a bag tree.

The zero-fuel branch is unused once the fuel exceeds the pattern. A `hashBag`
node becomes the multiset of the readings of its elements. Any other shape
falls through to the atom `U`, and the typing theorems never call it. -/
noncomputable def encodeFuel : Nat → Pattern → QPF.Fix CollShape
  | 0, _ => atomTree .u
  | bound + 1, pattern =>
      if pattern = .apply "U" [] then atomTree .u
      else if pattern = .apply "W" [] then atomTree .w
      else
        match pattern with
        | .collection .hashBag elements none =>
            bagTree (↑(elements.map (encodeFuel bound)))
        | _ => atomTree .u

/-- The reading of a pattern at fuel one larger than its size. -/
noncomputable def encodePattern (pattern : Pattern) : QPF.Fix CollShape :=
  encodeFuel (sizeOf pattern + 1) pattern

theorem encodeFuel_agree :
    (bound : Nat) → (pattern : Pattern) → sizeOf pattern < bound →
      (fuel : Nat) → sizeOf pattern < fuel →
        encodeFuel bound pattern = encodeFuel fuel pattern
  | 0, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | _, _, _, 0, small => absurd small (Nat.not_lt_zero _)
  | bound + 1, pattern, boundEnough, fuel + 1, fuelEnough => by
      by_cases isU : pattern = .apply "U" []
      · subst isU
        simp only [encodeFuel]
      · by_cases isW : pattern = .apply "W" []
        · subst isW
          simp only [encodeFuel, if_neg isU]
        · cases pattern with
          | bvar index =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | fvar name =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | lambda binder body =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | multiLambda arity binders body =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | subst body replacement =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | apply label arguments =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | collection collectionType elements rest =>
              cases collectionType with
              | vec =>
                  simp only [encodeFuel, if_neg isU, if_neg isW]
              | hashSet =>
                  simp only [encodeFuel, if_neg isU, if_neg isW]
              | hashBag =>
                  cases rest with
                  | some name =>
                      simp only [encodeFuel, if_neg isU, if_neg isW]
                  | none =>
                      simp only [encodeFuel, if_neg isU, if_neg isW]
                      suffices lists :
                          List.map (encodeFuel bound) elements =
                            List.map (encodeFuel fuel) elements by
                        exact congrArg bagTree
                          (congrArg (Multiset.ofList (α := QPF.Fix CollShape)) lists)
                      have eachBound : ∀ element ∈ elements, sizeOf element < bound := by
                        intro element member
                        have smaller := List.sizeOf_lt_of_mem member
                        simp only [Pattern.collection.sizeOf_spec] at boundEnough smaller
                        omega
                      have eachFuel : ∀ element ∈ elements, sizeOf element < fuel := by
                        intro element member
                        have smaller := List.sizeOf_lt_of_mem member
                        simp only [Pattern.collection.sizeOf_spec] at fuelEnough smaller
                        omega
                      clear isU isW boundEnough fuelEnough
                      induction elements with
                      | nil => rfl
                      | cons head tail inductionHypothesis =>
                          simp only [List.map_cons]
                          rw [List.cons.injEq]
                          refine ⟨?_, ?_⟩
                          · exact encodeFuel_agree bound head
                              (eachBound head List.mem_cons_self) fuel
                              (eachFuel head List.mem_cons_self)
                          · exact inductionHypothesis
                              (fun element member =>
                                eachBound element (List.mem_cons_of_mem head member))
                              (fun element member =>
                                eachFuel element (List.mem_cons_of_mem head member))

theorem map_encodeFuel (fuel : Nat) (elements : List Pattern)
    (each : ∀ element ∈ elements, sizeOf element < fuel) :
    elements.map (encodeFuel fuel) = elements.map encodePattern := by
  induction elements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, encodePattern]
      congr 1
      · exact encodeFuel_agree fuel head (each head List.mem_cons_self)
          (sizeOf head + 1) (Nat.lt_succ_self _)
      · exact inductionHypothesis fun element member =>
          each element (List.mem_cons_of_mem head member)

/-- A bag is the multiset of the readings of its elements. -/
theorem encodePattern_bag (elements : List Pattern) :
    encodePattern (.collection .hashBag elements none) =
      bagTree (↑(elements.map encodePattern)) := by
  have notU :
      Pattern.collection .hashBag elements none ≠ Pattern.apply "U" [] := by
    intro same
    cases same
  have notW :
      Pattern.collection .hashBag elements none ≠ Pattern.apply "W" [] := by
    intro same
    cases same
  change encodeFuel (sizeOf (Pattern.collection .hashBag elements none) + 1)
      (Pattern.collection .hashBag elements none) =
    bagTree (↑(elements.map encodePattern))
  simp only [encodeFuel, if_neg notU, if_neg notW]
  apply congrArg bagTree
  apply congrArg (Multiset.ofList (α := QPF.Fix CollShape))
  refine map_encodeFuel _ elements ?_
  intro element member
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Pattern.collection.sizeOf_spec] at smaller ⊢
  omega

theorem encodePattern_u : encodePattern (.apply "U" []) = atomTree .u := by
  unfold encodePattern
  simp [encodeFuel]

theorem encodePattern_w : encodePattern (.apply "W" []) = atomTree .w := by
  unfold encodePattern
  simp [encodeFuel]

/-- Permuting the elements of one bag does not change its reading. -/
theorem encode_list_perm {left right : List Pattern} (perm : left.Perm right) :
    encodePattern (.collection .hashBag left none) =
      encodePattern (.collection .hashBag right none) := by
  rw [encodePattern_bag, encodePattern_bag]
  apply congrArg bagTree
  exact Multiset.coe_eq_coe.mpr (perm.map encodePattern)

/-- A bag reading determines its elements up to permutation of their readings. -/
theorem encode_bag_eq_iff (left right : List Pattern) :
    encodePattern (.collection .hashBag left none) =
        encodePattern (.collection .hashBag right none) ↔
      (left.map encodePattern).Perm (right.map encodePattern) := by
  rw [encodePattern_bag, encodePattern_bag]
  constructor
  · intro same
    exact Multiset.coe_eq_coe.mp (bagTree_injective same)
  · intro perm
    exact congrArg bagTree (Multiset.coe_eq_coe.mpr perm)

/-- Every element of a bag satisfies a predicate that lifts over the bag. -/
theorem liftp_bag {α : Type} {p : α → Prop} {elements : Multiset α}
    (lifted : Functor.Liftp p (CollShape.bag elements)) {element : α}
    (member : element ∈ elements) : p element := by
  rcases lifted with ⟨shape, shapeEqual⟩
  cases shape with
  | atom _ =>
      dsimp only [Functor.map] at shapeEqual
      cases shapeEqual
  | bag children =>
      dsimp only [Functor.map] at shapeEqual
      injection shapeEqual with elementsEqual
      rw [← elementsEqual] at member
      obtain ⟨child, _, printed⟩ := Multiset.mem_map.mp member
      rw [← printed]
      exact child.property

/-- One node of the bag algebra, once its elements are already patterns. -/
noncomputable def nodePattern : CollShape Pattern → Pattern
  | .atom .u => .apply "U" []
  | .atom .w => .apply "W" []
  | .bag elements => .collection .hashBag elements.toList none

/-- A bag tree, printed as a pattern by choosing one list representative. -/
noncomputable def bagToPattern : QPF.Fix CollShape → Pattern :=
  QPF.Fix.rec nodePattern

theorem bagToPattern_mk (shape : CollShape (QPF.Fix CollShape)) :
    bagToPattern (QPF.Fix.mk shape) = nodePattern (bagToPattern <$> shape) := by
  rw [bagToPattern, QPF.Fix.rec_eq]

theorem elements_of_mem {elements : List Pattern}
    (each : ∀ element ∈ elements,
      HasType bagLanguage FreeTypeContext.empty [] element (.base "A")) :
    ElementsHaveType bagLanguage FreeTypeContext.empty [] elements (.base "A") := by
  induction elements with
  | nil => exact ElementsHaveType.nil [] (.base "A")
  | cons head tail inductionHypothesis =>
      exact ElementsHaveType.cons (each head List.mem_cons_self)
        (inductionHypothesis fun element member =>
          each element (List.mem_cons_of_mem head member))

theorem objects_of_mem {elements : List Pattern}
    (each : ∀ element ∈ elements, isObjectPattern element = true) :
    isObjectPatternList elements = true := by
  induction elements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [isObjectPatternList, each head List.mem_cons_self,
        inductionHypothesis fun element member =>
          each element (List.mem_cons_of_mem head member)]

theorem bagToPattern_hasType (tree : QPF.Fix CollShape) :
    HasType bagLanguage FreeTypeContext.empty [] (bagToPattern tree) (.base "A") := by
  refine QPF.Fix.ind
    (fun tree => HasType bagLanguage FreeTypeContext.empty [] (bagToPattern tree) (.base "A"))
    ?_ tree
  intro shape lifted
  rw [bagToPattern_mk]
  cases shape with
  | atom name =>
      cases name with
      | u =>
          dsimp only [nodePattern, Functor.map]
          exact HasType.constructor (rule := atomURule) (by simp [bagLanguage])
            (not_bare_atom atomURule rfl) ArgumentsHaveTypes.nil
      | w =>
          dsimp only [nodePattern, Functor.map]
          exact HasType.constructor (rule := atomWRule) (by simp [bagLanguage])
            (not_bare_atom atomWRule rfl) ArgumentsHaveTypes.nil
  | bag elements =>
      dsimp only [nodePattern, Functor.map]
      refine HasType.collectionConstructor (rule := hashBagRule) (by simp [bagLanguage]) rfl ?_
      refine elements_of_mem ?_
      intro element member
      rw [Multiset.mem_toList] at member
      obtain ⟨child, childMember, printed⟩ := Multiset.mem_map.mp member
      have typedChild := liftp_bag lifted childMember
      rw [← printed]
      exact typedChild

theorem bagToPattern_isObject (tree : QPF.Fix CollShape) :
    isObjectPattern (bagToPattern tree) = true := by
  refine QPF.Fix.ind (fun tree => isObjectPattern (bagToPattern tree) = true) ?_ tree
  intro shape lifted
  rw [bagToPattern_mk]
  cases shape with
  | atom name =>
      cases name <;> dsimp [nodePattern, Functor.map, isObjectPattern, isObjectPatternList]
  | bag elements =>
      dsimp only [nodePattern, Functor.map, isObjectPattern, Option.isNone]
      refine objects_of_mem ?_
      intro element member
      rw [Multiset.mem_toList] at member
      obtain ⟨child, childMember, printed⟩ := Multiset.mem_map.mp member
      have objectChild := liftp_bag lifted childMember
      rw [← printed]
      exact objectChild

/-- Printing a tree and reading the pattern returns the tree. -/
theorem encode_bagToPattern (tree : QPF.Fix CollShape) :
    encodePattern (bagToPattern tree) = tree := by
  refine QPF.Fix.ind (fun tree => encodePattern (bagToPattern tree) = tree) ?_ tree
  intro shape lifted
  rw [bagToPattern_mk]
  cases shape with
  | atom name =>
      cases name with
      | u =>
          dsimp only [nodePattern, Functor.map]
          rw [encodePattern_u, atomTree]
      | w =>
          dsimp only [nodePattern, Functor.map]
          rw [encodePattern_w, atomTree]
  | bag elements =>
      dsimp only [nodePattern, Functor.map]
      rw [encodePattern_bag]
      apply congrArg bagTree
      have printed :
          ↑((elements.map bagToPattern).toList.map encodePattern) =
            (elements.map bagToPattern).map encodePattern := by
        rw [← Multiset.map_coe, Multiset.coe_toList]
      rw [printed]
      have pointwise : ∀ child ∈ elements, encodePattern (bagToPattern child) = child :=
        fun child member => liftp_bag lifted member
      rw [Multiset.map_map]
      have mapped :
          elements.map (encodePattern ∘ bagToPattern) = elements.map id := by
        refine Multiset.map_congr rfl ?_
        intro child member
        exact pointwise child member
      rw [mapped, Multiset.map_id]

/-- Closed object patterns of the bag language, modulo the multiset reading. -/
def encodeSetoid : Setoid ClosedBag where
  r pattern other := encodePattern pattern.1 = encodePattern other.1
  iseqv := ⟨fun _ => rfl, fun equal => equal.symm, fun left right => left.trans right⟩

/-- The printed pattern of a bag tree, as a closed object pattern. -/
noncomputable def closedOfTree (tree : QPF.Fix CollShape) : ClosedBag :=
  ⟨bagToPattern tree, bagToPattern_hasType tree, bagToPattern_isObject tree⟩

/-- A pattern that is not an atom and not a bare hash bag reads as the atom `U`. -/
theorem encodeFuel_succ_fallback (pattern : Pattern) (bound : Nat)
    (notU : pattern ≠ .apply "U" [])
    (notW : pattern ≠ .apply "W" [])
    (notBag : ∀ elements, pattern ≠ .collection .hashBag elements none) :
    encodeFuel (bound + 1) pattern = atomTree .u := by
  unfold encodeFuel
  rw [if_neg notU, if_neg notW]
  cases pattern with
  | bvar _ => rfl
  | fvar _ => rfl
  | lambda _ _ => rfl
  | multiLambda _ _ _ => rfl
  | subst _ _ => rfl
  | apply _ _ => rfl
  | collection kind elements rest =>
      cases kind with
      | vec => rfl
      | hashSet => rfl
      | hashBag =>
          cases rest with
          | some _ => rfl
          | none => exact (notBag elements rfl).elim

theorem encodePattern_atom (pattern : Pattern)
    (notU : pattern ≠ .apply "U" [])
    (notW : pattern ≠ .apply "W" [])
    (notBag : ∀ elements, pattern ≠ .collection .hashBag elements none) :
    encodePattern pattern = atomTree .u := by
  unfold encodePattern
  exact encodeFuel_succ_fallback pattern (sizeOf pattern) notU notW notBag

theorem apply_nonempty_not_nullary (label atom : String) (before : List Pattern)
    (argument : Pattern) (after : List Pattern) :
    Pattern.apply label (before ++ argument :: after) ≠ Pattern.apply atom [] := by
  intro same
  injection same with _ args
  have lengths := congrArg List.length args
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  omega

/-- Bag permutation, and every other pattern step, preserves the multiset reading. -/
theorem encode_patternCong {left right : Pattern} (related : PatternCong left right) :
    encodePattern left = encodePattern right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | @bagPerm elements swapped perm => exact encode_list_perm perm
  | @setPerm elements swapped _perm =>
      exact (encodePattern_atom (.collection .hashSet elements none)
        (by intro same; cases same) (by intro same; cases same)
        (by intro _ same; cases same)).trans
        (encodePattern_atom (.collection .hashSet swapped none)
          (by intro same; cases same) (by intro same; cases same)
          (by intro _ same; cases same)).symm
  | @setDup before element after =>
      exact (encodePattern_atom
          (.collection .hashSet (before ++ element :: element :: after) none)
          (by intro same; cases same) (by intro same; cases same)
          (by intro _ same; cases same)).trans
        (encodePattern_atom (.collection .hashSet (before ++ element :: after) none)
          (by intro same; cases same) (by intro same; cases same)
          (by intro _ same; cases same)).symm
  | @applyAt label before leftPattern rightPattern after _related _ih =>
      exact (encodePattern_atom (.apply label (before ++ leftPattern :: after))
        (apply_nonempty_not_nullary label "U" before leftPattern after)
        (apply_nonempty_not_nullary label "W" before leftPattern after)
        (by intro _ same; cases same)).trans
        (encodePattern_atom (.apply label (before ++ rightPattern :: after))
          (apply_nonempty_not_nullary label "U" before rightPattern after)
          (apply_nonempty_not_nullary label "W" before rightPattern after)
          (by intro _ same; cases same)).symm
  | @lambdaAt binder leftBody rightBody _related _ih =>
      exact (encodePattern_atom (.lambda binder leftBody)
        (by intro same; cases same) (by intro same; cases same)
        (by intro _ same; cases same)).trans
        (encodePattern_atom (.lambda binder rightBody)
          (by intro same; cases same) (by intro same; cases same)
          (by intro _ same; cases same)).symm
  | @multiLambdaAt arity binders leftBody rightBody _related _ih =>
      exact (encodePattern_atom (.multiLambda arity binders leftBody)
        (by intro same; cases same) (by intro same; cases same)
        (by intro _ same; cases same)).trans
        (encodePattern_atom (.multiLambda arity binders rightBody)
          (by intro same; cases same) (by intro same; cases same)
          (by intro _ same; cases same)).symm
  | @collectionAt kind before leftPattern rightPattern after rest
      inductionHypothesis _ih =>
      cases kind with
      | hashBag =>
          cases rest with
          | none =>
              rw [encodePattern_bag, encodePattern_bag]
              apply congrArg bagTree
              apply congrArg (Multiset.ofList (α := QPF.Fix CollShape))
              simp only [List.map_append, List.map_cons, _ih]
          | some name =>
              exact (encodePattern_atom
                  (.collection .hashBag (before ++ leftPattern :: after) (some name))
                  (by intro same; cases same) (by intro same; cases same)
                  (by intro _ same; cases same)).trans
                (encodePattern_atom
                  (.collection .hashBag (before ++ rightPattern :: after) (some name))
                  (by intro same; cases same) (by intro same; cases same)
                  (by intro _ same; cases same)).symm
      | hashSet =>
          exact (encodePattern_atom
              (.collection .hashSet (before ++ leftPattern :: after) rest)
              (by intro same; cases same) (by intro same; cases same)
              (by intro _ same; cases same)).trans
            (encodePattern_atom
              (.collection .hashSet (before ++ rightPattern :: after) rest)
              (by intro same; cases same) (by intro same; cases same)
              (by intro _ same; cases same)).symm
      | vec =>
          exact (encodePattern_atom
              (.collection .vec (before ++ leftPattern :: after) rest)
              (by intro same; cases same) (by intro same; cases same)
              (by intro _ same; cases same)).trans
            (encodePattern_atom
              (.collection .vec (before ++ rightPattern :: after) rest)
              (by intro same; cases same) (by intro same; cases same)
              (by intro _ same; cases same)).symm

theorem elementsHaveType_of_mem {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
    {element : Pattern}
    (typed : ElementsHaveType language free bound elements elementType)
    (member : element ∈ elements) :
    HasType language free bound element elementType :=
  match typed with
  | .nil _ _ => by cases member
  | .cons headTyped tailTyped => by
      cases member with
      | head => exact headTyped
      | tail _ member => exact elementsHaveType_of_mem tailTyped member

theorem object_of_mem {element : Pattern} {elements : List Pattern}
    (objects : isObjectPatternList elements = true) (member : element ∈ elements) :
    isObjectPattern element = true := by
  induction elements with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      cases member with
      | head => exact objects.1
      | tail _ member => exact inductionHypothesis objects.2 member

/-- An application node is typed by one ordinary constructor rule. -/
theorem apply_rule_of_hasType
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply label arguments) type) :
    ∃ rule ∈ language.terms,
      ¬ UsesBareCollection rule ∧
      rule.label = label ∧
      type = .base rule.category ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  cases typed with
  | constructor membership notBare argumentsTyped =>
      exact ⟨_, membership, notBare, rfl, rfl, argumentsTyped⟩

/-- A collection node is a collection type or one bare collection rule. -/
theorem collection_rule_of_hasType
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {kind : CollType} {elements : List Pattern} {rest : Option String}
    {type : TypeExpr}
    (typed : HasType language free bound (.collection kind elements rest) type) :
    (∃ elementType,
        type = .collection kind elementType ∧
          ElementsHaveType language free bound elements elementType) ∨
      (∃ rule ∈ language.terms, ∃ parameterName elementType,
        rule.params =
            [.simple parameterName (.collection kind elementType)] ∧
          type = .base rule.category ∧
          ElementsHaveType language free bound elements elementType) := by
  cases typed with
  | collection elementsTyped =>
      exact Or.inl ⟨_, rfl, elementsTyped⟩
  | collectionConstructor membership shape elementsTyped =>
      exact Or.inr ⟨_, membership, _, _, ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2, rfl,
        elementsTyped⟩

/-- A closed bag pattern is an atom `U`, an atom `W`, or a hash bag of closed bag patterns. -/
theorem bag_closed_shape (pattern : Pattern)
    (typed : HasType bagLanguage FreeTypeContext.empty [] pattern (.base "A"))
    (object : isObjectPattern pattern = true) :
    pattern = .apply "U" [] ∨ pattern = .apply "W" [] ∨
      ∃ elements : List Pattern,
        pattern = .collection .hashBag elements none ∧
          ∀ element ∈ elements,
            HasType bagLanguage FreeTypeContext.empty [] element (.base "A") ∧
              isObjectPattern element = true := by
  cases pattern with
  | bvar _ => exact (bvar_not_typed_in_empty typed).elim
  | fvar _ => exact (fvar_not_typed_in_empty typed).elim
  | lambda _ _ =>
      generalize typeEq : TypeExpr.base "A" = result at typed
      cases typed
      cases typeEq
  | multiLambda _ _ _ =>
      generalize typeEq : TypeExpr.base "A" = result at typed
      cases typed
      cases typeEq
  | subst _ _ => simp [isObjectPattern] at object
  | apply label arguments =>
      rcases apply_rule_of_hasType typed with
        ⟨rule, membership, notBare, labelEq, _typeEq, argumentsTyped⟩
      simp only [bagLanguage, atomURule, atomWRule, hashBagRule, List.mem_cons,
        List.mem_nil_iff, or_false] at membership
      rcases membership with rfl | rfl | rfl
      · have lengthZero := ArgumentsHaveTypes.length_eq argumentsTyped
        simp only [List.length_nil] at lengthZero
        have argumentsNil : arguments = [] := List.length_eq_zero_iff.mp lengthZero
        subst argumentsNil
        cases labelEq
        exact Or.inl rfl
      · have lengthZero := ArgumentsHaveTypes.length_eq argumentsTyped
        simp only [List.length_nil] at lengthZero
        have argumentsNil : arguments = [] := List.length_eq_zero_iff.mp lengthZero
        subst argumentsNil
        cases labelEq
        exact Or.inr (Or.inl rfl)
      · exact (notBare ⟨"xs", .hashBag, .base "A", rfl⟩).elim
  | collection kind elements rest =>
      cases rest with
      | some _ => simp [isObjectPattern] at object
      | none =>
          rcases collection_rule_of_hasType typed with
            ⟨_elementType, typeEq, _elementsTyped⟩ |
            ⟨rule, membership, _parameterName, _elementType, paramsEq, _typeEq,
              elementsTyped⟩
          · cases typeEq
          · simp only [bagLanguage, atomURule, atomWRule, hashBagRule, List.mem_cons,
              List.mem_nil_iff, or_false] at membership
            rcases membership with rfl | rfl | rfl
            · cases paramsEq
            · cases paramsEq
            · injection paramsEq with headEq _tailEq
              injection headEq with _nameEq collEq
              injection collEq with kindEq elementEq
              subst kindEq
              subst elementEq
              simp only [isObjectPattern, Bool.and_eq_true] at object
              refine Or.inr (Or.inr ⟨elements, rfl, ?_⟩)
              intro element member
              exact ⟨elementsHaveType_of_mem elementsTyped member,
                object_of_mem object.2 member⟩

theorem encode_u_ne_w :
    encodePattern (.apply "U" []) ≠ encodePattern (.apply "W" []) := by
  rw [encodePattern_u, encodePattern_w]
  intro same
  have destEqual := congrArg QPF.Fix.dest same
  unfold atomTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

theorem encode_u_ne_bag (elements : List Pattern) :
    encodePattern (.apply "U" []) ≠
      encodePattern (.collection .hashBag elements none) := by
  rw [encodePattern_u, encodePattern_bag]
  intro same
  have destEqual := congrArg QPF.Fix.dest same
  unfold atomTree bagTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

theorem encode_w_ne_bag (elements : List Pattern) :
    encodePattern (.apply "W" []) ≠
      encodePattern (.collection .hashBag elements none) := by
  rw [encodePattern_w, encodePattern_bag]
  intro same
  have destEqual := congrArg QPF.Fix.dest same
  unfold atomTree bagTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

theorem bag_child_smaller {elements : List Pattern} {element : Pattern}
    (member : element ∈ elements) :
    sizeOf element < sizeOf (Pattern.collection .hashBag elements none) := by
  have listSmall := List.sizeOf_lt_of_mem member
  simp only [Pattern.collection.sizeOf_spec]
  omega

/-- Replacing children one by one sends a pointwise congruence to the bag. -/
theorem patternCong_bag_forall2_aux (before : List Pattern) {left right : List Pattern} :
    List.Forall₂ PatternCong left right →
      PatternCong (.collection .hashBag (before ++ left) none)
        (.collection .hashBag (before ++ right) none)
  | .nil => by
      exact PatternCong.refl _
  | .cons (b := rightHead) (l₁ := leftTail) headRelated tailRelated => by
      apply PatternCong.trans
      · exact PatternCong.collectionAt (kind := .hashBag) (before := before)
          (after := leftTail) (rest := none) headRelated
      · have step :=
          patternCong_bag_forall2_aux (before ++ [rightHead]) tailRelated
        simpa [List.append_assoc, List.singleton_append] using step

theorem patternCong_bag_forall2 {left right : List Pattern}
    (related : List.Forall₂ PatternCong left right) :
    PatternCong (.collection .hashBag left none) (.collection .hashBag right none) :=
  patternCong_bag_forall2_aux [] related

theorem exists_forall2_of_map_perm {α β : Type} (f : α → β) :
    ∀ {left right : List α}, (left.map f).Perm (right.map f) →
      ∃ middle, left.Perm middle ∧ List.Forall₂ (fun a b => f a = f b) middle right := by
  intro left right
  induction right generalizing left with
  | nil =>
      intro perm
      have leftNil : left = [] := by
        have lengthEq := List.Perm.length_eq perm
        simp only [List.length_map, List.length_nil, List.length_eq_zero_iff] at lengthEq
        exact lengthEq
      subst leftNil
      exact ⟨[], List.Perm.nil, List.Forall₂.nil⟩
  | cons head tail inductionHypothesis =>
      intro perm
      have headMem : f head ∈ (head :: tail).map f :=
        List.mem_map.mpr ⟨head, List.mem_cons_self, rfl⟩
      have mem : f head ∈ left.map f := (perm.mem_iff).mpr headMem
      obtain ⟨element, elementMem, encoded⟩ := List.mem_map.mp mem
      obtain ⟨before, after, rfl⟩ := List.append_of_mem elementMem
      have moved :
          ((before.map f) ++ f element :: after.map f).Perm
            (f element :: (before ++ after).map f) := by
        simp [List.map_append]
      have headPerm :
          (f element :: (before ++ after).map f).Perm (f head :: tail.map f) := by
        have rewriteMaps :
            (before ++ element :: after).map f =
              before.map f ++ f element :: after.map f := by
          simp [List.map_append, List.map_cons]
        rw [← rewriteMaps] at moved
        exact moved.symm.trans perm
      rw [encoded] at headPerm
      have tailPerm : ((before ++ after).map f).Perm (tail.map f) := headPerm.cons_inv
      obtain ⟨middleRest, restPerm, zipped⟩ :=
        inductionHypothesis (left := before ++ after) tailPerm
      refine ⟨element :: middleRest, ?_, List.Forall₂.cons encoded zipped⟩
      exact (@List.perm_middle _ element before after).trans (restPerm.cons element)

mutual

/-- Equal multiset readings of closed bag patterns are the pattern congruence. -/
theorem patternCong_of_encode_fuel :
    (fuel : Nat) → (left right : Pattern) →
    sizeOf left < fuel → sizeOf right < fuel →
    HasType bagLanguage FreeTypeContext.empty [] left (.base "A") →
    HasType bagLanguage FreeTypeContext.empty [] right (.base "A") →
    isObjectPattern left = true → isObjectPattern right = true →
    encodePattern left = encodePattern right →
    PatternCong left right
  | 0, _, _, small, _, _, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, left, right, leftSmall, rightSmall, typedLeft, typedRight,
      objectLeft, objectRight, same => by
      rcases bag_closed_shape left typedLeft objectLeft with rfl | rfl | ⟨elements, rfl, eachLeft⟩
      · rcases bag_closed_shape right typedRight objectRight with
          rfl | rfl | ⟨elementsRight, rfl, _⟩
        · exact PatternCong.refl _
        · exact absurd same encode_u_ne_w
        · exact absurd same (encode_u_ne_bag elementsRight)
      · rcases bag_closed_shape right typedRight objectRight with
          rfl | rfl | ⟨elementsRight, rfl, _⟩
        · exact absurd same encode_u_ne_w.symm
        · exact PatternCong.refl _
        · exact absurd same (encode_w_ne_bag elementsRight)
      · rcases bag_closed_shape right typedRight objectRight with
          rfl | rfl | ⟨elementsRight, rfl, eachRight⟩
        · exact absurd same (encode_u_ne_bag elements).symm
        · exact absurd same (encode_w_ne_bag elements).symm
        · rw [encode_bag_eq_iff] at same
          obtain ⟨middle, perm, zipped⟩ := exists_forall2_of_map_perm encodePattern same
          exact PatternCong.trans (PatternCong.bagPerm perm)
            (patternCong_bag_forall2
              (forall2_patternCong_fuel fuel
                (fun element member => (perm.mem_iff).mpr member) eachLeft eachRight
                (fun element member => by
                  have source := (perm.mem_iff).mpr member
                  have smaller := bag_child_smaller source
                  exact Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ leftSmall))
                (fun element member => by
                  have smaller := bag_child_smaller member
                  exact Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ rightSmall))
                zipped))
termination_by fuel _ _ _ _ _ _ _ _ _ => (fuel, 0)

/-- Pointwise equal readings of smaller closed patterns are the pattern congruence. -/
theorem forall2_patternCong_fuel (fuel : Nat) {middle right source : List Pattern}
    (inSource : ∀ element ∈ middle, element ∈ source)
    (eachSource : ∀ element ∈ source,
      HasType bagLanguage FreeTypeContext.empty [] element (.base "A") ∧
        isObjectPattern element = true)
    (eachRight : ∀ element ∈ right,
      HasType bagLanguage FreeTypeContext.empty [] element (.base "A") ∧
        isObjectPattern element = true)
    (sizeMiddle : ∀ element ∈ middle, sizeOf element < fuel)
    (sizeRight : ∀ element ∈ right, sizeOf element < fuel)
    (zipped : List.Forall₂ (fun a b => encodePattern a = encodePattern b) middle right) :
    List.Forall₂ PatternCong middle right :=
  match zipped with
  | .nil => List.Forall₂.nil
  | .cons (a := leftHead) (b := rightHead) (l₁ := leftTail) (l₂ := rightTail)
      sameEncode tail =>
      List.Forall₂.cons
        (patternCong_of_encode_fuel fuel leftHead rightHead
          (sizeMiddle leftHead (@List.mem_cons_self _ leftHead leftTail))
          (sizeRight rightHead (@List.mem_cons_self _ rightHead rightTail))
          (eachSource leftHead
            (inSource leftHead (@List.mem_cons_self _ leftHead leftTail))).1
          (eachRight rightHead (@List.mem_cons_self _ rightHead rightTail)).1
          (eachSource leftHead
            (inSource leftHead (@List.mem_cons_self _ leftHead leftTail))).2
          (eachRight rightHead (@List.mem_cons_self _ rightHead rightTail)).2
          sameEncode)
        (forall2_patternCong_fuel fuel
          (fun element member => inSource element (List.mem_cons_of_mem leftHead member))
          eachSource
          (fun element member => eachRight element (List.mem_cons_of_mem rightHead member))
          (fun element member => sizeMiddle element (List.mem_cons_of_mem leftHead member))
          (fun element member => sizeRight element (List.mem_cons_of_mem rightHead member))
          tail)
termination_by (fuel, middle.length + 1)

end

/-- A nested bag is not the bag of its element. Flattening is not this reading. -/
theorem nested_encode_ne :
    encodePattern (.collection .hashBag
        [.collection .hashBag [.apply "U" []] none] none) ≠
      encodePattern (.collection .hashBag [.apply "U" []] none) := by
  intro same
  rw [encode_bag_eq_iff] at same
  have child := List.singleton_perm_singleton.mp same
  rw [encodePattern_bag, encodePattern_u] at child
  have destEqual := congrArg QPF.Fix.dest child
  unfold bagTree atomTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

/-- A singleton bag is not the empty bag. The unit is not deleted. -/
theorem singleton_encode_ne_empty :
    encodePattern (.collection .hashBag [.apply "U" []] none) ≠
      encodePattern (.collection .hashBag [] none) := by
  intro same
  rw [encode_bag_eq_iff] at same
  have lengths := List.Perm.length_eq same
  simp only [List.length_map, List.length_cons, List.length_nil] at lengths
  cases lengths

/-- Every rule is a nullary atom or one hash bag of the base sort. -/
theorem bagLanguage_fragment : ∀ rule ∈ bagLanguage.terms, FragmentRule rule := by
  intro rule member
  simp only [bagLanguage, atomURule, atomWRule, hashBagRule, List.mem_cons, List.mem_nil_iff,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · intro parameter member
    simp at member
  · intro parameter member
    simp at member
  · intro parameter member
    simp only [List.mem_singleton] at member
    subst member
    simp [baseCollection?]

theorem bagLanguage_labels : (bagLanguage.terms.map (·.label)).Nodup := by
  decide

theorem bagLanguage_uniqueBare : UniqueBare bagLanguage := by
  intro rule₁ rule₂ kind element₁ element₂ mem₁ mem₂ _category bare₁ bare₂
  simp only [bagLanguage, atomURule, atomWRule, hashBagRule, List.mem_cons, List.mem_nil_iff,
    or_false] at mem₁ mem₂
  rcases mem₁ with rfl | rfl | rfl
  · simp [bareCollection?] at bare₁
  · simp [bareCollection?] at bare₁
  · rcases mem₂ with rfl | rfl | rfl
    · simp [bareCollection?] at bare₂
    · simp [bareCollection?] at bare₂
    · rfl

/-- The pattern congruence and the multiset reading are the same relation
on closed bag patterns. -/
noncomputable def encodeQuotientEquiv :
    Quotient (patternSetoid (language := bagLanguage) "A") ≃ Quotient encodeSetoid :=
  Quotient.congr (Equiv.refl ClosedBag) fun left right =>
    ⟨fun related => encode_patternCong related,
      fun related =>
        patternCong_of_encode_fuel (max (sizeOf left.1) (sizeOf right.1) + 1) left.1 right.1
          (Nat.lt_succ_of_le (Nat.le_max_left (sizeOf left.1) (sizeOf right.1)))
          (Nat.lt_succ_of_le (Nat.le_max_right (sizeOf left.1) (sizeOf right.1)))
          left.2.1 right.2.1 left.2.2 right.2.2 related⟩

/-- Indexed trees at the bag sort are the closed bag patterns. -/
noncomputable def bagTreeEquivObject :
    Tree bagLanguage ([], "A") ≃ ClosedBag :=
  closedIndexedEquiv bagLanguage_fragment bagLanguage_labels bagLanguage_uniqueBare "A"

/-- The indexed tree printed as one list representative of a bag tree. -/
noncomputable def indexedOfClosed (pattern : ClosedBag) : Tree bagLanguage ([], "A") :=
  bagTreeEquivObject.symm pattern

/-- The indexed equivalence prints a tree by `toPattern`. -/
theorem bagTreeEquivObject_val (tree : Tree bagLanguage ([], "A")) :
    (bagTreeEquivObject tree).1 = toPattern tree := by
  unfold bagTreeEquivObject closedIndexedEquiv
  rfl

/-- Reading the pattern of an indexed tree recovers that pattern. -/
theorem toPattern_indexedOfClosed (pattern : ClosedBag) :
    toPattern (indexedOfClosed pattern) = pattern.1 := by
  have back := congrArg Subtype.val (bagTreeEquivObject.apply_symm_apply pattern)
  unfold indexedOfClosed at back ⊢
  rw [bagTreeEquivObject_val] at back
  exact back

/-- A bag tree is an indexed tree modulo permutation of one bag parameter. -/
noncomputable def qpfTreeEquiv :
    QPF.Fix CollShape ≃ Quotient (treeSetoid (language := bagLanguage) "A") where
  toFun tree := Quotient.mk _ (indexedOfClosed (closedOfTree tree))
  invFun :=
    Quotient.lift (fun tree => encodePattern (toPattern tree))
      fun _ _ related => encode_patternCong (treeCong_pattern related)
  left_inv tree := by
    rw [Quotient.lift_mk]
    rw [toPattern_indexedOfClosed]
    exact encode_bagToPattern tree
  right_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro tree
    rw [Quotient.lift_mk]
    suffices related : TreeCong bagLanguage tree
        (indexedOfClosed (closedOfTree (encodePattern (toPattern tree)))) by
      exact (Quotient.sound related).symm
    refine pattern_treeCong bagLanguage_labels bagLanguage_uniqueBare tree
      (indexedOfClosed (closedOfTree (encodePattern (toPattern tree)))) ?_
    rw [toPattern_indexedOfClosed]
    refine patternCong_of_encode_fuel
      (max (sizeOf (toPattern tree))
        (sizeOf (bagToPattern (encodePattern (toPattern tree)))) + 1)
      (toPattern tree) (bagToPattern (encodePattern (toPattern tree)))
      (Nat.lt_succ_of_le (Nat.le_max_left _ _))
      (Nat.lt_succ_of_le (Nat.le_max_right _ _))
      ?_ ?_ ?_ ?_ ?_
    · simpa [Mettapedia.GSLT.Poly.BindingLanguage.typeContext] using toPattern_hasType tree
    · exact bagToPattern_hasType _
    · exact toPattern_isObject tree
    · exact bagToPattern_isObject _
    · exact (encode_bagToPattern _).symm

/-- The univariate bag carrier is the indexed quotient, transported along the
multiset reading. Permutation of children is the tree congruence. -/
noncomputable def bagClosedEquiv :
    QPF.Fix CollShape ≃ Quotient encodeSetoid :=
  qpfTreeEquiv.trans
    ((collectionQuotientEquiv bagLanguage_fragment bagLanguage_labels
      bagLanguage_uniqueBare "A").trans encodeQuotientEquiv)

/-- Closed bag patterns modulo permutation are the indexed trees modulo the
tree congruence, by the general quotient at this language and sort. -/
noncomputable def bagIndexedQuotient :
    Quotient (treeSetoid (language := bagLanguage) "A") ≃
      Quotient (patternSetoid (language := bagLanguage) "A") :=
  collectionQuotientEquiv bagLanguage_fragment bagLanguage_labels bagLanguage_uniqueBare "A"

end Mettapedia.GSLT.Poly.CollectionQuotient
