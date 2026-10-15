import Mettapedia.GSLT.LanguageDef.WellSorted
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

/-- Bag trees are the closed object patterns modulo permutation of bag elements. -/
noncomputable def bagClosedEquiv :
    QPF.Fix CollShape ≃ Quotient encodeSetoid where
  toFun tree := Quotient.mk _ (closedOfTree tree)
  invFun := Quotient.lift (fun pattern => encodePattern pattern.1) fun _ _ equal => equal
  left_inv tree := by
    change encodePattern (bagToPattern tree) = tree
    exact encode_bagToPattern tree
  right_inv pattern := by
    refine Quotient.inductionOn pattern ?_
    intro closed
    apply Quotient.sound
    exact encode_bagToPattern (encodePattern closed.1)

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

end Mettapedia.GSLT.Poly.CollectionQuotient
