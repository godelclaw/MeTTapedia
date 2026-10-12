import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.Poly.CollectionLanguage
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.OfFn
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.QPF.Univariate.Basic

/-!
# Sets as the finite-set quotient of the list polynomial

A language whose constructors are nullary or one `hashSet` of their own sort
prints closed object patterns at that sort. Reading each set as the finite set
of the readings of its elements forgets order and repeated elements. That
reading is the initial algebra of the finite-set quotient of the list
polynomial. Nesting is not erased.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionSetQuotient

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.CollectionLanguage

open scoped Classical

/-- The set constructor: one hash set of the base sort. -/
def hashSetRule : GrammarRule :=
  { label := "Set", category := "A",
    params := [.simple "xs" (.collection .hashSet (.base "A"))],
    syntaxPattern := [] }

/-- Nullary atoms and one hash set of the same sort. -/
def setLanguage : LanguageDef :=
  { name := "Sets", types := [{ name := "A" }],
    terms := [atomURule, atomWRule, hashSetRule],
    equations := [], rewrites := [] }

/-- A closed object pattern of the set language, typed at the base sort. -/
abbrev ClosedSet : Type :=
  {pattern : Pattern //
    HasType setLanguage FreeTypeContext.empty [] pattern (.base "A") ∧
      isObjectPattern pattern = true}

/-- An atom, or a finite set of elements of the same sort. -/
inductive SetShape (α : Type) where
  | atom (name : Atom)
  | set (elements : Finset α)

noncomputable instance : Functor SetShape where
  map f
    | .atom name => .atom name
    | .set elements => .set (f <$> elements)

inductive SetHead where
  | atom (name : Atom)
  | length (n : Nat)

abbrev setChild : SetHead → Type
  | .atom _ => Empty
  | .length n => Fin n

abbrev setPolynomial : PFunctor.{0, 0} :=
  ⟨SetHead, setChild⟩

noncomputable def setAbs {α : Type} : setPolynomial α → SetShape α
  | ⟨.atom name, _⟩ => .atom name
  | ⟨.length _, positions⟩ => .set (List.ofFn positions).toFinset

noncomputable def setRepr {α : Type} : SetShape α → setPolynomial α
  | .atom name => ⟨.atom name, Empty.elim⟩
  | .set elements =>
      ⟨.length (Quotient.out elements.val).length,
        fun index => (Quotient.out elements.val).get index⟩

theorem set_abs_repr {α : Type} (shape : SetShape α) :
    setAbs (setRepr shape) = shape := by
  cases shape with
  | atom _ => rfl
  | set elements =>
      simp only [setAbs, setRepr]
      change SetShape.set (List.ofFn (List.get (Quotient.out elements.val))).toFinset =
        SetShape.set elements
      rw [List.ofFn_get, ← List.toFinset_coe]
      have representative :
          (↑(Quotient.out elements.val) : Multiset α) = elements.val :=
        Quotient.out_eq elements.val
      rw [representative]
      exact congrArg SetShape.set (Finset.val_toFinset elements)

theorem set_abs_map {α β : Type} (f : α → β) (shape : setPolynomial α) :
    setAbs (setPolynomial.map f shape) = f <$> setAbs shape := by
  cases shape with
  | mk head positions =>
      rw [PFunctor.map_eq]
      cases head with
      | atom _ => rfl
      | length _ =>
          simp only [setAbs]
          dsimp only [Functor.map]
          congr 1
          rw [Function.comp_def, List.ofFn_comp' positions f, ← List.toFinset_coe,
            ← Multiset.map_coe, Multiset.toFinset_map, List.toFinset_coe]

/-- The set algebra is the list polynomial, read as a finite set at each length. -/
noncomputable instance setQPF : QPF.{0, 0, 0} SetShape where
  P := setPolynomial
  abs := setAbs
  repr := setRepr
  abs_repr := set_abs_repr
  abs_map := set_abs_map

noncomputable def setAtom (name : Atom) : QPF.Fix SetShape :=
  QPF.Fix.mk (.atom name)

noncomputable def setTree (elements : Finset (QPF.Fix SetShape)) : QPF.Fix SetShape :=
  QPF.Fix.mk (.set elements)

theorem setTree_injective {left right : Finset (QPF.Fix SetShape)}
    (same : setTree left = setTree right) : left = right := by
  have destEqual := congrArg QPF.Fix.dest same
  unfold setTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  injection destEqual

/-- Fuelled reading of a pattern as a set tree.

A `hashSet` node becomes the finite set of the readings of its elements.
Any other shape falls through to the atom `U`. -/
noncomputable def encodeFuel : Nat → Pattern → QPF.Fix SetShape
  | 0, _ => setAtom .u
  | bound + 1, pattern =>
      if pattern = .apply "U" [] then setAtom .u
      else if pattern = .apply "W" [] then setAtom .w
      else
        match pattern with
        | .collection .hashSet elements none =>
            setTree (elements.map (encodeFuel bound)).toFinset
        | _ => setAtom .u

/-- The reading of a pattern at fuel one larger than its size. -/
noncomputable def encodePattern (pattern : Pattern) : QPF.Fix SetShape :=
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
          | bvar _ =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | fvar _ =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | lambda _ _ =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | multiLambda _ _ _ =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | subst _ _ =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | apply _ _ =>
              simp only [encodeFuel, if_neg isU, if_neg isW]
          | collection collectionType elements rest =>
              cases collectionType with
              | vec =>
                  simp only [encodeFuel, if_neg isU, if_neg isW]
              | hashBag =>
                  simp only [encodeFuel, if_neg isU, if_neg isW]
              | hashSet =>
                  cases rest with
                  | some _ =>
                      simp only [encodeFuel, if_neg isU, if_neg isW]
                  | none =>
                      simp only [encodeFuel, if_neg isU, if_neg isW]
                      suffices lists :
                          List.map (encodeFuel bound) elements =
                            List.map (encodeFuel fuel) elements by
                        exact congrArg setTree (congrArg List.toFinset lists)
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

/-- A set is the finite set of the readings of its elements. -/
theorem encodePattern_set (elements : List Pattern) :
    encodePattern (.collection .hashSet elements none) =
      setTree (elements.map encodePattern).toFinset := by
  have notU :
      Pattern.collection .hashSet elements none ≠ Pattern.apply "U" [] := by
    intro same
    cases same
  have notW :
      Pattern.collection .hashSet elements none ≠ Pattern.apply "W" [] := by
    intro same
    cases same
  change encodeFuel (sizeOf (Pattern.collection .hashSet elements none) + 1)
      (Pattern.collection .hashSet elements none) =
    setTree (elements.map encodePattern).toFinset
  simp only [encodeFuel, if_neg notU, if_neg notW]
  apply congrArg setTree
  apply congrArg List.toFinset
  refine map_encodeFuel _ elements ?_
  intro element member
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Pattern.collection.sizeOf_spec] at smaller ⊢
  omega

theorem encodePattern_u : encodePattern (.apply "U" []) = setAtom .u := by
  unfold encodePattern
  simp [encodeFuel]

theorem encodePattern_w : encodePattern (.apply "W" []) = setAtom .w := by
  unfold encodePattern
  simp [encodeFuel]

/-- A set reading determines its elements up to permutation and duplicates. -/
theorem encode_set_eq_iff (left right : List Pattern) :
    encodePattern (.collection .hashSet left none) =
        encodePattern (.collection .hashSet right none) ↔
      (left.map encodePattern).toFinset = (right.map encodePattern).toFinset := by
  rw [encodePattern_set, encodePattern_set]
  constructor
  · intro same
    exact setTree_injective same
  · intro sets
    exact congrArg setTree sets

/-- Swapping the elements of a set does not change its reading. -/
theorem set_swap_same :
    encodePattern (.collection .hashSet [.apply "U" [], .apply "W" []] none) =
      encodePattern (.collection .hashSet [.apply "W" [], .apply "U" []] none) := by
  rw [encode_set_eq_iff]
  simp only [List.map_cons, List.map_nil, encodePattern_u, encodePattern_w]
  apply List.toFinset_eq_of_perm
  exact List.Perm.swap (setAtom .w) (setAtom .u) []

/-- A repeated element and one copy present the same set. -/
theorem set_duplicate_same :
    encodePattern (.collection .hashSet [.apply "U" [], .apply "U" []] none) =
      encodePattern (.collection .hashSet [.apply "U" []] none) := by
  rw [encode_set_eq_iff]
  simp only [List.map_cons, List.map_nil, encodePattern_u]
  apply List.toFinset.ext
  intro value
  simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self]

/-- Every element of a set satisfies a predicate that lifts over the set. -/
theorem liftp_set {α : Type} {p : α → Prop} {elements : Finset α}
    (lifted : Functor.Liftp p (SetShape.set elements)) {element : α}
    (member : element ∈ elements) : p element := by
  rcases lifted with ⟨shape, shapeEqual⟩
  cases shape with
  | atom _ =>
      dsimp only [Functor.map] at shapeEqual
      cases shapeEqual
  | set children =>
      dsimp only [Functor.map] at shapeEqual
      injection shapeEqual with elementsEqual
      rw [← elementsEqual] at member
      obtain ⟨child, _, printed⟩ := Finset.mem_image.mp member
      rw [← printed]
      exact child.property

/-- One node of the set algebra, once its elements are already patterns. -/
noncomputable def nodePattern : SetShape Pattern → Pattern
  | .atom .u => .apply "U" []
  | .atom .w => .apply "W" []
  | .set elements => .collection .hashSet elements.toList none

/-- A set tree, printed as a pattern by choosing one list representative. -/
noncomputable def setToPattern : QPF.Fix SetShape → Pattern :=
  QPF.Fix.rec nodePattern

theorem setToPattern_mk (shape : SetShape (QPF.Fix SetShape)) :
    setToPattern (QPF.Fix.mk shape) = nodePattern (setToPattern <$> shape) := by
  rw [setToPattern, QPF.Fix.rec_eq]

theorem elements_of_mem {elements : List Pattern}
    (each : ∀ element ∈ elements,
      HasType setLanguage FreeTypeContext.empty [] element (.base "A")) :
    ElementsHaveType setLanguage FreeTypeContext.empty [] elements (.base "A") := by
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

theorem setToPattern_hasType (tree : QPF.Fix SetShape) :
    HasType setLanguage FreeTypeContext.empty [] (setToPattern tree) (.base "A") := by
  refine QPF.Fix.ind
    (fun tree => HasType setLanguage FreeTypeContext.empty [] (setToPattern tree) (.base "A"))
    ?_ tree
  intro shape lifted
  rw [setToPattern_mk]
  cases shape with
  | atom name =>
      cases name with
      | u =>
          dsimp only [nodePattern, Functor.map]
          exact HasType.constructor (rule := atomURule) (by simp [setLanguage])
            (not_bare_atom atomURule rfl) ArgumentsHaveTypes.nil
      | w =>
          dsimp only [nodePattern, Functor.map]
          exact HasType.constructor (rule := atomWRule) (by simp [setLanguage])
            (not_bare_atom atomWRule rfl) ArgumentsHaveTypes.nil
  | set elements =>
      dsimp only [nodePattern, Functor.map]
      refine HasType.collectionConstructor (rule := hashSetRule) (by simp [setLanguage]) rfl ?_
      refine elements_of_mem ?_
      intro element member
      rw [Finset.mem_toList] at member
      obtain ⟨child, childMember, printed⟩ := Finset.mem_image.mp
        (by simpa [Finset.fmap_def] using member)
      have typedChild := liftp_set lifted childMember
      rw [← printed]
      exact typedChild

theorem setToPattern_isObject (tree : QPF.Fix SetShape) :
    isObjectPattern (setToPattern tree) = true := by
  refine QPF.Fix.ind (fun tree => isObjectPattern (setToPattern tree) = true) ?_ tree
  intro shape lifted
  rw [setToPattern_mk]
  cases shape with
  | atom name =>
      cases name <;> dsimp [nodePattern, Functor.map, isObjectPattern, isObjectPatternList]
  | set elements =>
      dsimp only [nodePattern, Functor.map, isObjectPattern, Option.isNone]
      refine objects_of_mem ?_
      intro element member
      rw [Finset.mem_toList] at member
      obtain ⟨child, childMember, printed⟩ := Finset.mem_image.mp
        (by simpa [Finset.fmap_def] using member)
      have objectChild := liftp_set lifted childMember
      rw [← printed]
      exact objectChild

/-- Printing a tree and reading the pattern returns the tree. -/
theorem encode_setToPattern (tree : QPF.Fix SetShape) :
    encodePattern (setToPattern tree) = tree := by
  refine QPF.Fix.ind (fun tree => encodePattern (setToPattern tree) = tree) ?_ tree
  intro shape lifted
  rw [setToPattern_mk]
  cases shape with
  | atom name =>
      cases name with
      | u =>
          dsimp only [nodePattern, Functor.map]
          rw [encodePattern_u, setAtom]
      | w =>
          dsimp only [nodePattern, Functor.map]
          rw [encodePattern_w, setAtom]
  | set elements =>
      dsimp only [nodePattern, Functor.map, Finset.fmap_def]
      rw [encodePattern_set]
      apply congrArg setTree
      ext child
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList, Finset.mem_image]
      constructor
      · rintro ⟨pattern, ⟨tree, member, patternAt⟩, printedChild⟩
        rw [← printedChild, ← patternAt, liftp_set lifted member]
        exact member
      · intro member
        exact ⟨setToPattern child, ⟨child, member, rfl⟩, liftp_set lifted member⟩

/-- Closed object patterns of the set language, modulo permutation and duplicates. -/
def encodeSetoid : Setoid ClosedSet where
  r pattern other := encodePattern pattern.1 = encodePattern other.1
  iseqv := ⟨fun _ => rfl, fun equal => equal.symm, fun left right => left.trans right⟩

/-- The printed pattern of a set tree, as a closed object pattern. -/
noncomputable def closedOfTree (tree : QPF.Fix SetShape) : ClosedSet :=
  ⟨setToPattern tree, setToPattern_hasType tree, setToPattern_isObject tree⟩

/-- Set trees are the closed object patterns modulo permutation and duplicates. -/
noncomputable def setClosedEquiv :
    QPF.Fix SetShape ≃ Quotient encodeSetoid where
  toFun tree := Quotient.mk _ (closedOfTree tree)
  invFun := Quotient.lift (fun pattern => encodePattern pattern.1) fun _ _ equal => equal
  left_inv tree := by
    change encodePattern (setToPattern tree) = tree
    exact encode_setToPattern tree
  right_inv pattern := by
    refine Quotient.inductionOn pattern ?_
    intro closed
    apply Quotient.sound
    exact encode_setToPattern (encodePattern closed.1)

/-- A nested set is not the set of its element. Flattening is not this reading. -/
theorem nested_set_ne :
    encodePattern (.collection .hashSet
        [.collection .hashSet [.apply "U" []] none] none) ≠
      encodePattern (.collection .hashSet [.apply "U" []] none) := by
  intro same
  rw [encode_set_eq_iff] at same
  simp only [List.map_cons, List.map_nil, encodePattern_u, encodePattern_set] at same
  have member : setTree ([setAtom .u].toFinset) ∈
      [setTree ([setAtom .u].toFinset)].toFinset :=
    List.mem_toFinset.mpr List.mem_cons_self
  rw [same] at member
  simp only [List.mem_toFinset, List.mem_singleton] at member
  have destEqual := congrArg QPF.Fix.dest member
  unfold setTree setAtom at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

/-- A singleton set is not the empty set. The unit is not deleted. -/
theorem singleton_set_ne_empty :
    encodePattern (.collection .hashSet [.apply "U" []] none) ≠
      encodePattern (.collection .hashSet [] none) := by
  intro same
  rw [encode_set_eq_iff] at same
  simp only [List.map_cons, List.map_nil, encodePattern_u] at same
  have member : setAtom .u ∈ [setAtom .u].toFinset := by simp
  rw [same] at member
  simp at member

end Mettapedia.GSLT.Poly.CollectionSetQuotient
