import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.Poly.CollectionIndexedQuotient
import Mettapedia.GSLT.Poly.CollectionLanguage
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Nodup
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
open Mettapedia.GSLT.Poly.CollectionIndexed
open Mettapedia.GSLT.Poly.CollectionIndexedEquiv
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

/-- Every rule is a nullary atom or one hash set of the base sort. -/
theorem setLanguage_fragment : ∀ rule ∈ setLanguage.terms, FragmentRule rule := by
  intro rule member
  simp only [setLanguage, atomURule, atomWRule, hashSetRule, List.mem_cons, List.mem_nil_iff,
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

theorem setLanguage_labels : (setLanguage.terms.map (·.label)).Nodup := by
  decide

theorem setLanguage_uniqueBare : UniqueBare setLanguage := by
  intro rule₁ rule₂ kind element₁ element₂ mem₁ mem₂ _category bare₁ bare₂
  simp only [setLanguage, atomURule, atomWRule, hashSetRule, List.mem_cons, List.mem_nil_iff,
    or_false] at mem₁ mem₂
  rcases mem₁ with rfl | rfl | rfl
  · simp [bareCollection?] at bare₁
  · simp [bareCollection?] at bare₁
  · rcases mem₂ with rfl | rfl | rfl
    · simp [bareCollection?] at bare₂
    · simp [bareCollection?] at bare₂
    · rfl

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

/-- A closed set pattern is an atom `U`, an atom `W`, or a hash set of closed set patterns. -/
theorem set_closed_shape (pattern : Pattern)
    (typed : HasType setLanguage FreeTypeContext.empty [] pattern (.base "A"))
    (object : isObjectPattern pattern = true) :
    pattern = .apply "U" [] ∨ pattern = .apply "W" [] ∨
      ∃ elements : List Pattern,
        pattern = .collection .hashSet elements none ∧
          ∀ element ∈ elements,
            HasType setLanguage FreeTypeContext.empty [] element (.base "A") ∧
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
      simp only [setLanguage, atomURule, atomWRule, hashSetRule, List.mem_cons,
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
      · exact (notBare ⟨"xs", .hashSet, .base "A", rfl⟩).elim
  | collection kind elements rest =>
      cases rest with
      | some _ => simp [isObjectPattern] at object
      | none =>
          rcases collection_rule_of_hasType typed with
            ⟨_elementType, typeEq, _elementsTyped⟩ |
            ⟨rule, membership, _parameterName, _elementType, paramsEq, _typeEq,
              elementsTyped⟩
          · cases typeEq
          · simp only [setLanguage, atomURule, atomWRule, hashSetRule, List.mem_cons,
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
  unfold setAtom at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

theorem encode_u_ne_set (elements : List Pattern) :
    encodePattern (.apply "U" []) ≠
      encodePattern (.collection .hashSet elements none) := by
  rw [encodePattern_u, encodePattern_set]
  intro same
  have destEqual := congrArg QPF.Fix.dest same
  unfold setAtom setTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

theorem encode_w_ne_set (elements : List Pattern) :
    encodePattern (.apply "W" []) ≠
      encodePattern (.collection .hashSet elements none) := by
  rw [encodePattern_w, encodePattern_set]
  intro same
  have destEqual := congrArg QPF.Fix.dest same
  unfold setAtom setTree at destEqual
  rw [QPF.Fix.dest_mk, QPF.Fix.dest_mk] at destEqual
  cases destEqual

theorem set_child_smaller {elements : List Pattern} {element : Pattern}
    (member : element ∈ elements) :
    sizeOf element < sizeOf (Pattern.collection .hashSet elements none) := by
  have listSmall := List.sizeOf_lt_of_mem member
  simp only [Pattern.collection.sizeOf_spec]
  omega

/-- Permutation and deletion of one adjacent duplicate, on the element list of a hash set. -/
inductive SetSteps : List Pattern → List Pattern → Prop where
  | refl (elements : List Pattern) : SetSteps elements elements
  | symm {left right : List Pattern} : SetSteps left right → SetSteps right left
  | trans {left mid right : List Pattern} :
      SetSteps left mid → SetSteps mid right → SetSteps left right
  | perm {left right : List Pattern} : left.Perm right → SetSteps left right
  | dup {before : List Pattern} {element : Pattern} {after : List Pattern} :
      SetSteps (before ++ element :: element :: after) (before ++ element :: after)
  | replace {before : List Pattern} {left right : Pattern} {after : List Pattern} :
      PatternCong left right →
        SetSteps (before ++ left :: after) (before ++ right :: after)

theorem setSteps_cons (head : Pattern) {left right : List Pattern}
    (steps : SetSteps left right) : SetSteps (head :: left) (head :: right) := by
  induction steps with
  | refl _ => exact SetSteps.refl _
  | symm _ inductionHypothesis => exact SetSteps.symm inductionHypothesis
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact SetSteps.trans inductionHypothesis inductionHypothesis'
  | perm related => exact SetSteps.perm (related.cons head)
  | @dup before _ _ => exact SetSteps.dup (before := head :: before)
  | @replace before _ _ _ related =>
      exact SetSteps.replace (before := head :: before) related

theorem patternCong_setSteps {left right : List Pattern} (steps : SetSteps left right) :
    PatternCong (.collection .hashSet left none) (.collection .hashSet right none) := by
  induction steps with
  | refl _ => exact PatternCong.refl _
  | symm _ inductionHypothesis => exact PatternCong.symm inductionHypothesis
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact PatternCong.trans inductionHypothesis inductionHypothesis'
  | perm related => exact PatternCong.setPerm related
  | dup => exact PatternCong.setDup
  | replace related =>
      exact PatternCong.collectionAt (kind := .hashSet) (rest := none) related

/-- Drop children whose reading is already present. The survivors are injective on readings. -/
theorem patternCong_merge :
    ∀ (elements : List Pattern),
      (∀ left right, left ∈ elements → right ∈ elements →
        encodePattern left = encodePattern right → PatternCong left right) →
      ∃ reduced : List Pattern,
        SetSteps elements reduced ∧
        (∀ element ∈ reduced, element ∈ elements) ∧
        (reduced.map encodePattern).Nodup ∧
        (reduced.map encodePattern).toFinset = (elements.map encodePattern).toFinset := by
  intro elements
  induction elements with
  | nil =>
      intro _
      refine ⟨[], SetSteps.refl [], ?_, ?_, ?_⟩
      · intro element member
        exact absurd member (List.not_mem_nil (a := element))
      · exact List.nodup_nil
      · rfl
  | cons head tail inductionHypothesis =>
      intro mergePair
      obtain ⟨reduced, steps, subset, nodup, fins⟩ :=
        inductionHypothesis fun left right memLeft memRight encoded =>
          mergePair left right (List.mem_cons_of_mem head memLeft)
            (List.mem_cons_of_mem head memRight) encoded
      by_cases hit : encodePattern head ∈ reduced.map encodePattern
      · obtain ⟨other, otherMem, sameEncode⟩ := List.mem_map.mp hit
        have otherIn : other ∈ tail := subset other otherMem
        obtain ⟨before, after, rfl⟩ := List.append_of_mem otherIn
        have headCong : PatternCong head other :=
          mergePair head other List.mem_cons_self
            (List.mem_cons_of_mem head otherIn) sameEncode.symm
        have grouped :
            (other :: (before ++ other :: after)).Perm
              (before ++ other :: other :: after) :=
          (List.perm_middle (a := other) (l₁ := before) (l₂ := other :: after)).symm
        refine ⟨reduced, ?_, ?_, nodup, ?_⟩
        · exact SetSteps.trans
            (SetSteps.replace (before := []) (after := before ++ other :: after) headCong)
            (SetSteps.trans (SetSteps.perm grouped)
              (SetSteps.trans
                (SetSteps.dup (before := before) (element := other) (after := after))
                steps))
        · intro element member
          exact List.mem_cons_of_mem head (subset element member)
        · rw [List.map_cons, List.toFinset_cons]
          have already :
              encodePattern head ∈ ((before ++ other :: after).map encodePattern).toFinset := by
            rw [← fins]
            exact List.mem_toFinset.mpr hit
          rw [Finset.insert_eq_of_mem already, fins]
      · refine ⟨head :: reduced, setSteps_cons head steps, ?_, ?_, ?_⟩
        · intro element member
          cases member with
          | head => exact List.mem_cons_self
          | tail _ member => exact List.mem_cons_of_mem head (subset element member)
        · rw [List.map_cons, List.nodup_cons]
          exact ⟨hit, nodup⟩
        · rw [List.map_cons, List.map_cons, List.toFinset_cons, List.toFinset_cons, fins]

theorem nodup_toFinset_perm {α : Type} [DecidableEq α] {left right : List α}
    (nodupLeft : left.Nodup) (nodupRight : right.Nodup)
    (same : left.toFinset = right.toFinset) : left.Perm right := by
  rw [List.perm_iff_count]
  intro item
  by_cases member : item ∈ left
  · have memberRight : item ∈ right := by
      exact List.mem_toFinset.mp (same ▸ List.mem_toFinset.mpr member)
    rw [List.count_eq_one_of_mem nodupLeft member,
      List.count_eq_one_of_mem nodupRight memberRight]
  · have notRight : item ∉ right := by
      intro memberRight
      exact member (List.mem_toFinset.mp (same.symm ▸ List.mem_toFinset.mpr memberRight))
    rw [List.count_eq_zero_of_not_mem member, List.count_eq_zero_of_not_mem notRight]

theorem encodeFuel_succ_fallback (pattern : Pattern) (bound : Nat)
    (notU : pattern ≠ .apply "U" [])
    (notW : pattern ≠ .apply "W" [])
    (notSet : ∀ elements, pattern ≠ .collection .hashSet elements none) :
    encodeFuel (bound + 1) pattern = setAtom .u := by
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
      | hashBag => rfl
      | hashSet =>
          cases rest with
          | some _ => rfl
          | none => exact (notSet elements rfl).elim

theorem encodePattern_atom (pattern : Pattern)
    (notU : pattern ≠ .apply "U" [])
    (notW : pattern ≠ .apply "W" [])
    (notSet : ∀ elements, pattern ≠ .collection .hashSet elements none) :
    encodePattern pattern = setAtom .u := by
  unfold encodePattern
  exact encodeFuel_succ_fallback pattern (sizeOf pattern) notU notW notSet

theorem apply_nonempty_not_nullary (label atom : String) (before : List Pattern)
    (argument : Pattern) (after : List Pattern) :
    Pattern.apply label (before ++ argument :: after) ≠ Pattern.apply atom [] := by
  intro same
  injection same with _ args
  have lengths := congrArg List.length args
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  omega

theorem toFinset_cons_dup {α : Type} [DecidableEq α]
    (before : List α) (element : α) (after : List α) :
    (before ++ element :: element :: after).toFinset =
      (before ++ element :: after).toFinset := by
  apply Finset.ext
  intro item
  simp only [List.mem_toFinset, List.mem_append, List.mem_cons]
  constructor
  · intro mem
    rcases mem with mem | mem | mem | mem
    · exact Or.inl mem
    · exact Or.inr (Or.inl mem)
    · exact Or.inr (Or.inl mem)
    · exact Or.inr (Or.inr mem)
  · intro mem
    rcases mem with mem | mem | mem
    · exact Or.inl mem
    · exact Or.inr (Or.inl mem)
    · exact Or.inr (Or.inr (Or.inr mem))

theorem encode_patternCong {left right : Pattern} (related : PatternCong left right) :
    encodePattern left = encodePattern right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | @bagPerm elements swapped _perm =>
      exact (encodePattern_atom (.collection .hashBag elements none)
        (by intro same; cases same) (by intro same; cases same)
        (by intro _ same; cases same)).trans
        (encodePattern_atom (.collection .hashBag swapped none)
          (by intro same; cases same) (by intro same; cases same)
          (by intro _ same; cases same)).symm
  | @setPerm elements swapped perm =>
      rw [encodePattern_set, encodePattern_set]
      exact congrArg setTree
        (List.toFinset_eq_of_perm (elements.map encodePattern) (swapped.map encodePattern)
          (perm.map encodePattern))
  | @setDup before element after =>
      rw [encodePattern_set, encodePattern_set]
      apply congrArg setTree
      simp only [List.map_append, List.map_cons]
      exact toFinset_cons_dup (before.map encodePattern) (encodePattern element)
        (after.map encodePattern)
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
      _inductionHypothesis encodeEqual =>
      cases kind with
      | hashSet =>
          cases rest with
          | none =>
              rw [encodePattern_set, encodePattern_set]
              apply congrArg setTree
              simp only [List.map_append, List.map_cons, encodeEqual]
          | some name =>
              exact (encodePattern_atom
                  (.collection .hashSet (before ++ leftPattern :: after) (some name))
                  (by intro same; cases same) (by intro same; cases same)
                  (by intro _ same; cases same)).trans
                (encodePattern_atom
                  (.collection .hashSet (before ++ rightPattern :: after) (some name))
                  (by intro same; cases same) (by intro same; cases same)
                  (by intro _ same; cases same)).symm
      | hashBag =>
          exact (encodePattern_atom
              (.collection .hashBag (before ++ leftPattern :: after) rest)
              (by intro same; cases same) (by intro same; cases same)
              (by intro _ same; cases same)).trans
            (encodePattern_atom
              (.collection .hashBag (before ++ rightPattern :: after) rest)
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

theorem patternCong_set_forall2_aux (before : List Pattern) {left right : List Pattern} :
    List.Forall₂ PatternCong left right →
      PatternCong (.collection .hashSet (before ++ left) none)
        (.collection .hashSet (before ++ right) none)
  | .nil => by
      exact PatternCong.refl _
  | .cons (b := rightHead) (l₁ := leftTail) headRelated tailRelated => by
      apply PatternCong.trans
      · exact PatternCong.collectionAt (kind := .hashSet) (before := before)
          (after := leftTail) (rest := none) headRelated
      · have step :=
          patternCong_set_forall2_aux (before ++ [rightHead]) tailRelated
        simpa [List.append_assoc, List.singleton_append] using step

theorem patternCong_set_forall2 {left right : List Pattern}
    (related : List.Forall₂ PatternCong left right) :
    PatternCong (.collection .hashSet left none) (.collection .hashSet right none) :=
  patternCong_set_forall2_aux [] related

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

theorem patternCong_of_encode_fuel :
    (fuel : Nat) → (left right : Pattern) →
    sizeOf left < fuel → sizeOf right < fuel →
    HasType setLanguage FreeTypeContext.empty [] left (.base "A") →
    HasType setLanguage FreeTypeContext.empty [] right (.base "A") →
    isObjectPattern left = true → isObjectPattern right = true →
    encodePattern left = encodePattern right →
    PatternCong left right
  | 0, _, _, small, _, _, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, left, right, leftSmall, rightSmall, typedLeft, typedRight,
      objectLeft, objectRight, same => by
      rcases set_closed_shape left typedLeft objectLeft with rfl | rfl | ⟨elements, rfl, eachLeft⟩
      · rcases set_closed_shape right typedRight objectRight with
          rfl | rfl | ⟨elementsRight, rfl, _⟩
        · exact PatternCong.refl _
        · exact absurd same encode_u_ne_w
        · exact absurd same (encode_u_ne_set elementsRight)
      · rcases set_closed_shape right typedRight objectRight with
          rfl | rfl | ⟨elementsRight, rfl, _⟩
        · exact absurd same encode_u_ne_w.symm
        · exact PatternCong.refl _
        · exact absurd same (encode_w_ne_set elementsRight)
      · rcases set_closed_shape right typedRight objectRight with
          rfl | rfl | ⟨elementsRight, rfl, eachRight⟩
        · exact absurd same (encode_u_ne_set elements).symm
        · exact absurd same (encode_w_ne_set elements).symm
        · rw [encode_set_eq_iff] at same
          obtain ⟨reducedLeft, stepsLeft, subLeft, nodupLeft, finLeft⟩ :=
            patternCong_merge elements fun childLeft childRight memLeft memRight encoded =>
              patternCong_of_encode_fuel fuel childLeft childRight
                (Nat.lt_of_lt_of_le (set_child_smaller memLeft) (Nat.le_of_lt_succ leftSmall))
                (Nat.lt_of_lt_of_le (set_child_smaller memRight) (Nat.le_of_lt_succ leftSmall))
                (eachLeft childLeft memLeft).1 (eachLeft childRight memRight).1
                (eachLeft childLeft memLeft).2 (eachLeft childRight memRight).2 encoded
          obtain ⟨reducedRight, stepsRight, subRight, nodupRight, finRight⟩ :=
            patternCong_merge elementsRight fun childLeft childRight memLeft memRight encoded =>
              patternCong_of_encode_fuel fuel childLeft childRight
                (Nat.lt_of_lt_of_le (set_child_smaller memLeft) (Nat.le_of_lt_succ rightSmall))
                (Nat.lt_of_lt_of_le (set_child_smaller memRight) (Nat.le_of_lt_succ rightSmall))
                (eachRight childLeft memLeft).1 (eachRight childRight memRight).1
                (eachRight childLeft memLeft).2 (eachRight childRight memRight).2 encoded
          have listsPerm :
              (reducedLeft.map encodePattern).Perm (reducedRight.map encodePattern) :=
            nodup_toFinset_perm nodupLeft nodupRight (finLeft.trans (same.trans finRight.symm))
          obtain ⟨middle, perm, zipped⟩ := exists_forall2_of_map_perm encodePattern listsPerm
          exact PatternCong.trans (patternCong_setSteps stepsLeft)
            (PatternCong.trans (PatternCong.setPerm perm)
              (PatternCong.trans
                (patternCong_set_forall2
                  (forall2_patternCong_fuel fuel
                    (fun element member =>
                      subLeft element ((perm.mem_iff).mpr member))
                    eachLeft
                    (fun element member => eachRight element (subRight element member))
                    (fun element member => by
                      have source := subLeft element ((perm.mem_iff).mpr member)
                      exact Nat.lt_of_lt_of_le (set_child_smaller source)
                        (Nat.le_of_lt_succ leftSmall))
                    (fun element member => by
                      have source := subRight element member
                      exact Nat.lt_of_lt_of_le (set_child_smaller source)
                        (Nat.le_of_lt_succ rightSmall))
                    zipped))
                (PatternCong.symm (patternCong_setSteps stepsRight))))
termination_by fuel _ _ _ _ _ _ _ _ _ => (fuel, 0)

theorem forall2_patternCong_fuel (fuel : Nat) {middle right source : List Pattern}
    (inSource : ∀ element ∈ middle, element ∈ source)
    (eachSource : ∀ element ∈ source,
      HasType setLanguage FreeTypeContext.empty [] element (.base "A") ∧
        isObjectPattern element = true)
    (eachRight : ∀ element ∈ right,
      HasType setLanguage FreeTypeContext.empty [] element (.base "A") ∧
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

/-- The pattern congruence and the finite-set reading are the same relation
on closed set patterns. -/
noncomputable def encodeQuotientEquiv :
    Quotient (patternSetoid (language := setLanguage) "A") ≃ Quotient encodeSetoid :=
  Quotient.congr (Equiv.refl ClosedSet) fun left right =>
    ⟨fun related => encode_patternCong related,
      fun related =>
        patternCong_of_encode_fuel (max (sizeOf left.1) (sizeOf right.1) + 1) left.1 right.1
          (Nat.lt_succ_of_le (Nat.le_max_left (sizeOf left.1) (sizeOf right.1)))
          (Nat.lt_succ_of_le (Nat.le_max_right (sizeOf left.1) (sizeOf right.1)))
          left.2.1 right.2.1 left.2.2 right.2.2 related⟩

/-- Indexed trees at the set sort are the closed set patterns. -/
noncomputable def setTreeEquivObject :
    Tree setLanguage ([], "A") ≃ ClosedSet :=
  closedIndexedEquiv setLanguage_fragment setLanguage_labels setLanguage_uniqueBare "A"

/-- The indexed tree printed as one list representative of a set tree. -/
noncomputable def indexedOfClosed (pattern : ClosedSet) : Tree setLanguage ([], "A") :=
  setTreeEquivObject.symm pattern

/-- The indexed equivalence prints a tree by `toPattern`. -/
theorem setTreeEquivObject_val (tree : Tree setLanguage ([], "A")) :
    (setTreeEquivObject tree).1 = toPattern tree := by
  unfold setTreeEquivObject closedIndexedEquiv
  rfl

/-- Reading the pattern of an indexed tree recovers that pattern. -/
theorem toPattern_indexedOfClosed (pattern : ClosedSet) :
    toPattern (indexedOfClosed pattern) = pattern.1 := by
  have back := congrArg Subtype.val (setTreeEquivObject.apply_symm_apply pattern)
  unfold indexedOfClosed at back ⊢
  rw [setTreeEquivObject_val] at back
  exact back

/-- A set tree is an indexed tree modulo permutation and deletion of a duplicate. -/
noncomputable def qpfTreeEquiv :
    QPF.Fix SetShape ≃ Quotient (treeSetoid (language := setLanguage) "A") where
  toFun tree := Quotient.mk _ (indexedOfClosed (closedOfTree tree))
  invFun :=
    Quotient.lift (fun tree => encodePattern (toPattern tree))
      fun _ _ related => encode_patternCong (treeCong_pattern related)
  left_inv tree := by
    rw [Quotient.lift_mk]
    rw [toPattern_indexedOfClosed]
    exact encode_setToPattern tree
  right_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro tree
    rw [Quotient.lift_mk]
    suffices related : TreeCong setLanguage tree
        (indexedOfClosed (closedOfTree (encodePattern (toPattern tree)))) by
      exact (Quotient.sound related).symm
    refine pattern_treeCong setLanguage_labels setLanguage_uniqueBare tree
      (indexedOfClosed (closedOfTree (encodePattern (toPattern tree)))) ?_
    rw [toPattern_indexedOfClosed]
    refine patternCong_of_encode_fuel
      (max (sizeOf (toPattern tree))
        (sizeOf (setToPattern (encodePattern (toPattern tree)))) + 1)
      (toPattern tree) (setToPattern (encodePattern (toPattern tree)))
      (Nat.lt_succ_of_le (Nat.le_max_left _ _))
      (Nat.lt_succ_of_le (Nat.le_max_right _ _))
      ?_ ?_ ?_ ?_ ?_
    · simpa [Mettapedia.GSLT.Poly.BindingLanguage.typeContext] using toPattern_hasType tree
    · exact setToPattern_hasType _
    · exact toPattern_isObject tree
    · exact setToPattern_isObject _
    · exact (encode_setToPattern _).symm

/-- The univariate set carrier is the indexed quotient, transported along the
finite-set reading. Permutation and deletion of a duplicate are the tree congruence. -/
noncomputable def setClosedEquiv :
    QPF.Fix SetShape ≃ Quotient encodeSetoid :=
  qpfTreeEquiv.trans
    ((collectionQuotientEquiv setLanguage_fragment setLanguage_labels
      setLanguage_uniqueBare "A").trans encodeQuotientEquiv)

/-- Closed set patterns modulo permutation and deletion of a duplicate are the
indexed trees modulo the tree congruence, by the general quotient at this
language and sort. -/
noncomputable def setIndexedQuotient :
    Quotient (treeSetoid (language := setLanguage) "A") ≃
      Quotient (patternSetoid (language := setLanguage) "A") :=
  collectionQuotientEquiv setLanguage_fragment setLanguage_labels setLanguage_uniqueBare "A"

end Mettapedia.GSLT.Poly.CollectionSetQuotient
