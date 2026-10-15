import Mettapedia.GSLT.Poly.CollectionIndexedCong

/-!
# Pattern congruence on one collection

A hash bag stays a hash bag. Its elements are related by permutation and by
the pattern congruence at one position. A hash set has those steps and also
deletes one of two equal elements. A vector is not given the permutation step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedEquiv

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Poly.CollectionIndexed

/-- Element relation of one hash bag: permutation, and the pattern congruence
at a single position. -/
inductive BagElementRel : List Pattern → List Pattern → Prop where
  | refl (elements : List Pattern) : BagElementRel elements elements
  | symm {left right : List Pattern} : BagElementRel left right → BagElementRel right left
  | trans {left mid right : List Pattern} :
      BagElementRel left mid → BagElementRel mid right → BagElementRel left right
  | perm {left right : List Pattern} : List.Perm left right → BagElementRel left right
  | atPoint {before : List Pattern} {left right : Pattern} {after : List Pattern} :
      PatternCong left right →
        BagElementRel (before ++ left :: after) (before ++ right :: after)

/-- Element relation of one hash set. A duplicate child may be deleted. -/
inductive SetElementRel : List Pattern → List Pattern → Prop where
  | refl (elements : List Pattern) : SetElementRel elements elements
  | symm {left right : List Pattern} : SetElementRel left right → SetElementRel right left
  | trans {left mid right : List Pattern} :
      SetElementRel left mid → SetElementRel mid right → SetElementRel left right
  | perm {left right : List Pattern} : List.Perm left right → SetElementRel left right
  | duplicate {before : List Pattern} {element : Pattern} {after : List Pattern} :
      SetElementRel (before ++ element :: element :: after) (before ++ element :: after)
  | atPoint {before : List Pattern} {left right : Pattern} {after : List Pattern} :
      PatternCong left right →
        SetElementRel (before ++ left :: after) (before ++ right :: after)

theorem collection_eq_hashBag {kind : CollType} {elements bagElements : List Pattern}
    {rest : Option String}
    (equal : Pattern.collection kind elements rest =
      Pattern.collection .hashBag bagElements none) :
    kind = .hashBag ∧ rest = none ∧ elements = bagElements := by
  simp only [Pattern.collection.injEq] at equal
  obtain ⟨kindEq, listsEq, restEq⟩ := equal
  exact ⟨kindEq, restEq, listsEq⟩

theorem collection_eq_hashSet {kind : CollType} {elements setElements : List Pattern}
    {rest : Option String}
    (equal : Pattern.collection kind elements rest =
      Pattern.collection .hashSet setElements none) :
    kind = .hashSet ∧ rest = none ∧ elements = setElements := by
  simp only [Pattern.collection.injEq] at equal
  obtain ⟨kindEq, listsEq, restEq⟩ := equal
  exact ⟨kindEq, restEq, listsEq⟩

theorem patternCong_bag_elements {left right : Pattern} (related : PatternCong left right)
    (shaped : (∃ elements, left = .collection .hashBag elements none) ∨
      (∃ elements, right = .collection .hashBag elements none)) :
    ∃ leftElements rightElements,
      left = .collection .hashBag leftElements none ∧
        right = .collection .hashBag rightElements none ∧
          BagElementRel leftElements rightElements := by
  induction related with
  | refl pattern =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨elements, equal⟩ := existsLeft
          exact ⟨elements, elements, equal, equal, BagElementRel.refl elements⟩
      | inr existsRight =>
          obtain ⟨elements, equal⟩ := existsRight
          exact ⟨elements, elements, equal, equal, BagElementRel.refl elements⟩
  | symm _ inductionHypothesis =>
      obtain ⟨rightElements, leftElements, rightEq, leftEq, relatedElements⟩ :=
        inductionHypothesis shaped.symm
      exact ⟨leftElements, rightElements, leftEq, rightEq, BagElementRel.symm relatedElements⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨leftElements, midElements, leftEq, midEq, relatedLeft⟩ :=
            inductionHypothesis (Or.inl existsLeft)
          obtain ⟨midElements', rightElements, midEq', rightEq, relatedRight⟩ :=
            inductionHypothesis' (Or.inl ⟨midElements, midEq⟩)
          have sameMid := midEq.symm.trans midEq'
          simp only [Pattern.collection.injEq] at sameMid
          obtain ⟨_, listsEq, _⟩ := sameMid
          subst listsEq
          exact ⟨leftElements, rightElements, leftEq, rightEq,
            BagElementRel.trans relatedLeft relatedRight⟩
      | inr existsRight =>
          obtain ⟨midElements, rightElements, midEq, rightEq, relatedRight⟩ :=
            inductionHypothesis' (Or.inr existsRight)
          obtain ⟨leftElements, midElements', leftEq, midEq', relatedLeft⟩ :=
            inductionHypothesis (Or.inr ⟨midElements, midEq⟩)
          have sameMid := midEq'.symm.trans midEq
          simp only [Pattern.collection.injEq] at sameMid
          obtain ⟨_, listsEq, _⟩ := sameMid
          subst listsEq
          exact ⟨leftElements, rightElements, leftEq, rightEq,
            BagElementRel.trans relatedLeft relatedRight⟩
  | bagPerm permutation =>
      expose_names
      exact ⟨elements, swapped, rfl, rfl, BagElementRel.perm permutation⟩
  | setPerm _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | setDup =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | applyAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | lambdaAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | multiLambdaAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | collectionAt step _ =>
      expose_names
      cases shaped with
      | inl existsLeft =>
          obtain ⟨bagElements, equal⟩ := existsLeft
          obtain ⟨kindEq, restEq, listsEq⟩ := collection_eq_hashBag equal
          cases kindEq
          cases restEq
          subst listsEq
          exact ⟨before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
            BagElementRel.atPoint step⟩
      | inr existsRight =>
          obtain ⟨_bagElements, equal⟩ := existsRight
          obtain ⟨kindEq, restEq, listsEq⟩ := collection_eq_hashBag equal
          cases kindEq
          cases restEq
          subst listsEq
          exact ⟨before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
            BagElementRel.atPoint step⟩

theorem patternCong_set_elements {left right : Pattern} (related : PatternCong left right)
    (shaped : (∃ elements, left = .collection .hashSet elements none) ∨
      (∃ elements, right = .collection .hashSet elements none)) :
    ∃ leftElements rightElements,
      left = .collection .hashSet leftElements none ∧
        right = .collection .hashSet rightElements none ∧
          SetElementRel leftElements rightElements := by
  induction related with
  | refl pattern =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨elements, equal⟩ := existsLeft
          exact ⟨elements, elements, equal, equal, SetElementRel.refl elements⟩
      | inr existsRight =>
          obtain ⟨elements, equal⟩ := existsRight
          exact ⟨elements, elements, equal, equal, SetElementRel.refl elements⟩
  | symm _ inductionHypothesis =>
      obtain ⟨rightElements, leftElements, rightEq, leftEq, relatedElements⟩ :=
        inductionHypothesis shaped.symm
      exact ⟨leftElements, rightElements, leftEq, rightEq, SetElementRel.symm relatedElements⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨leftElements, midElements, leftEq, midEq, relatedLeft⟩ :=
            inductionHypothesis (Or.inl existsLeft)
          obtain ⟨midElements', rightElements, midEq', rightEq, relatedRight⟩ :=
            inductionHypothesis' (Or.inl ⟨midElements, midEq⟩)
          have sameMid := midEq.symm.trans midEq'
          simp only [Pattern.collection.injEq] at sameMid
          obtain ⟨_, listsEq, _⟩ := sameMid
          subst listsEq
          exact ⟨leftElements, rightElements, leftEq, rightEq,
            SetElementRel.trans relatedLeft relatedRight⟩
      | inr existsRight =>
          obtain ⟨midElements, rightElements, midEq, rightEq, relatedRight⟩ :=
            inductionHypothesis' (Or.inr existsRight)
          obtain ⟨leftElements, midElements', leftEq, midEq', relatedLeft⟩ :=
            inductionHypothesis (Or.inr ⟨midElements, midEq⟩)
          have sameMid := midEq'.symm.trans midEq
          simp only [Pattern.collection.injEq] at sameMid
          obtain ⟨_, listsEq, _⟩ := sameMid
          subst listsEq
          exact ⟨leftElements, rightElements, leftEq, rightEq,
            SetElementRel.trans relatedLeft relatedRight⟩
  | bagPerm _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | setPerm permutation =>
      expose_names
      exact ⟨elements, swapped, rfl, rfl, SetElementRel.perm permutation⟩
  | setDup =>
      expose_names
      exact ⟨before ++ element :: element :: after, before ++ element :: after, rfl, rfl,
        SetElementRel.duplicate⟩
  | applyAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | lambdaAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | multiLambdaAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
  | collectionAt step _ =>
      expose_names
      cases shaped with
      | inl existsLeft =>
          obtain ⟨setElements, equal⟩ := existsLeft
          obtain ⟨kindEq, restEq, listsEq⟩ := collection_eq_hashSet equal
          cases kindEq
          cases restEq
          subst listsEq
          exact ⟨before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
            SetElementRel.atPoint step⟩
      | inr existsRight =>
          obtain ⟨_setElements, equal⟩ := existsRight
          obtain ⟨kindEq, restEq, listsEq⟩ := collection_eq_hashSet equal
          cases kindEq
          cases restEq
          subst listsEq
          exact ⟨before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
            SetElementRel.atPoint step⟩

/-- Move a pointwise pattern congruence across a permutation of the left list. -/
theorem forall2_perm_transport {left leftPermuted right : List Pattern}
    (permuted : List.Perm left leftPermuted)
    (pointwise : List.Forall₂ PatternCong left right) :
    ∃ rightPermuted, List.Perm right rightPermuted ∧
      List.Forall₂ PatternCong leftPermuted rightPermuted := by
  induction permuted generalizing right with
  | nil =>
      cases pointwise
      exact ⟨[], List.Perm.nil, List.Forall₂.nil⟩
  | cons shared _inner inductionHypothesis =>
      obtain ⟨rightHead, rightTail, headRelated, tailRelated, rightEq⟩ :=
        List.forall₂_cons_left_iff.mp pointwise
      subst rightEq
      obtain ⟨tailPermuted, tailPerm, tailPoint⟩ := inductionHypothesis tailRelated
      exact ⟨rightHead :: tailPermuted, List.Perm.cons rightHead tailPerm,
        List.Forall₂.cons headRelated tailPoint⟩
  | swap first second rest =>
      obtain ⟨head, rightTail, headRelated, tailRelated, rightEq⟩ :=
        List.forall₂_cons_left_iff.mp pointwise
      obtain ⟨next, rightRest, nextRelated, restRelated, tailEq⟩ :=
        List.forall₂_cons_left_iff.mp tailRelated
      subst rightEq
      subst tailEq
      refine ⟨next :: head :: rightRest, ?_, ?_⟩
      · exact List.Perm.swap next head rightRest
      · exact List.Forall₂.cons nextRelated
          (List.Forall₂.cons headRelated restRelated)
  | trans _first _second inductionHypothesis inductionHypothesis' =>
      obtain ⟨middle, middlePerm, middlePoint⟩ := inductionHypothesis pointwise
      obtain ⟨rightPermuted, rightPerm, rightPoint⟩ := inductionHypothesis' middlePoint
      exact ⟨rightPermuted, middlePerm.trans rightPerm, rightPoint⟩

/-- A bag of patterns is a permutation of one side followed by the pattern
congruence at each position. The middle list of a transitivity step is not
retained. -/
theorem bagElementRel_align {left right : List Pattern}
    (related : BagElementRel left right) :
    ∃ aligned, List.Perm right aligned ∧ List.Forall₂ PatternCong left aligned := by
  induction related with
  | refl elements =>
      exact ⟨elements, List.Perm.refl elements, forall2_pattern_of_eq rfl⟩
  | symm _ inductionHypothesis =>
      obtain ⟨aligned, permAligned, pointwise⟩ := inductionHypothesis
      exact forall2_perm_transport permAligned.symm (forall2_pattern_symm pointwise)
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      obtain ⟨alignedLeft, permMid, pointLeft⟩ := inductionHypothesis
      obtain ⟨alignedRight, permRight, pointMid⟩ := inductionHypothesis'
      obtain ⟨aligned, permAligned, pointAligned⟩ :=
        forall2_perm_transport permMid pointMid
      exact ⟨aligned, permRight.trans permAligned,
        forall2_pattern_trans pointLeft pointAligned⟩
  | @perm source _target permutation =>
      exact ⟨source, permutation.symm, forall2_pattern_of_eq rfl⟩
  | atPoint step =>
      exact ⟨_, List.Perm.refl _, forall2_pattern_replace step⟩

end Mettapedia.GSLT.Poly.CollectionIndexedEquiv
