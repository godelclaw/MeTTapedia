import Mettapedia.GSLT.Poly.CollectionIndexedComplete
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Perm.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Quotient of an indexed collection tree

Permuting one bag or set parameter, and deleting one duplicate set child, is
the same equivalence on closed patterns and on indexed trees. A vector has no
such step, so its quotient is the tree.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedEquiv

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Poly.BindingLanguage hiding toPattern
open Mettapedia.GSLT.Poly.BindingSignature
open Mettapedia.GSLT.Poly.CollectionIndexed
open IPFunctor

variable {language : LanguageDef}

/-- Replace the first `done` children by the right-hand children. -/
def pastedChildren {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (left right : Child language Γ sort operator) (done : Nat)
    (direction : Fin ((indexedSignature language).arity operator).length) :
    Tree language
      ((polynomial (indexedSignature language)).src (Γ, sort) operator direction) :=
  if direction.val < done then right direction else left direction

theorem pasted_zero {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (left right : Child language Γ sort operator) :
    pastedChildren operator left right 0 = left := by
  funext direction
  simp [pastedChildren]

theorem pasted_full {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (left right : Child language Γ sort operator) :
    pastedChildren operator left right ((indexedSignature language).arity operator).length =
      right := by
  funext direction
  have below : direction.val < ((indexedSignature language).arity operator).length :=
    direction.isLt
  simp [pastedChildren, below]

/-- Pointwise tree steps under one operator are one tree step. -/
theorem treeCong_pointwise {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (left right : Child language Γ sort operator)
    (steps : ∀ direction, TreeCong language (left direction) (right direction)) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator left)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator right) := by
  let total := ((indexedSignature language).arity operator).length
  have advance : ∀ done, done ≤ total →
      TreeCong language
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator (pastedChildren operator left right 0))
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator (pastedChildren operator left right done)) := by
    intro done
    induction done with
    | zero =>
        intro _
        exact TreeCong.refl _
    | succ done inductionHypothesis =>
        intro bound
        have previous : done ≤ total := Nat.le_of_succ_le bound
        apply TreeCong.trans (inductionHypothesis previous)
        by_cases room : done < total
        · let changed : Fin total := ⟨done, room⟩
          have atChanged :
              TreeCong language
                (pastedChildren operator left right done changed)
                (pastedChildren operator left right (done + 1) changed) := by
            simp only [pastedChildren]
            rw [if_neg (by omega : ¬ done < done), if_pos (by omega : done < done + 1)]
            exact steps changed
          have stable :
              ∀ direction, direction ≠ changed →
                pastedChildren operator left right done direction =
                  pastedChildren operator left right (done + 1) direction := by
            intro direction different
            simp only [pastedChildren]
            by_cases earlier : direction.val < done
            · rw [if_pos earlier, if_pos (Nat.lt_succ_of_lt earlier)]
            · have later : done + 1 ≤ direction.val := by
                have notChanged : direction.val ≠ done := by
                  intro same
                  apply different
                  apply Fin.ext
                  exact same
                omega
              rw [if_neg earlier, if_neg (by omega : ¬ direction.val < done + 1)]
          exact TreeCong.congr operator
            (pastedChildren operator left right done)
            (pastedChildren operator left right (done + 1))
            changed atChanged stable
        · have sameChildren :
              pastedChildren operator left right done =
                pastedChildren operator left right (done + 1) := by
            funext direction
            have earlier : direction.val < done := by
              have below : direction.val < total := direction.isLt
              omega
            simp [pastedChildren, earlier, Nat.lt_succ_of_lt earlier]
          rw [sameChildren]
          exact TreeCong.refl _
  have finished := advance total (Nat.le_refl _)
  rw [pasted_zero, pasted_full] at finished
  exact finished

/-- Every direction of a bare collection is the element sort in the empty
local context. -/
theorem bare_direction {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (direction : Fin ((indexedSignature language).arity operator).length) :
    ((indexedSignature language).arity operator).get direction = (([] : List String), element) := by
  obtain ⟨_name, paramsEq⟩ := bare_rule_params shape
  obtain ⟨countsOne, lengthsOne⟩ := bare_head operator shape
  have expanded :
      expandSlots [.simple _name (.collection kind (.base element))] [0]
          [((indexedSignature language).arity operator).length] =
        List.replicate ((indexedSignature language).arity operator).length (([] : List String), element) := by
    simp [expandSlots, expandParam, baseCollection?]
  have slots :
      (indexedSignature language).arity operator =
        List.replicate ((indexedSignature language).arity operator).length (([] : List String), element) := by
    have counted :
        expandSlots operator.1.1.params operator.2.counts operator.2.lengths =
          expandSlots operator.1.1.params [0] operator.2.lengths := by
      rw [countsOne]
    have lengthed :
        expandSlots operator.1.1.params [0] operator.2.lengths =
          expandSlots operator.1.1.params [0]
            [((indexedSignature language).arity operator).length] := by
      rw [lengthsOne]
    have paramsDone :
        expandSlots operator.1.1.params [0]
            [((indexedSignature language).arity operator).length] =
          expandSlots [.simple _name (.collection kind (.base element))] [0]
            [((indexedSignature language).arity operator).length] := by
      rw [paramsEq]
    have arityRfl :
        (indexedSignature language).arity operator =
          expandSlots operator.1.1.params operator.2.counts operator.2.lengths := rfl
    exact arityRfl.trans (counted.trans (lengthed.trans (paramsDone.trans expanded)))
  rw [List.get_of_eq slots direction, List.get_eq_getElem]
  simp [List.getElem_replicate]

/-- A bare collection's head is the rule, the count zero, and the arity length.
Two bare heads of one kind at one sort with the same length are the same head. -/
theorem bare_operator_eq {sort element : String} {kind : CollType}
    (left right : (indexedSignature language).Op sort)
    (leftShape : bareCollection? left.1.1 = some (kind, element))
    (rightShape : bareCollection? right.1.1 = some (kind, element))
    (uniqueBare : UniqueBare language)
    (sameLength :
      ((indexedSignature language).arity left).length =
        ((indexedSignature language).arity right).length) :
    left = right := by
  rcases left with ⟨packedLeft, dataLeft⟩
  rcases right with ⟨packedRight, dataRight⟩
  have sameRule : packedLeft.1 = packedRight.1 :=
    uniqueBare packedLeft.2.1 packedRight.2.1
      (packedLeft.2.2.2.trans packedRight.2.2.2.symm) leftShape rightShape
  have packedEq : packedLeft = packedRight := Subtype.ext sameRule
  subst packedEq
  obtain ⟨countsL, lengthsL⟩ := bare_head ⟨packedLeft, dataLeft⟩ leftShape
  obtain ⟨countsR, lengthsR⟩ := bare_head ⟨packedLeft, dataRight⟩ rightShape
  have dataEq : dataLeft = dataRight := by
    apply headData_ext
    · rw [countsL, countsR]
    · rw [lengthsL, lengthsR, sameLength]
  subst dataEq
  rfl

/-- Read a bare-collection child at the element sort. -/
def elementChild {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (children : Child language Γ sort operator)
    (direction : Fin ((indexedSignature language).arity operator).length) :
    Tree language (Γ, element) :=
  cast
    (congrArg (Tree language)
      (collection_direction_lands operator direction (bare_direction operator shape direction)))
    (children direction)

theorem elementChild_toPattern {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (children : Child language Γ sort operator)
    (direction : Fin ((indexedSignature language).arity operator).length) :
    toPattern (elementChild operator shape children direction) =
      toPattern (children direction) := by
  unfold elementChild
  exact toPattern_cast
    (collection_direction_lands operator direction (bare_direction operator shape direction))
    (children direction)

/-- Put a bare child back at the polynomial direction. -/
def childFromElement {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (direction : Fin ((indexedSignature language).arity operator).length)
    (tree : Tree language (Γ, element)) :
    Tree language
      ((polynomial (indexedSignature language)).src (Γ, sort) operator direction) :=
  cast
    (congrArg (Tree language)
      (collection_direction_lands operator direction
        (bare_direction operator shape direction)).symm)
    tree

theorem childFromElement_toPattern {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (direction : Fin ((indexedSignature language).arity operator).length)
    (tree : Tree language (Γ, element)) :
    toPattern (childFromElement operator shape direction tree) = toPattern tree := by
  unfold childFromElement
  exact toPattern_cast
    (collection_direction_lands operator direction
      (bare_direction operator shape direction)).symm
    tree

theorem childFromElement_elementChild {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (children : Child language Γ sort operator)
    (direction : Fin ((indexedSignature language).arity operator).length) :
    childFromElement operator shape direction
        (elementChild operator shape children direction) =
      children direction := by
  unfold childFromElement elementChild
  rw [cast_cast]
  rfl

/-- Printing is injective on the trees at one index. -/
theorem toPattern_fn_injective
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language) (index : List String × String) :
    Function.Injective (fun tree : Tree language index => toPattern tree) :=
  fun _left _right same => toPattern_injective labels uniqueBare _left _right same

/-- `ofFn` reads its function at the corresponding index. -/
theorem ofFn_get_apply {α : Type} {n : Nat} (values : Fin n → α) (index : Fin n) :
    (List.ofFn values).get ⟨index.val, List.length_ofFn.symm ▸ index.isLt⟩ =
      values index := by
  rw [List.get_eq_getElem, List.getElem_ofFn]

/-- A segment at offset zero is the element child. The landing proofs may differ. -/
theorem segmentChild_at_zero {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (children : Child language Γ sort operator)
    (index : Fin ((indexedSignature language).arity operator).length)
    (fit : 0 + index.val < ((indexedSignature language).arity operator).length)
    (uniform :
      ((indexedSignature language).arity operator).get ⟨0 + index.val, fit⟩ =
        (([] : List String), element)) :
    segmentChild operator 0 index fit uniform children =
      elementChild operator shape children index := by
  unfold segmentChild atElement elementChild
  have directionEq :
      (⟨0 + index.val, fit⟩ :
          Fin ((indexedSignature language).arity operator).length) = index := by
    apply Fin.ext
    show 0 + index.val = index.val
    exact Nat.zero_add _
  apply eq_of_heq
  rw [cast_heq_iff_heq, heq_cast_iff_heq]
  exact congr_arg_heq children directionEq

/-- Casting an element tree out and back is the element tree. -/
theorem elementChild_of_childFromElement {Γ : List String} {sort element : String}
    {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    (trees : Fin ((indexedSignature language).arity operator).length →
      Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity operator).length) :
    elementChild operator shape
        (fun direction => childFromElement operator shape direction (trees direction))
        direction =
      trees direction := by
  unfold elementChild childFromElement
  rw [cast_cast]
  exact cast_eq _ _

/-- Permuting a bare hash bag, and rewriting one element, is the tree congruence
when each element step is already a tree step. -/
theorem bareBag_treeCong
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort element : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftShape : bareCollection? leftOp.1.1 = some (.hashBag, element))
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightShape : bareCollection? rightOp.1.1 = some (.hashBag, element))
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (related : PatternCong
      (nodeOf leftOp fun direction => toPattern (leftChildren direction))
      (nodeOf rightOp fun direction => toPattern (rightChildren direction))) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  simp only [nodeOf, leftShape, rightShape] at related
  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, elementsRel⟩ :=
    patternCong_bag_elements related
      (Or.inl ⟨List.ofFn fun direction => toPattern (leftChildren direction), rfl⟩)
  simp only [Pattern.collection.injEq] at leftEq rightEq
  obtain ⟨_, leftList, _⟩ := leftEq
  obtain ⟨_, rightList, _⟩ := rightEq
  subst leftList
  subst rightList
  obtain ⟨aligned, permAligned, pointwise⟩ := bagElementRel_align elementsRel
  have sameLength :
      ((indexedSignature language).arity leftOp).length =
        ((indexedSignature language).arity rightOp).length := by
    have pointLength := List.Forall₂.length_eq pointwise
    have permLength := List.Perm.length_eq permAligned
    simp only [List.length_ofFn] at pointLength permLength
    exact pointLength.trans permLength.symm
  have operators :=
    bare_operator_eq leftOp rightOp leftShape rightShape uniqueBare sameLength
  subst operators
  let source : Fin ((indexedSignature language).arity leftOp).length →
      Tree language (Γ, element) :=
    fun direction => elementChild leftOp leftShape rightChildren direction
  have sourcePrinted :
      List.ofFn (fun direction => toPattern (source direction)) =
        List.ofFn (fun direction => toPattern (rightChildren direction)) := by
    refine ofFn_pointwise ?_
    intro direction
    exact elementChild_toPattern leftOp leftShape rightChildren direction
  have alignedLength :
      aligned.length = ((indexedSignature language).arity leftOp).length := by
    have permLength := List.Perm.length_eq permAligned
    simp only [sourcePrinted.symm, List.length_ofFn] at permLength
    exact permLength.symm
  have alignedBound
      (index : Fin ((indexedSignature language).arity leftOp).length) :
      index.val < aligned.length :=
    alignedLength.symm ▸ index.isLt
  have inPrinted
      (index : Fin ((indexedSignature language).arity leftOp).length) :
      aligned.get ⟨index.val, alignedBound index⟩ ∈
        List.ofFn fun direction => toPattern (rightChildren direction) :=
    permAligned.symm.subset (List.get_mem aligned ⟨index.val, alignedBound index⟩)
  let pick : Fin ((indexedSignature language).arity leftOp).length →
      Fin ((indexedSignature language).arity leftOp).length :=
    fun index => Classical.choose (List.mem_ofFn.mp (inPrinted index))
  have pick_spec
      (index : Fin ((indexedSignature language).arity leftOp).length) :
      toPattern (rightChildren (pick index)) =
        aligned.get ⟨index.val, alignedBound index⟩ :=
    Classical.choose_spec (List.mem_ofFn.mp (inPrinted index))
  let pickedElement : Fin ((indexedSignature language).arity leftOp).length →
      Tree language (Γ, element) :=
    fun index => source (pick index)
  have pickedPrinted :
      List.ofFn (fun index => toPattern (pickedElement index)) = aligned := by
    refine List.ext_get ?_ ?_
    · simp only [List.length_ofFn, alignedLength.symm]
    · intro n hOfFn hAligned
      let index : Fin ((indexedSignature language).arity leftOp).length :=
        ⟨n, by simpa [List.length_ofFn] using hOfFn⟩
      have read :=
        ofFn_get_apply (fun i => toPattern (pickedElement i)) index
      have sameGet :
          (List.ofFn fun i => toPattern (pickedElement i)).get ⟨n, hOfFn⟩ =
            (List.ofFn fun i => toPattern (pickedElement i)).get
              ⟨index.val, List.length_ofFn.symm ▸ index.isLt⟩ := by
        apply congrArg
          (List.get (List.ofFn fun i => toPattern (pickedElement i)))
        apply Fin.ext
        rfl
      rw [sameGet, read]
      have asElement :
          toPattern (pickedElement index) =
            toPattern (rightChildren (pick index)) := by
        simp only [pickedElement]
        exact elementChild_toPattern leftOp leftShape rightChildren (pick index)
      rw [asElement, pick_spec index]
  let picked : Child language Γ sort leftOp :=
    fun direction => childFromElement leftOp leftShape direction (pickedElement direction)
  have pointwiseElements :
      List.Forall₂ PatternCong
        (List.ofFn fun direction => toPattern (leftChildren direction))
        (List.ofFn fun direction => toPattern (pickedElement direction)) :=
    pickedPrinted.symm ▸ pointwise
  have pointSteps :
      ∀ direction, TreeCong language (leftChildren direction) (picked direction) := by
    intro direction
    apply ih
    rw [childFromElement_toPattern]
    have hx :
        direction.val <
          (List.ofFn fun d => toPattern (leftChildren d)).length :=
      List.length_ofFn.symm ▸ direction.isLt
    have hy :
        direction.val <
          (List.ofFn fun d => toPattern (pickedElement d)).length :=
      List.length_ofFn.symm ▸ direction.isLt
    have atPoint :=
      (List.forall₂_iff_get.mp pointwiseElements).2 direction.val hx hy
    rw [ofFn_get_apply (fun d => toPattern (leftChildren d)) direction,
      ofFn_get_apply (fun d => toPattern (pickedElement d)) direction] at atPoint
    simp only [pickedElement] at atPoint
    exact atPoint
  have ordered :=
    treeCong_pointwise leftOp leftChildren picked pointSteps
  have treePerm :
      List.Perm (List.ofFn source) (List.ofFn pickedElement) := by
    have patternPerm :
        List.Perm
          (List.map toPattern (List.ofFn source))
          (List.map toPattern (List.ofFn pickedElement)) := by
      have mapSource :
          List.map toPattern (List.ofFn source) =
            List.ofFn fun direction => toPattern (source direction) := by
        rw [List.map_ofFn]
        refine ofFn_pointwise ?_
        intro direction
        rfl
      have mapPicked :
          List.map toPattern (List.ofFn pickedElement) =
            List.ofFn fun direction => toPattern (pickedElement direction) := by
        rw [List.map_ofFn]
        refine ofFn_pointwise ?_
        intro direction
        rfl
      rw [mapSource, mapPicked, sourcePrinted, pickedPrinted]
      exact permAligned
    exact (List.map_perm_map_iff
      (toPattern_fn_injective labels uniqueBare (Γ, element))).mp patternPerm
  have boundZero : 0 < leftOp.1.1.params.length := by
    obtain ⟨_, paramsEq⟩ := bare_rule_params leftShape
    simp [paramsEq]
  have shapeZero :
      baseCollection? (leftOp.1.1.params.get ⟨0, boundZero⟩) =
        some (.hashBag, element) := by
    obtain ⟨name, paramsEq⟩ := bare_rule_params leftShape
    rw [List.get_of_eq paramsEq ⟨0, boundZero⟩,
      singleton_get_zero
        (TermParam.simple name (.collection .hashBag (.base element)))
        (paramsEq ▸ boundZero)]
    simp [baseCollection?]
  have startZero :
      0 =
        slotCount (leftOp.1.1.params.take 0) (leftOp.2.counts.take 0)
          (leftOp.2.lengths.take 0) := by
    simp [List.take_zero, slotCount]
  have lengthFull :
      ((indexedSignature language).arity leftOp).length =
        leftOp.2.lengths.getD 0 0 := by
    obtain ⟨_, lengthsOne⟩ := bare_head leftOp leftShape
    rw [lengthsOne, List.getD_cons_zero]
  exact TreeCong.trans ordered (TreeCong.symm (TreeCong.bagPerm leftOp 0
    ((indexedSignature language).arity leftOp).length (by omega) .hashBag (Or.inl rfl) 0
    boundZero shapeZero startZero lengthFull
    (fun index => by
      refine (congrArg (List.get ((indexedSignature language).arity leftOp)) ?_).symm.trans
        (bare_direction leftOp leftShape index)
      apply Fin.ext
      show index.val = 0 + index.val
      exact (Nat.zero_add index.val).symm)
    rightChildren picked
    (by
      intro direction outside
      cases outside <;> omega)
    (by
      refine List.Perm.trans (l₂ := List.ofFn source) ?_ (List.Perm.trans treePerm ?_)
      · refine Eq.rec
          (motive := fun lists _ => List.Perm lists (List.ofFn source))
          (List.Perm.refl (List.ofFn source)) ?_
        symm
        refine ofFn_pointwise ?_
        intro index
        exact segmentChild_at_zero leftOp leftShape rightChildren index _ _
      · refine Eq.rec
          (motive := fun lists _ => List.Perm (List.ofFn pickedElement) lists)
          (List.Perm.refl (List.ofFn pickedElement)) ?_
        refine ofFn_pointwise ?_
        intro index
        exact ((segmentChild_at_zero leftOp leftShape picked index _ _).trans
          (elementChild_of_childFromElement leftOp leftShape pickedElement index)).symm)))

/-- The element lists of a bare bag are its one segment. A permutation of those
lists is the tree congruence. -/
theorem bare_bagPerm {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (.hashBag, element))
    (left right : Child language Γ sort operator)
    (permuted : List.Perm
      (List.ofFn fun index => elementChild operator shape left index)
      (List.ofFn fun index => elementChild operator shape right index)) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator left)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator right) := by
  have boundZero : 0 < operator.1.1.params.length := by
    obtain ⟨_, paramsEq⟩ := bare_rule_params shape
    simp [paramsEq]
  have shapeZero :
      baseCollection? (operator.1.1.params.get ⟨0, boundZero⟩) =
        some (.hashBag, element) := by
    obtain ⟨name, paramsEq⟩ := bare_rule_params shape
    rw [List.get_of_eq paramsEq ⟨0, boundZero⟩,
      singleton_get_zero
        (TermParam.simple name (.collection .hashBag (.base element)))
        (paramsEq ▸ boundZero)]
    simp [baseCollection?]
  have startZero :
      0 =
        slotCount (operator.1.1.params.take 0) (operator.2.counts.take 0)
          (operator.2.lengths.take 0) := by
    simp [List.take_zero, slotCount]
  have lengthFull :
      ((indexedSignature language).arity operator).length =
        operator.2.lengths.getD 0 0 := by
    obtain ⟨_, lengthsOne⟩ := bare_head operator shape
    rw [lengthsOne, List.getD_cons_zero]
  exact TreeCong.bagPerm operator 0
    ((indexedSignature language).arity operator).length (by omega) .hashBag (Or.inl rfl) 0
    boundZero shapeZero startZero lengthFull
    (fun index => by
      refine (congrArg (List.get ((indexedSignature language).arity operator)) ?_).symm.trans
        (bare_direction operator shape index)
      apply Fin.ext
      show index.val = 0 + index.val
      exact (Nat.zero_add index.val).symm)
    left right
    (by
      intro direction outside
      cases outside <;> omega)
    (by
      refine List.Perm.trans
        (l₂ := List.ofFn fun index => elementChild operator shape left index)
        ?_ (List.Perm.trans permuted ?_)
      · refine Eq.rec
          (motive := fun lists _ =>
            List.Perm lists (List.ofFn fun index => elementChild operator shape left index))
          (List.Perm.refl _) ?_
        symm
        refine ofFn_pointwise ?_
        intro index
        exact segmentChild_at_zero operator shape left index _ _
      · refine Eq.rec
          (motive := fun lists _ =>
            List.Perm (List.ofFn fun index => elementChild operator shape right index) lists)
          (List.Perm.refl _) ?_
        refine ofFn_pointwise ?_
        intro index
        exact (segmentChild_at_zero operator shape right index _ _).symm)

theorem collection_eq_vec {kind : CollType} {elements vecElements : List Pattern}
    {rest : Option String}
    (equal : Pattern.collection kind elements rest =
      Pattern.collection .vec vecElements none) :
    kind = .vec ∧ rest = none ∧ elements = vecElements := by
  simp only [Pattern.collection.injEq] at equal
  obtain ⟨kindEq, listsEq, restEq⟩ := equal
  exact ⟨kindEq, restEq, listsEq⟩

/-- A vector keeps its element order. The element lists are related pointwise. -/
theorem patternCong_vec_elements {left right : Pattern} (related : PatternCong left right)
    (shaped : (∃ elements, left = .collection .vec elements none) ∨
      (∃ elements, right = .collection .vec elements none)) :
    ∃ leftElements rightElements,
      left = .collection .vec leftElements none ∧
        right = .collection .vec rightElements none ∧
          List.Forall₂ PatternCong leftElements rightElements := by
  induction related with
  | refl pattern =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨elements, equal⟩ := existsLeft
          exact ⟨elements, elements, equal, equal, forall2_pattern_of_eq rfl⟩
      | inr existsRight =>
          obtain ⟨elements, equal⟩ := existsRight
          exact ⟨elements, elements, equal, equal, forall2_pattern_of_eq rfl⟩
  | symm _ inductionHypothesis =>
      obtain ⟨rightElements, leftElements, rightEq, leftEq, pointwise⟩ :=
        inductionHypothesis shaped.symm
      exact ⟨leftElements, rightElements, leftEq, rightEq, forall2_pattern_symm pointwise⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨leftElements, midElements, leftEq, midEq, pointLeft⟩ :=
            inductionHypothesis (Or.inl existsLeft)
          obtain ⟨midElements', rightElements, midEq', rightEq, pointRight⟩ :=
            inductionHypothesis' (Or.inl ⟨midElements, midEq⟩)
          have sameMid := midEq.symm.trans midEq'
          simp only [Pattern.collection.injEq] at sameMid
          obtain ⟨_, listsEq, _⟩ := sameMid
          subst listsEq
          exact ⟨leftElements, rightElements, leftEq, rightEq,
            forall2_pattern_trans pointLeft pointRight⟩
      | inr existsRight =>
          obtain ⟨midElements, rightElements, midEq, rightEq, pointRight⟩ :=
            inductionHypothesis' (Or.inr existsRight)
          obtain ⟨leftElements, midElements', leftEq, midEq', pointLeft⟩ :=
            inductionHypothesis (Or.inr ⟨midElements, midEq⟩)
          have sameMid := midEq'.symm.trans midEq
          simp only [Pattern.collection.injEq] at sameMid
          obtain ⟨_, listsEq, _⟩ := sameMid
          subst listsEq
          exact ⟨leftElements, rightElements, leftEq, rightEq,
            forall2_pattern_trans pointLeft pointRight⟩
  | bagPerm _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, equal⟩ := existsRight
          cases equal
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
          obtain ⟨vecElements, equal⟩ := existsLeft
          obtain ⟨kindEq, restEq, listsEq⟩ := collection_eq_vec equal
          cases kindEq
          cases restEq
          subst listsEq
          exact ⟨before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
            forall2_pattern_replace step⟩
      | inr existsRight =>
          obtain ⟨_vecElements, equal⟩ := existsRight
          obtain ⟨kindEq, restEq, listsEq⟩ := collection_eq_vec equal
          cases kindEq
          cases restEq
          subst listsEq
          exact ⟨before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
            forall2_pattern_replace step⟩

/-- A bare vector reflects the pattern congruence as the tree congruence.
There is no permutation to undo. -/
theorem vecBare_treeCong
    (_labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort element : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftShape : bareCollection? leftOp.1.1 = some (.vec, element))
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightShape : bareCollection? rightOp.1.1 = some (.vec, element))
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (related : PatternCong
      (nodeOf leftOp fun direction => toPattern (leftChildren direction))
      (nodeOf rightOp fun direction => toPattern (rightChildren direction))) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  simp only [nodeOf, leftShape, rightShape] at related
  obtain ⟨_, _, leftEq, rightEq, pointwise⟩ :=
    patternCong_vec_elements related
      (Or.inl ⟨List.ofFn fun direction => toPattern (leftChildren direction), rfl⟩)
  simp only [Pattern.collection.injEq] at leftEq rightEq
  obtain ⟨_, leftList, _⟩ := leftEq
  obtain ⟨_, rightList, _⟩ := rightEq
  subst leftList
  subst rightList
  have sameLength :
      ((indexedSignature language).arity leftOp).length =
        ((indexedSignature language).arity rightOp).length := by
    simpa [List.length_ofFn] using List.Forall₂.length_eq pointwise
  have operators :=
    bare_operator_eq leftOp rightOp leftShape rightShape uniqueBare sameLength
  subst operators
  have pointSteps :
      ∀ direction, TreeCong language (leftChildren direction) (rightChildren direction) := by
    intro direction
    apply ih
    have hx :
        direction.val <
          (List.ofFn fun d => toPattern (leftChildren d)).length :=
      List.length_ofFn.symm ▸ direction.isLt
    have hy :
        direction.val <
          (List.ofFn fun d => toPattern (rightChildren d)).length :=
      List.length_ofFn.symm ▸ direction.isLt
    have atPoint :=
      (List.forall₂_iff_get.mp pointwise).2 direction.val hx hy
    rw [ofFn_get_apply (fun d => toPattern (leftChildren d)) direction,
      ofFn_get_apply (fun d => toPattern (rightChildren d)) direction] at atPoint
    exact atPoint
  exact treeCong_pointwise leftOp leftChildren rightChildren pointSteps

theorem bagElementRel_length {left right : List Pattern}
    (related : BagElementRel left right) : left.length = right.length := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | perm permutation => exact List.Perm.length_eq permutation
  | atPoint _ => simp [List.length_append, List.length_cons]

/-- A set step preserves membership of pattern-congruence classes in both directions. -/
theorem setElementRel_both {left right : List Pattern}
    (related : SetElementRel left right) :
    (∀ pattern, pattern ∈ left → ∃ image, image ∈ right ∧ PatternCong pattern image) ∧
      (∀ pattern, pattern ∈ right → ∃ image, image ∈ left ∧ PatternCong image pattern) := by
  induction related with
  | refl _ =>
      exact ⟨fun pattern member => ⟨pattern, member, PatternCong.refl pattern⟩,
        fun pattern member => ⟨pattern, member, PatternCong.refl pattern⟩⟩
  | symm _ inductionHypothesis =>
      exact ⟨fun pattern member => by
          obtain ⟨image, imageMem, step⟩ := inductionHypothesis.2 pattern member
          exact ⟨image, imageMem, PatternCong.symm step⟩,
        fun pattern member => by
          obtain ⟨image, imageMem, step⟩ := inductionHypothesis.1 pattern member
          exact ⟨image, imageMem, PatternCong.symm step⟩⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact ⟨fun pattern member => by
          obtain ⟨mid, midMem, stepLeft⟩ := inductionHypothesis.1 pattern member
          obtain ⟨image, imageMem, stepRight⟩ := inductionHypothesis'.1 mid midMem
          exact ⟨image, imageMem, PatternCong.trans stepLeft stepRight⟩,
        fun pattern member => by
          obtain ⟨mid, midMem, stepRight⟩ := inductionHypothesis'.2 pattern member
          obtain ⟨image, imageMem, stepLeft⟩ := inductionHypothesis.2 mid midMem
          exact ⟨image, imageMem, PatternCong.trans stepLeft stepRight⟩⟩
  | perm permutation =>
      exact ⟨fun pattern member =>
          ⟨pattern, (List.Perm.mem_iff permutation).mp member, PatternCong.refl pattern⟩,
        fun pattern member =>
          ⟨pattern, (List.Perm.mem_iff permutation).mpr member, PatternCong.refl pattern⟩⟩
  | @duplicate before copied after =>
      exact ⟨fun pattern member => by
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with memBefore | rfl | rfl | memAfter
          · exact ⟨pattern, List.mem_append.mpr (Or.inl memBefore), PatternCong.refl pattern⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr
                (show pattern ∈ pattern :: after from List.mem_cons_self)),
              PatternCong.refl pattern⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr
                (show pattern ∈ pattern :: after from List.mem_cons_self)),
              PatternCong.refl pattern⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr (List.mem_cons_of_mem copied memAfter)),
              PatternCong.refl pattern⟩,
        fun pattern member => by
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with memBefore | rfl | memAfter
          · exact ⟨pattern, List.mem_append.mpr (Or.inl memBefore), PatternCong.refl pattern⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr
                (show pattern ∈ pattern :: pattern :: after from List.mem_cons_self)),
              PatternCong.refl pattern⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr
                (List.mem_cons_of_mem copied (List.mem_cons_of_mem copied memAfter))),
              PatternCong.refl pattern⟩⟩
  | @atPoint before leftPattern rightPattern after step =>
      exact ⟨fun pattern member => by
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with memBefore | rfl | memAfter
          · exact ⟨pattern, List.mem_append.mpr (Or.inl memBefore), PatternCong.refl pattern⟩
          · exact ⟨rightPattern,
              List.mem_append.mpr (Or.inr
                (show rightPattern ∈ rightPattern :: after from List.mem_cons_self)), step⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr (List.mem_cons_of_mem rightPattern memAfter)),
              PatternCong.refl pattern⟩,
        fun pattern member => by
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with memBefore | rfl | memAfter
          · exact ⟨pattern, List.mem_append.mpr (Or.inl memBefore), PatternCong.refl pattern⟩
          · exact ⟨leftPattern,
              List.mem_append.mpr (Or.inr
                (show leftPattern ∈ leftPattern :: after from List.mem_cons_self)), step⟩
          · exact ⟨pattern,
              List.mem_append.mpr (Or.inr (List.mem_cons_of_mem leftPattern memAfter)),
              PatternCong.refl pattern⟩⟩

/-- The element lists of a bare set are its one segment. A permutation of those
lists is the tree congruence. -/
theorem bare_setPerm {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (.hashSet, element))
    (left right : Child language Γ sort operator)
    (permuted : List.Perm
      (List.ofFn fun index => elementChild operator shape left index)
      (List.ofFn fun index => elementChild operator shape right index)) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator left)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator right) := by
  have boundZero : 0 < operator.1.1.params.length := by
    obtain ⟨_, paramsEq⟩ := bare_rule_params shape
    simp [paramsEq]
  have shapeZero :
      baseCollection? (operator.1.1.params.get ⟨0, boundZero⟩) =
        some (.hashSet, element) := by
    obtain ⟨name, paramsEq⟩ := bare_rule_params shape
    rw [List.get_of_eq paramsEq ⟨0, boundZero⟩,
      singleton_get_zero
        (TermParam.simple name (.collection .hashSet (.base element)))
        (paramsEq ▸ boundZero)]
    simp [baseCollection?]
  have startZero :
      0 =
        slotCount (operator.1.1.params.take 0) (operator.2.counts.take 0)
          (operator.2.lengths.take 0) := by
    simp [List.take_zero, slotCount]
  have lengthFull :
      ((indexedSignature language).arity operator).length =
        operator.2.lengths.getD 0 0 := by
    obtain ⟨_, lengthsOne⟩ := bare_head operator shape
    rw [lengthsOne, List.getD_cons_zero]
  exact TreeCong.bagPerm operator 0
    ((indexedSignature language).arity operator).length (by omega) .hashSet (Or.inr rfl) 0
    boundZero shapeZero startZero lengthFull
    (fun index => by
      refine (congrArg (List.get ((indexedSignature language).arity operator)) ?_).symm.trans
        (bare_direction operator shape index)
      apply Fin.ext
      show index.val = 0 + index.val
      exact (Nat.zero_add index.val).symm)
    left right
    (by
      intro direction outside
      cases outside <;> omega)
    (by
      refine List.Perm.trans
        (l₂ := List.ofFn fun index => elementChild operator shape left index)
        ?_ (List.Perm.trans permuted ?_)
      · refine Eq.rec
          (motive := fun lists _ =>
            List.Perm lists (List.ofFn fun index => elementChild operator shape left index))
          (List.Perm.refl _) ?_
        symm
        refine ofFn_pointwise ?_
        intro index
        exact segmentChild_at_zero operator shape left index _ _
      · refine Eq.rec
          (motive := fun lists _ =>
            List.Perm (List.ofFn fun index => elementChild operator shape right index) lists)
          (List.Perm.refl _) ?_
        refine ofFn_pointwise ?_
        intro index
        exact (segmentChild_at_zero operator shape right index _ _).symm)

theorem treeCong_of_eq {index : List String × String}
    {left right : Tree language index} (equal : left = right) :
    TreeCong language left right := by
  subst equal
  exact TreeCong.refl _

theorem treeCong_cast {index index' : List String × String} (equal : index = index')
    {left right : Tree language index} (related : TreeCong language left right) :
    TreeCong language
      (cast (congrArg (Tree language) equal) left)
      (cast (congrArg (Tree language) equal) right) := by
  subst equal
  simp only [cast_eq]
  exact related

theorem treeCong_of_cast {index index' : List String × String} (equal : index = index')
    {left right : Tree language index}
    (related : TreeCong language
      (cast (congrArg (Tree language) equal) left)
      (cast (congrArg (Tree language) equal) right)) :
    TreeCong language left right := by
  subst equal
  simpa only [cast_eq] using related

theorem child_cast_agree {Γ : List String} {element : String}
    {indexT indexS : List String × String}
    (landsT : indexT = (Γ, element)) (landsS : indexS = (Γ, element))
    (tree : Tree language (Γ, element)) :
    cast (congrArg (Tree language) (landsT.trans landsS.symm))
        (cast (congrArg (Tree language) landsT.symm) tree) =
      cast (congrArg (Tree language) landsS.symm) tree := by
  subst landsT
  subst landsS
  rfl

/-- Send two distinct positions to `0` and `1`. -/
theorem exists_place_two {n : Nat} (i j : Fin n) (different : i ≠ j) (wide : 2 ≤ n) :
    ∃ σ : Equiv.Perm (Fin n),
      σ ⟨0, by omega⟩ = i ∧ σ ⟨1, by omega⟩ = j := by
  have zeroLt : 0 < n := by omega
  have oneLt : 1 < n := by omega
  let zero : Fin n := ⟨0, zeroLt⟩
  let one : Fin n := ⟨1, oneLt⟩
  have zeroEq : (⟨0, by omega⟩ : Fin n) = zero := by
    apply Fin.ext
    rfl
  have oneEq : (⟨1, by omega⟩ : Fin n) = one := by
    apply Fin.ext
    rfl
  suffices ∃ σ : Equiv.Perm (Fin n), σ zero = i ∧ σ one = j by
    obtain ⟨σ, atZero, atOne⟩ := this
    exact ⟨σ, zeroEq.symm ▸ atZero, oneEq.symm ▸ atOne⟩
  have zero_ne_one : zero ≠ one := by
    intro same
    exact Nat.zero_ne_one (congrArg Fin.val same)
  by_cases i0 : i = zero
  · subst i0
    by_cases j1 : j = one
    · subst j1
      exact ⟨Equiv.refl _, rfl, rfl⟩
    · have zero_ne_j : zero ≠ j := different
      refine ⟨Equiv.swap j one, ?_, ?_⟩
      · exact Equiv.swap_apply_of_ne_of_ne zero_ne_j zero_ne_one
      · exact Equiv.swap_apply_right j one
  · by_cases i1 : i = one
    · subst i1
      by_cases j0 : j = zero
      · subst j0
        refine ⟨Equiv.swap zero one, ?_, ?_⟩
        · exact Equiv.swap_apply_left zero one
        · exact Equiv.swap_apply_right zero one
      · have j_ne_one : j ≠ one := different.symm
        refine ⟨(Equiv.swap one j).trans (Equiv.swap zero one), ?_, ?_⟩
        · rw [Equiv.trans_apply]
          have stayed : (Equiv.swap one j) zero = zero :=
            Equiv.swap_apply_of_ne_of_ne zero_ne_one (Ne.symm j0)
          rw [stayed]
          exact Equiv.swap_apply_left zero one
        · rw [Equiv.trans_apply]
          have moved : (Equiv.swap one j) one = j := Equiv.swap_apply_left one j
          rw [moved]
          exact Equiv.swap_apply_of_ne_of_ne j0 j_ne_one
    · by_cases j0 : j = zero
      · subst j0
        refine ⟨(Equiv.swap i one).trans (Equiv.swap zero i), ?_, ?_⟩
        · rw [Equiv.trans_apply]
          have stayed : (Equiv.swap i one) zero = zero :=
            Equiv.swap_apply_of_ne_of_ne (Ne.symm i0) zero_ne_one
          rw [stayed]
          exact Equiv.swap_apply_left zero i
        · rw [Equiv.trans_apply]
          have moved : (Equiv.swap i one) one = i := Equiv.swap_apply_right i one
          rw [moved]
          exact Equiv.swap_apply_right zero i
      · by_cases j1 : j = one
        · subst j1
          refine ⟨Equiv.swap zero i, ?_, ?_⟩
          · exact Equiv.swap_apply_left zero i
          · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm zero_ne_one) (Ne.symm i1)
        · refine ⟨(Equiv.swap zero i).trans (Equiv.swap one j), ?_, ?_⟩
          · rw [Equiv.trans_apply]
            have moved : (Equiv.swap zero i) zero = i := Equiv.swap_apply_left zero i
            rw [moved]
            exact Equiv.swap_apply_of_ne_of_ne i1 different
          · rw [Equiv.trans_apply]
            have stayed : (Equiv.swap zero i) one = one :=
              Equiv.swap_apply_of_ne_of_ne (Ne.symm zero_ne_one) (Ne.symm i1)
            rw [stayed]
            exact Equiv.swap_apply_left one j

/-- A bare collection head with a chosen element count. -/
def resizedBare {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element)) (n : Nat) :
    (indexedSignature language).Op sort :=
  ⟨operator.1, {
      counts := [0]
      lengths := [n]
      counts_length := by
        obtain ⟨_, paramsEq⟩ := bare_rule_params shape
        simp [paramsEq]
      lengths_length := by
        obtain ⟨_, paramsEq⟩ := bare_rule_params shape
        simp [paramsEq]
      counts_fixed := by
        intro index _
        cases index <;> simp [List.getD]
      lengths_fixed := by
        intro index premise
        obtain ⟨name, paramsEq⟩ := bare_rule_params shape
        cases index with
        | zero =>
            have contrad : False := by
              simp [paramsEq, List.getD, baseCollection?, missingParameter] at premise
            exact contrad.elim
        | succ _ =>
            simp [List.getD] }⟩

theorem resized_shape {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element)) (n : Nat) :
    bareCollection? (resizedBare operator shape n).1.1 = some (kind, element) := by
  simpa [resizedBare] using shape

theorem resized_length {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element)) (n : Nat) :
    ((indexedSignature language).arity (resizedBare operator shape n)).length = n := by
  rw [bare_slot_length (resizedBare operator shape n) (resized_shape operator shape n)]
  simp [resizedBare, List.headD]

/-- Children of a bare collection, read from a family indexed by the element count. -/
def familyChildren {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    {k : Nat}
    (lengthEq : ((indexedSignature language).arity operator).length = k)
    (trees : Fin k → Tree language (Γ, element)) : Child language Γ sort operator :=
  fun direction =>
    childFromElement operator shape direction (trees (direction.cast lengthEq))

def familyNode {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    {k : Nat}
    (lengthEq : ((indexedSignature language).arity operator).length = k)
    (trees : Fin k → Tree language (Γ, element)) : Tree language (Γ, sort) :=
  IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
    operator (familyChildren operator shape lengthEq trees)

theorem family_atElement {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (kind, element))
    {k : Nat}
    (lengthEq : ((indexedSignature language).arity operator).length = k)
    (trees : Fin k → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity operator).length)
    (uniform : ((indexedSignature language).arity operator).get direction = ([], element)) :
    atElement operator direction uniform (familyChildren operator shape lengthEq trees) =
      trees (direction.cast lengthEq) := by
  unfold atElement familyChildren childFromElement
  rw [cast_cast]
  exact cast_eq _ _

/-- Delete the first of two equal children of a bare hash set. -/
theorem bare_setDeleteZero {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (.hashSet, element))
    {n : Nat}
    (lengthEq : ((indexedSignature language).arity operator).length = n)
    (wide : 2 ≤ n)
    (trees : Fin n → Tree language (Γ, element))
    (copies : trees ⟨0, by omega⟩ = trees ⟨1, by omega⟩) :
    TreeCong language
      (familyNode operator shape lengthEq trees)
      (familyNode (resizedBare operator shape (n - 1))
        (resized_shape operator shape (n - 1))
        (resized_length operator shape (n - 1))
        (fun index : Fin (n - 1) => trees ⟨index.val + 1, by have := index.isLt; omega⟩)) := by
  let source := operator
  let target := resizedBare operator shape (n - 1)
  let sourceShape := shape
  let targetShape := resized_shape operator shape (n - 1)
  let sourceLength : ((indexedSignature language).arity source).length = n := lengthEq
  let targetLength := resized_length operator shape (n - 1)
  let sourceTrees := trees
  let targetTrees : Fin (n - 1) → Tree language (Γ, element) :=
    fun index => trees ⟨index.val + 1, by have := index.isLt; omega⟩
  let sourceChildren := familyChildren source sourceShape sourceLength sourceTrees
  let targetChildren := familyChildren target targetShape targetLength targetTrees
  let removed : Fin ((indexedSignature language).arity source).length :=
    ⟨0, by simpa [sourceLength] using Nat.zero_lt_of_lt wide⟩
  have successor : removed.val + 1 < ((indexedSignature language).arity source).length := by
    simpa [removed, sourceLength] using Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) wide
  have parameterBound : 0 < source.1.1.params.length := by
    obtain ⟨_, paramsEq⟩ := bare_rule_params sourceShape
    rw [paramsEq]
    simp
  have deletion : SetDeletion language Γ sort element source target sourceChildren targetChildren
      removed 0 0 := {
    sameRule := rfl
    sameCounts := by
      have leftCounts : source.2.counts = [0] := (bare_head source sourceShape).1
      have rightCounts : target.2.counts = [0] := rfl
      rw [leftCounts, rightCounts]
    lengthsDrop := by
      have leftLengths : source.2.lengths = [n] := by
        rw [(bare_head source sourceShape).2, sourceLength]
      have rightLengths : target.2.lengths = [n - 1] := rfl
      rw [leftLengths, rightLengths]
      simp [List.set_cons_zero]
    lengthDrop := by
      have tLen : ((indexedSignature language).arity target).length = n - 1 :=
        resized_length operator shape (n - 1)
      have sLen : ((indexedSignature language).arity source).length = n := lengthEq
      omega
    successor := successor
    parameterBound := parameterBound
    parameterShape := by
      obtain ⟨name, paramsEq⟩ := bare_rule_params sourceShape
      rw [List.get_of_eq paramsEq ⟨0, parameterBound⟩,
        singleton_get_zero
          (TermParam.simple name (.collection .hashSet (.base element)))
          (paramsEq ▸ parameterBound)]
      simp [baseCollection?]
    inSegment := by
      refine ⟨Nat.zero_le _, ?_⟩
      have removedZero : removed.val = 0 := by simp [removed]
      rw [removedZero]
      have lenHead : source.2.lengths.getD 0 0 = n := by
        rw [(bare_head source sourceShape).2, sourceLength]
        simp
      rw [lenHead]
      omega
    segmentIsPrefix := by simp [List.take_zero, slotCount]
    removedDecl := bare_direction source sourceShape removed
    nextDecl := bare_direction source sourceShape ⟨removed.val + 1, successor⟩
    duplicate := by
      have leftTree :=
        family_atElement source sourceShape sourceLength sourceTrees removed
          (bare_direction source sourceShape removed)
      have rightTree :=
        family_atElement source sourceShape sourceLength sourceTrees
          ⟨removed.val + 1, successor⟩
          (bare_direction source sourceShape ⟨removed.val + 1, successor⟩)
      rw [leftTree, rightTree]
      have leftIndex : removed.cast sourceLength = (⟨0, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp [removed]
      have rightIndex :
          (⟨removed.val + 1, successor⟩ :
              Fin ((indexedSignature language).arity source).length).cast sourceLength =
            (⟨1, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp [removed]
      rw [leftIndex, rightIndex]
      exact copies
    arityErase := by
      have srcList : (indexedSignature language).arity source =
          List.replicate n ([], element) := by
        rw [bare_arity source sourceShape]
        have headD : source.2.lengths.headD 0 = n := by
          rw [(bare_head source sourceShape).2, sourceLength]
          simp
        rw [headD]
      have tgtList : (indexedSignature language).arity target =
          List.replicate (n - 1) ([], element) := by
        rw [bare_arity target targetShape]
        have headD : target.2.lengths.headD 0 = n - 1 := rfl
        rw [headD]
      have removedZero : removed.val = 0 := by simp [removed]
      have asSucc : n = (n - 1) + 1 := by omega
      calc
        (indexedSignature language).arity target
            = List.replicate (n - 1) ([], element) := tgtList
        _ = (List.replicate n ([], element)).eraseIdx 0 := by
              conv_rhs => rw [asSucc]
              rw [List.replicate_succ, List.eraseIdx_cons_zero]
        _ = (List.replicate n ([], element)).eraseIdx removed.val := by
              rw [removedZero]
        _ = ((indexedSignature language).arity source).eraseIdx removed.val := by
              rw [← srcList]
    kept := by
      intro direction
      have dropBound : direction.val + 1 < ((indexedSignature language).arity source).length := by
        have low : direction.val < n - 1 := targetLength ▸ direction.isLt
        have high : direction.val + 1 < n := by omega
        exact lengthEq.symm ▸ high
      let dropped := dropDirection removed.val removed.isLt direction.val dropBound
      have droppedVal : dropped.val = direction.val + 1 := by
        simp [dropped, dropDirection, removed, Fin.val_mk]
      have sameDrop :
          dropped =
            dropDirection removed.val removed.isLt direction.val
              (by
                have directionBound := direction.isLt
                omega) := by
        apply Fin.ext
        simp [dropped, dropDirection, removed, Fin.val_mk]
      rw [← sameDrop]
      have landsT :
          (polynomial (indexedSignature language)).src (Γ, sort) target direction =
            (Γ, element) :=
        collection_direction_lands (Γ := Γ) target direction
          (bare_direction target targetShape direction)
      have landsS :
          (polynomial (indexedSignature language)).src (Γ, sort) source dropped =
            (Γ, element) :=
        collection_direction_lands (Γ := Γ) source dropped
          (bare_direction source sourceShape dropped)
      refine ⟨landsT.trans landsS.symm, ?_⟩
      have sameTree :
          targetTrees (direction.cast targetLength) =
            sourceTrees (dropped.cast sourceLength) := by
        apply congrArg sourceTrees
        apply Fin.ext
        exact droppedVal.symm
      unfold targetChildren sourceChildren familyChildren childFromElement
      rw [sameTree]
      exact child_cast_agree landsT landsS _
  }
  simpa [familyNode, sourceChildren, targetChildren, source, target, sourceShape, targetShape,
    sourceLength, targetLength, sourceTrees, targetTrees] using
    TreeCong.setDup source target sourceChildren targetChildren removed 0 0 deletion

/-- A bare hash set of a chosen length, with children supplied as a family. -/
def bareSetNode {Γ : List String} {sort element : String}
    (seed : (indexedSignature language).Op sort)
    (shape : bareCollection? seed.1.1 = some (.hashSet, element))
    (k : Nat) (trees : Fin k → Tree language (Γ, element)) : Tree language (Γ, sort) :=
  familyNode (resizedBare seed shape k) (resized_shape seed shape k)
    (resized_length seed shape k) trees

theorem ofFn_along_length {α : Type*} {n k : Nat} (lengthEq : n = k)
    (trees : Fin k → α) (values : Fin n → α)
    (point : ∀ index, values index = trees (index.cast lengthEq)) :
    List.ofFn values = List.ofFn trees := by
  cases lengthEq
  refine ofFn_pointwise ?_
  intro index
  simpa [Fin.cast_refl] using point index

theorem bareSetNode_perm {Γ : List String} {sort element : String}
    (seed : (indexedSignature language).Op sort)
    (shape : bareCollection? seed.1.1 = some (.hashSet, element))
    {k : Nat} {left right : Fin k → Tree language (Γ, element)}
    (permuted : List.Perm (List.ofFn left) (List.ofFn right)) :
    TreeCong language (bareSetNode seed shape k left) (bareSetNode seed shape k right) := by
  let operator := resizedBare seed shape k
  let operatorShape := resized_shape seed shape k
  let lengthEq := resized_length seed shape k
  have elementPerm :
      List.Perm
        (List.ofFn fun index =>
          elementChild operator operatorShape (familyChildren operator operatorShape lengthEq left)
            index)
        (List.ofFn fun index =>
          elementChild operator operatorShape
            (familyChildren operator operatorShape lengthEq right) index) := by
    have rewrite (trees : Fin k → Tree language (Γ, element)) :
        List.ofFn (fun index =>
            elementChild operator operatorShape
              (familyChildren operator operatorShape lengthEq trees) index) =
          List.ofFn trees := by
      refine ofFn_along_length lengthEq trees _ ?_
      intro index
      unfold familyChildren
      exact elementChild_of_childFromElement operator operatorShape
        (fun direction => trees (direction.cast lengthEq)) index
    rw [rewrite left, rewrite right]
    exact permuted
  simpa [bareSetNode, familyNode, operator, operatorShape, lengthEq] using
    bare_setPerm operator operatorShape
      (familyChildren operator operatorShape lengthEq left)
      (familyChildren operator operatorShape lengthEq right) elementPerm

theorem bareSetNode_point {Γ : List String} {sort element : String}
    (seed : (indexedSignature language).Op sort)
    (shape : bareCollection? seed.1.1 = some (.hashSet, element))
    {k : Nat} {left right : Fin k → Tree language (Γ, element)}
    (steps : ∀ index, TreeCong language (left index) (right index)) :
    TreeCong language (bareSetNode seed shape k left) (bareSetNode seed shape k right) := by
  unfold bareSetNode familyNode
  apply treeCong_pointwise
  intro direction
  unfold familyChildren childFromElement
  apply treeCong_cast
    (collection_direction_lands (resizedBare seed shape k) direction
      (bare_direction (resizedBare seed shape k) (resized_shape seed shape k) direction)).symm
  exact steps (direction.cast (resized_length seed shape k))

theorem resized_resized {sort element : String}
    (seed : (indexedSignature language).Op sort)
    (shape : bareCollection? seed.1.1 = some (.hashSet, element))
    (k m : Nat) :
    resizedBare (resizedBare seed shape k) (resized_shape seed shape k) m =
      resizedBare seed shape m := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply headData_ext <;> rfl

theorem familyNode_of_eq {Γ : List String} {sort element : String} {kind : CollType}
    {op1 op2 : (indexedSignature language).Op sort}
    (opEq : op1 = op2)
    (shape1 : bareCollection? op1.1.1 = some (kind, element))
    {k : Nat}
    (len1 : ((indexedSignature language).arity op1).length = k)
    (trees : Fin k → Tree language (Γ, element)) :
    familyNode op1 shape1 len1 trees =
      familyNode op2 (opEq ▸ shape1) (opEq ▸ len1) trees := by
  subst opEq
  rfl

theorem familyNode_proofs_irrel {Γ : List String} {sort element : String} {kind : CollType}
    (operator : (indexedSignature language).Op sort)
    (shape1 shape2 : bareCollection? operator.1.1 = some (kind, element))
    {k : Nat}
    (len1 len2 : ((indexedSignature language).arity operator).length = k)
    (trees : Fin k → Tree language (Γ, element)) :
    familyNode operator shape1 len1 trees = familyNode operator shape2 len2 trees := by
  unfold familyNode familyChildren childFromElement
  apply congrArg
    (fun children =>
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator children)
  funext direction
  have indexEq : direction.cast len1 = direction.cast len2 := by
    apply Fin.ext
    rfl
  rw [indexEq]

theorem bareSetNode_dup {Γ : List String} {sort element : String}
    (seed : (indexedSignature language).Op sort)
    (shape : bareCollection? seed.1.1 = some (.hashSet, element))
    {n : Nat} (wide : 2 ≤ n) (trees : Fin n → Tree language (Γ, element))
    (copies : trees ⟨0, by omega⟩ = trees ⟨1, by omega⟩) :
    TreeCong language (bareSetNode seed shape n trees)
      (bareSetNode seed shape (n - 1)
        (fun index : Fin (n - 1) => trees ⟨index.val + 1, by have := index.isLt; omega⟩)) := by
  unfold bareSetNode
  have raw :=
    bare_setDeleteZero (resizedBare seed shape n) (resized_shape seed shape n)
      (resized_length seed shape n) wide trees copies
  have opEq := resized_resized seed shape n (n - 1)
  let shorter : Fin (n - 1) → Tree language (Γ, element) :=
    fun index => trees ⟨index.val + 1, by have := index.isLt; omega⟩
  have moved :=
    familyNode_of_eq opEq
      (resized_shape (resizedBare seed shape n) (resized_shape seed shape n) (n - 1))
      (resized_length (resizedBare seed shape n) (resized_shape seed shape n) (n - 1))
      shorter
  have irrel :=
    familyNode_proofs_irrel (resizedBare seed shape (n - 1))
      (opEq ▸
        resized_shape (resizedBare seed shape n) (resized_shape seed shape n) (n - 1))
      (resized_shape seed shape (n - 1))
      (opEq ▸
        resized_length (resizedBare seed shape n) (resized_shape seed shape n) (n - 1))
      (resized_length seed shape (n - 1))
      shorter
  exact TreeCong.trans raw (treeCong_of_eq (moved.trans irrel))

theorem bareSetNode_cast {Γ : List String} {sort element : String}
    (seed : (indexedSignature language).Op sort)
    (shape : bareCollection? seed.1.1 = some (.hashSet, element))
    {k : Nat} {left right : Fin k → Tree language (Γ, element)}
    (agree : ∀ index, left index = right index) :
    bareSetNode seed shape k left = bareSetNode seed shape k right := by
  unfold bareSetNode familyNode familyChildren
  apply congrArg
    (fun children =>
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        (resizedBare seed shape k) children)
  funext direction
  apply congrArg
  exact agree _

/-- Two families with the same set of pattern-congruence classes determine
congruent bare hash-set nodes. Deletion removes one of two congruent copies. -/
theorem setCover_engine {index : List String × String} {Γ : List String} {element : String}
    (node : ∀ k : Nat, (Fin k → Tree language (Γ, element)) → Tree language index)
    (node_perm : ∀ {k : Nat} {left right : Fin k → Tree language (Γ, element)},
      List.Perm (List.ofFn left) (List.ofFn right) →
        TreeCong language (node k left) (node k right))
    (node_point : ∀ {k : Nat} {left right : Fin k → Tree language (Γ, element)},
      (∀ index, TreeCong language (left index) (right index)) →
        TreeCong language (node k left) (node k right))
    (node_dup : ∀ {n : Nat} (wide : 2 ≤ n) (trees : Fin n → Tree language (Γ, element))
      (copies : trees ⟨0, by omega⟩ = trees ⟨1, by omega⟩),
      TreeCong language (node n trees)
        (node (n - 1) (fun index : Fin (n - 1) =>
          trees ⟨index.val + 1, by have := index.isLt; omega⟩)))
    (node_cast : ∀ {k : Nat} {left right : Fin k → Tree language (Γ, element)},
      (∀ index, left index = right index) → node k left = node k right) :
    ∀ (fuel : Nat) {n m : Nat}
      (left : Fin n → Tree language (Γ, element))
      (right : Fin m → Tree language (Γ, element)),
      n + m ≤ fuel →
      (∀ i : Fin n, ∃ j : Fin m,
        PatternCong (toPattern (left i)) (toPattern (right j))) →
      (∀ j : Fin m, ∃ i : Fin n,
        PatternCong (toPattern (left i)) (toPattern (right j))) →
      (∀ i : Fin n, ∀ other : Tree language (Γ, element),
        PatternCong (toPattern (left i)) (toPattern other) →
          TreeCong language (left i) other) →
      TreeCong language (node n left) (node m right) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n m left right bound _coverL _coverR _ih
      have nZero : n = 0 := by omega
      have mZero : m = 0 := by omega
      subst nZero
      subst mZero
      have agree : ∀ index, left index = right index := fun index => Fin.elim0 index
      rw [node_cast agree]
      exact TreeCong.refl _
  | succ fuel inductionHypothesis =>
      intro n m left right bound coverL coverR ih
      by_cases nZero : n = 0
      · subst nZero
        by_cases mZero : m = 0
        · subst mZero
          have agree : ∀ index, left index = right index := fun index => Fin.elim0 index
          rw [node_cast agree]
          exact TreeCong.refl _
        · have mPos : 0 < m := by omega
          exact Fin.elim0 (Classical.choose (coverR ⟨0, mPos⟩))
      · by_cases mZero : m = 0
        · subst mZero
          have nPos : 0 < n := by omega
          exact Fin.elim0 (Classical.choose (coverL ⟨0, nPos⟩))
        · let rightPaired : Prop :=
            ∃ j₁ j₂ : Fin m, j₁ ≠ j₂ ∧
              PatternCong (toPattern (right j₁)) (toPattern (right j₂))
          let leftPaired : Prop :=
            ∃ i₁ i₂ : Fin n, i₁ ≠ i₂ ∧
              PatternCong (toPattern (left i₁)) (toPattern (left i₂))
          cases Classical.em rightPaired with
          | inl paired =>
              let j₁ := Classical.choose paired
              let rest := Classical.choose_spec paired
              let j₂ := Classical.choose rest
              have spec := Classical.choose_spec rest
              obtain ⟨different, relatedPrints⟩ := spec
              have wide : 2 ≤ m := by
                by_contra small
                have mLe : m ≤ 1 := by omega
                have j₁Zero : j₁.val = 0 := by have := j₁.isLt; omega
                have j₂Zero : j₂.val = 0 := by have := j₂.isLt; omega
                apply different
                apply Fin.ext
                rw [j₁Zero, j₂Zero]
              obtain ⟨i₀, toJ₁⟩ := coverR j₁
              have toJ₂ : PatternCong (toPattern (left i₀)) (toPattern (right j₂)) :=
                PatternCong.trans toJ₁ relatedPrints
              have between : TreeCong language (right j₂) (right j₁) :=
                TreeCong.trans (TreeCong.symm (ih i₀ (right j₂) toJ₂))
                  (ih i₀ (right j₁) toJ₁)
              let right' : Fin m → Tree language (Γ, element) :=
                fun index => if index = j₂ then right j₁ else right index
              have pointRight : ∀ index, TreeCong language (right index) (right' index) := by
                intro index
                by_cases same : index = j₂
                · subst same
                  simp only [right', if_pos rfl]
                  exact between
                · simp only [right', if_neg same]
                  exact TreeCong.refl _
              have equalCopies : right' j₁ = right' j₂ := by
                simp only [right']
                split_ifs <;> rfl
              obtain ⟨σ, σZero, σOne⟩ := exists_place_two j₁ j₂ different wide
              let reordered : Fin m → Tree language (Γ, element) :=
                fun position => right' (σ position)
              have reorderedZero : reordered ⟨0, by omega⟩ = right' j₁ := by
                simp only [reordered]
                rw [σZero]
              have reorderedOne : reordered ⟨1, by omega⟩ = right' j₂ := by
                simp only [reordered]
                rw [σOne]
              have copies : reordered ⟨0, by omega⟩ = reordered ⟨1, by omega⟩ := by
                rw [reorderedZero, reorderedOne, equalCopies]
              have permReorder : List.Perm (List.ofFn reordered) (List.ofFn right') := by
                have asComp : List.ofFn reordered = List.ofFn (right' ∘ σ) :=
                  ofFn_pointwise fun _ => rfl
                rw [asComp]
                exact Equiv.Perm.ofFn_comp_perm σ right'
              let shorter : Fin (m - 1) → Tree language (Γ, element) :=
                fun index => reordered ⟨index.val + 1, by have := index.isLt; omega⟩
              have represent (index : Fin m) :
                  ∃ slot : Fin (m - 1), shorter slot = right' index := by
                let position := σ.symm index
                by_cases atZero : position = ⟨0, by omega⟩
                · refine ⟨⟨0, by omega⟩, ?_⟩
                  have indexAt : index = j₁ := by
                    have applied := σ.apply_symm_apply index
                    rw [show σ.symm index = ⟨0, by omega⟩ from atZero] at applied
                    rw [σZero] at applied
                    exact applied.symm
                  simp only [shorter, reorderedOne, equalCopies, indexAt]
                · have posNe : position.val ≠ 0 := by
                    intro zeroVal
                    apply atZero
                    exact Fin.ext zeroVal
                  refine ⟨⟨position.val - 1, by have := position.isLt; omega⟩, ?_⟩
                  simp only [shorter, reordered]
                  apply congrArg right'
                  apply Fin.ext
                  have posEq :
                      (⟨position.val - 1 + 1, by have := position.isLt; omega⟩ : Fin m) =
                        position := by
                    apply Fin.ext
                    show position.val - 1 + 1 = position.val
                    omega
                  have step1 :
                      (σ ⟨position.val - 1 + 1, by have := position.isLt; omega⟩).val =
                        (σ position).val :=
                    congrArg (fun item => (σ item).val) posEq
                  have step2 : (σ position).val = index.val :=
                    congrArg Fin.val (σ.apply_symm_apply index)
                  exact step1.trans step2
              have coverL' : ∀ i : Fin n, ∃ slot : Fin (m - 1),
                  PatternCong (toPattern (left i)) (toPattern (shorter slot)) := by
                intro i
                obtain ⟨j, step⟩ := coverL i
                have step' : PatternCong (toPattern (left i)) (toPattern (right' j)) := by
                  by_cases same : j = j₂
                  · subst same
                    simp only [right', if_pos rfl]
                    exact PatternCong.trans step (PatternCong.symm relatedPrints)
                  · simp only [right', if_neg same]
                    exact step
                obtain ⟨slot, slotEq⟩ := represent j
                refine ⟨slot, ?_⟩
                rw [slotEq]
                exact step'
              have coverR' : ∀ slot : Fin (m - 1), ∃ i : Fin n,
                  PatternCong (toPattern (left i)) (toPattern (shorter slot)) := by
                intro slot
                let source := σ ⟨slot.val + 1, by have := slot.isLt; omega⟩
                have asRight : shorter slot = right' source := by
                  simp [shorter, reordered, source]
                rw [asRight]
                obtain ⟨i, step⟩ := coverR source
                refine ⟨i, ?_⟩
                by_cases same : source = j₂
                · have stepCopy :
                      PatternCong (toPattern (left i)) (toPattern (right j₁)) := by
                    rw [same] at step
                    exact PatternCong.trans step (PatternCong.symm relatedPrints)
                  simpa [right', same] using stepCopy
                · simpa [right', same] using step
              have shorterBound : n + (m - 1) ≤ fuel := by omega
              have deleted :=
                TreeCong.trans (node_point pointRight)
                  (TreeCong.trans (TreeCong.symm (node_perm permReorder))
                    (node_dup wide reordered copies))
              exact TreeCong.trans
                (inductionHypothesis left shorter shorterBound coverL' coverR' ih)
                (TreeCong.symm deleted)
          | inr notRight =>
              cases Classical.em leftPaired with
              | inl paired =>
                  let i₁ := Classical.choose paired
                  let rest := Classical.choose_spec paired
                  let i₂ := Classical.choose rest
                  have spec := Classical.choose_spec rest
                  obtain ⟨different, relatedPrints⟩ := spec
                  have wide : 2 ≤ n := by
                    by_contra small
                    have nLe : n ≤ 1 := by omega
                    have i₁Zero : i₁.val = 0 := by have := i₁.isLt; omega
                    have i₂Zero : i₂.val = 0 := by have := i₂.isLt; omega
                    apply different
                    apply Fin.ext
                    rw [i₁Zero, i₂Zero]
                  have between : TreeCong language (left i₂) (left i₁) :=
                    TreeCong.trans (TreeCong.symm (ih i₁ (left i₂) relatedPrints))
                      (ih i₁ (left i₁) (PatternCong.refl _))
                  let left' : Fin n → Tree language (Γ, element) :=
                    fun index => if index = i₂ then left i₁ else left index
                  have pointLeft : ∀ index, TreeCong language (left index) (left' index) := by
                    intro index
                    by_cases same : index = i₂
                    · subst same
                      simp only [left', if_pos rfl]
                      exact between
                    · simp only [left', if_neg same]
                      exact TreeCong.refl _
                  have equalCopies : left' i₁ = left' i₂ := by
                    simp only [left']
                    split_ifs <;> rfl
                  obtain ⟨σ, σZero, σOne⟩ := exists_place_two i₁ i₂ different wide
                  let reordered : Fin n → Tree language (Γ, element) :=
                    fun position => left' (σ position)
                  have copies : reordered ⟨0, by omega⟩ = reordered ⟨1, by omega⟩ := by
                    simp only [reordered]
                    rw [σZero, σOne, equalCopies]
                  have permReorder : List.Perm (List.ofFn reordered) (List.ofFn left') := by
                    have asComp : List.ofFn reordered = List.ofFn (left' ∘ σ) :=
                      ofFn_pointwise fun _ => rfl
                    rw [asComp]
                    exact Equiv.Perm.ofFn_comp_perm σ left'
                  let shorter : Fin (n - 1) → Tree language (Γ, element) :=
                    fun index => reordered ⟨index.val + 1, by have := index.isLt; omega⟩
                  have ih' : ∀ index : Fin (n - 1), ∀ other : Tree language (Γ, element),
                      PatternCong (toPattern (shorter index)) (toPattern other) →
                        TreeCong language (shorter index) other := by
                    intro index other related
                    let source := σ ⟨index.val + 1, by have := index.isLt; omega⟩
                    have shorterEq : shorter index = left' source := by
                      simp [shorter, reordered, source]
                    rw [shorterEq]
                    by_cases same : source = i₂
                    · have relatedOld :
                          PatternCong (toPattern (left i₁)) (toPattern other) := by
                        rw [shorterEq] at related
                        simpa [left', same] using related
                      have step := ih i₁ other relatedOld
                      simpa [left', same] using step
                    · have relatedOld :
                          PatternCong (toPattern (left source)) (toPattern other) := by
                        rw [shorterEq] at related
                        simpa [left', same] using related
                      simpa [left', same] using ih source other relatedOld
                  have coverL' : ∀ index : Fin (n - 1), ∃ j : Fin m,
                      PatternCong (toPattern (shorter index)) (toPattern (right j)) := by
                    intro index
                    let source := σ ⟨index.val + 1, by have := index.isLt; omega⟩
                    have shorterEq : shorter index = left' source := by
                      simp [shorter, reordered, source]
                    by_cases same : source = i₂
                    · obtain ⟨j, step⟩ := coverL i₁
                      refine ⟨j, ?_⟩
                      rw [shorterEq]
                      simpa [left', same] using step
                    · obtain ⟨j, step⟩ := coverL source
                      refine ⟨j, ?_⟩
                      rw [shorterEq]
                      simpa [left', same] using step
                  have coverR' : ∀ j : Fin m, ∃ index : Fin (n - 1),
                      PatternCong (toPattern (shorter index)) (toPattern (right j)) := by
                    intro j
                    obtain ⟨i, step⟩ := coverR j
                    have step' : PatternCong (toPattern (left' i)) (toPattern (right j)) := by
                      by_cases same : i = i₂
                      · subst same
                        simp only [left', if_pos rfl]
                        exact PatternCong.trans relatedPrints step
                      · simp only [left', if_neg same]
                        exact step
                    let position := σ.symm i
                    by_cases atZero : position = ⟨0, by omega⟩
                    · refine ⟨⟨0, by omega⟩, ?_⟩
                      have iAt : i = i₁ := by
                        have applied := σ.apply_symm_apply i
                        rw [show σ.symm i = ⟨0, by omega⟩ from atZero] at applied
                        rw [σZero] at applied
                        exact applied.symm
                      have shorterHead : shorter ⟨0, by omega⟩ = left' i₁ := by
                        simp only [shorter, reordered]
                        rw [show (⟨1, by omega⟩ : Fin n) = ⟨0 + 1, by omega⟩ from rfl, σOne]
                        rw [equalCopies]
                      have stepHead :
                          PatternCong (toPattern (left' i₁)) (toPattern (right j)) := by
                        simpa [iAt] using step'
                      exact shorterHead.symm ▸ stepHead
                    · have posNe : position.val ≠ 0 := by
                        intro zeroVal
                        apply atZero
                        exact Fin.ext zeroVal
                      refine ⟨⟨position.val - 1, by have := position.isLt; omega⟩, ?_⟩
                      have shorterEq : shorter ⟨position.val - 1, by have := position.isLt; omega⟩ =
                          left' i := by
                        simp only [shorter, reordered]
                        apply congrArg left'
                        apply Fin.ext
                        have posEq :
                            (⟨position.val - 1 + 1, by have := position.isLt; omega⟩ : Fin n) =
                              position := by
                          apply Fin.ext
                          show position.val - 1 + 1 = position.val
                          omega
                        have step1 :
                            (σ ⟨position.val - 1 + 1, by have := position.isLt; omega⟩).val =
                              (σ position).val :=
                          congrArg (fun item => (σ item).val) posEq
                        have step2 : (σ position).val = i.val :=
                          congrArg Fin.val (σ.apply_symm_apply i)
                        exact step1.trans step2
                      rw [shorterEq]
                      exact step'
                  have shorterBound : (n - 1) + m ≤ fuel := by omega
                  have deleted :=
                    TreeCong.trans (node_point pointLeft)
                      (TreeCong.trans (TreeCong.symm (node_perm permReorder))
                        (node_dup wide reordered copies))
                  exact TreeCong.trans deleted
                    (inductionHypothesis shorter right shorterBound coverL' coverR' ih')
              | inr notLeft =>
                  let f : Fin m → Fin n := fun j => Classical.choose (coverR j)
                  have fSpec (j : Fin m) :
                      PatternCong (toPattern (left (f j))) (toPattern (right j)) :=
                    Classical.choose_spec (coverR j)
                  have fInj : Function.Injective f := by
                    intro j₁ j₂ same
                    by_contra different
                    apply notRight
                    refine ⟨j₁, j₂, different, ?_⟩
                    exact PatternCong.trans (PatternCong.symm (fSpec j₁))
                      (by simpa [same] using fSpec j₂)
                  let g : Fin n → Fin m := fun i => Classical.choose (coverL i)
                  have gSpec (i : Fin n) :
                      PatternCong (toPattern (left i)) (toPattern (right (g i))) :=
                    Classical.choose_spec (coverL i)
                  have gInj : Function.Injective g := by
                    intro i₁ i₂ same
                    by_contra different
                    apply notLeft
                    refine ⟨i₁, i₂, different, ?_⟩
                    exact PatternCong.trans (gSpec i₁)
                      (PatternCong.symm (by simpa [same] using gSpec i₂))
                  have mn : m ≤ n := Fin.le_of_injective f fInj
                  have nm : n ≤ m := Fin.le_of_injective g gInj
                  have eqLen : n = m := by omega
                  subst eqLen
                  have fBij : Function.Bijective f :=
                    (Finite.injective_iff_bijective (f := f)).mp fInj
                  let e := Equiv.ofBijective f fBij
                  let aligned : Fin n → Tree language (Γ, element) :=
                    fun index => right (e.symm index)
                  have steps : ∀ index, TreeCong language (left index) (aligned index) := by
                    intro index
                    have source : f (e.symm index) = index := by
                      have applied : e (e.symm index) = index := e.apply_symm_apply index
                      change (Equiv.ofBijective f fBij) (e.symm index) = index at applied
                      rwa [Equiv.ofBijective_apply] at applied
                    have related := fSpec (e.symm index)
                    rw [source] at related
                    simpa [aligned] using ih index (right (e.symm index)) related
                  have permAligned :
                      List.Perm (List.ofFn aligned) (List.ofFn right) := by
                    have asComp : List.ofFn aligned = List.ofFn (right ∘ e.symm) :=
                      ofFn_pointwise fun _ => rfl
                    rw [asComp]
                    exact Equiv.Perm.ofFn_comp_perm e.symm right
                  exact TreeCong.trans (node_point steps) (node_perm permAligned)

theorem resized_eq_self {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (.hashSet, element)) :
    resizedBare operator shape ((indexedSignature language).arity operator).length =
      operator := by
  obtain ⟨countsOne, lengthsOne⟩ := bare_head operator shape
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply headData_ext
  · exact countsOne.symm
  · exact lengthsOne.symm

theorem resized_eq_target {sort element : String}
    (seed target : (indexedSignature language).Op sort)
    (seedShape : bareCollection? seed.1.1 = some (.hashSet, element))
    (targetShape : bareCollection? target.1.1 = some (.hashSet, element))
    (uniqueBare : UniqueBare language)
    {m : Nat}
    (targetLength : ((indexedSignature language).arity target).length = m) :
    resizedBare seed seedShape m = target :=
  bare_operator_eq (resizedBare seed seedShape m) target
    (resized_shape seed seedShape m) targetShape uniqueBare
    (by rw [resized_length, targetLength])

theorem bareSetNode_original {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (shape : bareCollection? operator.1.1 = some (.hashSet, element))
    (children : Child language Γ sort operator) :
    bareSetNode operator shape ((indexedSignature language).arity operator).length
        (fun direction => elementChild operator shape children direction) =
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator children := by
  have opEq := resized_eq_self operator shape
  unfold bareSetNode
  refine (familyNode_of_eq (k := ((indexedSignature language).arity operator).length) opEq
      (resized_shape operator shape ((indexedSignature language).arity operator).length)
      (resized_length operator shape ((indexedSignature language).arity operator).length)
      (fun direction => elementChild operator shape children direction)).trans ?_
  refine (familyNode_proofs_irrel (k := ((indexedSignature language).arity operator).length)
      operator
      (opEq ▸ resized_shape operator shape
        ((indexedSignature language).arity operator).length)
      shape
      rfl
      rfl
      (fun direction => elementChild operator shape children direction)).trans ?_
  unfold familyNode familyChildren
  apply congrArg
    (fun continuation =>
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator continuation)
  funext direction
  have indexEq : direction.cast (Eq.refl _) = direction := by
    apply Fin.ext
    rfl
  rw [indexEq]
  exact childFromElement_elementChild operator shape children direction

/-- A bare hash set reflects the pattern congruence as the tree congruence. -/
theorem setBare_treeCong
    (_labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort element : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftShape : bareCollection? leftOp.1.1 = some (.hashSet, element))
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightShape : bareCollection? rightOp.1.1 = some (.hashSet, element))
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (related : PatternCong
      (nodeOf leftOp fun direction => toPattern (leftChildren direction))
      (nodeOf rightOp fun direction => toPattern (rightChildren direction))) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  simp only [nodeOf, leftShape, rightShape] at related
  obtain ⟨_, _, leftEq, rightEq, elementsRel⟩ :=
    patternCong_set_elements related
      (Or.inl ⟨List.ofFn fun direction => toPattern (leftChildren direction), rfl⟩)
  simp only [Pattern.collection.injEq] at leftEq rightEq
  obtain ⟨_, leftList, _⟩ := leftEq
  obtain ⟨_, rightList, _⟩ := rightEq
  subst leftList
  subst rightList
  let n := ((indexedSignature language).arity leftOp).length
  let m := ((indexedSignature language).arity rightOp).length
  let leftTrees : Fin n → Tree language (Γ, element) :=
    fun direction => elementChild leftOp leftShape leftChildren direction
  let rightTrees : Fin m → Tree language (Γ, element) :=
    fun direction => elementChild rightOp rightShape rightChildren direction
  have covers := setElementRel_both elementsRel
  have leftPrinted :
      List.ofFn (fun direction => toPattern (leftTrees direction)) =
        List.ofFn (fun direction => toPattern (leftChildren direction)) := by
    refine ofFn_pointwise ?_
    intro direction
    exact elementChild_toPattern leftOp leftShape leftChildren direction
  have rightPrinted :
      List.ofFn (fun direction => toPattern (rightTrees direction)) =
        List.ofFn (fun direction => toPattern (rightChildren direction)) := by
    refine ofFn_pointwise ?_
    intro direction
    exact elementChild_toPattern rightOp rightShape rightChildren direction
  have coverL : ∀ i : Fin n, ∃ j : Fin m,
      PatternCong (toPattern (leftTrees i)) (toPattern (rightTrees j)) := by
    intro i
    have mem : toPattern (leftTrees i) ∈
        List.ofFn fun direction => toPattern (leftChildren direction) := by
      rw [← leftPrinted]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨image, imageMem, step⟩ := covers.1 (toPattern (leftTrees i)) mem
    have imageMem' : image ∈ List.ofFn fun direction => toPattern (rightTrees direction) := by
      rw [rightPrinted]
      exact imageMem
    obtain ⟨j, imageEq⟩ := List.mem_ofFn.mp imageMem'
    exact ⟨j, by simpa [imageEq] using step⟩
  have coverR : ∀ j : Fin m, ∃ i : Fin n,
      PatternCong (toPattern (leftTrees i)) (toPattern (rightTrees j)) := by
    intro j
    have mem : toPattern (rightTrees j) ∈
        List.ofFn fun direction => toPattern (rightChildren direction) := by
      rw [← rightPrinted]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    obtain ⟨image, imageMem, step⟩ := covers.2 (toPattern (rightTrees j)) mem
    have imageMem' : image ∈ List.ofFn fun direction => toPattern (leftTrees direction) := by
      rw [leftPrinted]
      exact imageMem
    obtain ⟨i, imageEq⟩ := List.mem_ofFn.mp imageMem'
    exact ⟨i, by simpa [imageEq] using step⟩
  have ihTrees : ∀ i : Fin n, ∀ other : Tree language (Γ, element),
      PatternCong (toPattern (leftTrees i)) (toPattern other) →
        TreeCong language (leftTrees i) other := by
    intro i other relatedTrees
    let otherChild := childFromElement leftOp leftShape i other
    have relatedChild :
        PatternCong (toPattern (leftChildren i)) (toPattern otherChild) := by
      rw [← elementChild_toPattern leftOp leftShape leftChildren i,
        childFromElement_toPattern leftOp leftShape i other]
      exact relatedTrees
    have step := ih i otherChild relatedChild
    have transported :
        TreeCong language
          (childFromElement leftOp leftShape i (leftTrees i))
          (childFromElement leftOp leftShape i other) := by
      rw [← childFromElement_elementChild leftOp leftShape leftChildren i] at step
      exact step
    exact treeCong_of_cast
      (collection_direction_lands leftOp i (bare_direction leftOp leftShape i)).symm
      transported
  have compared :=
    setCover_engine (bareSetNode leftOp leftShape)
      (fun {_k} {_left} {_right} permuted =>
        bareSetNode_perm leftOp leftShape permuted)
      (fun {_k} {_left} {_right} steps =>
        bareSetNode_point leftOp leftShape steps)
      (fun {_n} wide trees copies =>
        bareSetNode_dup leftOp leftShape wide trees copies)
      (fun {_k} {_left} {_right} agree =>
        bareSetNode_cast leftOp leftShape agree)
      (n + m) leftTrees rightTrees (Nat.le_refl _) coverL coverR ihTrees
  have leftOriginal := bareSetNode_original leftOp leftShape leftChildren
  have rightResized : resizedBare leftOp leftShape m = rightOp :=
    resized_eq_target leftOp rightOp leftShape rightShape uniqueBare rfl
  have rightOriginal :
      bareSetNode leftOp leftShape m rightTrees =
        IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          rightOp rightChildren := by
    unfold bareSetNode
    refine (familyNode_of_eq (k := m) rightResized
        (resized_shape leftOp leftShape m)
        (resized_length leftOp leftShape m) rightTrees).trans ?_
    refine (familyNode_proofs_irrel (k := m) rightOp
        (rightResized ▸ resized_shape leftOp leftShape m) rightShape
        rfl rfl rightTrees).trans ?_
    unfold familyNode familyChildren
    apply congrArg
      (fun continuation =>
        IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          rightOp continuation)
    funext direction
    have indexEq : direction.cast (Eq.refl _) = direction := by
      apply Fin.ext
      rfl
    rw [indexEq]
    exact childFromElement_elementChild rightOp rightShape rightChildren direction
  rw [← leftOriginal, ← rightOriginal]
  exact compared

/-- A multi-lambda stays a multi-lambda of the same arity and names. -/
theorem patternCong_multi_body {left right : Pattern} (related : PatternCong left right)
    (shaped : (∃ arity binders body, left = .multiLambda arity binders body) ∨
      (∃ arity binders body, right = .multiLambda arity binders body)) :
    ∃ arity binders body body',
      left = .multiLambda arity binders body ∧
        right = .multiLambda arity binders body' ∧ PatternCong body body' := by
  induction related with
  | refl pattern =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨arity, binders, body, equal⟩ := existsLeft
          exact ⟨arity, binders, body, body, equal, equal, PatternCong.refl body⟩
      | inr existsRight =>
          obtain ⟨arity, binders, body, equal⟩ := existsRight
          exact ⟨arity, binders, body, body, equal, equal, PatternCong.refl body⟩
  | symm _ inductionHypothesis =>
      obtain ⟨arity, binders, body, body', rightEq, leftEq, step⟩ :=
        inductionHypothesis shaped.symm
      exact ⟨arity, binders, body', body, leftEq, rightEq, PatternCong.symm step⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨arity, binders, body, midBody, leftEq, midEq, stepLeft⟩ :=
            inductionHypothesis (Or.inl existsLeft)
          obtain ⟨arity', binders', midBody', rightBody, midEq', rightEq, stepRight⟩ :=
            inductionHypothesis' (Or.inl ⟨arity, binders, midBody, midEq⟩)
          have sameMid := midEq.symm.trans midEq'
          simp only [Pattern.multiLambda.injEq] at sameMid
          obtain ⟨arities, names, bodies⟩ := sameMid
          subst arities
          subst names
          subst bodies
          exact ⟨arity, binders, body, rightBody, leftEq, rightEq,
            PatternCong.trans stepLeft stepRight⟩
      | inr existsRight =>
          obtain ⟨arity, binders, midBody, rightBody, midEq, rightEq, stepRight⟩ :=
            inductionHypothesis' (Or.inr existsRight)
          obtain ⟨arity', binders', body, midBody', leftEq, midEq', stepLeft⟩ :=
            inductionHypothesis (Or.inr ⟨arity, binders, midBody, midEq⟩)
          have sameMid := midEq'.symm.trans midEq
          simp only [Pattern.multiLambda.injEq] at sameMid
          obtain ⟨arities, names, bodies⟩ := sameMid
          subst arities
          subst names
          subst bodies
          exact ⟨arity', binders', body, rightBody, leftEq, rightEq,
            PatternCong.trans stepLeft stepRight⟩
  | bagPerm _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, _, equal⟩ := existsRight; cases equal
  | setPerm _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, _, equal⟩ := existsRight; cases equal
  | setDup =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, _, equal⟩ := existsRight; cases equal
  | applyAt _ _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, _, equal⟩ := existsRight; cases equal
  | lambdaAt _ _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, _, equal⟩ := existsRight; cases equal
  | multiLambdaAt step _ =>
      expose_names
      exact ⟨arity, binders, left_1, right_1, rfl, rfl, step⟩
  | collectionAt _ _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, _, equal⟩ := existsRight; cases equal

/-- The body of one printed argument, read back out of the pattern congruence.
A parameter outside the two multi-binder shapes contributes no count. -/
theorem printArgument_body (parameter : TermParam) (count count' : Nat)
    (left right : Pattern)
    (related : PatternCong (printArgument parameter count left)
      (printArgument parameter count' right))
    (countZero : (multiBase? parameter).isNone → count = 0)
    (countZero' : (multiBase? parameter).isNone → count' = 0) :
    count = count' ∧ PatternCong left right := by
  have peelMulti
      (multiRelated :
        PatternCong (.multiLambda count [] left) (.multiLambda count' [] right)) :
      count = count' ∧ PatternCong left right := by
    obtain ⟨_arity, _names, body, body', leftEq, rightEq, step⟩ :=
      patternCong_multi_body multiRelated (Or.inl ⟨count, [], left, rfl⟩)
    simp only [Pattern.multiLambda.injEq] at leftEq rightEq
    obtain ⟨countEq, _namesEq, bodyEq⟩ := leftEq
    obtain ⟨countEq', _namesEq', bodyEq'⟩ := rightEq
    subst bodyEq
    subst bodyEq'
    exact ⟨countEq.trans countEq'.symm, step⟩
  have peelNone (notMulti : (multiBase? parameter).isNone) : count = 0 ∧ count' = 0 :=
    ⟨countZero notMulti, countZero' notMulti⟩
  have peelId (notMulti : (multiBase? parameter).isNone)
      (asLeft : printArgument parameter count left = left)
      (asRight : printArgument parameter count' right = right) :
      count = count' ∧ PatternCong left right := by
    obtain ⟨countEq, countEq'⟩ := peelNone notMulti
    refine ⟨countEq.trans countEq'.symm, ?_⟩
    rw [asLeft, asRight] at related
    exact related
  have peelOne (notMulti : (multiBase? parameter).isNone)
      (asLeft : printArgument parameter count left = .lambda none left)
      (asRight : printArgument parameter count' right = .lambda none right) :
      count = count' ∧ PatternCong left right := by
    obtain ⟨countEq, countEq'⟩ := peelNone notMulti
    refine ⟨countEq.trans countEq'.symm, ?_⟩
    rw [asLeft, asRight] at related
    obtain ⟨_, body, body', leftEq, rightEq, step⟩ :=
      patternCong_lambda_body related (Or.inl ⟨none, left, rfl⟩)
    simp only [Pattern.lambda.injEq] at leftEq rightEq
    obtain ⟨_, leftBody⟩ := leftEq
    obtain ⟨_, rightBody⟩ := rightEq
    subst leftBody
    subst rightBody
    exact step
  cases parameter with
  | simple _ type =>
      cases type with
      | base _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
      | arrow _ _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
      | multiBinder _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
      | collection _ _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
  | abstractionNamed _ _ type =>
      cases type with
      | base _ =>
          exact peelOne (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
      | arrow domain codomain =>
          cases domain with
          | base _ =>
              cases codomain with
              | base _ =>
                  exact peelOne (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
              | arrow _ _ =>
                  exact peelId (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
              | multiBinder _ =>
                  exact peelId (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
              | collection _ _ =>
                  exact peelId (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
          | arrow _ _ =>
              exact peelId (by simp [multiBase?])
                (by simp [printArgument, slotBinders, wrapBinders])
                (by simp [printArgument, slotBinders, wrapBinders])
          | multiBinder _ =>
              exact peelId (by simp [multiBase?])
                (by simp [printArgument, slotBinders, wrapBinders])
                (by simp [printArgument, slotBinders, wrapBinders])
          | collection _ _ =>
              exact peelId (by simp [multiBase?])
                (by simp [printArgument, slotBinders, wrapBinders])
                (by simp [printArgument, slotBinders, wrapBinders])
      | multiBinder _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
      | collection _ _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simp only [printArgument] at related
          exact peelMulti related
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              cases inner with
              | base _ =>
                  cases codomain with
                  | base _ =>
                      simp only [printArgument] at related
                      exact peelMulti related
                  | arrow _ _ =>
                      exact peelId (by simp [multiBase?])
                        (by simp [printArgument, slotBinders, wrapBinders])
                        (by simp [printArgument, slotBinders, wrapBinders])
                  | multiBinder _ =>
                      exact peelId (by simp [multiBase?])
                        (by simp [printArgument, slotBinders, wrapBinders])
                        (by simp [printArgument, slotBinders, wrapBinders])
                  | collection _ _ =>
                      exact peelId (by simp [multiBase?])
                        (by simp [printArgument, slotBinders, wrapBinders])
                        (by simp [printArgument, slotBinders, wrapBinders])
              | arrow _ _ =>
                  exact peelId (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
              | multiBinder _ =>
                  exact peelId (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
              | collection _ _ =>
                  exact peelId (by simp [multiBase?])
                    (by simp [printArgument, slotBinders, wrapBinders])
                    (by simp [printArgument, slotBinders, wrapBinders])
          | base _ =>
              exact peelId (by simp [multiBase?])
                (by simp [printArgument, slotBinders, wrapBinders])
                (by simp [printArgument, slotBinders, wrapBinders])
          | arrow _ _ =>
              exact peelId (by simp [multiBase?])
                (by simp [printArgument, slotBinders, wrapBinders])
                (by simp [printArgument, slotBinders, wrapBinders])
          | collection _ _ =>
              exact peelId (by simp [multiBase?])
                (by simp [printArgument, slotBinders, wrapBinders])
                (by simp [printArgument, slotBinders, wrapBinders])
      | multiBinder _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])
      | collection _ _ =>
          exact peelId (by simp [multiBase?])
            (by simp [printArgument, slotBinders, wrapBinders])
            (by simp [printArgument, slotBinders, wrapBinders])

/-- Binders and vectors only. A bag or a set needs a quotient step. -/
def paramsPlain : List TermParam → Bool
  | [] => true
  | parameter :: parameters =>
      match baseCollection? parameter with
      | some (.hashBag, _) => false
      | some (.hashSet, _) => false
      | _ => paramsPlain parameters

/-- Assembled arguments of a binder-or-vector head determine the counts, the
lengths, and every printed direction. -/
theorem plain_assemble {total total' : Nat}
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
    (plain : paramsPlain parameters = true)
    (related : List.Forall₂ PatternCong
      (assemblePrinted printed offset parameters counts lengths)
      (assemblePrinted printed' offset parameters counts' lengths')) :
    counts = counts' ∧ lengths = lengths' ∧
      ∀ index : Nat, index < slotCount parameters counts lengths →
        PatternCong (nthPrinted printed (offset + index))
          (nthPrinted printed' (offset + index)) := by
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
                          cases kind with
                          | hashBag =>
                              simp [paramsPlain, reading] at plain
                          | hashSet =>
                              simp [paramsPlain, reading] at plain
                          | vec =>
                              have tailPlain : paramsPlain parameters = true := by
                                simp [paramsPlain, reading] at plain
                                exact plain
                              simp only [assemblePrinted, reading] at related
                              cases related with
                              | cons headRel tailRel =>
                                  obtain ⟨leftElements, rightElements, leftEq, rightEq, pointwise⟩ :=
                                    patternCong_vec_elements headRel
                                      (Or.inl ⟨List.ofFn fun index : Fin length =>
                                        nthPrinted printed (offset + index.val), rfl⟩)
                                  simp only [Pattern.collection.injEq] at leftEq rightEq
                                  obtain ⟨_, leftList, _⟩ := leftEq
                                  obtain ⟨_, rightList, _⟩ := rightEq
                                  subst leftList
                                  subst rightList
                                  have lengthEq : length = length' := by
                                    simpa [List.length_ofFn] using
                                      List.Forall₂.length_eq pointwise
                                  subst lengthEq
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
                                    inductionHypothesis (offset + length) counts lengths counts'
                                      lengths' tailCountsLength tailLengthsLength tailCountsLength'
                                      tailLengthsLength' tailCountsFixed tailCountsFixed'
                                      tailLengthsFixed tailLengthsFixed' tailPlain tailRel
                                  refine ⟨?_, ?_, ?_⟩
                                  · rw [countEq, countsTailEq]
                                  · rw [lengthsTailEq]
                                  · intro index indexBound
                                    have width :
                                        slotCount (parameter :: parameters) (count :: counts)
                                            (length :: lengths) =
                                          length + slotCount parameters counts lengths := by
                                      simp [slotCount, directionsOf, reading]
                                    rw [width] at indexBound
                                    by_cases below : index < length
                                    · have hx :
                                          index <
                                            (List.ofFn fun i : Fin length =>
                                              nthPrinted printed (offset + i.val)).length :=
                                        List.length_ofFn.symm ▸ below
                                      have hy :
                                          index <
                                            (List.ofFn fun i : Fin length =>
                                              nthPrinted printed' (offset + i.val)).length :=
                                        List.length_ofFn.symm ▸ below
                                      have atPoint :=
                                        (List.forall₂_iff_get.mp pointwise).2 index hx hy
                                      rw [ofFn_get_apply
                                          (fun i : Fin length =>
                                            nthPrinted printed (offset + i.val))
                                          ⟨index, below⟩,
                                        ofFn_get_apply
                                          (fun i : Fin length =>
                                            nthPrinted printed' (offset + i.val))
                                          ⟨index, below⟩] at atPoint
                                      simpa using atPoint
                                    · have tailBound :
                                          index - length <
                                            slotCount parameters counts lengths := by
                                        omega
                                      have shifted := tailAgree (index - length) tailBound
                                      have reassoc :
                                          (offset + length) + (index - length) =
                                            offset + index := by omega
                                      rw [reassoc] at shifted
                                      exact shifted
                      | none =>
                          have tailPlain : paramsPlain parameters = true := by
                            simp [paramsPlain, reading] at plain
                            exact plain
                          simp only [assemblePrinted, reading] at related
                          cases related with
                          | cons headRel tailRel =>
                              have countCanonical :
                                  (multiBase? parameter).isNone → count = 0 := by
                                intro notMulti
                                have fixed := countsFixed 0 (by simpa [List.getD] using notMulti)
                                simpa [List.getD] using fixed
                              have countCanonical' :
                                  (multiBase? parameter).isNone → count' = 0 := by
                                intro notMulti
                                have fixed := countsFixed' 0 (by simpa [List.getD] using notMulti)
                                simpa [List.getD] using fixed
                              obtain ⟨countEq, bodyCong⟩ :=
                                printArgument_body parameter count count'
                                  (nthPrinted printed offset) (nthPrinted printed' offset)
                                  headRel countCanonical countCanonical'
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
                                  tailLengthsLength' tailCountsFixed tailCountsFixed'
                                  tailLengthsFixed tailLengthsFixed' tailPlain tailRel
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
                                | zero => simpa [Nat.zero_add] using bodyCong
                                | succ index =>
                                    have tailBound :
                                        index < slotCount parameters counts lengths := by omega
                                    have shifted := tailAgree index tailBound
                                    have reassoc :
                                        (offset + 1) + index = offset + index.succ := by omega
                                    rw [reassoc] at shifted
                                    exact shifted

/-- A parameter list contains a hash set. -/
def paramsHasSet : List TermParam → Bool
  | [] => false
  | parameter :: parameters =>
      match baseCollection? parameter with
      | some (.hashSet, _) => true
      | _ => paramsHasSet parameters

/-- A parameter whose collection is a hash set. Binder counts ignore it, and its
length is the datum a set deletion may change. -/
def isHashSetParam (parameter : TermParam) : Bool :=
  match baseCollection? parameter with
  | some (.hashSet, _) => true
  | _ => false

theorem paramsHasSet_get {parameters : List TermParam} {index : Nat} {element : String}
    (bound : index < parameters.length)
    (shape : baseCollection? (parameters.get ⟨index, bound⟩) = some (.hashSet, element)) :
    paramsHasSet parameters = true := by
  induction parameters generalizing index with
  | nil => simp at bound
  | cons parameter parameters inductionHypothesis =>
      cases index with
      | zero =>
          have shapeHead : baseCollection? parameter = some (.hashSet, element) := by
            simpa [List.get_eq_getElem, List.getElem_cons_zero] using shape
          simp [paramsHasSet, shapeHead]
      | succ index =>
          have tailBound : index < parameters.length := by
            simp at bound
            omega
          have tailShape :
              baseCollection? (parameters.get ⟨index, tailBound⟩) =
                some (.hashSet, element) := by
            simpa [List.get_cons_succ] using shape
          have tail := inductionHypothesis tailBound tailShape
          cases reading : baseCollection? parameter with
          | some packed =>
              obtain ⟨kind, _sort⟩ := packed
              cases kind with
              | hashSet => simp [paramsHasSet, reading]
              | hashBag => simpa [paramsHasSet, reading] using tail
              | vec => simpa [paramsHasSet, reading] using tail
          | none => simpa [paramsHasSet, reading] using tail

theorem assemblePrinted_length {total : Nat} (printed : Fin total → Pattern) (offset : Nat)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length) :
    (assemblePrinted printed offset parameters counts lengths).length = parameters.length := by
  induction parameters generalizing counts lengths offset with
  | nil =>
      cases counts <;> cases lengths <;> simp [assemblePrinted]
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp at lengthsLength
                omega
              cases reading : baseCollection? parameter with
              | some _ =>
                  simp only [assemblePrinted, reading, List.length_cons]
                  exact congrArg Nat.succ
                    (inductionHypothesis (offset + length) counts lengths tailCounts tailLengths)
              | none =>
                  simp only [assemblePrinted, reading, List.length_cons]
                  exact congrArg Nat.succ
                    (inductionHypothesis (offset + 1) counts lengths tailCounts tailLengths)

/-- How many directions the first `done` parameters occupy. -/
def takenSlots (parameters : List TermParam) (counts lengths : List Nat) (done : Nat) : Nat :=
  slotCount (parameters.take done) (counts.take done) (lengths.take done)

theorem takenSlots_zero (parameters : List TermParam) (counts lengths : List Nat) :
    takenSlots parameters counts lengths 0 = 0 := by
  simp [takenSlots, List.take_zero, slotCount]

theorem takenSlots_all (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length) :
    takenSlots parameters counts lengths parameters.length =
      slotCount parameters counts lengths := by
  simp only [takenSlots]
  have countsTake : counts.take parameters.length = counts := by
    rw [← countsLength, List.take_length]
  have lengthsTake : lengths.take parameters.length = lengths := by
    rw [← lengthsLength, List.take_length]
  rw [countsTake, lengthsTake, List.take_length]

theorem takenSlots_step (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (done : Nat) (doneBound : done < parameters.length) :
    takenSlots parameters counts lengths (done + 1) =
      takenSlots parameters counts lengths done +
        directionsOf (parameters.get ⟨done, doneBound⟩) (counts.getD done 0)
          (lengths.getD done 0) := by
  induction parameters generalizing counts lengths done with
  | nil => simp at doneBound
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp at lengthsLength
                omega
              cases done with
              | zero =>
                  simp [takenSlots, List.take_zero, slotCount]
              | succ done =>
                  have tailBound : done < parameters.length := by
                    simp at doneBound
                    omega
                  have tail :=
                    inductionHypothesis counts lengths tailCounts tailLengths done tailBound
                  simp only [takenSlots, List.take_succ_cons, slotCount, List.get_cons_succ,
                    List.getD_cons_succ] at tail ⊢
                  omega

theorem takenSlots_succ (parameter : TermParam) (parameters : List TermParam)
    (count : Nat) (counts : List Nat) (length : Nat) (lengths : List Nat) (done : Nat) :
    takenSlots (parameter :: parameters) (count :: counts) (length :: lengths) (done + 1) =
      directionsOf parameter count length +
        takenSlots parameters counts lengths done := by
  simp [takenSlots, List.take_succ_cons, slotCount]

/-- Binder counts and non-set lengths are fixed by the assembled arguments. -/
theorem recover_no_set {total total' : Nat}
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
    (noSet : paramsHasSet parameters = false)
    (related : List.Forall₂ PatternCong
      (assemblePrinted printed offset parameters counts lengths)
      (assemblePrinted printed' offset parameters counts' lengths')) :
    counts = counts' ∧ lengths = lengths' := by
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
                  | nil => exact ⟨rfl, rfl⟩
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
                        simpa [List.getD] using
                          countsFixed (index + 1) (by simpa [List.getD] using hypothesis)
                      have tailCountsFixed' : ∀ index : Nat,
                          (multiBase? (parameters.getD index missingParameter)).isNone →
                            counts'.getD index 0 = 0 := by
                        intro index hypothesis
                        simpa [List.getD] using
                          countsFixed' (index + 1) (by simpa [List.getD] using hypothesis)
                      have tailLengthsFixed : ∀ index : Nat,
                          (baseCollection? (parameters.getD index missingParameter)).isNone →
                            lengths.getD index 0 = 0 := by
                        intro index hypothesis
                        simpa [List.getD] using
                          lengthsFixed (index + 1) (by simpa [List.getD] using hypothesis)
                      have tailLengthsFixed' : ∀ index : Nat,
                          (baseCollection? (parameters.getD index missingParameter)).isNone →
                            lengths'.getD index 0 = 0 := by
                        intro index hypothesis
                        simpa [List.getD] using
                          lengthsFixed' (index + 1) (by simpa [List.getD] using hypothesis)
                      cases reading : baseCollection? parameter with
                      | some packed =>
                          obtain ⟨kind, _element⟩ := packed
                          cases kind with
                          | hashSet => simp [paramsHasSet, reading] at noSet
                          | hashBag =>
                              have tailNoSet : paramsHasSet parameters = false := by
                                simpa [paramsHasSet, reading] using noSet
                              simp only [assemblePrinted, reading] at related
                              cases related with
                              | cons headRel tailRel =>
                                  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, elementsRel⟩ :=
                                    patternCong_bag_elements headRel
                                      (Or.inl ⟨List.ofFn fun index : Fin length =>
                                        nthPrinted printed (offset + index.val), rfl⟩)
                                  simp only [Pattern.collection.injEq] at leftEq rightEq
                                  obtain ⟨_, leftList, _⟩ := leftEq
                                  obtain ⟨_, rightList, _⟩ := rightEq
                                  subst leftList
                                  subst rightList
                                  have lengthEq : length = length' := by
                                    simpa [List.length_ofFn] using bagElementRel_length elementsRel
                                  subst lengthEq
                                  have countEq : count = count' := by
                                    have countZero : count = 0 := by
                                      simpa [List.getD] using countsFixed 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    have countZero' : count' = 0 := by
                                      simpa [List.getD] using countsFixed' 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    rw [countZero, countZero']
                                  obtain ⟨countsTailEq, lengthsTailEq⟩ :=
                                    inductionHypothesis (offset + length) counts lengths counts'
                                      lengths' tailCountsLength tailLengthsLength tailCountsLength'
                                      tailLengthsLength' tailCountsFixed tailCountsFixed'
                                      tailLengthsFixed tailLengthsFixed' tailNoSet tailRel
                                  exact ⟨by rw [countEq, countsTailEq], by rw [lengthsTailEq]⟩
                          | vec =>
                              have tailNoSet : paramsHasSet parameters = false := by
                                simpa [paramsHasSet, reading] using noSet
                              simp only [assemblePrinted, reading] at related
                              cases related with
                              | cons headRel tailRel =>
                                  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, pointwise⟩ :=
                                    patternCong_vec_elements headRel
                                      (Or.inl ⟨List.ofFn fun index : Fin length =>
                                        nthPrinted printed (offset + index.val), rfl⟩)
                                  simp only [Pattern.collection.injEq] at leftEq rightEq
                                  obtain ⟨_, leftList, _⟩ := leftEq
                                  obtain ⟨_, rightList, _⟩ := rightEq
                                  subst leftList
                                  subst rightList
                                  have lengthEq : length = length' := by
                                    simpa [List.length_ofFn] using
                                      List.Forall₂.length_eq pointwise
                                  subst lengthEq
                                  have countEq : count = count' := by
                                    have countZero : count = 0 := by
                                      simpa [List.getD] using countsFixed 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    have countZero' : count' = 0 := by
                                      simpa [List.getD] using countsFixed' 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    rw [countZero, countZero']
                                  obtain ⟨countsTailEq, lengthsTailEq⟩ :=
                                    inductionHypothesis (offset + length) counts lengths counts'
                                      lengths' tailCountsLength tailLengthsLength tailCountsLength'
                                      tailLengthsLength' tailCountsFixed tailCountsFixed'
                                      tailLengthsFixed tailLengthsFixed' tailNoSet tailRel
                                  exact ⟨by rw [countEq, countsTailEq], by rw [lengthsTailEq]⟩
                      | none =>
                          have tailNoSet : paramsHasSet parameters = false := by
                            simpa [paramsHasSet, reading] using noSet
                          simp only [assemblePrinted, reading] at related
                          cases related with
                          | cons headRel tailRel =>
                              obtain ⟨countEq, _body⟩ :=
                                printArgument_body parameter count count'
                                  (nthPrinted printed offset) (nthPrinted printed' offset) headRel
                                  (by
                                    intro notMulti
                                    simpa [List.getD] using
                                      countsFixed 0 (by simpa [List.getD] using notMulti))
                                  (by
                                    intro notMulti
                                    simpa [List.getD] using
                                      countsFixed' 0 (by simpa [List.getD] using notMulti))
                              have lengthEq : length = length' := by
                                have lengthZero : length = 0 := by
                                  simpa [List.getD] using
                                    lengthsFixed 0 (by simp [List.getD, reading])
                                have lengthZero' : length' = 0 := by
                                  simpa [List.getD] using
                                    lengthsFixed' 0 (by simp [List.getD, reading])
                                rw [lengthZero, lengthZero']
                              obtain ⟨countsTailEq, lengthsTailEq⟩ :=
                                inductionHypothesis (offset + 1) counts lengths counts' lengths'
                                  tailCountsLength tailLengthsLength tailCountsLength'
                                  tailLengthsLength' tailCountsFixed tailCountsFixed'
                                  tailLengthsFixed tailLengthsFixed' tailNoSet tailRel
                              exact ⟨by rw [countEq, countsTailEq], by rw [lengthEq, lengthsTailEq]⟩

/-- Binder counts agree, and so does every length that is not a hash set.
A hash-set length is not part of the result: a set deletion may change it. -/
theorem recover_partial {total total' : Nat}
    (printed : Fin total → Pattern) (printed' : Fin total' → Pattern)
    (offset offset' : Nat) (parameters : List TermParam)
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
    (related : List.Forall₂ PatternCong
      (assemblePrinted printed offset parameters counts lengths)
      (assemblePrinted printed' offset' parameters counts' lengths')) :
    counts = counts' ∧
      (∀ index : Nat,
        isHashSetParam (parameters.getD index missingParameter) = false →
          lengths.getD index 0 = lengths'.getD index 0) := by
  induction parameters generalizing counts lengths counts' lengths' offset offset' with
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
                  | nil => exact ⟨rfl, fun _ _ => rfl⟩
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
                        simpa [List.getD] using
                          countsFixed (index + 1) (by simpa [List.getD] using hypothesis)
                      have tailCountsFixed' : ∀ index : Nat,
                          (multiBase? (parameters.getD index missingParameter)).isNone →
                            counts'.getD index 0 = 0 := by
                        intro index hypothesis
                        simpa [List.getD] using
                          countsFixed' (index + 1) (by simpa [List.getD] using hypothesis)
                      have tailLengthsFixed : ∀ index : Nat,
                          (baseCollection? (parameters.getD index missingParameter)).isNone →
                            lengths.getD index 0 = 0 := by
                        intro index hypothesis
                        simpa [List.getD] using
                          lengthsFixed (index + 1) (by simpa [List.getD] using hypothesis)
                      have tailLengthsFixed' : ∀ index : Nat,
                          (baseCollection? (parameters.getD index missingParameter)).isNone →
                            lengths'.getD index 0 = 0 := by
                        intro index hypothesis
                        simpa [List.getD] using
                          lengthsFixed' (index + 1) (by simpa [List.getD] using hypothesis)
                      cases reading : baseCollection? parameter with
                      | some packed =>
                          obtain ⟨kind, element⟩ := packed
                          cases kind with
                          | hashSet =>
                              simp only [assemblePrinted, reading] at related
                              cases related with
                              | cons _headRel tailRel =>
                                  have countEq : count = count' := by
                                    have countZ : count = 0 := by
                                      simpa [List.getD] using countsFixed 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    have countZ' : count' = 0 := by
                                      simpa [List.getD] using countsFixed' 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    rw [countZ, countZ']
                                  obtain ⟨countsTailEq, lengthsAgree⟩ :=
                                    inductionHypothesis (offset + length) (offset' + length')
                                      counts lengths counts' lengths' tailCountsLength
                                      tailLengthsLength tailCountsLength' tailLengthsLength'
                                      tailCountsFixed tailCountsFixed' tailLengthsFixed
                                      tailLengthsFixed' tailRel
                                  refine ⟨by rw [countEq, countsTailEq], ?_⟩
                                  intro index marked
                                  cases index with
                                  | zero =>
                                      have bad : isHashSetParam parameter = true := by
                                        simp [isHashSetParam, reading]
                                      have marked' : isHashSetParam parameter = false := by
                                        simpa [List.getD] using marked
                                      rw [bad] at marked'
                                      cases marked'
                                  | succ index =>
                                      exact lengthsAgree index (by simpa [List.getD] using marked)
                          | hashBag =>
                              simp only [assemblePrinted, reading] at related
                              cases related with
                              | cons headRel tailRel =>
                                  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, elementsRel⟩ :=
                                    patternCong_bag_elements headRel
                                      (Or.inl ⟨List.ofFn fun index : Fin length =>
                                        nthPrinted printed (offset + index.val), rfl⟩)
                                  simp only [Pattern.collection.injEq] at leftEq rightEq
                                  obtain ⟨_, leftList, _⟩ := leftEq
                                  obtain ⟨_, rightList, _⟩ := rightEq
                                  subst leftList
                                  subst rightList
                                  have lengthEq : length = length' := by
                                    simpa [List.length_ofFn] using bagElementRel_length elementsRel
                                  subst lengthEq
                                  have countEq : count = count' := by
                                    have countZ : count = 0 := by
                                      simpa [List.getD] using countsFixed 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    have countZ' : count' = 0 := by
                                      simpa [List.getD] using countsFixed' 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    rw [countZ, countZ']
                                  obtain ⟨countsTailEq, lengthsAgree⟩ :=
                                    inductionHypothesis (offset + length) (offset' + length)
                                      counts lengths counts' lengths' tailCountsLength
                                      tailLengthsLength tailCountsLength' tailLengthsLength'
                                      tailCountsFixed tailCountsFixed' tailLengthsFixed
                                      tailLengthsFixed' tailRel
                                  refine ⟨by rw [countEq, countsTailEq], ?_⟩
                                  intro index marked
                                  cases index with
                                  | zero => simp [List.getD]
                                  | succ index =>
                                      exact lengthsAgree index (by simpa [List.getD] using marked)
                          | vec =>
                              simp only [assemblePrinted, reading] at related
                              cases related with
                              | cons headRel tailRel =>
                                  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, pointwise⟩ :=
                                    patternCong_vec_elements headRel
                                      (Or.inl ⟨List.ofFn fun index : Fin length =>
                                        nthPrinted printed (offset + index.val), rfl⟩)
                                  simp only [Pattern.collection.injEq] at leftEq rightEq
                                  obtain ⟨_, leftList, _⟩ := leftEq
                                  obtain ⟨_, rightList, _⟩ := rightEq
                                  subst leftList
                                  subst rightList
                                  have lengthEq : length = length' := by
                                    simpa [List.length_ofFn] using
                                      List.Forall₂.length_eq pointwise
                                  subst lengthEq
                                  have countEq : count = count' := by
                                    have countZ : count = 0 := by
                                      simpa [List.getD] using countsFixed 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    have countZ' : count' = 0 := by
                                      simpa [List.getD] using countsFixed' 0
                                        (by simp [List.getD, multiBase_of_collection reading])
                                    rw [countZ, countZ']
                                  obtain ⟨countsTailEq, lengthsAgree⟩ :=
                                    inductionHypothesis (offset + length) (offset' + length)
                                      counts lengths counts' lengths' tailCountsLength
                                      tailLengthsLength tailCountsLength' tailLengthsLength'
                                      tailCountsFixed tailCountsFixed' tailLengthsFixed
                                      tailLengthsFixed' tailRel
                                  refine ⟨by rw [countEq, countsTailEq], ?_⟩
                                  intro index marked
                                  cases index with
                                  | zero => simp [List.getD]
                                  | succ index =>
                                      exact lengthsAgree index (by simpa [List.getD] using marked)
                      | none =>
                          simp only [assemblePrinted, reading] at related
                          cases related with
                          | cons headRel tailRel =>
                              obtain ⟨countEq, _body⟩ :=
                                printArgument_body parameter count count'
                                  (nthPrinted printed offset) (nthPrinted printed' offset') headRel
                                  (by
                                    intro notMulti
                                    simpa [List.getD] using
                                      countsFixed 0 (by simpa [List.getD] using notMulti))
                                  (by
                                    intro notMulti
                                    simpa [List.getD] using
                                      countsFixed' 0 (by simpa [List.getD] using notMulti))
                              have lengthEq : length = length' := by
                                have lengthZero : length = 0 := by
                                  simpa [List.getD] using
                                    lengthsFixed 0 (by simp [List.getD, reading])
                                have lengthZero' : length' = 0 := by
                                  simpa [List.getD] using
                                    lengthsFixed' 0 (by simp [List.getD, reading])
                                rw [lengthZero, lengthZero']
                              obtain ⟨countsTailEq, lengthsAgree⟩ :=
                                inductionHypothesis (offset + 1) (offset' + 1) counts lengths
                                  counts' lengths' tailCountsLength tailLengthsLength
                                  tailCountsLength' tailLengthsLength' tailCountsFixed
                                  tailCountsFixed' tailLengthsFixed tailLengthsFixed' tailRel
                              refine ⟨by rw [countEq, countsTailEq], ?_⟩
                              intro index marked
                              cases index with
                              | zero => simpa [List.getD] using lengthEq
                              | succ index =>
                                  exact lengthsAgree index (by simpa [List.getD] using marked)

/-- One collection parameter splits the arity into a prefix, a replicate, and a suffix. -/
theorem expand_split (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    {parameterIndex : Nat} (parameterBound : parameterIndex < parameters.length)
    {kind : CollType} {element : String}
    (shape : baseCollection? (parameters.get ⟨parameterIndex, parameterBound⟩) =
      some (kind, element)) :
    expandSlots parameters counts lengths =
      expandSlots (parameters.take parameterIndex) (counts.take parameterIndex)
          (lengths.take parameterIndex) ++
        List.replicate (lengths.getD parameterIndex 0) ([], element) ++
        expandSlots (parameters.drop (parameterIndex + 1)) (counts.drop (parameterIndex + 1))
          (lengths.drop (parameterIndex + 1)) := by
  induction parameters generalizing counts lengths parameterIndex with
  | nil => simp at parameterBound
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp at lengthsLength
                omega
              cases parameterIndex with
              | zero =>
                  have shapeHead : baseCollection? parameter = some (kind, element) := by
                    simpa [List.get_cons_zero] using shape
                  simp only [List.take_zero, List.getD_cons_zero, expandSlots, shapeHead, expandParam]
                  rfl
              | succ parameterIndex =>
                  have tailBound : parameterIndex < parameters.length := by
                    simp at parameterBound
                    omega
                  have tailShape :
                      baseCollection? (parameters.get ⟨parameterIndex, tailBound⟩) =
                        some (kind, element) := by
                    simpa [List.get_cons_succ] using shape
                  have tail :=
                    inductionHypothesis counts lengths tailCounts tailLengths tailBound tailShape
                  simp only [expandSlots, List.take_succ_cons, List.drop_succ_cons,
                    List.getD_cons_succ] at tail ⊢
                  rw [tail]
                  simp [List.append_assoc]

theorem segment_room {sort : String}
    (operator : (indexedSignature language).Op sort)
    {parameterIndex : Nat} (parameterBound : parameterIndex < operator.1.1.params.length)
    (collection :
      (baseCollection? (operator.1.1.params.get ⟨parameterIndex, parameterBound⟩)).isSome) :
    takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        operator.2.lengths.getD parameterIndex 0 ≤
      ((indexedSignature language).arity operator).length := by
  have split :=
    slotCount_focus operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length parameterIndex parameterBound collection
  rw [expandSlots_length]
  simp only [takenSlots] at split ⊢
  omega

theorem expand_segment_getElem (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    {parameterIndex : Nat} (parameterBound : parameterIndex < parameters.length)
    {kind : CollType} {element : String}
    (shape : baseCollection? (parameters.get ⟨parameterIndex, parameterBound⟩) =
      some (kind, element))
    (index : Fin (lengths.getD parameterIndex 0))
    (fit :
      takenSlots parameters counts lengths parameterIndex + index.val <
        (expandSlots parameters counts lengths).length) :
    (expandSlots parameters counts lengths)[
        takenSlots parameters counts lengths parameterIndex + index.val] =
      ([], element) := by
  have split := expand_split parameters counts lengths countsLength lengthsLength parameterBound shape
  generalize hlist : expandSlots parameters counts lengths = slots at split fit ⊢
  subst split
  have prefixLength :=
    expandSlots_length (parameters.take parameterIndex) (counts.take parameterIndex)
      (lengths.take parameterIndex)
  have indexBound : index.val < lengths.getD parameterIndex 0 := index.isLt
  have inMiddle :
      takenSlots parameters counts lengths parameterIndex + index.val <
        (expandSlots (parameters.take parameterIndex) (counts.take parameterIndex)
            (lengths.take parameterIndex) ++
          List.replicate (lengths.getD parameterIndex 0) ([], element)).length := by
    simp only [takenSlots, List.length_append, List.length_replicate, prefixLength] at *
    omega
  rw [List.getElem_append_left inMiddle]
  have pastPrefix :
      (expandSlots (parameters.take parameterIndex) (counts.take parameterIndex)
          (lengths.take parameterIndex)).length ≤
        takenSlots parameters counts lengths parameterIndex + index.val := by
    rw [prefixLength]
    simp [takenSlots]
  rw [List.getElem_append_right pastPrefix]
  simp [takenSlots, prefixLength, List.getElem_replicate]

/-- Put element trees into one segment and keep every other direction. -/
def overlaySegment {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort) (start length : Nat)
    (fit : start + length ≤ ((indexedSignature language).arity operator).length)
    (uniform : ∀ index : Fin length,
      ((indexedSignature language).arity operator).get
          ⟨start + index.val, by
            have indexLt := index.isLt
            omega⟩ = ([], element))
    (base : Child language Γ sort operator)
    (trees : Fin length → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity operator).length) :
    Tree language
      ((polynomial (indexedSignature language)).src (Γ, sort) operator direction) :=
  if inside : start ≤ direction.val ∧ direction.val < start + length then
    have indexLt : direction.val - start < length := by
      rcases inside with ⟨_lo, hi⟩
      omega
    have absLt : start + (direction.val - start) <
        ((indexedSignature language).arity operator).length := by
      have directionLt := direction.isLt
      rcases inside with ⟨lo, _hi⟩
      omega
    let index : Fin length := ⟨direction.val - start, indexLt⟩
    let absolute : Fin ((indexedSignature language).arity operator).length :=
      ⟨start + (direction.val - start), absLt⟩
    have sameDirection : absolute = direction := by
      apply Fin.ext
      show start + (direction.val - start) = direction.val
      rcases inside with ⟨lo, _hi⟩
      omega
    cast (congrArg (Tree language)
      ((collection_direction_lands operator absolute (uniform index)).symm.trans
        (congrArg
          (fun direction =>
            (polynomial (indexedSignature language)).src (Γ, sort) operator direction)
          sameDirection)))
      (trees index)
  else
    base direction

theorem overlay_outside {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort) (start length : Nat)
    (fit : start + length ≤ ((indexedSignature language).arity operator).length)
    (uniform : ∀ index : Fin length,
      ((indexedSignature language).arity operator).get
          ⟨start + index.val, by
            have indexLt := index.isLt
            omega⟩ = ([], element))
    (base : Child language Γ sort operator)
    (trees : Fin length → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity operator).length)
    (outside : direction.val < start ∨ start + length ≤ direction.val) :
    overlaySegment operator start length fit uniform base trees direction = base direction := by
  simp only [overlaySegment]
  rw [dif_neg]
  intro inside
  cases outside <;> omega

/-- The first `k` parameters and the remaining parameters partition the arity. -/
theorem slotCount_take_drop (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (k : Nat) (kLe : k ≤ parameters.length) :
    slotCount (parameters.take k) (counts.take k) (lengths.take k) +
        slotCount (parameters.drop k) (counts.drop k) (lengths.drop k) =
      slotCount parameters counts lengths := by
  induction parameters generalizing counts lengths k with
  | nil =>
      cases counts <;> cases lengths <;> simp [slotCount] at kLe ⊢
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp at lengthsLength
                omega
              cases k with
              | zero => simp [slotCount]
              | succ k =>
                  have kLe' : k ≤ parameters.length := by
                    simp at kLe
                    omega
                  have tail :=
                    inductionHypothesis counts lengths tailCounts tailLengths k kLe'
                  simp only [List.take_succ_cons, List.drop_succ_cons, slotCount] at tail ⊢
                  omega

theorem takenSlots_le (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    {done : Nat} (doneLe : done ≤ parameters.length) :
    takenSlots parameters counts lengths done ≤ slotCount parameters counts lengths := by
  rw [← slotCount_take_drop parameters counts lengths countsLength lengthsLength done doneLe]
  exact Nat.le_add_right _ _

/-- The assembled argument at one parameter reads the children at that slot. -/
theorem assemble_at {total : Nat} (printed : Fin total → Pattern) (offset : Nat)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (done : Nat) (doneBound : done < parameters.length) :
    (assemblePrinted printed offset parameters counts lengths).getD done (.bvar 0) =
      match baseCollection? (parameters.get ⟨done, doneBound⟩) with
      | some (kind, _) =>
          .collection kind
            (List.ofFn fun index : Fin (lengths.getD done 0) =>
              nthPrinted printed
                (offset + takenSlots parameters counts lengths done + index.val))
            none
      | none =>
          printArgument (parameters.get ⟨done, doneBound⟩) (counts.getD done 0)
            (nthPrinted printed (offset + takenSlots parameters counts lengths done)) := by
  induction parameters generalizing counts lengths offset done with
  | nil => simp at doneBound
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp at countsLength
      | cons count counts =>
          cases lengths with
          | nil => simp at lengthsLength
          | cons length lengths =>
              have tailCounts : counts.length = parameters.length := by
                simp at countsLength
                omega
              have tailLengths : lengths.length = parameters.length := by
                simp at lengthsLength
                omega
              cases done with
              | zero =>
                  have headGet :
                      (parameter :: parameters).get ⟨0, doneBound⟩ = parameter :=
                    List.getElem_cons_zero parameter parameters doneBound
                  cases reading : baseCollection? parameter with
                  | some packed =>
                      obtain ⟨kind, _element⟩ := packed
                      simp only [assemblePrinted, reading, List.getD_cons_zero, takenSlots_zero,
                        Nat.add_zero, headGet]
                      rfl
                  | none =>
                      simp only [assemblePrinted, reading, List.getD_cons_zero, takenSlots_zero,
                        Nat.add_zero, headGet]
              | succ done =>
                  have tailBound : done < parameters.length := by
                    simp at doneBound
                    omega
                  cases reading : baseCollection? parameter with
                  | some packed =>
                      obtain ⟨_kind, _element⟩ := packed
                      have tail :=
                        inductionHypothesis (offset + length) counts lengths tailCounts
                          tailLengths done tailBound
                      simp only [assemblePrinted, reading, List.getD_cons_succ,
                        List.get_eq_getElem, List.getElem_cons_succ, takenSlots_succ,
                        directionsOf, Nat.add_assoc] at tail ⊢
                      exact tail
                  | none =>
                      have tail :=
                        inductionHypothesis (offset + 1) counts lengths tailCounts tailLengths
                          done tailBound
                      simp only [assemblePrinted, reading, List.getD_cons_succ,
                        List.get_eq_getElem, List.getElem_cons_succ, takenSlots_succ,
                        directionsOf, Nat.add_assoc] at tail ⊢
                      exact tail

theorem assemble_at_none {total : Nat} (printed : Fin total → Pattern)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (done : Nat) (doneBound : done < parameters.length)
    (reading : baseCollection? (parameters.get ⟨done, doneBound⟩) = none) :
    (assemblePrinted printed 0 parameters counts lengths).getD done (.bvar 0) =
      printArgument (parameters.get ⟨done, doneBound⟩) (counts.getD done 0)
        (nthPrinted printed (takenSlots parameters counts lengths done)) := by
  rw [assemble_at printed 0 parameters counts lengths countsLength lengthsLength done doneBound]
  rw [reading]
  simp

theorem assemble_at_vec {total : Nat} (printed : Fin total → Pattern)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (done : Nat) (doneBound : done < parameters.length) {element : String}
    (reading : baseCollection? (parameters.get ⟨done, doneBound⟩) = some (.vec, element)) :
    (assemblePrinted printed 0 parameters counts lengths).getD done (.bvar 0) =
      .collection .vec
        (List.ofFn fun index : Fin (lengths.getD done 0) =>
          nthPrinted printed (takenSlots parameters counts lengths done + index.val))
        none := by
  rw [assemble_at printed 0 parameters counts lengths countsLength lengthsLength done doneBound]
  rw [reading]
  simp

theorem assemble_at_set {total : Nat} (printed : Fin total → Pattern)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (done : Nat) (doneBound : done < parameters.length) {element : String}
    (reading : baseCollection? (parameters.get ⟨done, doneBound⟩) = some (.hashSet, element)) :
    (assemblePrinted printed 0 parameters counts lengths).getD done (.bvar 0) =
      .collection .hashSet
        (List.ofFn fun index : Fin (lengths.getD done 0) =>
          nthPrinted printed (takenSlots parameters counts lengths done + index.val))
        none := by
  rw [assemble_at printed 0 parameters counts lengths countsLength lengthsLength done doneBound]
  rw [reading]
  simp

theorem assemble_at_bag {total : Nat} (printed : Fin total → Pattern)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (done : Nat) (doneBound : done < parameters.length) {element : String}
    (reading : baseCollection? (parameters.get ⟨done, doneBound⟩) = some (.hashBag, element)) :
    (assemblePrinted printed 0 parameters counts lengths).getD done (.bvar 0) =
      .collection .hashBag
        (List.ofFn fun index : Fin (lengths.getD done 0) =>
          nthPrinted printed (takenSlots parameters counts lengths done + index.val))
        none := by
  rw [assemble_at printed 0 parameters counts lengths countsLength lengthsLength done doneBound]
  rw [reading]
  simp

/-- One segment child of an overlay is the element tree placed there. -/
theorem overlay_segment {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort) (start length : Nat)
    (room : start + length ≤ ((indexedSignature language).arity operator).length)
    (uniform : ∀ index : Fin length,
      ((indexedSignature language).arity operator).get
          ⟨start + index.val, by
            have indexLt := index.isLt
            omega⟩ = ([], element))
    (base : Child language Γ sort operator)
    (trees : Fin length → Tree language (Γ, element))
    (index : Fin length)
    (fit : start + index.val < ((indexedSignature language).arity operator).length) :
    segmentChild operator start index fit (uniform index)
        (overlaySegment operator start length room uniform base trees) =
      trees index := by
  unfold segmentChild atElement overlaySegment
  have inside : start ≤ start + index.val ∧ start + index.val < start + length := by
    refine ⟨Nat.le_add_right _ _, ?_⟩
    have indexLt := index.isLt
    omega
  rw [dif_pos inside]
  apply eq_of_heq
  rw [cast_heq_iff_heq, cast_heq_iff_heq]
  refine congr_arg_heq trees ?_
  apply Fin.ext
  show start + index.val - start = index.val
  have indexLt := index.isLt
  omega

/-- Replace one collection length and keep the rule, the counts, and the other
lengths. The replaced parameter is a hash set, so the fixed-length condition
still holds. -/
def resizedAt {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (n : Nat) : (indexedSignature language).Op sort :=
  ⟨operator.1, {
      counts := operator.2.counts
      lengths := operator.2.lengths.set parameterIndex n
      counts_length := operator.2.counts_length
      lengths_length := by simp [List.length_set, operator.2.lengths_length]
      counts_fixed := operator.2.counts_fixed
      lengths_fixed := by
        intro index premise
        by_cases same : index = parameterIndex
        · have paramGet :
              operator.1.1.params.getD parameterIndex missingParameter =
                operator.1.1.params.get ⟨parameterIndex, bound⟩ :=
            List.getD_eq_get (d := missingParameter) (i := ⟨parameterIndex, bound⟩)
          have marked :
              (baseCollection?
                  (operator.1.1.params.getD parameterIndex missingParameter)).isNone =
                false := by
            rw [paramGet, shape]
            rfl
          have contrad : False := by
            have premiseAt : (baseCollection?
                (operator.1.1.params.getD parameterIndex missingParameter)).isNone := by
              simpa [same] using premise
            rw [marked] at premiseAt
            exact Bool.false_ne_true premiseAt
          exact contrad.elim
        · by_cases inRange : index < operator.2.lengths.length
          · have inRange' : index < (operator.2.lengths.set parameterIndex n).length := by
              simpa [List.length_set] using inRange
            rw [List.getD_eq_getElem (hn := inRange')]
            rw [List.getElem_set_ne (Ne.symm same)]
            have old := operator.2.lengths_fixed index premise
            rwa [List.getD_eq_getElem (hn := inRange)] at old
          · have outRange : operator.2.lengths.length ≤ index := Nat.le_of_not_lt inRange
            have outRange' : (operator.2.lengths.set parameterIndex n).length ≤ index := by
              simpa [List.length_set] using outRange
            exact List.getD_eq_default (d := 0) (hn := outRange')
    }⟩

/-- The prefix of a length list stops before the index that `set` replaces. -/
theorem resizedAt_lengths_take {sort : String}
    (operator : (indexedSignature language).Op sort) (parameterIndex n : Nat) :
    (operator.2.lengths.set parameterIndex n).take parameterIndex =
      operator.2.lengths.take parameterIndex :=
  List.take_set_of_le (Nat.le_refl _)

/-- The suffix after a replaced length is the original suffix. -/
theorem resizedAt_lengths_drop {sort : String}
    (operator : (indexedSignature language).Op sort) (parameterIndex n : Nat) :
    (operator.2.lengths.set parameterIndex n).drop (parameterIndex + 1) =
      operator.2.lengths.drop (parameterIndex + 1) :=
  List.drop_set_of_lt (Nat.lt_succ_self _)

/-- The replaced entry reads back as the length that was written. -/
theorem resizedAt_getD {sort : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.2.lengths.length)
    (n : Nat) :
    (operator.2.lengths.set parameterIndex n).getD parameterIndex 0 = n := by
  have inRange : parameterIndex < (operator.2.lengths.set parameterIndex n).length := by
    simpa [List.length_set] using bound
  rw [List.getD_eq_getElem (hn := inRange)]
  exact List.getElem_set_self inRange

/-- Writing the length a head already stores does not change the operator. -/
theorem resizedAt_eq_self {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (n : Nat)
    (nEq : n = operator.2.lengths.getD parameterIndex 0) :
    resizedAt operator parameterIndex bound shape n = operator := by
  subst nEq
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply headData_ext
  · rfl
  · have lenBound : parameterIndex < operator.2.lengths.length := by
      simpa [operator.2.lengths_length] using bound
    rw [List.getD_eq_getElem (hn := lenBound)]
    exact List.set_getElem_self lenBound

/-- One collection parameter splits an arity into a prefix, a replicate, and a suffix. -/
theorem arity_at_parameter {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    {kind : CollType}
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (kind, element)) :
    (indexedSignature language).arity operator =
      expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate (operator.2.lengths.getD parameterIndex 0) ([], element) ++
        expandSlots (operator.1.1.params.drop (parameterIndex + 1))
          (operator.2.counts.drop (parameterIndex + 1))
          (operator.2.lengths.drop (parameterIndex + 1)) :=
  expand_split operator.1.1.params operator.2.counts operator.2.lengths
    operator.2.counts_length operator.2.lengths_length bound shape

/-- Resizing one hash-set length replaces only that replicate. -/
theorem resizedAt_arity {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (n : Nat) :
    (indexedSignature language).arity (resizedAt operator parameterIndex bound shape n) =
      expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate n ([], element) ++
        expandSlots (operator.1.1.params.drop (parameterIndex + 1))
          (operator.2.counts.drop (parameterIndex + 1))
          (operator.2.lengths.drop (parameterIndex + 1)) := by
  have raw :=
    arity_at_parameter (resizedAt operator parameterIndex bound shape n) parameterIndex
      (by simpa [resizedAt] using bound) (by simpa [resizedAt] using shape)
  have lenBound : parameterIndex < operator.2.lengths.length := by
    simpa [operator.2.lengths_length] using bound
  simp only [resizedAt, resizedAt_lengths_take, resizedAt_lengths_drop,
    resizedAt_getD operator parameterIndex lenBound n] at raw
  exact raw

/-- The directions before a parameter are the prefix of the arity. -/
theorem segmentStart_length {sort : String}
    (operator : (indexedSignature language).Op sort) (parameterIndex : Nat) :
    takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex =
      (expandSlots (operator.1.1.params.take parameterIndex)
        (operator.2.counts.take parameterIndex)
        (operator.2.lengths.take parameterIndex)).length := by
  rw [expandSlots_length]
  rfl

/-- A resized hash-set direction before the segment is still inside the original arity. -/
theorem resized_prefix_fit {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (_k : Nat) {directionVal : Nat}
    (hPrefix : directionVal <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) :
    directionVal < ((indexedSignature language).arity operator).length := by
  have split := arity_at_parameter operator parameterIndex bound shape
  have lenEq := congrArg List.length split
  simp only [List.length_append, List.length_replicate] at lenEq
  rw [← segmentStart_length operator parameterIndex] at lenEq
  have startLe :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          operator.2.lengths.getD parameterIndex 0 +
          (expandSlots (operator.1.1.params.drop (parameterIndex + 1))
            (operator.2.counts.drop (parameterIndex + 1))
            (operator.2.lengths.drop (parameterIndex + 1))).length :=
    Nat.le_trans
      (Nat.le_add_right _ (operator.2.lengths.getD parameterIndex 0))
      (Nat.le_add_right _ _)
  rw [lenEq]
  exact Nat.lt_of_lt_of_le hPrefix startLe

/-- Reading an entry is unchanged by replacing the list with an equal list. -/
theorem getElem_of_eq {α : Type*} {l l' : List α} (h : l = l') {i : Nat}
    (hi : i < l.length) : l[i] = l'[i]'(h ▸ hi) := by
  cases h
  rfl

/-- The declaration before the resized segment agrees with the original operator. -/
theorem resized_prefix_decl {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) :
    ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).get direction =
      ((indexedSignature language).arity operator).get
        ⟨direction.val, resized_prefix_fit operator parameterIndex bound shape k hPrefix⟩ := by
  rw [List.get_eq_getElem]
  have startEq := segmentStart_length operator parameterIndex
  have inPrefix : direction.val <
      (expandSlots (operator.1.1.params.take parameterIndex)
        (operator.2.counts.take parameterIndex)
        (operator.2.lengths.take parameterIndex)).length := by
    rw [← startEq]
    exact hPrefix
  have inMidLeft : direction.val <
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate k ([], element)).length := by
    rw [List.length_append]
    omega
  have inMidRight : direction.val <
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate (operator.2.lengths.getD parameterIndex 0) ([], element)).length := by
    rw [List.length_append]
    omega
  have leftRead :=
    getElem_of_eq (resizedAt_arity operator parameterIndex bound shape k) direction.isLt
  have rightRead :=
    getElem_of_eq (arity_at_parameter operator parameterIndex bound shape)
      (resized_prefix_fit operator parameterIndex bound shape k hPrefix)
  rw [leftRead]
  simp only [List.get_eq_getElem]
  rw [rightRead]
  rw [List.getElem_append_left inMidLeft, List.getElem_append_left inPrefix]
  rw [List.getElem_append_left inMidRight, List.getElem_append_left inPrefix]

/-- A direction inside the resized segment is the element sort. -/
theorem resized_segment_decl {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (lo : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
      direction.val)
    (hi : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k) :
    ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).get direction = ([], element) := by
  rw [List.get_eq_getElem]
  have read :=
    getElem_of_eq (resizedAt_arity operator parameterIndex bound shape k) direction.isLt
  rw [read]
  have startEq := segmentStart_length operator parameterIndex
  have inMid : direction.val <
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate k ([], element)).length := by
    rw [List.length_append, List.length_replicate, ← startEq]
    omega
  rw [List.getElem_append_left inMid]
  have past :
      (expandSlots (operator.1.1.params.take parameterIndex)
        (operator.2.counts.take parameterIndex)
        (operator.2.lengths.take parameterIndex)).length ≤ direction.val := by
    rw [← startEq]
    exact lo
  rw [List.getElem_append_right past]
  simp [List.getElem_replicate]

/-- A resized direction after the segment lands in the original arity. -/
theorem resized_suffix_fit {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat) {directionVal : Nat}
    (hDir : directionVal <
      ((indexedSignature language).arity (resizedAt operator parameterIndex bound shape k)).length)
    (hPast : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        k ≤ directionVal) :
    directionVal + operator.2.lengths.getD parameterIndex 0 - k <
      ((indexedSignature language).arity operator).length := by
  have resLen := congrArg List.length (resizedAt_arity operator parameterIndex bound shape k)
  have opLen := congrArg List.length (arity_at_parameter operator parameterIndex bound shape)
  simp only [List.length_append, List.length_replicate] at resLen opLen
  rw [← segmentStart_length operator parameterIndex] at resLen opLen
  rw [opLen]
  rw [resLen] at hDir
  omega

/-- The declaration after the resized segment agrees with the shifted original direction. -/
theorem resized_suffix_decl {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hPast : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        k ≤ direction.val) :
    ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).get direction =
      ((indexedSignature language).arity operator).get
        ⟨direction.val + operator.2.lengths.getD parameterIndex 0 - k,
          resized_suffix_fit operator parameterIndex bound shape k direction.isLt hPast⟩ := by
  rw [List.get_eq_getElem]
  have leftRead :=
    getElem_of_eq (resizedAt_arity operator parameterIndex bound shape k) direction.isLt
  have rightRead :=
    getElem_of_eq (arity_at_parameter operator parameterIndex bound shape)
      (resized_suffix_fit operator parameterIndex bound shape k direction.isLt hPast)
  rw [leftRead]
  simp only [List.get_eq_getElem]
  rw [rightRead]
  have startEq := segmentStart_length operator parameterIndex
  have pastLeft :
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate k ([], element)).length ≤ direction.val := by
    rw [List.length_append, List.length_replicate, ← startEq]
    exact hPast
  have pastRight :
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate (operator.2.lengths.getD parameterIndex 0) ([], element)).length ≤
        direction.val + operator.2.lengths.getD parameterIndex 0 - k := by
    rw [List.length_append, List.length_replicate, ← startEq]
    have kLe : k ≤ direction.val :=
      Nat.le_trans (Nat.le_add_left k _) hPast
    have startLe :
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
          direction.val - k :=
      (Nat.le_sub_iff_add_le kLe).mpr hPast
    have shifted :=
      Nat.add_le_add_right startLe (operator.2.lengths.getD parameterIndex 0)
    have rearrange :
        direction.val - k + operator.2.lengths.getD parameterIndex 0 =
          direction.val + operator.2.lengths.getD parameterIndex 0 - k := by
      rw [Nat.add_comm (direction.val - k), ← Nat.add_sub_assoc kLe, Nat.add_comm]
    rw [← rearrange]
    exact shifted
  rw [List.getElem_append_right pastLeft, List.getElem_append_right pastRight]
  congr 1
  have kLe : k ≤ direction.val :=
    Nat.le_trans (Nat.le_add_left k _) hPast
  have leftLen :
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate k ([], element)).length =
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k := by
    rw [List.length_append, List.length_replicate, ← startEq]
  have rightLen :
      (expandSlots (operator.1.1.params.take parameterIndex)
          (operator.2.counts.take parameterIndex)
          (operator.2.lengths.take parameterIndex) ++
        List.replicate (operator.2.lengths.getD parameterIndex 0) ([], element)).length =
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          operator.2.lengths.getD parameterIndex 0 := by
    rw [List.length_append, List.length_replicate, ← startEq]
  rw [leftLen, rightLen]
  calc
    direction.val -
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
            k) =
        direction.val -
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex -
            k := by
      rw [Nat.sub_add_eq]
    _ =
        direction.val - k -
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
      rw [Nat.sub_right_comm]
    _ =
        direction.val - k + operator.2.lengths.getD parameterIndex 0 -
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
            operator.2.lengths.getD parameterIndex 0) := by
      exact (Nat.add_sub_add_right (direction.val - k) _ _).symm
    _ =
        direction.val + operator.2.lengths.getD parameterIndex 0 - k -
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
            operator.2.lengths.getD parameterIndex 0) := by
      rw [Nat.add_comm (direction.val - k), ← Nat.add_sub_assoc kLe, Nat.add_comm]

/-- The polynomial source before the segment is the original source. -/
theorem splice_prefix_src {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) :
    (polynomial (indexedSignature language)).src (Γ, sort)
        (resizedAt operator parameterIndex bound shape k) direction =
      (polynomial (indexedSignature language)).src (Γ, sort) operator
        ⟨direction.val, resized_prefix_fit operator parameterIndex bound shape k hPrefix⟩ := by
  rw [polynomial_direction, polynomial_direction,
    resized_prefix_decl operator parameterIndex bound shape k direction hPrefix]

/-- The polynomial source inside the segment is the element sort. -/
theorem splice_segment_src {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (lo : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
      direction.val)
    (hi : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k) :
    (polynomial (indexedSignature language)).src (Γ, sort)
        (resizedAt operator parameterIndex bound shape k) direction = (Γ, element) :=
  collection_direction_lands (resizedAt operator parameterIndex bound shape k) direction
    (resized_segment_decl operator parameterIndex bound shape k direction lo hi)

/-- The polynomial source after the segment is the shifted original source. -/
theorem splice_suffix_src {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hPast : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        k ≤ direction.val) :
    (polynomial (indexedSignature language)).src (Γ, sort)
        (resizedAt operator parameterIndex bound shape k) direction =
      (polynomial (indexedSignature language)).src (Γ, sort) operator
        ⟨direction.val + operator.2.lengths.getD parameterIndex 0 - k,
          resized_suffix_fit operator parameterIndex bound shape k direction.isLt hPast⟩ := by
  rw [polynomial_direction, polynomial_direction,
    resized_suffix_decl operator parameterIndex bound shape k direction hPast]

/-- Children of one resized hash-set parameter: the segment is the supplied family,
and every other direction is an original child, shifted past the new length. -/
def spliceChild {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element)) :
    Child language Γ sort (resizedAt operator parameterIndex bound shape k) :=
  fun direction =>
    if hPrefix : direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex then
      cast (congrArg (Tree language)
          (splice_prefix_src (Γ := Γ) operator parameterIndex bound shape k direction hPrefix).symm)
        (outside ⟨direction.val, resized_prefix_fit operator parameterIndex bound shape k hPrefix⟩)
    else if hSeg : direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k then
      cast (congrArg (Tree language)
          (splice_segment_src (Γ := Γ) operator parameterIndex bound shape k direction
            (by omega) hSeg).symm)
        (trees ⟨direction.val -
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex,
            by omega⟩)
    else
      cast (congrArg (Tree language)
          (splice_suffix_src (Γ := Γ) operator parameterIndex bound shape k direction
            (by omega)).symm)
        (outside ⟨direction.val + operator.2.lengths.getD parameterIndex 0 - k,
          resized_suffix_fit operator parameterIndex bound shape k direction.isLt (by omega)⟩)

/-- The tree obtained by resizing one hash-set parameter around a fixed outside. -/
def spliceNode {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    (k : Nat) (trees : Fin k → Tree language (Γ, element)) : Tree language (Γ, sort) :=
  IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
    (resizedAt operator parameterIndex bound shape k)
    (spliceChild operator parameterIndex bound shape k outside trees)

/-- Directions outside the resized segment do not read the element family. -/
theorem splice_outside {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees trees' : Fin k → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hOut : direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ∨
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
        direction.val) :
    spliceChild operator parameterIndex bound shape k outside trees direction =
      spliceChild operator parameterIndex bound shape k outside trees' direction := by
  unfold spliceChild
  by_cases hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex
  · simp only [dif_pos hPrefix]
  · have hPast :
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
          direction.val := by
      cases hOut with
      | inl low => omega
      | inr high => exact high
    have notSeg : ¬ direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k :=
      Nat.not_lt_of_ge hPast
    simp only [dif_neg hPrefix, dif_neg notSeg]

/-- One resized segment direction is the element tree placed there. -/
theorem splice_at {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (index : Fin k)
    (fit : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        index.val <
      ((indexedSignature language).arity (resizedAt operator parameterIndex bound shape k)).length)
    (uniform : ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).get
        ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
            index.val, fit⟩ = ([], element)) :
    segmentChild (resizedAt operator parameterIndex bound shape k)
        (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex)
        index fit uniform
        (spliceChild operator parameterIndex bound shape k outside trees) =
      trees index := by
  unfold segmentChild atElement spliceChild
  have notPrefix : ¬
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
    have indexLt := index.isLt
    omega
  have inSeg :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k := by
    have indexLt := index.isLt
    omega
  rw [dif_neg notPrefix, dif_pos inSeg]
  apply eq_of_heq
  rw [cast_heq_iff_heq, cast_heq_iff_heq]
  refine congr_arg_heq trees ?_
  apply Fin.ext
  show takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
      index.val -
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex =
    index.val
  have indexLt := index.isLt
  omega

/-- A family index stays inside the resized arity. -/
theorem resized_index_fit {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k index : Nat) (indexLt : index < k) :
    takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + index <
      ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).length := by
  have lenEq := congrArg List.length (resizedAt_arity operator parameterIndex bound shape k)
  simp only [List.length_append, List.length_replicate] at lenEq
  rw [← segmentStart_length operator parameterIndex] at lenEq
  have room :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + index <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k +
          (expandSlots (operator.1.1.params.drop (parameterIndex + 1))
            (operator.2.counts.drop (parameterIndex + 1))
            (operator.2.lengths.drop (parameterIndex + 1))).length :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left indexLt _) (Nat.le_add_right _ _)
  rw [← lenEq] at room
  exact room

/-- Permuting the element family is a hash-set bag step. The outside directions stay. -/
theorem spliceNode_perm {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    {k : Nat} {left right : Fin k → Tree language (Γ, element)}
    (permuted : List.Perm (List.ofFn left) (List.ofFn right)) :
    TreeCong language
      (spliceNode operator parameterIndex bound shape outside k left)
      (spliceNode operator parameterIndex bound shape outside k right) := by
  have lenBound : parameterIndex < operator.2.lengths.length := by
    simpa [operator.2.lengths_length] using bound
  have lenEq := congrArg List.length (resizedAt_arity operator parameterIndex bound shape k)
  simp only [List.length_append, List.length_replicate] at lenEq
  rw [← segmentStart_length operator parameterIndex] at lenEq
  have fit :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
        ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape k)).length := by
    rw [lenEq]
    exact Nat.le_add_right _ _
  have uniform (index : Fin k) :
      ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape k)).get
        ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
            index.val,
          resized_index_fit operator parameterIndex bound shape k index.val index.isLt⟩ =
        ([], element) :=
    resized_segment_decl operator parameterIndex bound shape k
      ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val,
        resized_index_fit operator parameterIndex bound shape k index.val index.isLt⟩
      (Nat.le_add_right _ _) (Nat.add_lt_add_left index.isLt _)
  have shaped :
      baseCollection? ((resizedAt operator parameterIndex bound shape k).1.1.params.get
        ⟨parameterIndex, by simpa [resizedAt] using bound⟩) = some (.hashSet, element) := by
    simpa [resizedAt] using shape
  have segLen : k =
      (resizedAt operator parameterIndex bound shape k).2.lengths.getD parameterIndex 0 := by
    simpa [resizedAt] using (resizedAt_getD operator parameterIndex lenBound k).symm
  have segStart :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex =
        slotCount ((resizedAt operator parameterIndex bound shape k).1.1.params.take parameterIndex)
          ((resizedAt operator parameterIndex bound shape k).2.counts.take parameterIndex)
          ((resizedAt operator parameterIndex bound shape k).2.lengths.take parameterIndex) := by
    simp only [takenSlots, resizedAt, resizedAt_lengths_take]
  have outsideEq :
      ∀ direction : Fin ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape k)).length,
        direction.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ∨
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
            direction.val →
          spliceChild operator parameterIndex bound shape k outside left direction =
            spliceChild operator parameterIndex bound shape k outside right direction := by
    intro direction hOut
    exact splice_outside operator parameterIndex bound shape k outside left right direction hOut
  have rewrite (trees : Fin k → Tree language (Γ, element)) :
      List.ofFn (fun index =>
          segmentChild (resizedAt operator parameterIndex bound shape k)
            (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex)
            index (resized_index_fit operator parameterIndex bound shape k index.val index.isLt)
            (uniform index)
            (spliceChild operator parameterIndex bound shape k outside trees)) =
        List.ofFn trees := by
    refine ofFn_pointwise ?_
    intro index
    exact splice_at operator parameterIndex bound shape k outside trees index
      (resized_index_fit operator parameterIndex bound shape k index.val index.isLt) (uniform index)
  exact TreeCong.bagPerm (resizedAt operator parameterIndex bound shape k)
      (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) k fit
      .hashSet (Or.inr rfl) parameterIndex (by simpa [resizedAt] using bound) shaped segStart
      segLen uniform
      (spliceChild operator parameterIndex bound shape k outside left)
      (spliceChild operator parameterIndex bound shape k outside right)
      outsideEq
      ((rewrite left).symm ▸ (rewrite right).symm ▸ permuted)

/-- A pointwise tree step on the element family stays inside the splice. -/
theorem spliceNode_point {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    {k : Nat} {left right : Fin k → Tree language (Γ, element)}
    (steps : ∀ index, TreeCong language (left index) (right index)) :
    TreeCong language
      (spliceNode operator parameterIndex bound shape outside k left)
      (spliceNode operator parameterIndex bound shape outside k right) := by
  unfold spliceNode
  apply treeCong_pointwise
  intro direction
  unfold spliceChild
  by_cases hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex
  · simp only [dif_pos hPrefix]
    exact TreeCong.refl _
  · by_cases hSeg : direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k
    · simp only [dif_neg hPrefix, dif_pos hSeg]
      apply treeCong_cast
        (splice_segment_src (Γ := Γ) operator parameterIndex bound shape k direction
          (by omega) hSeg).symm
      exact steps ⟨direction.val -
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex,
          by omega⟩
    · simp only [dif_neg hPrefix, dif_neg hSeg]
      exact TreeCong.refl _

/-- Equal element families build the same splice. -/
theorem spliceNode_cast {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    {k : Nat} {left right : Fin k → Tree language (Γ, element)}
    (agree : ∀ index, left index = right index) :
    spliceNode operator parameterIndex bound shape outside k left =
      spliceNode operator parameterIndex bound shape outside k right := by
  unfold spliceNode
  apply congrArg
    (fun children =>
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        (resizedAt operator parameterIndex bound shape k) children)
  funext direction
  unfold spliceChild
  by_cases hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex
  · simp only [dif_pos hPrefix]
  · by_cases hSeg : direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k
    · simp only [dif_neg hPrefix, dif_pos hSeg]
      apply congrArg
      exact agree _
    · simp only [dif_neg hPrefix, dif_neg hSeg]

theorem cast_trans {α β γ : Sort _} (h : α = β) (h' : β = γ) (a : α) :
    cast h' (cast h a) = cast (h.trans h') a := by
  cases h
  cases h'
  rfl

theorem castEq_iff_heq {α β : Sort _} (e : α = β) (a : α) (a' : β) :
    cast e a = a' ↔ HEq a a' := by
  cases e
  simp [cast_eq]

theorem atElement_fin {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    {d1 d2 : Fin ((indexedSignature language).arity operator).length}
    (eq : d1 = d2)
    (u1 : ((indexedSignature language).arity operator).get d1 = ([], element))
    (u2 : ((indexedSignature language).arity operator).get d2 = ([], element))
    (children : Child language Γ sort operator) :
    atElement operator d1 u1 children = atElement operator d2 u2 children := by
  cases eq
  have h := proof_irrel u1 u2
  subst h
  rfl

theorem liftBind_op {Γ : List String} {sort : String}
    {op1 op2 : (indexedSignature language).Op sort}
    (opEq : op1 = op2)
    (children : Child language Γ sort op1) :
    IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        op1 children =
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        op2 (cast (congrArg (Child language Γ sort) opEq) children) := by
  subst opEq
  rfl

theorem cast_child_direction {Γ : List String} {sort : String}
    {op1 op2 : (indexedSignature language).Op sort}
    (h : op1 = op2)
    (children : Child language Γ sort op1)
    (direction : Fin ((indexedSignature language).arity op2).length) :
    HEq (cast (congrArg (Child language Γ sort) h) children direction)
      (children
        (Fin.cast
          (congrArg
            (fun op : (indexedSignature language).Op sort =>
              ((indexedSignature language).arity op).length)
            h.symm)
          direction)) := by
  subst h
  simp [cast_eq]

/-- A splice at the operator's own hash-set length is that operator. -/
theorem spliceNode_segment {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    (k : Nat)
    (kEq : k = operator.2.lengths.getD parameterIndex 0) :
    spliceNode operator parameterIndex bound shape outside k
        (fun index : Fin k =>
          atElement operator
            ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                parameterIndex + index.val,
              by
                have indexLt := index.isLt
                have room :=
                  segment_room operator bound (by rw [shape]; rfl)
                omega⟩
            (by
              rw [List.get_eq_getElem]
              exact expand_segment_getElem operator.1.1.params operator.2.counts
                operator.2.lengths operator.2.counts_length operator.2.lengths_length bound
                shape (index.cast kEq)
                (by
                  have indexLt := index.isLt
                  have room :=
                    segment_room operator bound (by rw [shape]; rfl)
                  have sameLength :
                      (expandSlots operator.1.1.params operator.2.counts
                          operator.2.lengths).length =
                        ((indexedSignature language).arity operator).length := rfl
                  have castVal : (index.cast kEq).val = index.val := rfl
                  rw [← sameLength] at room
                  omega))
            outside) =
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator outside := by
  unfold spliceNode
  have opEq := resizedAt_eq_self operator parameterIndex bound shape k kEq
  rw [liftBind_op opEq]
  apply congrArg
    (fun children =>
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator children)
  funext direction
  apply eq_of_heq
  refine HEq.trans (cast_child_direction opEq _ direction) ?_
  let moved : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length :=
    Fin.cast
      (congrArg
        (fun op : (indexedSignature language).Op sort =>
          ((indexedSignature language).arity op).length)
        opEq.symm)
      direction
  change HEq
    (spliceChild operator parameterIndex bound shape k outside _ moved)
    (outside direction)
  have movedVal : moved.val = direction.val := by
    simp [moved]
  unfold spliceChild
  by_cases hPrefix : moved.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex
  · simp only [dif_pos hPrefix]
    rw [cast_heq_iff_heq]
    refine congr_arg_heq outside ?_
    apply Fin.ext
    exact movedVal
  · by_cases hSeg : moved.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k
    · simp only [dif_neg hPrefix, dif_pos hSeg]
      unfold atElement
      rw [cast_heq_iff_heq, cast_heq_iff_heq]
      refine congr_arg_heq outside ?_
      apply Fin.ext
      simp [movedVal]
      omega
    · simp only [dif_neg hPrefix, dif_neg hSeg]
      rw [cast_heq_iff_heq]
      refine congr_arg_heq outside ?_
      apply Fin.ext
      simp [movedVal, kEq]

/-- Deleting the first of two equal element trees shortens that one hash-set parameter. -/
theorem spliceNode_dup {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    {n : Nat} (wide : 2 ≤ n) (trees : Fin n → Tree language (Γ, element))
    (copies : trees ⟨0, by omega⟩ = trees ⟨1, by omega⟩) :
    TreeCong language
      (spliceNode operator parameterIndex bound shape outside n trees)
      (spliceNode operator parameterIndex bound shape outside (n - 1)
        (fun index : Fin (n - 1) =>
          trees ⟨index.val + 1, by have := index.isLt; omega⟩)) := by
  have zeroLt : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_succ 1) wide)
  have oneLt : 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) wide
  have lenBound : parameterIndex < operator.2.lengths.length := by
    simpa [operator.2.lengths_length] using bound
  let source := resizedAt operator parameterIndex bound shape n
  let target := resizedAt operator parameterIndex bound shape (n - 1)
  let start :=
    takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex
  let sourceChildren := spliceChild operator parameterIndex bound shape n outside trees
  let shorter : Fin (n - 1) → Tree language (Γ, element) :=
    fun index => trees ⟨index.val + 1, by have := index.isLt; omega⟩
  let targetChildren :=
    spliceChild operator parameterIndex bound shape (n - 1) outside shorter
  let removed : Fin ((indexedSignature language).arity source).length :=
    ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + 0,
      resized_index_fit operator parameterIndex bound shape n 0 zeroLt⟩
  have successor : removed.val + 1 < ((indexedSignature language).arity source).length :=
    resized_index_fit operator parameterIndex bound shape n 1 oneLt
  have srcLen := congrArg List.length (resizedAt_arity operator parameterIndex bound shape n)
  have tgtLen := congrArg List.length (resizedAt_arity operator parameterIndex bound shape (n - 1))
  simp only [List.length_append, List.length_replicate] at srcLen tgtLen
  rw [← segmentStart_length operator parameterIndex] at srcLen tgtLen
  have lenDrop :
      ((indexedSignature language).arity target).length + 1 =
        ((indexedSignature language).arity source).length := by
    rw [srcLen, tgtLen]
    omega
  have deletion : SetDeletion language Γ sort element source target sourceChildren targetChildren
      removed parameterIndex start := {
    sameRule := rfl
    sameCounts := rfl
    lengthsDrop := by
      have getN : source.2.lengths.getD parameterIndex 0 = n := by
        simpa [source, resizedAt] using resizedAt_getD operator parameterIndex lenBound n
      rw [getN]
      simp only [source, target, resizedAt, List.set_set]
    lengthDrop := lenDrop
    successor := successor
    parameterBound := by simpa [source, resizedAt] using bound
    parameterShape := by simpa [source, resizedAt] using shape
    inSegment := by
      refine ⟨?_, ?_⟩
      · simp [removed, start]
      · have getN : source.2.lengths.getD parameterIndex 0 = n := by
          simpa [source, resizedAt] using resizedAt_getD operator parameterIndex lenBound n
        rw [getN]
        simpa [removed, start] using Nat.add_lt_add_left oneLt
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex)
    segmentIsPrefix := by
      simp only [start, takenSlots, source, resizedAt, resizedAt_lengths_take]
    removedDecl :=
      resized_segment_decl operator parameterIndex bound shape n removed
        (Nat.le_add_right _ _) (Nat.add_lt_add_left zeroLt _)
    nextDecl :=
      resized_segment_decl operator parameterIndex bound shape n ⟨removed.val + 1, successor⟩
        (Nat.le_add_right _ _) (Nat.add_lt_add_left oneLt _)
    duplicate := by
      have leftAt :=
        splice_at operator parameterIndex bound shape n outside trees ⟨0, zeroLt⟩
          (resized_index_fit operator parameterIndex bound shape n 0 zeroLt)
          (resized_segment_decl operator parameterIndex bound shape n removed
            (Nat.le_add_right _ _) (Nat.add_lt_add_left zeroLt _))
      have rightAt :=
        splice_at operator parameterIndex bound shape n outside trees ⟨1, oneLt⟩
          (resized_index_fit operator parameterIndex bound shape n 1 oneLt)
          (resized_segment_decl operator parameterIndex bound shape n
            ⟨removed.val + 1, successor⟩
            (Nat.le_add_right _ _) (Nat.add_lt_add_left oneLt _))
      unfold segmentChild at leftAt rightAt
      simp only [source, sourceChildren] at leftAt ⊢
      rw [leftAt]
      have align :
          (⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
              (⟨1, oneLt⟩ : Fin n).val,
            resized_index_fit operator parameterIndex bound shape n 1 oneLt⟩ :
            Fin ((indexedSignature language).arity
              (resizedAt operator parameterIndex bound shape n)).length) =
            ⟨removed.val + 1, successor⟩ := by
        apply Fin.ext
        simp [removed]
      have bridge :=
        (atElement_fin (resizedAt operator parameterIndex bound shape n) align
          (resized_segment_decl operator parameterIndex bound shape n
            ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
                (⟨1, oneLt⟩ : Fin n).val,
              resized_index_fit operator parameterIndex bound shape n 1 oneLt⟩
            (Nat.le_add_right _ _) (Nat.add_lt_add_left oneLt _))
          (resized_segment_decl operator parameterIndex bound shape n ⟨removed.val + 1, successor⟩
            (Nat.le_add_right _ _) (Nat.add_lt_add_left oneLt _))
          (spliceChild operator parameterIndex bound shape n outside trees)).symm.trans rightAt
      rw [bridge]
      have zeroEq : (⟨0, zeroLt⟩ : Fin n) = ⟨0, by omega⟩ := by
        apply Fin.ext
        rfl
      have oneEq : (⟨1, oneLt⟩ : Fin n) = ⟨1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [zeroEq, oneEq]
      exact copies
    arityErase := by
      show (indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape (n - 1)) =
        ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape n)).eraseIdx removed.val
      have idx : removed.val =
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
        simp [removed]
      have eraseAt :
          ((indexedSignature language).arity
              (resizedAt operator parameterIndex bound shape n)).eraseIdx removed.val =
            ((indexedSignature language).arity
              (resizedAt operator parameterIndex bound shape n)).eraseIdx
              (takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                parameterIndex) :=
        congrArg
          (List.eraseIdx
            ((indexedSignature language).arity
              (resizedAt operator parameterIndex bound shape n)))
          idx
      rw [eraseAt]
      rw [resizedAt_arity operator parameterIndex bound shape (n - 1),
        resizedAt_arity operator parameterIndex bound shape n]
      have startLen := (segmentStart_length operator parameterIndex).symm
      have inFirst :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex <
            (expandSlots (operator.1.1.params.take parameterIndex)
                (operator.2.counts.take parameterIndex)
                (operator.2.lengths.take parameterIndex) ++
              List.replicate n ([], element)).length := by
        rw [List.length_append, List.length_replicate, ← startLen]
        exact Nat.add_lt_add_left zeroLt _
      rw [List.eraseIdx_append_of_lt_length inFirst]
      have atJoin :
          (expandSlots (operator.1.1.params.take parameterIndex)
              (operator.2.counts.take parameterIndex)
              (operator.2.lengths.take parameterIndex) ++
            List.replicate n ([], element)).eraseIdx
              (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) =
            expandSlots (operator.1.1.params.take parameterIndex)
              (operator.2.counts.take parameterIndex)
              (operator.2.lengths.take parameterIndex) ++
            (List.replicate n ([], element)).eraseIdx 0 := by
        rw [← startLen]
        have raw :=
          List.eraseIdx_append_of_length_le
            (Nat.le_refl
              (expandSlots (operator.1.1.params.take parameterIndex)
                (operator.2.counts.take parameterIndex)
                (operator.2.lengths.take parameterIndex)).length)
            (List.replicate n ([], element))
        rw [Nat.sub_self
          (expandSlots (operator.1.1.params.take parameterIndex)
            (operator.2.counts.take parameterIndex)
            (operator.2.lengths.take parameterIndex)).length] at raw
        exact raw
      rw [atJoin, List.eraseIdx_replicate, if_pos zeroLt, List.append_assoc]
    kept := by
      intro direction
      by_cases hLt : direction.val < removed.val
      · have hPrefix : direction.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
          simpa [removed] using hLt
        have dropBound : direction.val < ((indexedSignature language).arity source).length :=
          lenDrop ▸ Nat.lt_succ_of_lt direction.isLt
        let dropped : Fin ((indexedSignature language).arity source).length :=
          ⟨direction.val, dropBound⟩
        have sameDrop :
            dropped =
              dropDirection removed.val removed.isLt direction.val
                (by
                  have directionBound := direction.isLt
                  omega) := by
          apply Fin.ext
          simp [dropped, dropDirection, if_pos hLt, Fin.val_mk]
        have hDrop : dropped.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
          simpa [dropped] using hPrefix
        have leftSrc :=
          splice_prefix_src (Γ := Γ) operator parameterIndex bound shape (n - 1) direction hPrefix
        have rightSrc :=
          splice_prefix_src (Γ := Γ) operator parameterIndex bound shape n dropped hDrop
        have finEq :
            (⟨direction.val,
                resized_prefix_fit operator parameterIndex bound shape (n - 1) hPrefix⟩ :
              Fin ((indexedSignature language).arity operator).length) =
              ⟨dropped.val,
                resized_prefix_fit operator parameterIndex bound shape n hDrop⟩ := by
          apply Fin.ext
          simp [dropped]
        have srcT :
            (polynomial (indexedSignature language)).src (Γ, sort) target direction =
              (polynomial (indexedSignature language)).src (Γ, sort) source dropped :=
          leftSrc.trans
            ((congrArg ((polynomial (indexedSignature language)).src (Γ, sort) operator) finEq).trans
              rightSrc.symm)
        rw [← sameDrop]
        refine ⟨srcT, ?_⟩
        rw [castEq_iff_heq]
        unfold targetChildren sourceChildren spliceChild
        simp only [dif_pos hPrefix, dif_pos hDrop]
        rw [cast_heq_iff_heq]
        apply HEq.symm
        rw [cast_heq_iff_heq]
      · by_cases hSeg : direction.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
              (n - 1)
        · have loT :
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
                direction.val := by
            simpa [removed] using Nat.not_lt.mp hLt
          have dropBound : direction.val + 1 <
              ((indexedSignature language).arity source).length :=
            lenDrop ▸ Nat.succ_lt_succ direction.isLt
          let dropped : Fin ((indexedSignature language).arity source).length :=
            ⟨direction.val + 1, dropBound⟩
          have sameDrop :
              dropped =
                dropDirection removed.val removed.isLt direction.val
                  (by
                    have directionBound := direction.isLt
                    omega) := by
            apply Fin.ext
            simp [dropped, dropDirection, if_neg hLt, Fin.val_mk]
          have notPrefix : ¬ direction.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
            simpa [removed] using hLt
          have loS : takenSlots operator.1.1.params operator.2.counts operator.2.lengths
              parameterIndex ≤ dropped.val := by
            simp only [dropped]
            exact Nat.le_trans loT (Nat.le_succ direction.val)
          have hiS : dropped.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
                n := by
            simp only [dropped]
            omega
          have notPrefixD : ¬ dropped.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
            simp only [dropped]
            exact Nat.not_lt_of_ge (Nat.le_trans loT (Nat.le_succ direction.val))
          have leftSrc :=
            splice_segment_src (Γ := Γ) operator parameterIndex bound shape (n - 1) direction loT
              hSeg
          have rightSrc :=
            splice_segment_src (Γ := Γ) operator parameterIndex bound shape n dropped loS hiS
          have srcT :
              (polynomial (indexedSignature language)).src (Γ, sort) target direction =
                (polynomial (indexedSignature language)).src (Γ, sort) source dropped :=
            leftSrc.trans rightSrc.symm
          rw [← sameDrop]
          refine ⟨srcT, ?_⟩
          rw [castEq_iff_heq]
          unfold targetChildren sourceChildren spliceChild shorter
          simp only [dif_neg notPrefix, dif_pos hSeg, dif_neg notPrefixD, dif_pos hiS]
          rw [cast_heq_iff_heq]
          apply HEq.symm
          rw [cast_heq_iff_heq]
          apply HEq.symm
          refine congr_arg_heq trees ?_
          apply Fin.ext
          simp only [dropped]
          omega
        · have hPast :
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
                (n - 1) ≤ direction.val :=
            Nat.not_lt.mp hSeg
          have dropBound : direction.val + 1 <
              ((indexedSignature language).arity source).length :=
            lenDrop ▸ Nat.succ_lt_succ direction.isLt
          let dropped : Fin ((indexedSignature language).arity source).length :=
            ⟨direction.val + 1, dropBound⟩
          have sameDrop :
              dropped =
                dropDirection removed.val removed.isLt direction.val
                  (by
                    have directionBound := direction.isLt
                    omega) := by
            apply Fin.ext
            simp [dropped, dropDirection, if_neg hLt, Fin.val_mk]
          have notPrefix : ¬ direction.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
            simpa [removed] using hLt
          have pastDir :
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
                  n ≤ direction.val + 1 := by
            omega
          have pastD : takenSlots operator.1.1.params operator.2.counts operator.2.lengths
              parameterIndex + n ≤ dropped.val := by
            simpa [dropped, Fin.val_mk] using pastDir
          have notPrefixD : ¬ dropped.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
            simp only [dropped]
            exact Nat.not_lt_of_ge (Nat.le_trans (Nat.le_of_not_lt notPrefix) (Nat.le_succ _))
          have notSegD : ¬ dropped.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
                n :=
            Nat.not_lt_of_ge pastD
          have leftSrc :=
            splice_suffix_src (Γ := Γ) operator parameterIndex bound shape (n - 1) direction hPast
          have rightSrc :=
            splice_suffix_src (Γ := Γ) operator parameterIndex bound shape n dropped pastD
          have srcT :
              (polynomial (indexedSignature language)).src (Γ, sort) target direction =
                (polynomial (indexedSignature language)).src (Γ, sort) source dropped := by
            have sourceSrc :
                (polynomial (indexedSignature language)).src (Γ, sort) source dropped =
                  (polynomial (indexedSignature language)).src (Γ, sort)
                    (resizedAt operator parameterIndex bound shape n) dropped := rfl
            rw [leftSrc, sourceSrc, rightSrc]
            apply congrArg
              ((polynomial (indexedSignature language)).src (Γ, sort) operator)
            apply Fin.ext
            simp only [dropped]
            omega
          rw [← sameDrop]
          refine ⟨srcT, ?_⟩
          rw [castEq_iff_heq]
          unfold targetChildren sourceChildren spliceChild
          simp only [dif_neg notPrefix, dif_neg hSeg, dif_neg notPrefixD, dif_neg notSegD]
          rw [cast_heq_iff_heq]
          apply HEq.symm
          rw [cast_heq_iff_heq]
          apply HEq.symm
          refine congr_arg_heq outside ?_
          apply Fin.ext
          simp only [dropped]
          omega
  }
  simpa [spliceNode, source, target, sourceChildren, targetChildren, removed, start, shorter] using
    TreeCong.setDup source target sourceChildren targetChildren removed parameterIndex start
      deletion

/-- The element trees of one hash-set parameter, read at that parameter's length. -/
def segmentTrees {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (kEq : k = operator.2.lengths.getD parameterIndex 0)
    (children : Child language Γ sort operator) :
    Fin k → Tree language (Γ, element) :=
  fun index =>
    atElement operator
      ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val,
        by
          have indexLt := index.isLt
          have room := segment_room operator bound (by rw [shape]; rfl)
          rw [← kEq] at room
          omega⟩
      (by
        rw [List.get_eq_getElem]
        exact expand_segment_getElem operator.1.1.params operator.2.counts
          operator.2.lengths operator.2.counts_length operator.2.lengths_length bound
          shape (index.cast kEq)
          (by
            have indexLt := index.isLt
            have room := segment_room operator bound (by rw [shape]; rfl)
            have sameLength :
                (expandSlots operator.1.1.params operator.2.counts
                    operator.2.lengths).length =
                  ((indexedSignature language).arity operator).length := rfl
            have castVal : (index.cast kEq).val = index.val := rfl
            rw [← sameLength] at room
            omega))
      children

/-- A splice at the stored length does not depend on which proof reads the segment. -/
theorem spliceNode_at_self {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    (k : Nat)
    (kEq : k = operator.2.lengths.getD parameterIndex 0)
    (trees : Fin k → Tree language (Γ, element))
    (agree : ∀ index,
      trees index = segmentTrees operator parameterIndex bound shape k kEq outside index) :
    spliceNode operator parameterIndex bound shape outside k trees =
      IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator outside := by
  have base := spliceNode_segment operator parameterIndex bound shape outside k kEq
  refine (spliceNode_cast operator parameterIndex bound shape outside ?point).trans base
  intro index
  rw [agree]
  unfold segmentTrees
  apply atElement_fin
  · apply Fin.ext
    rfl

/-- The induction hypothesis, read on the element trees of one hash-set segment. -/
theorem segmentTrees_ih {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (kEq : k = operator.2.lengths.getD parameterIndex 0)
    (children : Child language Γ sort operator)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (children direction)) (toPattern other) →
          TreeCong language (children direction) other) :
    ∀ index : Fin k, ∀ other : Tree language (Γ, element),
      PatternCong
          (toPattern (segmentTrees operator parameterIndex bound shape k kEq children index))
          (toPattern other) →
        TreeCong language
          (segmentTrees operator parameterIndex bound shape k kEq children index) other := by
  intro index other related
  have fit :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val <
        ((indexedSignature language).arity operator).length := by
    have indexLt := index.isLt
    have room := segment_room operator bound (by rw [shape]; rfl)
    rw [← kEq] at room
    omega
  let direction : Fin ((indexedSignature language).arity operator).length :=
    ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        index.val, fit⟩
  have decl :
      ((indexedSignature language).arity operator).get direction = ([], element) := by
    rw [List.get_eq_getElem]
    exact expand_segment_getElem operator.1.1.params operator.2.counts
      operator.2.lengths operator.2.counts_length operator.2.lengths_length bound
      shape (index.cast kEq)
      (by
        have indexLt := index.isLt
        have room := segment_room operator bound (by rw [shape]; rfl)
        have sameLength :
            (expandSlots operator.1.1.params operator.2.counts operator.2.lengths).length =
              ((indexedSignature language).arity operator).length := rfl
        have castVal : (index.cast kEq).val = index.val := rfl
        rw [← sameLength] at room
        omega)
  have srcEq :
      (polynomial (indexedSignature language)).src (Γ, sort) operator direction = (Γ, element) := by
    rw [polynomial_direction, decl]
    rfl
  have treeEq :
      segmentTrees operator parameterIndex bound shape k kEq children index =
        cast (congrArg (Tree language) srcEq) (children direction) := by
    unfold segmentTrees atElement
    apply eq_of_heq
    rw [cast_heq_iff_heq]
    apply HEq.symm
    rw [cast_heq_iff_heq]
  let otherChild : Tree language
      ((polynomial (indexedSignature language)).src (Γ, sort) operator direction) :=
    cast (congrArg (Tree language) srcEq.symm) other
  have relatedChild :
      PatternCong (toPattern (children direction)) (toPattern otherChild) := by
    have leftPrint :
        toPattern (segmentTrees operator parameterIndex bound shape k kEq children index) =
          toPattern (children direction) := by
      rw [treeEq]
      exact toPattern_cast srcEq (children direction)
    rw [← leftPrint, toPattern_cast srcEq.symm other]
    exact related
  have step := ih direction otherChild relatedChild
  have back : cast (congrArg (Tree language) srcEq) otherChild = other := by
    unfold otherChild
    apply eq_of_heq
    rw [cast_heq_iff_heq, cast_heq_iff_heq]
  rw [treeEq]
  have transported := treeCong_cast srcEq step
  rw [back] at transported
  exact transported

/-- Replace the element family of one hash-set parameter whose length stays fixed. -/
theorem set_overlay_current {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (leftChildren current : Child language Γ sort operator)
    (k : Nat)
    (kEq : k = operator.2.lengths.getD parameterIndex 0)
    (coverL : ∀ i : Fin k, ∃ j : Fin k,
      PatternCong
        (toPattern (segmentTrees operator parameterIndex bound shape k kEq leftChildren i))
        (toPattern (segmentTrees operator parameterIndex bound shape k kEq current j)))
    (coverR : ∀ j : Fin k, ∃ i : Fin k,
      PatternCong
        (toPattern (segmentTrees operator parameterIndex bound shape k kEq leftChildren i))
        (toPattern (segmentTrees operator parameterIndex bound shape k kEq current j)))
    (ihTrees : ∀ i : Fin k, ∀ other : Tree language (Γ, element),
      PatternCong
          (toPattern (segmentTrees operator parameterIndex bound shape k kEq leftChildren i))
          (toPattern other) →
        TreeCong language
          (segmentTrees operator parameterIndex bound shape k kEq leftChildren i) other) :
    ∃ current' : Child language Γ sort operator,
      TreeCong language
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator current')
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator current) ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        direction.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex →
          current' direction = current direction) ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
            direction.val →
          direction.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                parameterIndex + k →
            current' direction = leftChildren direction) ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
            direction.val →
          current' direction = current direction) := by
  have opEq := resizedAt_eq_self operator parameterIndex bound shape k kEq
  let leftTrees := segmentTrees operator parameterIndex bound shape k kEq leftChildren
  let rightTrees := segmentTrees operator parameterIndex bound shape k kEq current
  let raw := spliceChild operator parameterIndex bound shape k current leftTrees
  let current' : Child language Γ sort operator :=
    cast (congrArg (Child language Γ sort) opEq) raw
  refine ⟨current', ?_, ?_, ?_, ?_⟩
  · have compared :=
      setCover_engine
        (fun k' family => spliceNode operator parameterIndex bound shape current k' family)
        (fun {_k} {_left} {_right} permuted =>
          spliceNode_perm operator parameterIndex bound shape current permuted)
        (fun {_k} {_left} {_right} steps =>
          spliceNode_point operator parameterIndex bound shape current steps)
        (fun {_n} wide family copies =>
          spliceNode_dup operator parameterIndex bound shape current wide family copies)
        (fun {_k} {_left} {_right} agree =>
          spliceNode_cast operator parameterIndex bound shape current agree)
        (k + k) leftTrees rightTrees (Nat.le_refl _) coverL coverR ihTrees
    have leftNode :
        spliceNode operator parameterIndex bound shape current k leftTrees =
          IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator current' := by
      unfold spliceNode
      exact liftBind_op opEq raw
    have rightNode :
        spliceNode operator parameterIndex bound shape current k rightTrees =
          IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator current :=
      spliceNode_at_self operator parameterIndex bound shape current k kEq rightTrees
        (fun _ => rfl)
    rw [leftNode, rightNode] at compared
    exact compared
  · intro direction low
    apply eq_of_heq
    refine HEq.trans (cast_child_direction opEq raw direction) ?_
    let moved : Fin ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).length :=
      Fin.cast
        (congrArg
          (fun op : (indexedSignature language).Op sort =>
            ((indexedSignature language).arity op).length)
          opEq.symm)
        direction
    change HEq
      (spliceChild operator parameterIndex bound shape k current leftTrees moved)
      (current direction)
    have movedVal : moved.val = direction.val := by simp [moved]
    unfold spliceChild
    have inPrefix : moved.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
      rw [movedVal]
      exact low
    simp only [dif_pos inPrefix]
    rw [cast_heq_iff_heq]
    refine congr_arg_heq current ?_
    apply Fin.ext
    exact movedVal
  · intro direction low high
    apply eq_of_heq
    refine HEq.trans (cast_child_direction opEq raw direction) ?_
    let moved : Fin ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).length :=
      Fin.cast
        (congrArg
          (fun op : (indexedSignature language).Op sort =>
            ((indexedSignature language).arity op).length)
          opEq.symm)
        direction
    change HEq
      (spliceChild operator parameterIndex bound shape k current leftTrees moved)
      (leftChildren direction)
    have movedVal : moved.val = direction.val := by simp [moved]
    unfold spliceChild
    have notPrefix : ¬ moved.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
      rw [movedVal]
      exact Nat.not_lt_of_ge low
    have inSeg : moved.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k := by
      rw [movedVal]
      exact high
    simp only [dif_neg notPrefix, dif_pos inSeg]
    unfold leftTrees segmentTrees atElement
    rw [cast_heq_iff_heq, cast_heq_iff_heq]
    refine congr_arg_heq leftChildren ?_
    apply Fin.ext
    simp [movedVal]
    omega
  · intro direction high
    apply eq_of_heq
    refine HEq.trans (cast_child_direction opEq raw direction) ?_
    let moved : Fin ((indexedSignature language).arity
        (resizedAt operator parameterIndex bound shape k)).length :=
      Fin.cast
        (congrArg
          (fun op : (indexedSignature language).Op sort =>
            ((indexedSignature language).arity op).length)
          opEq.symm)
        direction
    change HEq
      (spliceChild operator parameterIndex bound shape k current leftTrees moved)
      (current direction)
    have movedVal : moved.val = direction.val := by simp [moved]
    unfold spliceChild
    have notPrefix : ¬ moved.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
      rw [movedVal]
      exact Nat.not_lt_of_ge
        (Nat.le_trans
          (Nat.le_add_right
            (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex)
            k)
          high)
    have notSeg : ¬ moved.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k := by
      rw [movedVal]
      exact Nat.not_lt_of_ge high
    simp only [dif_neg notPrefix, dif_neg notSeg]
    rw [cast_heq_iff_heq]
    refine congr_arg_heq current ?_
    apply Fin.ext
    simp [movedVal, kEq]

/-- Change one hash-set length to a covered family. The other directions stay. -/
theorem adopt_one_set {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (outside : Child language Γ sort operator)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (outside direction)) (toPattern other) →
          TreeCong language (outside direction) other)
    {k : Nat}
    (trees : Fin k → Tree language (Γ, element))
    (coverL : ∀ i : Fin (operator.2.lengths.getD parameterIndex 0),
      ∃ j : Fin k,
        PatternCong
          (toPattern (segmentTrees operator parameterIndex bound shape
            (operator.2.lengths.getD parameterIndex 0) rfl outside i))
          (toPattern (trees j)))
    (coverR : ∀ j : Fin k,
      ∃ i : Fin (operator.2.lengths.getD parameterIndex 0),
        PatternCong
          (toPattern (segmentTrees operator parameterIndex bound shape
            (operator.2.lengths.getD parameterIndex 0) rfl outside i))
          (toPattern (trees j))) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator outside)
      (spliceNode operator parameterIndex bound shape outside k trees) := by
  have base :=
    spliceNode_at_self operator parameterIndex bound shape outside
      (operator.2.lengths.getD parameterIndex 0) rfl
      (segmentTrees operator parameterIndex bound shape
        (operator.2.lengths.getD parameterIndex 0) rfl outside)
      (fun _ => rfl)
  have compared :=
    setCover_engine
      (fun k' family => spliceNode operator parameterIndex bound shape outside k' family)
      (fun {_k} {_left} {_right} permuted =>
        spliceNode_perm operator parameterIndex bound shape outside permuted)
      (fun {_k} {_left} {_right} steps =>
        spliceNode_point operator parameterIndex bound shape outside steps)
      (fun {_n} wide family copies =>
        spliceNode_dup operator parameterIndex bound shape outside wide family copies)
      (fun {_k} {_left} {_right} agree =>
        spliceNode_cast operator parameterIndex bound shape outside agree)
      (operator.2.lengths.getD parameterIndex 0 + k)
      (segmentTrees operator parameterIndex bound shape
        (operator.2.lengths.getD parameterIndex 0) rfl outside)
      trees (Nat.le_refl _) coverL coverR
      (segmentTrees_ih operator parameterIndex bound shape
        (operator.2.lengths.getD parameterIndex 0) rfl outside ih)
  rw [← base]
  exact compared

/-- One hash-set parameter, already at the same length on both sides. The set
cover overlays the left element trees; directions outside that segment stay. -/
theorem hashSet_step {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (done : Nat) (doneBound : done < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨done, doneBound⟩) =
      some (.hashSet, element))
    (leftChildren rightChildren current : Child language Γ sort operator)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths))
    (rightToCurrent : TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator rightChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator current))
    (aligned : ∀ direction : Fin ((indexedSignature language).arity operator).length,
      direction.val <
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths done →
        PatternCong (toPattern (leftChildren direction)) (toPattern (current direction)))
    (suffix : ∀ direction : Fin ((indexedSignature language).arity operator).length,
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths done ≤
          direction.val →
        current direction = rightChildren direction) :
    ∃ current' : Child language Γ sort operator,
      TreeCong language
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator rightChildren)
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator current') ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        direction.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) →
          PatternCong (toPattern (leftChildren direction))
            (toPattern (current' direction))) ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) ≤
            direction.val →
          current' direction = rightChildren direction) := by
  let start := takenSlots operator.1.1.params operator.2.counts operator.2.lengths done
  let segLen := operator.2.lengths.getD done 0
  have segEq : segLen = operator.2.lengths.getD done 0 := rfl
  have stepEq :=
    takenSlots_step operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length done doneBound
  have widthEq : directionsOf (operator.1.1.params.get ⟨done, doneBound⟩)
      (operator.2.counts.getD done 0) (operator.2.lengths.getD done 0) = segLen := by
    rw [directionsOf, shape]
  have lenL :=
    assemblePrinted_length (fun direction => toPattern (leftChildren direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length
  have lenR :=
    assemblePrinted_length (fun direction => toPattern (rightChildren direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length
  have atArgs :=
    (List.forall₂_iff_get.mp argRel).2 done (lenL.symm ▸ doneBound) (lenR.symm ▸ doneBound)
  have leftArg :=
    assemble_at_set (fun direction => toPattern (leftChildren direction))
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length done doneBound shape
  have rightArg :=
    assemble_at_set (fun direction => toPattern (rightChildren direction))
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length done doneBound shape
  rw [← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenL.symm ▸ doneBound⟩),
    ← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenR.symm ▸ doneBound⟩)] at atArgs
  rw [leftArg, rightArg] at atArgs
  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, elementsRel⟩ :=
    patternCong_set_elements atArgs
      (Or.inl ⟨List.ofFn fun index : Fin segLen =>
        nthPrinted (fun direction => toPattern (leftChildren direction))
          (start + index.val), rfl⟩)
  simp only [Pattern.collection.injEq] at leftEq rightEq
  obtain ⟨_, leftList, _⟩ := leftEq
  obtain ⟨_, rightList, _⟩ := rightEq
  subst leftList
  subst rightList
  have covers := setElementRel_both elementsRel
  have dirBound (index : Fin segLen) :
      start + index.val < ((indexedSignature language).arity operator).length := by
    have indexLt := index.isLt
    have room := segment_room operator doneBound (by rw [shape]; rfl)
    rw [← segEq] at room
    simp only [start] at room ⊢
    omega
  have leftPrinted :
      List.ofFn (fun index =>
          toPattern (segmentTrees operator done doneBound shape segLen segEq leftChildren index)) =
        List.ofFn (fun index : Fin segLen =>
          nthPrinted (fun direction => toPattern (leftChildren direction))
            (start + index.val)) := by
    refine ofFn_pointwise ?_
    intro index
    have asTree :
        segmentTrees operator done doneBound shape segLen segEq leftChildren index =
          atElement operator ⟨start + index.val, dirBound index⟩
            (by
              rw [List.get_eq_getElem]
              exact expand_segment_getElem operator.1.1.params operator.2.counts
                operator.2.lengths operator.2.counts_length operator.2.lengths_length
                doneBound shape (index.cast segEq)
                (by
                  have indexLt := index.isLt
                  have room := segment_room operator doneBound (by rw [shape]; rfl)
                  have sameLength :
                      (expandSlots operator.1.1.params operator.2.counts
                          operator.2.lengths).length =
                        ((indexedSignature language).arity operator).length := rfl
                  have castVal : (index.cast segEq).val = index.val := rfl
                  rw [← sameLength] at room
                  omega))
            leftChildren := by
      unfold segmentTrees
      apply atElement_fin
      · apply Fin.ext
        simp [start]
    rw [asTree, toPattern_atElement]
    exact (nthPrinted_of_lt
      (fun direction => toPattern (leftChildren direction)) (dirBound index)).symm
  have rightPrinted :
      List.ofFn (fun index =>
          toPattern (segmentTrees operator done doneBound shape segLen segEq current index)) =
        List.ofFn (fun index : Fin segLen =>
          nthPrinted (fun direction => toPattern (rightChildren direction))
            (start + index.val)) := by
    refine ofFn_pointwise ?_
    intro index
    have asTree :
        segmentTrees operator done doneBound shape segLen segEq current index =
          atElement operator ⟨start + index.val, dirBound index⟩
            (by
              rw [List.get_eq_getElem]
              exact expand_segment_getElem operator.1.1.params operator.2.counts
                operator.2.lengths operator.2.counts_length operator.2.lengths_length
                doneBound shape (index.cast segEq)
                (by
                  have indexLt := index.isLt
                  have room := segment_room operator doneBound (by rw [shape]; rfl)
                  have sameLength :
                      (expandSlots operator.1.1.params operator.2.counts
                          operator.2.lengths).length =
                        ((indexedSignature language).arity operator).length := rfl
                  have castVal : (index.cast segEq).val = index.val := rfl
                  rw [← sameLength] at room
                  omega))
            current := by
      unfold segmentTrees
      apply atElement_fin
      · apply Fin.ext
        simp [start]
    rw [asTree, toPattern_atElement]
    have childEq :
        current ⟨start + index.val, dirBound index⟩ =
          rightChildren ⟨start + index.val, dirBound index⟩ :=
      suffix ⟨start + index.val, dirBound index⟩ (by simp [start])
    rw [childEq]
    exact (nthPrinted_of_lt
      (fun direction => toPattern (rightChildren direction)) (dirBound index)).symm
  have coverL : ∀ i : Fin segLen, ∃ j : Fin segLen,
      PatternCong
        (toPattern (segmentTrees operator done doneBound shape segLen segEq leftChildren i))
        (toPattern (segmentTrees operator done doneBound shape segLen segEq current j)) := by
    intro i
    have mem : toPattern (segmentTrees operator done doneBound shape segLen segEq leftChildren i) ∈
        List.ofFn fun index : Fin segLen =>
          nthPrinted (fun direction => toPattern (leftChildren direction))
            (start + index.val) := by
      rw [← leftPrinted]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨image, imageMem, step⟩ := covers.1 _ mem
    have imageMem' : image ∈
        List.ofFn fun index =>
          toPattern (segmentTrees operator done doneBound shape segLen segEq current index) := by
      rw [rightPrinted]
      exact imageMem
    obtain ⟨j, imageEq⟩ := List.mem_ofFn.mp imageMem'
    exact ⟨j, by simpa [imageEq] using step⟩
  have coverR : ∀ j : Fin segLen, ∃ i : Fin segLen,
      PatternCong
        (toPattern (segmentTrees operator done doneBound shape segLen segEq leftChildren i))
        (toPattern (segmentTrees operator done doneBound shape segLen segEq current j)) := by
    intro j
    have mem : toPattern (segmentTrees operator done doneBound shape segLen segEq current j) ∈
        List.ofFn fun index : Fin segLen =>
          nthPrinted (fun direction => toPattern (rightChildren direction))
            (start + index.val) := by
      rw [← rightPrinted]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    obtain ⟨image, imageMem, step⟩ := covers.2 _ mem
    have imageMem' : image ∈
        List.ofFn fun index =>
          toPattern (segmentTrees operator done doneBound shape segLen segEq leftChildren index) := by
      rw [leftPrinted]
      exact imageMem
    obtain ⟨i, imageEq⟩ := List.mem_ofFn.mp imageMem'
    exact ⟨i, by simpa [imageEq] using step⟩
  obtain ⟨current', forward, samePrefix, sameSegment, sameSuffix⟩ :=
    set_overlay_current operator done doneBound shape leftChildren current segLen segEq
      coverL coverR
      (segmentTrees_ih operator done doneBound shape segLen segEq leftChildren ih)
  refine ⟨current', rightToCurrent.trans (TreeCong.symm forward), ?_, ?_⟩
  · intro direction bound
    by_cases earlier : direction.val < start
    · have stayed : current' direction = current direction :=
        samePrefix direction (by simpa [start] using earlier)
      rw [stayed]
      exact aligned direction (by simpa [start] using earlier)
    · have inSeg : direction.val < start + segLen := by
        have slots :
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
              start + segLen := by
          rw [stepEq, widthEq]
        omega
      have childEq : current' direction = leftChildren direction :=
        sameSegment direction (by simpa [start] using Nat.le_of_not_lt earlier)
          (by simpa [start] using inSeg)
      rw [childEq]
      exact PatternCong.refl _
  · intro direction bound
    have slots :
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
          start + segLen := by
      rw [stepEq, widthEq]
    have past : start + segLen ≤ direction.val := by omega
    have stayed : current' direction = current direction :=
      sameSuffix direction (by simpa [start] using past)
    rw [stayed]
    exact suffix direction (by simpa [start] using Nat.le_trans (Nat.le_add_right start segLen) past)

theorem extend_alignment
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (done : Nat) (doneBound : done < operator.1.1.params.length)
    (leftChildren rightChildren current : Child language Γ sort operator)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths))
    (rightToCurrent : TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator rightChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator current))
    (aligned : ∀ direction : Fin ((indexedSignature language).arity operator).length,
      direction.val <
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths done →
        PatternCong (toPattern (leftChildren direction)) (toPattern (current direction)))
    (suffix : ∀ direction : Fin ((indexedSignature language).arity operator).length,
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths done ≤
          direction.val →
        current direction = rightChildren direction) :
    ∃ current' : Child language Γ sort operator,
      TreeCong language
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator rightChildren)
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator current') ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        direction.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) →
          PatternCong (toPattern (leftChildren direction))
            (toPattern (current' direction))) ∧
      (∀ direction : Fin ((indexedSignature language).arity operator).length,
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) ≤
            direction.val →
          current' direction = rightChildren direction) := by
  let start := takenSlots operator.1.1.params operator.2.counts operator.2.lengths done
  have stepEq :=
    takenSlots_step operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length done doneBound
  have nextLe : done + 1 ≤ operator.1.1.params.length := by omega
  have nextSlots :=
    takenSlots_le operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length nextLe
  have widthRoom :
      start + directionsOf (operator.1.1.params.get ⟨done, doneBound⟩)
          (operator.2.counts.getD done 0) (operator.2.lengths.getD done 0) ≤
        ((indexedSignature language).arity operator).length := by
    rw [← stepEq, expandSlots_length]
    exact nextSlots
  have lenL :=
    assemblePrinted_length (fun direction => toPattern (leftChildren direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length
  have lenR :=
    assemblePrinted_length (fun direction => toPattern (rightChildren direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length
  have atArgs :=
    (List.forall₂_iff_get.mp argRel).2 done (lenL.symm ▸ doneBound) (lenR.symm ▸ doneBound)
  cases reading : baseCollection? (operator.1.1.params.get ⟨done, doneBound⟩) with
  | some packed =>
      obtain ⟨kind, element⟩ := packed
      cases kind with
      | hashSet =>
          exact hashSet_step operator done doneBound reading leftChildren rightChildren
            current ih argRel rightToCurrent aligned suffix
      | vec =>
          let segLen := operator.2.lengths.getD done 0
          have widthEq : directionsOf (operator.1.1.params.get ⟨done, doneBound⟩)
              (operator.2.counts.getD done 0) (operator.2.lengths.getD done 0) = segLen := by
            rw [directionsOf, reading]
          by_cases empty : segLen = 0
          · refine ⟨current, rightToCurrent, ?_, ?_⟩
            · intro direction bound
              have sameSlots :
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                    start := by
                rw [stepEq, widthEq, empty]
                simp [start]
              exact aligned direction (by omega)
            · intro direction bound
              have sameSlots :
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                    start := by
                rw [stepEq, widthEq, empty]
                simp [start]
              exact suffix direction (by omega)
          · have leftArg :=
              assemble_at_vec (fun direction => toPattern (leftChildren direction))
                operator.1.1.params operator.2.counts operator.2.lengths
                operator.2.counts_length operator.2.lengths_length done doneBound reading
            have rightArg :=
              assemble_at_vec (fun direction => toPattern (rightChildren direction))
                operator.1.1.params operator.2.counts operator.2.lengths
                operator.2.counts_length operator.2.lengths_length done doneBound reading
            rw [← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenL.symm ▸ doneBound⟩),
              ← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenR.symm ▸ doneBound⟩)] at atArgs
            rw [leftArg, rightArg] at atArgs
            obtain ⟨_leftElements, _rightElements, leftEq, rightEq, pointwise⟩ :=
              patternCong_vec_elements atArgs
                (Or.inl ⟨List.ofFn fun index : Fin segLen =>
                  nthPrinted (fun direction => toPattern (leftChildren direction))
                    (start + index.val), rfl⟩)
            simp only [Pattern.collection.injEq] at leftEq rightEq
            obtain ⟨_, leftList, _⟩ := leftEq
            obtain ⟨_, rightList, _⟩ := rightEq
            subst leftList
            subst rightList
            refine ⟨current, rightToCurrent, ?_, ?_⟩
            · intro direction bound
              by_cases earlier : direction.val < start
              · exact aligned direction earlier
              · have indexFit : direction.val - start < segLen := by
                  have slots :
                      takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                          (done + 1) = start + segLen := by
                    rw [stepEq, widthEq]
                  omega
                let index : Fin segLen := ⟨direction.val - start, indexFit⟩
                have atIndex :=
                  (List.forall₂_iff_get.mp pointwise).2 index.val
                    (by rw [List.length_ofFn]; exact index.isLt)
                    (by rw [List.length_ofFn]; exact index.isLt)
                rw [ofFn_get_apply, ofFn_get_apply] at atIndex
                have dirFit : direction.val <
                    ((indexedSignature language).arity operator).length := direction.isLt
                have startFit : start + index.val <
                    ((indexedSignature language).arity operator).length := by
                  omega
                have asStart : direction.val = start + index.val := by
                  simp [index]
                  omega
                have dirEq :
                    direction = ⟨start + index.val, startFit⟩ := by
                  apply Fin.ext
                  exact asStart
                have childEq :
                    current ⟨start + index.val, startFit⟩ =
                      rightChildren ⟨start + index.val, startFit⟩ :=
                  suffix _ (Nat.le_add_right _ _)
                rw [nthPrinted_of_lt _ (by omega : start + index.val <
                    ((indexedSignature language).arity operator).length),
                  nthPrinted_of_lt _ (by omega : start + index.val <
                    ((indexedSignature language).arity operator).length)] at atIndex
                rw [dirEq, childEq]
                simpa [Fin.eta] using atIndex
            · intro direction bound
              have slots :
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                    start + segLen := by
                rw [stepEq, widthEq]
              exact suffix direction (by omega)
      | hashBag =>
          let segLen := operator.2.lengths.getD done 0
          have widthEq : directionsOf (operator.1.1.params.get ⟨done, doneBound⟩)
              (operator.2.counts.getD done 0) (operator.2.lengths.getD done 0) = segLen := by
            rw [directionsOf, reading]
          by_cases empty : segLen = 0
          · refine ⟨current, rightToCurrent, ?_, ?_⟩
            · intro direction bound
              have sameSlots :
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                    start := by
                rw [stepEq, widthEq, empty]
                simp [start]
              exact aligned direction (by omega)
            · intro direction bound
              have sameSlots :
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                    start := by
                rw [stepEq, widthEq, empty]
                simp [start]
              exact suffix direction (by omega)
          · have leftArg :=
              assemble_at_bag (fun direction => toPattern (leftChildren direction))
                operator.1.1.params operator.2.counts operator.2.lengths
                operator.2.counts_length operator.2.lengths_length done doneBound reading
            have rightArg :=
              assemble_at_bag (fun direction => toPattern (rightChildren direction))
                operator.1.1.params operator.2.counts operator.2.lengths
                operator.2.counts_length operator.2.lengths_length done doneBound reading
            rw [← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenL.symm ▸ doneBound⟩),
              ← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenR.symm ▸ doneBound⟩)] at atArgs
            rw [leftArg, rightArg] at atArgs
            obtain ⟨_leftElements, _rightElements, leftEq, rightEq, elementsRel⟩ :=
              patternCong_bag_elements atArgs
                (Or.inl ⟨List.ofFn fun index : Fin segLen =>
                  nthPrinted (fun direction => toPattern (leftChildren direction))
                    (start + index.val), rfl⟩)
            simp only [Pattern.collection.injEq] at leftEq rightEq
            obtain ⟨_, leftList, _⟩ := leftEq
            obtain ⟨_, rightList, _⟩ := rightEq
            subst leftList
            subst rightList
            obtain ⟨alignedList, permAligned, pointwise⟩ := bagElementRel_align elementsRel
            have fitLen : start + segLen ≤
                ((indexedSignature language).arity operator).length := by
              have room := widthRoom
              rw [widthEq] at room
              exact room
            have uniform (index : Fin segLen) :
                ((indexedSignature language).arity operator).get
                    ⟨start + index.val, by
                      have indexLt := index.isLt
                      omega⟩ = ([], element) := by
              rw [List.get_eq_getElem]
              exact expand_segment_getElem operator.1.1.params operator.2.counts
                operator.2.lengths operator.2.counts_length operator.2.lengths_length doneBound
                reading index (by
                  have indexLt := index.isLt
                  have sameLength :
                      (expandSlots operator.1.1.params operator.2.counts
                          operator.2.lengths).length =
                        ((indexedSignature language).arity operator).length := rfl
                  rw [sameLength]
                  omega)
            let rightElem : Fin segLen → Tree language (Γ, element) :=
              fun index =>
                atElement operator ⟨start + index.val, by
                  have indexLt := index.isLt
                  omega⟩ (uniform index) rightChildren
            have rightPrinted :
                List.ofFn (fun index => toPattern (rightElem index)) =
                  List.ofFn fun index : Fin segLen =>
                    nthPrinted (fun direction => toPattern (rightChildren direction))
                      (start + index.val) := by
              refine ofFn_pointwise ?_
              intro index
              rw [toPattern_atElement]
              have printedBound :
                  start + index.val < ((indexedSignature language).arity operator).length := by
                have indexLt := index.isLt
                omega
              exact (nthPrinted_of_lt
                (fun direction => toPattern (rightChildren direction)) printedBound).symm
            have alignedLength : alignedList.length = segLen := by
              have permLength := List.Perm.length_eq permAligned
              simp only [List.length_ofFn] at permLength
              exact permLength.symm
            have alignedBound (index : Fin segLen) : index.val < alignedList.length :=
              alignedLength.symm ▸ index.isLt
            have inPrinted (index : Fin segLen) :
                alignedList.get ⟨index.val, alignedBound index⟩ ∈
                  List.ofFn fun direction => toPattern (rightElem direction) := by
              rw [rightPrinted]
              exact permAligned.symm.subset
                (List.get_mem alignedList ⟨index.val, alignedBound index⟩)
            let pick : Fin segLen → Fin segLen :=
              fun index => Classical.choose (List.mem_ofFn.mp (inPrinted index))
            have pick_spec (index : Fin segLen) :
                toPattern (rightElem (pick index)) =
                  alignedList.get ⟨index.val, alignedBound index⟩ :=
              Classical.choose_spec (List.mem_ofFn.mp (inPrinted index))
            let pickedElem : Fin segLen → Tree language (Γ, element) :=
              fun index => rightElem (pick index)
            have pickedPrinted :
                List.ofFn (fun index => toPattern (pickedElem index)) = alignedList := by
              refine List.ext_get ?_ ?_
              · simp only [List.length_ofFn, alignedLength]
              · intro n hOfFn hAligned
                let index : Fin segLen := ⟨n, by simpa [List.length_ofFn] using hOfFn⟩
                have read := ofFn_get_apply (fun i => toPattern (pickedElem i)) index
                have sameGet :
                    (List.ofFn fun i => toPattern (pickedElem i)).get ⟨n, hOfFn⟩ =
                      (List.ofFn fun i => toPattern (pickedElem i)).get
                        ⟨index.val, List.length_ofFn.symm ▸ index.isLt⟩ := by
                  apply congrArg
                    (List.get (List.ofFn fun i => toPattern (pickedElem i)))
                  apply Fin.ext
                  rfl
                rw [sameGet, read, pick_spec index]
            have pointwiseElements :
                List.Forall₂ PatternCong
                  (List.ofFn fun index : Fin segLen =>
                    nthPrinted (fun direction => toPattern (leftChildren direction))
                      (start + index.val))
                  (List.ofFn fun index => toPattern (pickedElem index)) :=
              pickedPrinted.symm ▸ pointwise
            let current' := overlaySegment operator start segLen fitLen uniform current pickedElem
            have outsideProof :
                ∀ direction : Fin ((indexedSignature language).arity operator).length,
                  direction.val < start ∨ start + segLen ≤ direction.val →
                    current direction = current' direction := by
              intro direction outside
              exact (overlay_outside operator start segLen fitLen uniform current pickedElem
                direction outside).symm
            have leftSeg :
                List.ofFn (fun index =>
                  segmentChild operator start index (by omega) (uniform index) current) =
                  List.ofFn rightElem := by
              refine ofFn_pointwise ?_
              intro index
              unfold segmentChild
              have childEq :
                  current ⟨start + index.val, by omega⟩ =
                    rightChildren ⟨start + index.val, by omega⟩ :=
                suffix _ (Nat.le_add_right _ _)
              simp only [atElement, childEq, rightElem]
            have rightSeg :
                List.ofFn (fun index =>
                  segmentChild operator start index (by omega) (uniform index) current') =
                  List.ofFn pickedElem := by
              refine ofFn_pointwise ?_
              intro index
              exact overlay_segment operator start segLen fitLen uniform current pickedElem index
                (by omega)
            have treePerm : List.Perm (List.ofFn rightElem) (List.ofFn pickedElem) := by
              have patternPerm :
                  List.Perm
                    (List.ofFn fun index => toPattern (rightElem index))
                    (List.ofFn fun index => toPattern (pickedElem index)) := by
                rw [rightPrinted, pickedPrinted]
                exact permAligned
              have asMap :
                  List.map toPattern (List.ofFn rightElem) =
                    List.ofFn fun index => toPattern (rightElem index) := by
                rw [List.map_ofFn]
                exact ofFn_pointwise fun _ => rfl
              have asMap' :
                  List.map toPattern (List.ofFn pickedElem) =
                    List.ofFn fun index => toPattern (pickedElem index) := by
                rw [List.map_ofFn]
                exact ofFn_pointwise fun _ => rfl
              have patternPerm' :
                  List.Perm (List.map toPattern (List.ofFn rightElem))
                    (List.map toPattern (List.ofFn pickedElem)) := by
                rw [asMap, asMap']
                exact patternPerm
              exact (List.map_perm_map_iff
                (toPattern_fn_injective labels uniqueBare (Γ, element))).mp patternPerm'
            have permStep :=
              TreeCong.bagPerm operator start segLen fitLen .hashBag (Or.inl rfl) done doneBound
                reading (by simp [start, takenSlots]) rfl uniform current current' outsideProof
                (leftSeg.symm ▸ rightSeg.symm ▸ treePerm)
            refine ⟨current', rightToCurrent.trans permStep, ?_, ?_⟩
            · intro direction bound
              by_cases earlier : direction.val < start
              · have stayed : current' direction = current direction :=
                  overlay_outside operator start segLen fitLen uniform current pickedElem direction
                    (Or.inl earlier)
                rw [stayed]
                exact aligned direction earlier
              · have indexFit : direction.val - start < segLen := by
                  have slots :
                      takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                          (done + 1) = start + segLen := by
                    rw [stepEq, widthEq]
                  omega
                let index : Fin segLen := ⟨direction.val - start, indexFit⟩
                have atIndex :=
                  (List.forall₂_iff_get.mp pointwiseElements).2 index.val
                    (by rw [List.length_ofFn]; exact index.isLt)
                    (by rw [List.length_ofFn]; exact index.isLt)
                rw [ofFn_get_apply, ofFn_get_apply] at atIndex
                have startFit : start + index.val <
                    ((indexedSignature language).arity operator).length := by omega
                have asStart : direction.val = start + index.val := by
                  simp [index]
                  omega
                have dirEq : direction = ⟨start + index.val, startFit⟩ := by
                  apply Fin.ext
                  exact asStart
                rw [nthPrinted_of_lt _ startFit] at atIndex
                have placed :
                    toPattern (current' ⟨start + index.val, startFit⟩) =
                      toPattern (pickedElem index) := by
                  have segEq :=
                    overlay_segment operator start segLen fitLen uniform current pickedElem index
                      startFit
                  have asChild :
                      toPattern
                          (segmentChild operator start index startFit (uniform index) current') =
                        toPattern (current' ⟨start + index.val, startFit⟩) := by
                    unfold segmentChild
                    exact toPattern_atElement operator ⟨start + index.val, startFit⟩
                      (uniform index) current'
                  rw [← asChild]
                  exact congrArg toPattern segEq
                rw [dirEq, placed]
                simpa using atIndex
            · intro direction bound
              have slots :
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                    start + segLen := by
                rw [stepEq, widthEq]
              have past : start + segLen ≤ direction.val := by omega
              have stayed : current' direction = current direction :=
                overlay_outside operator start segLen fitLen uniform current pickedElem direction
                  (Or.inr past)
              rw [stayed]
              exact suffix direction (by omega)
  | none =>
      have leftArg :=
        assemble_at_none (fun direction => toPattern (leftChildren direction))
          operator.1.1.params operator.2.counts operator.2.lengths
          operator.2.counts_length operator.2.lengths_length done doneBound reading
      have rightArg :=
        assemble_at_none (fun direction => toPattern (rightChildren direction))
          operator.1.1.params operator.2.counts operator.2.lengths
          operator.2.counts_length operator.2.lengths_length done doneBound reading
      rw [← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenL.symm ▸ doneBound⟩),
        ← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenR.symm ▸ doneBound⟩)] at atArgs
      rw [leftArg, rightArg] at atArgs
      have paramGet :
          operator.1.1.params.getD done missingParameter =
            operator.1.1.params.get ⟨done, doneBound⟩ :=
        List.getD_eq_get (d := missingParameter) (i := ⟨done, doneBound⟩)
      obtain ⟨_countEq, bodyCong⟩ :=
        printArgument_body (operator.1.1.params.get ⟨done, doneBound⟩)
          (operator.2.counts.getD done 0) (operator.2.counts.getD done 0)
          (nthPrinted (fun direction => toPattern (leftChildren direction)) start)
          (nthPrinted (fun direction => toPattern (rightChildren direction)) start) atArgs
          (by
            intro notMulti
            exact operator.2.counts_fixed done (by
              rw [paramGet]
              exact notMulti))
          (by
            intro notMulti
            exact operator.2.counts_fixed done (by
              rw [paramGet]
              exact notMulti))
      have widthEq :
          directionsOf (operator.1.1.params.get ⟨done, doneBound⟩)
              (operator.2.counts.getD done 0) (operator.2.lengths.getD done 0) = 1 := by
        rw [directionsOf, reading]
      have startFit : start < ((indexedSignature language).arity operator).length := by
        have slots :
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
              start + 1 := by
          rw [stepEq, widthEq]
        have room : start + 1 ≤ ((indexedSignature language).arity operator).length := by
          have widened := widthRoom
          rw [widthEq] at widened
          exact widened
        omega
      rw [nthPrinted_of_lt _ startFit, nthPrinted_of_lt _ startFit] at bodyCong
      refine ⟨current, rightToCurrent, ?_, ?_⟩
      · intro direction bound
        by_cases earlier : direction.val < start
        · exact aligned direction earlier
        · have atStart : direction.val = start := by
            have slots :
                takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
                  start + 1 := by
              rw [stepEq, widthEq]
            omega
          have dirEq : direction = ⟨start, startFit⟩ := by
            apply Fin.ext
            exact atStart
          have childEq : current ⟨start, startFit⟩ = rightChildren ⟨start, startFit⟩ :=
            suffix ⟨start, startFit⟩ (by simp [start])
          rw [dirEq, childEq]
          simpa [Fin.eta] using bodyCong
      · intro direction bound
        have slots :
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths (done + 1) =
              start + 1 := by
          rw [stepEq, widthEq]
        exact suffix direction (by omega)

/-- A cast tree keeps the induction hypothesis of the tree it came from. -/
theorem ih_cast {index index' : List String × String}
    (eq : index = index') (tree : Tree language index)
    (preserved : ∀ other : Tree language index,
      PatternCong (toPattern tree) (toPattern other) → TreeCong language tree other)
    (other : Tree language index')
    (related : PatternCong
      (toPattern (cast (congrArg (Tree language) eq) tree)) (toPattern other)) :
    TreeCong language (cast (congrArg (Tree language) eq) tree) other := by
  have relatedOld :
      PatternCong (toPattern tree)
        (toPattern (cast (congrArg (Tree language) eq.symm) other)) := by
    rw [toPattern_cast eq tree] at related
    rw [← toPattern_cast eq.symm other] at related
    exact related
  have step := preserved _ relatedOld
  have casted := treeCong_cast eq step
  have back :
      cast (congrArg (Tree language) eq)
          (cast (congrArg (Tree language) eq.symm) other) = other := by
    apply eq_of_heq
    rw [cast_heq_iff_heq, cast_heq_iff_heq]
  rw [back] at casted
  exact casted

/-- Printing a prefix child of a splice is printing the outside child. -/
theorem spliceChild_toPattern_prefix {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) :
    toPattern (spliceChild operator parameterIndex bound shape k outside trees direction) =
      toPattern (outside
        ⟨direction.val, resized_prefix_fit operator parameterIndex bound shape k hPrefix⟩) := by
  unfold spliceChild
  simp only [dif_pos hPrefix]
  exact toPattern_cast
    (splice_prefix_src (Γ := Γ) operator parameterIndex bound shape k direction hPrefix).symm _

/-- Printing a segment child of a splice is printing the supplied element tree. -/
theorem spliceChild_toPattern_segment {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (lo : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
      direction.val)
    (hi : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k) :
    toPattern (spliceChild operator parameterIndex bound shape k outside trees direction) =
      toPattern (trees
        ⟨direction.val -
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex,
          by omega⟩) := by
  unfold spliceChild
  have notPrefix : ¬ direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex :=
    Nat.not_lt_of_ge lo
  simp only [dif_neg notPrefix, dif_pos hi]
  exact toPattern_cast
    (splice_segment_src (Γ := Γ) operator parameterIndex bound shape k direction lo hi).symm _

/-- Printing a suffix child of a splice is printing the shifted outside child. -/
theorem spliceChild_toPattern_suffix {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (direction : Fin ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (hPast : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        k ≤ direction.val) :
    toPattern (spliceChild operator parameterIndex bound shape k outside trees direction) =
      toPattern (outside
        ⟨direction.val + operator.2.lengths.getD parameterIndex 0 - k,
          resized_suffix_fit operator parameterIndex bound shape k direction.isLt hPast⟩) := by
  unfold spliceChild
  have notPrefix : ¬ direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex :=
    Nat.not_lt_of_ge
      (Nat.le_trans
        (Nat.le_add_right
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) k)
        hPast)
  have notSeg : ¬ direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k :=
    Nat.not_lt_of_ge hPast
  simp only [dif_neg notPrefix, dif_neg notSeg]
  exact toPattern_cast
    (splice_suffix_src (Γ := Γ) operator parameterIndex bound shape k direction hPast).symm _

/-- Element trees named by a cover inherit the element induction hypothesis. -/
theorem target_element_ih {Γ : List String} {element : String} {n m : Nat}
    (leftSegment : Fin n → Tree language (Γ, element))
    (rightSegment : Fin m → Tree language (Γ, element))
    (leftIh : ∀ i : Fin n, ∀ other : Tree language (Γ, element),
      PatternCong (toPattern (leftSegment i)) (toPattern other) →
        TreeCong language (leftSegment i) other)
    (coverR : ∀ j : Fin m, ∃ i : Fin n,
      PatternCong (toPattern (leftSegment i)) (toPattern (rightSegment j))) :
    ∀ j : Fin m, ∀ other : Tree language (Γ, element),
      PatternCong (toPattern (rightSegment j)) (toPattern other) →
        TreeCong language (rightSegment j) other := by
  intro j other related
  obtain ⟨i, toRight⟩ := coverR j
  exact (TreeCong.symm (leftIh i (rightSegment j) toRight)).trans
    (leftIh i other (PatternCong.trans toRight related))

/-- A splice keeps the induction hypothesis: outside children by the cast, and the
new segment by the element hypothesis of the family that was written there. -/
theorem spliceChild_ih {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (outside direction)) (toPattern other) →
          TreeCong language (outside direction) other)
    (treeIh : ∀ index : Fin k, ∀ other : Tree language (Γ, element),
      PatternCong (toPattern (trees index)) (toPattern other) →
        TreeCong language (trees index) other) :
    ∀ direction
      (other : Tree language
        ((polynomial (indexedSignature language)).src (Γ, sort)
          (resizedAt operator parameterIndex bound shape k) direction)),
      PatternCong
          (toPattern (spliceChild operator parameterIndex bound shape k outside trees direction))
          (toPattern other) →
        TreeCong language
          (spliceChild operator parameterIndex bound shape k outside trees direction) other := by
  intro direction other related
  unfold spliceChild at related ⊢
  by_cases hPrefix : direction.val <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex
  · simp only [dif_pos hPrefix] at related ⊢
    exact ih_cast
      (splice_prefix_src (Γ := Γ) operator parameterIndex bound shape k direction hPrefix).symm
      (outside ⟨direction.val,
        resized_prefix_fit operator parameterIndex bound shape k hPrefix⟩)
      (fun other' rel =>
        ih ⟨direction.val, resized_prefix_fit operator parameterIndex bound shape k hPrefix⟩
          other' rel)
      other related
  · by_cases hSeg : direction.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k
    · simp only [dif_neg hPrefix, dif_pos hSeg] at related ⊢
      exact ih_cast
        (splice_segment_src (Γ := Γ) operator parameterIndex bound shape k direction
          (by omega) hSeg).symm
        (trees ⟨direction.val -
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex,
            by omega⟩)
        (fun other' rel => treeIh _ other' rel)
        other related
    · simp only [dif_neg hPrefix, dif_neg hSeg] at related ⊢
      exact ih_cast
        (splice_suffix_src (Γ := Γ) operator parameterIndex bound shape k direction
          (by omega)).symm
        (outside ⟨direction.val + operator.2.lengths.getD parameterIndex 0 - k,
          resized_suffix_fit operator parameterIndex bound shape k direction.isLt (by omega)⟩)
        (fun other' rel => ih _ other' rel)
        other related

/-- `List.set` leaves every other `getD` entry unchanged. -/
theorem lengths_set_getD_ne (lengths : List Nat) (index value i : Nat) (different : i ≠ index) :
    (lengths.set index value).getD i 0 = lengths.getD i 0 := by
  by_cases iLt : i < lengths.length
  · have iLt' : i < (lengths.set index value).length := by
      simpa [List.length_set] using iLt
    rw [List.getD_eq_getElem (hn := iLt'), List.getD_eq_getElem (hn := iLt)]
    rw [List.getElem_set_ne (Ne.symm different)]
  · have iGe : lengths.length ≤ i := Nat.le_of_not_lt iLt
    have iGe' : (lengths.set index value).length ≤ i := by
      simpa [List.length_set] using iGe
    rw [List.getD_eq_default (d := 0) (hn := iGe), List.getD_eq_default (d := 0) (hn := iGe')]

/-- Earlier parameters occupy at most as many directions as a later prefix. -/
theorem takenSlots_mono (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    {i j : Nat} (ij : i ≤ j) (jLe : j ≤ parameters.length) :
    takenSlots parameters counts lengths i ≤ takenSlots parameters counts lengths j := by
  suffices ∀ j, i ≤ j → j ≤ parameters.length →
      takenSlots parameters counts lengths i ≤ takenSlots parameters counts lengths j by
    exact this j ij jLe
  intro j
  induction extra : j - i generalizing j with
  | zero =>
      intro ij jLe
      have : j = i := by omega
      subst this
      exact Nat.le_refl _
  | succ extra inductionHypothesis =>
      intro ij jLe
      have predBound : j - 1 < parameters.length := by omega
      have smaller :=
        inductionHypothesis (j - 1) (by omega) (by omega) (Nat.le_of_lt predBound)
      have step :=
        takenSlots_step parameters counts lengths countsLength lengthsLength (j - 1) predBound
      have jEq : j - 1 + 1 = j := by omega
      rw [← jEq, step]
      exact Nat.le_trans smaller (Nat.le_add_right _ _)

/-- Replacing one hash-set length shifts every later prefix by that difference. -/
theorem takenSlots_set_shift (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (parameterIndex : Nat) (bound : parameterIndex < parameters.length)
    {element : String}
    (shape : baseCollection? (parameters.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k done : Nat) (low : parameterIndex < done) (high : done ≤ parameters.length) :
    takenSlots parameters counts (lengths.set parameterIndex k) done =
      takenSlots parameters counts lengths done + k - lengths.getD parameterIndex 0 := by
  induction done with
  | zero => omega
  | succ done inductionHypothesis =>
      have doneBound : done < parameters.length := by omega
      have lengthsLength' : (lengths.set parameterIndex k).length = parameters.length := by
        simpa [List.length_set] using lengthsLength
      have stepOld :=
        takenSlots_step parameters counts lengths countsLength lengthsLength done doneBound
      have stepNew :=
        takenSlots_step parameters counts (lengths.set parameterIndex k)
          countsLength lengthsLength' done doneBound
      by_cases crossed : done = parameterIndex
      · subst crossed
        have startEq :
            takenSlots parameters counts (lengths.set done k) done =
              takenSlots parameters counts lengths done := by
          simp only [takenSlots]
          rw [List.take_set_of_le (Nat.le_refl done)]
        have written : (lengths.set done k).getD done 0 = k := by
          have inRange : done < (lengths.set done k).length := by
            rw [List.length_set, lengthsLength]
            exact bound
          rw [List.getD_eq_getElem (hn := inRange)]
          exact List.getElem_set_self inRange
        have width :
            directionsOf (parameters.get ⟨done, bound⟩) (counts.getD done 0)
                (lengths.getD done 0) =
              lengths.getD done 0 := by
          rw [directionsOf, shape]
        rw [stepOld, stepNew, startEq, width]
        have widthNew :
            directionsOf (parameters.get ⟨done, bound⟩) (counts.getD done 0)
                ((lengths.set done k).getD done 0) =
              k := by
          rw [written]
          rw [directionsOf, shape]
        rw [widthNew]
        omega
      · have low' : parameterIndex < done := by omega
        have shifted := inductionHypothesis low' (Nat.le_of_lt doneBound)
        have sameEntry :=
          lengths_set_getD_ne lengths parameterIndex k done crossed
        rw [stepOld, stepNew, shifted, sameEntry]
        have oldLe : lengths.getD parameterIndex 0 ≤
            takenSlots parameters counts lengths (parameterIndex + 1) := by
          have atIndex :=
            takenSlots_step parameters counts lengths countsLength lengthsLength
              parameterIndex bound
          have widthAt :
              directionsOf (parameters.get ⟨parameterIndex, bound⟩)
                  (counts.getD parameterIndex 0) (lengths.getD parameterIndex 0) =
                lengths.getD parameterIndex 0 := by
            rw [directionsOf, shape]
          rw [atIndex, widthAt]
          exact Nat.le_add_left _ _
        have later : takenSlots parameters counts lengths (parameterIndex + 1) ≤
            takenSlots parameters counts lengths done :=
          takenSlots_mono parameters counts lengths countsLength lengthsLength
            (Nat.succ_le_of_lt low') (Nat.le_of_lt doneBound)
        omega

/-- The element trees of one hash-set parameter print as that parameter's list. -/
theorem segment_prints_eq {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (done : Nat) (doneBound : done < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨done, doneBound⟩) =
      some (.hashSet, element))
    (children : Child language Γ sort operator) :
    List.ofFn (fun index =>
        toPattern (segmentTrees operator done doneBound shape
          (operator.2.lengths.getD done 0) rfl children index)) =
      List.ofFn (fun index : Fin (operator.2.lengths.getD done 0) =>
        nthPrinted (fun direction => toPattern (children direction))
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths done +
            index.val)) := by
  refine ofFn_pointwise ?_
  intro index
  have fit :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths done + index.val <
        ((indexedSignature language).arity operator).length := by
    have indexLt := index.isLt
    have room := segment_room operator doneBound (by rw [shape]; rfl)
    omega
  have asTree :
      segmentTrees operator done doneBound shape (operator.2.lengths.getD done 0) rfl
          children index =
        atElement operator
          ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths done + index.val,
            fit⟩
          (by
            rw [List.get_eq_getElem]
            exact expand_segment_getElem operator.1.1.params operator.2.counts
              operator.2.lengths operator.2.counts_length operator.2.lengths_length
              doneBound shape index
              (by
                have indexLt := index.isLt
                have room := segment_room operator doneBound (by rw [shape]; rfl)
                have sameLength :
                    (expandSlots operator.1.1.params operator.2.counts
                        operator.2.lengths).length =
                      ((indexedSignature language).arity operator).length := rfl
                rw [← sameLength] at room
                omega))
          children := by
    unfold segmentTrees
    apply atElement_fin
    · apply Fin.ext
      rfl
  rw [asTree, toPattern_atElement]
  exact (nthPrinted_of_lt (fun direction => toPattern (children direction)) fit).symm

/-- The two element lists of one hash-set argument cover each other. -/
theorem set_segment_covers {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (rightOp : (indexedSignature language).Op sort)
    (done : Nat) (doneBound : done < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨done, doneBound⟩) =
      some (.hashSet, element))
    (children : Child language Γ sort operator)
    (rightChildren : Child language Γ sort rightOp)
    (sameRule : operator.1.1 = rightOp.1.1)
    (rightBound : done < rightOp.1.1.params.length)
    (shapeR : baseCollection? (rightOp.1.1.params.get ⟨done, rightBound⟩) =
      some (.hashSet, element))
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (children direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params rightOp.2.counts rightOp.2.lengths)) :
    (∀ i : Fin (operator.2.lengths.getD done 0),
      ∃ j : Fin (rightOp.2.lengths.getD done 0),
        PatternCong
          (toPattern (segmentTrees operator done doneBound shape
            (operator.2.lengths.getD done 0) rfl children i))
          (toPattern (segmentTrees rightOp done rightBound shapeR
            (rightOp.2.lengths.getD done 0) rfl rightChildren j))) ∧
      (∀ j : Fin (rightOp.2.lengths.getD done 0),
        ∃ i : Fin (operator.2.lengths.getD done 0),
          PatternCong
            (toPattern (segmentTrees operator done doneBound shape
              (operator.2.lengths.getD done 0) rfl children i))
            (toPattern (segmentTrees rightOp done rightBound shapeR
              (rightOp.2.lengths.getD done 0) rfl rightChildren j))) := by
  have paramsEq : rightOp.1.1.params = operator.1.1.params :=
    congrArg (fun rule => rule.params) sameRule.symm
  let rightCounts := rightOp.2.counts
  let rightLengths := rightOp.2.lengths
  have slotsEq :
      takenSlots rightOp.1.1.params rightCounts rightLengths done =
        takenSlots operator.1.1.params rightCounts rightLengths done :=
    congrArg (fun parameters => takenSlots parameters rightCounts rightLengths done) paramsEq
  have rightCountsLength : rightOp.2.counts.length = operator.1.1.params.length := by
    rw [rightOp.2.counts_length, paramsEq]
  have rightLengthsLength : rightOp.2.lengths.length = operator.1.1.params.length := by
    rw [rightOp.2.lengths_length, paramsEq]
  have lenL :=
    assemblePrinted_length (fun direction => toPattern (children direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length
  have lenR :=
    assemblePrinted_length (fun direction => toPattern (rightChildren direction)) 0
      operator.1.1.params rightOp.2.counts rightOp.2.lengths
      rightCountsLength rightLengthsLength
  have atArgs :=
    (List.forall₂_iff_get.mp argRel).2 done (lenL.symm ▸ doneBound) (lenR.symm ▸ doneBound)
  have leftArg :=
    assemble_at_set (fun direction => toPattern (children direction))
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length done doneBound shape
  have rightArg :=
    assemble_at_set (fun direction => toPattern (rightChildren direction))
      operator.1.1.params rightOp.2.counts rightOp.2.lengths
      rightCountsLength rightLengthsLength done doneBound shape
  rw [← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenL.symm ▸ doneBound⟩),
    ← List.getD_eq_get (d := .bvar 0) (i := ⟨done, lenR.symm ▸ doneBound⟩)] at atArgs
  rw [leftArg, rightArg] at atArgs
  obtain ⟨_leftElements, _rightElements, leftEq, rightEq, elementsRel⟩ :=
    patternCong_set_elements atArgs
      (Or.inl ⟨List.ofFn fun index : Fin (operator.2.lengths.getD done 0) =>
        nthPrinted (fun direction => toPattern (children direction))
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths done +
            index.val), rfl⟩)
  simp only [Pattern.collection.injEq] at leftEq rightEq
  obtain ⟨_, leftList, _⟩ := leftEq
  obtain ⟨_, rightList, _⟩ := rightEq
  subst leftList
  subst rightList
  have covers := setElementRel_both elementsRel
  have leftPrinted := segment_prints_eq operator done doneBound shape children
  have rightBase := segment_prints_eq rightOp done rightBound shapeR rightChildren
  have rightPrinted :
      List.ofFn (fun index =>
          toPattern (segmentTrees rightOp done rightBound shapeR
            (rightOp.2.lengths.getD done 0) rfl rightChildren index)) =
        List.ofFn (fun index : Fin (rightOp.2.lengths.getD done 0) =>
          nthPrinted (fun direction => toPattern (rightChildren direction))
            (takenSlots operator.1.1.params rightOp.2.counts rightOp.2.lengths done +
              index.val)) := by
    rw [rightBase]
    refine ofFn_pointwise ?_
    intro index
    have posEq :
        takenSlots rightOp.1.1.params rightOp.2.counts rightOp.2.lengths done + index.val =
          takenSlots operator.1.1.params rightOp.2.counts rightOp.2.lengths done +
            index.val := by
      rw [slotsEq]
    rw [posEq]
  refine ⟨?_, ?_⟩
  · intro i
    have mem :
        toPattern (segmentTrees operator done doneBound shape
          (operator.2.lengths.getD done 0) rfl children i) ∈
          List.ofFn fun index : Fin (operator.2.lengths.getD done 0) =>
            nthPrinted (fun direction => toPattern (children direction))
              (takenSlots operator.1.1.params operator.2.counts operator.2.lengths done +
                index.val) := by
      rw [← leftPrinted]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨image, imageMem, step⟩ := covers.1 _ mem
    have imageMem' :
        image ∈ List.ofFn fun index =>
          toPattern (segmentTrees rightOp done rightBound shapeR
            (rightOp.2.lengths.getD done 0) rfl rightChildren index) := by
      rw [rightPrinted]
      exact imageMem
    obtain ⟨j, imageEq⟩ := List.mem_ofFn.mp imageMem'
    exact ⟨j, by simpa [imageEq] using step⟩
  · intro j
    have mem :
        toPattern (segmentTrees rightOp done rightBound shapeR
          (rightOp.2.lengths.getD done 0) rfl rightChildren j) ∈
          List.ofFn fun index : Fin (rightOp.2.lengths.getD done 0) =>
            nthPrinted (fun direction => toPattern (rightChildren direction))
              (takenSlots operator.1.1.params rightOp.2.counts rightOp.2.lengths done +
                index.val) := by
      rw [← rightPrinted]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    obtain ⟨image, imageMem, step⟩ := covers.2 _ mem
    have imageMem' :
        image ∈ List.ofFn fun index =>
          toPattern (segmentTrees operator done doneBound shape
            (operator.2.lengths.getD done 0) rfl children index) := by
      rw [leftPrinted]
      exact imageMem
    obtain ⟨i, imageEq⟩ := List.mem_ofFn.mp imageMem'
    exact ⟨i, by simpa [imageEq] using step⟩

/-- Once both heads carry the same lengths, the parameter walk is the tree congruence. -/
theorem sameHead_walk
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (leftChildren rightChildren : Child language Γ sort operator)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator rightChildren) := by
  have advance :
      ∀ fuel done (current : Child language Γ sort operator),
        done + fuel = operator.1.1.params.length →
        TreeCong language
          (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator rightChildren)
          (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator current) →
        (∀ direction : Fin ((indexedSignature language).arity operator).length,
          direction.val <
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths done →
            PatternCong (toPattern (leftChildren direction))
              (toPattern (current direction))) →
        (∀ direction : Fin ((indexedSignature language).arity operator).length,
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths done ≤
              direction.val →
            current direction = rightChildren direction) →
        TreeCong language
          (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator leftChildren)
          (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator rightChildren) := by
    intro fuel
    induction fuel with
    | zero =>
        intro done current sum rightToCurrent aligned suffix
        have doneAll : done = operator.1.1.params.length := by omega
        subst doneAll
        have covered :
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                operator.1.1.params.length =
              ((indexedSignature language).arity operator).length := by
          rw [takenSlots_all _ _ _ operator.2.counts_length operator.2.lengths_length,
            expandSlots_length]
        have steps :
            ∀ direction, TreeCong language (leftChildren direction) (current direction) := by
          intro direction
          apply ih
          have bound :
              direction.val <
                takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                  operator.1.1.params.length := by
            rw [covered]
            exact direction.isLt
          exact aligned direction bound
        exact (treeCong_pointwise operator leftChildren current steps).trans
          (TreeCong.symm rightToCurrent)
    | succ fuel inductionHypothesis =>
        intro done current sum rightToCurrent aligned suffix
        have doneBound : done < operator.1.1.params.length := by omega
        obtain ⟨current', stepped, aligned', suffix'⟩ :=
          extend_alignment labels uniqueBare operator done doneBound leftChildren rightChildren
            current ih argRel rightToCurrent aligned suffix
        exact inductionHypothesis (done + 1) current' (by omega) stepped aligned' suffix'
  exact advance operator.1.1.params.length 0 rightChildren (by omega) (TreeCong.refl _)
    (by
      intro direction bound
      simp [takenSlots_zero] at bound)
    (by
      intro direction _
      rfl)

/-- Equal counts and pointwise lengths make the two operator nodes the same head. -/
theorem agreed_lengths_walk
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (operator : (indexedSignature language).Op sort)
    (children : Child language Γ sort operator)
    (rightOp : (indexedSignature language).Op sort)
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
        PatternCong (toPattern (children direction)) (toPattern other) →
          TreeCong language (children direction) other)
    (sameRule : operator.1.1 = rightOp.1.1)
    (countsEq : operator.2.counts = rightOp.2.counts)
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (children direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params rightOp.2.counts rightOp.2.lengths))
    (allLengths : ∀ i, i < operator.1.1.params.length →
      operator.2.lengths.getD i 0 = rightOp.2.lengths.getD i 0) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        operator children)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  have lengthsEq : operator.2.lengths = rightOp.2.lengths := by
    have lenLen : operator.2.lengths.length = rightOp.2.lengths.length := by
      rw [operator.2.lengths_length, rightOp.2.lengths_length]
      exact congrArg List.length (congrArg (fun rule => rule.params) sameRule)
    apply List.ext_get lenLen
    intro n h₁ h₂
    rw [← List.getD_eq_get (d := 0) (i := ⟨n, h₁⟩),
      ← List.getD_eq_get (d := 0) (i := ⟨n, h₂⟩)]
    exact allLengths n (by simpa [operator.2.lengths_length] using h₁)
  have opEq : operator = rightOp := by
    rcases operator with ⟨packedLeft, dataLeft⟩
    rcases rightOp with ⟨packedRight, dataRight⟩
    have packedEq : packedLeft = packedRight := Subtype.ext sameRule
    subst packedEq
    have dataEq : dataLeft = dataRight := headData_ext countsEq lengthsEq
    subst dataEq
    rfl
  subst opEq
  exact sameHead_walk labels uniqueBare operator children rightChildren ih argRel

/-- `List.set` does not change a prefix that stops at the replaced index. -/
theorem takenSlots_set_before
    (parameters : List TermParam) (counts lengths : List Nat)
    (parameterIndex k : Nat) {j : Nat} (jLe : j ≤ parameterIndex) :
    takenSlots parameters counts (lengths.set parameterIndex k) j =
      takenSlots parameters counts lengths j := by
  simp only [takenSlots]
  rw [List.take_set_of_le jLe]

/-- A direction before the resized segment still lies in the resized arity. -/
theorem resized_early_fit {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat) {pos : Nat}
    (hPrefix : pos <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) :
    pos < ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length := by
  have lengthsLength' :
      (operator.2.lengths.set parameterIndex k).length = operator.1.1.params.length := by
    simpa [List.length_set] using operator.2.lengths_length
  have covered :
      takenSlots operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) operator.1.1.params.length =
        ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape k)).length := by
    unfold resizedAt
    rw [takenSlots_all _ _ _ operator.2.counts_length lengthsLength', expandSlots_length]
  have slotsSame :=
    takenSlots_set_before operator.1.1.params operator.2.counts operator.2.lengths
      parameterIndex k (Nat.le_refl parameterIndex)
  have mono :=
    takenSlots_mono operator.1.1.params operator.2.counts
      (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength'
      (Nat.le_of_lt bound) (Nat.le_refl _)
  rw [← covered]
  exact Nat.lt_of_lt_of_le (by rw [slotsSame]; exact hPrefix) mono

/-- A position before the resized segment prints as the outside child. -/
theorem nth_splice_prefix {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    {pos : Nat}
    (hPrefix : pos <
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex) :
    nthPrinted (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction))
        pos =
      nthPrinted (fun direction => toPattern (outside direction)) pos := by
  have posFit := resized_early_fit operator parameterIndex bound shape k hPrefix
  rw [nthPrinted_of_lt _ posFit]
  rw [spliceChild_toPattern_prefix operator parameterIndex bound shape k outside trees
    ⟨pos, posFit⟩ hPrefix]
  apply Eq.symm
  rw [nthPrinted_of_lt (fun direction => toPattern (outside direction))
    (resized_prefix_fit operator parameterIndex bound shape k hPrefix)]

/-- A position after the resized segment prints as the shifted outside child. -/
theorem nth_splice_suffix {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    {pos oldPos : Nat}
    (hPast : takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
      k ≤ pos)
    (posFit : pos < ((indexedSignature language).arity
      (resizedAt operator parameterIndex bound shape k)).length)
    (valEq : pos + operator.2.lengths.getD parameterIndex 0 - k = oldPos) :
    nthPrinted (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction))
        pos =
      nthPrinted (fun direction => toPattern (outside direction)) oldPos := by
  have shiftedFit :=
    resized_suffix_fit operator parameterIndex bound shape k posFit hPast
  have oldFit : oldPos < ((indexedSignature language).arity operator).length := by
    rw [← valEq]
    exact shiftedFit
  rw [nthPrinted_of_lt _ posFit]
  rw [spliceChild_toPattern_suffix operator parameterIndex bound shape k outside trees
    ⟨pos, posFit⟩ hPast]
  have finEq :
      (⟨pos + operator.2.lengths.getD parameterIndex 0 - k, shiftedFit⟩ :
        Fin ((indexedSignature language).arity operator).length) =
        ⟨oldPos, oldFit⟩ := by
    apply Fin.ext
    exact valEq
  rw [finEq]
  exact (nthPrinted_of_lt (fun direction => toPattern (outside direction)) oldFit).symm

/-- A position inside the resized segment prints as the supplied element tree. -/
theorem nth_splice_segment {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (index : Fin k) :
    nthPrinted (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction))
        (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val) =
      toPattern (trees index) := by
  have posFit :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val <
        ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape k)).length := by
    have lengthsLength' :
        (operator.2.lengths.set parameterIndex k).length = operator.1.1.params.length := by
      simpa [List.length_set] using operator.2.lengths_length
    have covered :
        takenSlots operator.1.1.params operator.2.counts
            (operator.2.lengths.set parameterIndex k) operator.1.1.params.length =
          ((indexedSignature language).arity
            (resizedAt operator parameterIndex bound shape k)).length := by
      unfold resizedAt
      rw [takenSlots_all _ _ _ operator.2.counts_length lengthsLength', expandSlots_length]
    have stepNew :=
      takenSlots_step operator.1.1.params operator.2.counts
        (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength'
        parameterIndex bound
    have written :=
      resizedAt_getD operator parameterIndex
        (by simpa [operator.2.lengths_length] using bound) k
    have slotsSame :=
      takenSlots_set_before operator.1.1.params operator.2.counts operator.2.lengths
        parameterIndex k (Nat.le_refl parameterIndex)
    have nextLe :
        takenSlots operator.1.1.params operator.2.counts
            (operator.2.lengths.set parameterIndex k) (parameterIndex + 1) ≤
          takenSlots operator.1.1.params operator.2.counts
            (operator.2.lengths.set parameterIndex k) operator.1.1.params.length :=
      takenSlots_mono operator.1.1.params operator.2.counts
        (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength'
        (Nat.succ_le_of_lt bound) (Nat.le_refl _)
    have indexLt := index.isLt
    have width :
        directionsOf (operator.1.1.params.get ⟨parameterIndex, bound⟩)
            (operator.2.counts.getD parameterIndex 0)
            ((operator.2.lengths.set parameterIndex k).getD parameterIndex 0) =
          k := by
      rw [written]
      rw [directionsOf, shape]
    rw [← covered]
    refine Nat.lt_of_lt_of_le ?_ nextLe
    rw [stepNew, width, slotsSame]
    omega
  have lo :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex ≤
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val :=
    Nat.le_add_right _ _
  have hi :
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
          index.val <
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k := by
    have indexLt := index.isLt
    omega
  rw [nthPrinted_of_lt _ posFit]
  rw [spliceChild_toPattern_segment operator parameterIndex bound shape k outside trees
    ⟨takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
        index.val, posFit⟩ lo hi]
  apply congrArg toPattern
  apply congrArg trees
  apply Fin.ext
  show takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
      index.val -
      takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex =
    index.val
  omega

/-- `isHashSetParam` picks a hash set out of the parameter list. -/
theorem hashSet_shape_of_flag {parameters : List TermParam} {index : Nat}
    (bound : index < parameters.length)
    (flag : isHashSetParam (parameters.getD index missingParameter) = true) :
    ∃ element : String,
      baseCollection? (parameters.get ⟨index, bound⟩) = some (.hashSet, element) := by
  have paramGet :
      parameters.getD index missingParameter = parameters.get ⟨index, bound⟩ :=
    List.getD_eq_get (d := missingParameter) (i := ⟨index, bound⟩)
  match reading : baseCollection? (parameters.get ⟨index, bound⟩) with
  | none =>
      simp only [isHashSetParam, paramGet, reading] at flag
      exact (Bool.false_ne_true flag).elim
  | some (.vec, _) =>
      simp only [isHashSetParam, paramGet, reading] at flag
      exact (Bool.false_ne_true flag).elim
  | some (.hashBag, _) =>
      simp only [isHashSetParam, paramGet, reading] at flag
      exact (Bool.false_ne_true flag).elim
  | some (.hashSet, element) =>
      exact ⟨element, rfl⟩

/-- Parameters before the resized hash set assemble exactly as they did. -/
theorem assemble_before {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (j : Nat) (jLt : j < parameterIndex) (jBound : j < operator.1.1.params.length) :
    (assemblePrinted (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)).getD
        j (.bvar 0) =
      (assemblePrinted (fun direction => toPattern (outside direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths).getD j (.bvar 0) := by
  have lengthsLength' :
      (operator.2.lengths.set parameterIndex k).length = operator.1.1.params.length := by
    simpa [List.length_set] using operator.2.lengths_length
  rw [assemble_at (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)
      operator.2.counts_length lengthsLength' j jBound]
  rw [assemble_at (fun direction => toPattern (outside direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length j jBound]
  have lenEq :=
    lengths_set_getD_ne operator.2.lengths parameterIndex k j (Nat.ne_of_lt jLt)
  have slotsEq :=
    takenSlots_set_before operator.1.1.params operator.2.counts operator.2.lengths
      parameterIndex k (Nat.le_of_lt jLt)
  cases reading : baseCollection? (operator.1.1.params.get ⟨j, jBound⟩) with
  | some packed =>
      obtain ⟨kind, _elementSort⟩ := packed
      simp only [Nat.zero_add]
      rw [lenEq, slotsEq]
      apply congrArg (fun elements => Pattern.collection kind elements none)
      refine ofFn_pointwise ?_
      intro index
      have step :=
        takenSlots_step operator.1.1.params operator.2.counts operator.2.lengths
          operator.2.counts_length operator.2.lengths_length j jBound
      have width :
          directionsOf (operator.1.1.params.get ⟨j, jBound⟩) (operator.2.counts.getD j 0)
              (operator.2.lengths.getD j 0) =
            operator.2.lengths.getD j 0 := by
        rw [directionsOf, reading]
      have later :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths (j + 1) ≤
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex :=
        takenSlots_mono operator.1.1.params operator.2.counts operator.2.lengths
          operator.2.counts_length operator.2.lengths_length
          (Nat.succ_le_of_lt jLt) (Nat.le_of_lt bound)
      have indexLt := index.isLt
      have hPrefix :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths j + index.val <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
        rw [step, width] at later
        omega
      exact nth_splice_prefix operator parameterIndex bound shape k outside trees hPrefix
  | none =>
      simp only [Nat.zero_add]
      rw [slotsEq]
      apply congrArg (printArgument (operator.1.1.params.get ⟨j, jBound⟩)
        (operator.2.counts.getD j 0))
      have step :=
        takenSlots_step operator.1.1.params operator.2.counts operator.2.lengths
          operator.2.counts_length operator.2.lengths_length j jBound
      have width :
          directionsOf (operator.1.1.params.get ⟨j, jBound⟩) (operator.2.counts.getD j 0)
              (operator.2.lengths.getD j 0) =
            1 := by
        rw [directionsOf, reading]
      have later :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths (j + 1) ≤
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex :=
        takenSlots_mono operator.1.1.params operator.2.counts operator.2.lengths
          operator.2.counts_length operator.2.lengths_length
          (Nat.succ_le_of_lt jLt) (Nat.le_of_lt bound)
      have hPrefix :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths j <
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex := by
        rw [step, width] at later
        omega
      exact nth_splice_prefix operator parameterIndex bound shape k outside trees hPrefix

/-- Parameters after the resized hash set assemble as the unshifted outside children. -/
theorem assemble_after {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (j : Nat) (jGt : parameterIndex < j) (jBound : j < operator.1.1.params.length) :
    (assemblePrinted (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)).getD
        j (.bvar 0) =
      (assemblePrinted (fun direction => toPattern (outside direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths).getD j (.bvar 0) := by
  have lengthsLength' :
      (operator.2.lengths.set parameterIndex k).length = operator.1.1.params.length := by
    simpa [List.length_set] using operator.2.lengths_length
  have shift :=
    takenSlots_set_shift operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length parameterIndex bound shape k j
      jGt (Nat.le_of_lt jBound)
  have nextShift :=
    takenSlots_set_shift operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length parameterIndex bound shape k
      (parameterIndex + 1) (Nat.lt_succ_self parameterIndex) (Nat.succ_le_of_lt bound)
  have stepAt :=
    takenSlots_step operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length parameterIndex bound
  have collapsed :
      takenSlots operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) (parameterIndex + 1) =
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k := by
    have widthAt :
        directionsOf (operator.1.1.params.get ⟨parameterIndex, bound⟩)
            (operator.2.counts.getD parameterIndex 0)
            (operator.2.lengths.getD parameterIndex 0) =
          operator.2.lengths.getD parameterIndex 0 := by
      rw [directionsOf, shape]
    rw [nextShift, stepAt, widthAt]
    omega
  have oldLenLe :
      operator.2.lengths.getD parameterIndex 0 ≤
        takenSlots operator.1.1.params operator.2.counts operator.2.lengths j := by
    have mono :=
      takenSlots_mono operator.1.1.params operator.2.counts operator.2.lengths
        operator.2.counts_length operator.2.lengths_length
        (Nat.succ_le_of_lt jGt) (Nat.le_of_lt jBound)
    have widthAt :
        directionsOf (operator.1.1.params.get ⟨parameterIndex, bound⟩)
            (operator.2.counts.getD parameterIndex 0)
            (operator.2.lengths.getD parameterIndex 0) =
          operator.2.lengths.getD parameterIndex 0 := by
      rw [directionsOf, shape]
    rw [stepAt, widthAt] at mono
    omega
  have laterStart :
      takenSlots operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) (parameterIndex + 1) ≤
        takenSlots operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) j :=
    takenSlots_mono operator.1.1.params operator.2.counts
      (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength'
      (Nat.succ_le_of_lt jGt) (Nat.le_of_lt jBound)
  have covered :
      takenSlots operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) operator.1.1.params.length =
        ((indexedSignature language).arity
          (resizedAt operator parameterIndex bound shape k)).length := by
    unfold resizedAt
    rw [takenSlots_all _ _ _ operator.2.counts_length lengthsLength', expandSlots_length]
  rw [assemble_at (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)
      operator.2.counts_length lengthsLength' j jBound]
  rw [assemble_at (fun direction => toPattern (outside direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length j jBound]
  have lenEq :=
    lengths_set_getD_ne operator.2.lengths parameterIndex k j (Nat.ne_of_lt jGt).symm
  cases reading : baseCollection? (operator.1.1.params.get ⟨j, jBound⟩) with
  | some packed =>
      obtain ⟨kind, _elementSort⟩ := packed
      simp only [Nat.zero_add]
      rw [lenEq]
      apply congrArg (fun elements => Pattern.collection kind elements none)
      refine ofFn_pointwise ?_
      intro index
      have stepNew :=
        takenSlots_step operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength' j jBound
      have width :
          directionsOf (operator.1.1.params.get ⟨j, jBound⟩) (operator.2.counts.getD j 0)
              ((operator.2.lengths.set parameterIndex k).getD j 0) =
            operator.2.lengths.getD j 0 := by
        rw [directionsOf, reading, lenEq]
      have indexLt := index.isLt
      have posLt :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j + index.val <
            takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) (j + 1) := by
        rw [stepNew, width]
        omega
      have nextLe :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) (j + 1) ≤
            takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) operator.1.1.params.length :=
        takenSlots_mono operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength'
          (Nat.succ_le_of_lt jBound) (Nat.le_refl _)
      have posFit :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j + index.val <
            ((indexedSignature language).arity
              (resizedAt operator parameterIndex bound shape k)).length := by
        rw [← covered]
        exact Nat.lt_of_lt_of_le posLt nextLe
      have hPast :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
            takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j + index.val := by
        rw [collapsed] at laterStart
        omega
      have valEq :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j + index.val +
            operator.2.lengths.getD parameterIndex 0 - k =
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths j + index.val := by
        rw [shift]
        omega
      exact nth_splice_suffix operator parameterIndex bound shape k outside trees hPast posFit valEq
  | none =>
      simp only [Nat.zero_add]
      apply congrArg (printArgument (operator.1.1.params.get ⟨j, jBound⟩)
        (operator.2.counts.getD j 0))
      have stepNew :=
        takenSlots_step operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength' j jBound
      have width :
          directionsOf (operator.1.1.params.get ⟨j, jBound⟩) (operator.2.counts.getD j 0)
              ((operator.2.lengths.set parameterIndex k).getD j 0) =
            1 := by
        rw [directionsOf, reading]
      have posLt :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j <
            takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) (j + 1) := by
        rw [stepNew, width]
        omega
      have nextLe :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) (j + 1) ≤
            takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) operator.1.1.params.length :=
        takenSlots_mono operator.1.1.params operator.2.counts
          (operator.2.lengths.set parameterIndex k) operator.2.counts_length lengthsLength'
          (Nat.succ_le_of_lt jBound) (Nat.le_refl _)
      have posFit :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j <
            ((indexedSignature language).arity
              (resizedAt operator parameterIndex bound shape k)).length := by
        rw [← covered]
        exact Nat.lt_of_lt_of_le posLt nextLe
      have hPast :
          takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex + k ≤
            takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j := by
        rw [collapsed] at laterStart
        omega
      have valEq :
          takenSlots operator.1.1.params operator.2.counts
              (operator.2.lengths.set parameterIndex k) j +
            operator.2.lengths.getD parameterIndex 0 - k =
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths j := by
        rw [shift]
        omega
      exact nth_splice_suffix operator parameterIndex bound shape k outside trees hPast posFit valEq

/-- The resized hash set assembles as the element list that was written into it. -/
theorem resizedSet_assemble {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (rightOp : (indexedSignature language).Op sort)
    (rightChildren : Child language Γ sort rightOp)
    (rightCountsLength : rightOp.2.counts.length = operator.1.1.params.length)
    (rightLengthsLength : rightOp.2.lengths.length = operator.1.1.params.length)
    (kEq : k = rightOp.2.lengths.getD parameterIndex 0)
    (treesPrint :
      List.ofFn (fun index => toPattern (trees index)) =
        List.ofFn (fun index : Fin k =>
          nthPrinted (fun direction => toPattern (rightChildren direction))
            (takenSlots operator.1.1.params rightOp.2.counts rightOp.2.lengths parameterIndex +
              index.val))) :
    (assemblePrinted (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)).getD
        parameterIndex (.bvar 0) =
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params rightOp.2.counts rightOp.2.lengths).getD parameterIndex (.bvar 0) := by
  have lengthsLength' :
      (operator.2.lengths.set parameterIndex k).length = operator.1.1.params.length := by
    simpa [List.length_set] using operator.2.lengths_length
  have written :=
    resizedAt_getD operator parameterIndex
      (by simpa [operator.2.lengths_length] using bound) k
  have startSame :=
    takenSlots_set_before operator.1.1.params operator.2.counts operator.2.lengths
      parameterIndex k (Nat.le_refl parameterIndex)
  rw [assemble_at_set (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction))
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)
      operator.2.counts_length lengthsLength' parameterIndex bound shape]
  rw [assemble_at_set (fun direction => toPattern (rightChildren direction))
      operator.1.1.params rightOp.2.counts rightOp.2.lengths
      rightCountsLength rightLengthsLength parameterIndex bound shape]
  simp only
  rw [written, startSame, ← kEq]
  have leftList :
      List.ofFn (fun index : Fin k =>
        nthPrinted (fun direction =>
            toPattern (spliceChild operator parameterIndex bound shape k outside trees direction))
          (takenSlots operator.1.1.params operator.2.counts operator.2.lengths parameterIndex +
            index.val)) =
        List.ofFn (fun index => toPattern (trees index)) := by
    refine ofFn_pointwise ?_
    intro index
    exact nth_splice_segment operator parameterIndex bound shape k outside trees index
  rw [leftList, treesPrint]

/-- Resizing one hash set preserves the assembled argument relation. -/
theorem argRel_resized {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (parameterIndex : Nat)
    (bound : parameterIndex < operator.1.1.params.length)
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, bound⟩) =
      some (.hashSet, element))
    (k : Nat)
    (outside : Child language Γ sort operator)
    (trees : Fin k → Tree language (Γ, element))
    (rightOp : (indexedSignature language).Op sort)
    (rightChildren : Child language Γ sort rightOp)
    (rightCountsLength : rightOp.2.counts.length = operator.1.1.params.length)
    (rightLengthsLength : rightOp.2.lengths.length = operator.1.1.params.length)
    (kEq : k = rightOp.2.lengths.getD parameterIndex 0)
    (treesPrint :
      List.ofFn (fun index => toPattern (trees index)) =
        List.ofFn (fun index : Fin k =>
          nthPrinted (fun direction => toPattern (rightChildren direction))
            (takenSlots operator.1.1.params rightOp.2.counts rightOp.2.lengths parameterIndex +
              index.val)))
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (outside direction)) 0
        operator.1.1.params operator.2.counts operator.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params rightOp.2.counts rightOp.2.lengths)) :
    List.Forall₂ PatternCong
      (assemblePrinted (fun direction =>
          toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
        operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k))
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        operator.1.1.params rightOp.2.counts rightOp.2.lengths) := by
  have lengthsLength' :
      (operator.2.lengths.set parameterIndex k).length = operator.1.1.params.length := by
    simpa [List.length_set] using operator.2.lengths_length
  have lenNew :=
    assemblePrinted_length (fun direction =>
        toPattern (spliceChild operator parameterIndex bound shape k outside trees direction)) 0
      operator.1.1.params operator.2.counts (operator.2.lengths.set parameterIndex k)
      operator.2.counts_length lengthsLength'
  have lenOld :=
    assemblePrinted_length (fun direction => toPattern (outside direction)) 0
      operator.1.1.params operator.2.counts operator.2.lengths
      operator.2.counts_length operator.2.lengths_length
  have lenRight :=
    assemblePrinted_length (fun direction => toPattern (rightChildren direction)) 0
      operator.1.1.params rightOp.2.counts rightOp.2.lengths
      rightCountsLength rightLengthsLength
  apply List.forall₂_iff_get.mpr
  refine ⟨by rw [lenNew, lenRight], ?_⟩
  intro i hNew hRight
  have iBound : i < operator.1.1.params.length := by
    simpa [lenNew] using hNew
  have oldAt :=
    (List.forall₂_iff_get.mp argRel).2 i (by simpa [lenOld] using iBound)
      (by simpa [lenRight] using iBound)
  rw [← List.getD_eq_get (d := .bvar 0) (i := ⟨i, hNew⟩),
    ← List.getD_eq_get (d := .bvar 0) (i := ⟨i, hRight⟩)]
  rw [← List.getD_eq_get (d := .bvar 0)
      (i := ⟨i, by simpa [lenOld] using iBound⟩),
    ← List.getD_eq_get (d := .bvar 0)
      (i := ⟨i, by simpa [lenRight] using iBound⟩)] at oldAt
  by_cases earlier : i < parameterIndex
  · rw [assemble_before operator parameterIndex bound shape k outside trees i earlier iBound]
    exact oldAt
  · by_cases focus : i = parameterIndex
    · subst focus
      rw [resizedSet_assemble operator i bound shape k outside trees rightOp rightChildren
        rightCountsLength rightLengthsLength kEq treesPrint]
      exact PatternCong.refl _
    · have jGt : parameterIndex < i := by omega
      rw [assemble_after operator parameterIndex bound shape k outside trees i jGt iBound]
      exact oldAt

/-- Bring every hash-set length into agreement with the right operator, then walk. -/
theorem set_apply_from
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (rightOp : (indexedSignature language).Op sort)
    (rightChildren : Child language Γ sort rightOp) :
    ∀ (fuel : Nat)
      (operator : (indexedSignature language).Op sort)
      (children : Child language Γ sort operator)
      (_ih : ∀ direction
          (other : Tree language
            ((polynomial (indexedSignature language)).src (Γ, sort) operator direction)),
          PatternCong (toPattern (children direction)) (toPattern other) →
            TreeCong language (children direction) other)
      (_sameRule : operator.1.1 = rightOp.1.1)
      (_countsEq : operator.2.counts = rightOp.2.counts)
      (_plain : ∀ index : Nat,
        isHashSetParam (operator.1.1.params.getD index missingParameter) = false →
          operator.2.lengths.getD index 0 = rightOp.2.lengths.getD index 0)
      (_argRel : List.Forall₂ PatternCong
        (assemblePrinted (fun direction => toPattern (children direction)) 0
          operator.1.1.params operator.2.counts operator.2.lengths)
        (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
          operator.1.1.params rightOp.2.counts rightOp.2.lengths))
      (done : Nat)
      (_doneLe : done ≤ operator.1.1.params.length)
      (_fuelBound : operator.1.1.params.length - done ≤ fuel)
      (_prefixOk : ∀ i, i < done →
        operator.2.lengths.getD i 0 = rightOp.2.lengths.getD i 0),
      TreeCong language
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          operator children)
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
          rightOp rightChildren) := by
  intro fuel
  induction fuel with
  | zero =>
      intro operator children ih sameRule countsEq _plain argRel done doneLe _fuelBound prefixOk
      have doneAll : done = operator.1.1.params.length := by omega
      subst doneAll
      exact agreed_lengths_walk labels uniqueBare operator children rightOp rightChildren ih
        sameRule countsEq argRel (fun i hi => prefixOk i hi)
  | succ fuel inductionHypothesis =>
      intro operator children ih sameRule countsEq plain argRel done doneLe _fuelBound prefixOk
      by_cases doneAll : done = operator.1.1.params.length
      · subst doneAll
        exact agreed_lengths_walk labels uniqueBare operator children rightOp rightChildren ih
          sameRule countsEq argRel (fun i hi => prefixOk i hi)
      · have doneBound : done < operator.1.1.params.length := by omega
        cases setFlag : isHashSetParam (operator.1.1.params.getD done missingParameter) with
        | false =>
            have lenEq := plain done setFlag
            exact inductionHypothesis operator children ih sameRule countsEq plain argRel (done + 1)
              (by omega) (by omega)
              (by
                intro i hi
                by_cases same : i = done
                · subst same
                  exact lenEq
                · exact prefixOk i (by omega))
        | true =>
            by_cases lenEq : operator.2.lengths.getD done 0 = rightOp.2.lengths.getD done 0
            · exact inductionHypothesis operator children ih sameRule countsEq plain argRel
                (done + 1) (by omega) (by omega)
                (by
                  intro i hi
                  by_cases same : i = done
                  · subst same
                    exact lenEq
                  · exact prefixOk i (by omega))
            · obtain ⟨element, shape⟩ := hashSet_shape_of_flag doneBound setFlag
              have paramsEq : rightOp.1.1.params = operator.1.1.params :=
                congrArg (fun rule => rule.params) sameRule.symm
              have rightBound : done < rightOp.1.1.params.length := by
                simpa [paramsEq] using doneBound
              have shapeR :
                  baseCollection? (rightOp.1.1.params.get ⟨done, rightBound⟩) =
                    some (.hashSet, element) := by
                simpa [paramsEq] using shape
              let newLen := rightOp.2.lengths.getD done 0
              let trees :=
                segmentTrees rightOp done rightBound shapeR newLen rfl rightChildren
              have covers :=
                set_segment_covers operator rightOp done doneBound shape children rightChildren
                  sameRule rightBound shapeR argRel
              have treesPrint :
                  List.ofFn (fun index => toPattern (trees index)) =
                    List.ofFn (fun index : Fin newLen =>
                      nthPrinted (fun direction => toPattern (rightChildren direction))
                        (takenSlots operator.1.1.params rightOp.2.counts rightOp.2.lengths done +
                          index.val)) := by
                simp only [trees, newLen]
                have raw := segment_prints_eq rightOp done rightBound shapeR rightChildren
                let rightCounts := rightOp.2.counts
                let rightLengths := rightOp.2.lengths
                have slotsEq :
                    takenSlots rightOp.1.1.params rightCounts rightLengths done =
                      takenSlots operator.1.1.params rightCounts rightLengths done :=
                  congrArg
                    (fun parameters => takenSlots parameters rightCounts rightLengths done)
                    paramsEq
                rw [raw]
                refine ofFn_pointwise ?_
                intro index
                rw [slotsEq]
              have treeIh :=
                target_element_ih
                  (segmentTrees operator done doneBound shape
                    (operator.2.lengths.getD done 0) rfl children)
                  trees
                  (segmentTrees_ih operator done doneBound shape
                    (operator.2.lengths.getD done 0) rfl children ih)
                  covers.2
              have adopted :=
                adopt_one_set operator done doneBound shape children ih trees covers.1 covers.2
              have newIh :=
                spliceChild_ih operator done doneBound shape newLen children trees ih treeIh
              have rightCountsLength : rightOp.2.counts.length = operator.1.1.params.length := by
                rw [rightOp.2.counts_length, paramsEq]
              have rightLengthsLength : rightOp.2.lengths.length = operator.1.1.params.length := by
                rw [rightOp.2.lengths_length, paramsEq]
              have newArgRel :=
                argRel_resized operator done doneBound shape newLen children trees rightOp
                  rightChildren rightCountsLength rightLengthsLength rfl treesPrint argRel
              have newCounts :
                  (resizedAt operator done doneBound shape newLen).2.counts = rightOp.2.counts := by
                simpa [resizedAt] using countsEq
              have ruleKept :
                  (resizedAt operator done doneBound shape newLen).1.1 = rightOp.1.1 := by
                simpa [resizedAt] using sameRule
              have newPlain :
                  ∀ index : Nat,
                    isHashSetParam ((resizedAt operator done doneBound shape newLen).1.1.params.getD
                        index missingParameter) = false →
                      (resizedAt operator done doneBound shape newLen).2.lengths.getD index 0 =
                        rightOp.2.lengths.getD index 0 := by
                intro index hyp
                by_cases same : index = done
                · rw [same] at hyp
                  simp only [resizedAt] at hyp
                  have marked :
                      isHashSetParam (operator.1.1.params.getD done missingParameter) = true := by
                    rw [isHashSetParam,
                      List.getD_eq_get (d := missingParameter) (i := ⟨done, doneBound⟩), shape]
                  rw [marked] at hyp
                  exact (Bool.false_ne_true hyp.symm).elim
                · have kept :=
                    lengths_set_getD_ne operator.2.lengths done newLen index same
                  have old := plain index (by simpa [resizedAt] using hyp)
                  simpa [resizedAt] using kept.trans old
              have newPrefix :
                  ∀ i, i < done + 1 →
                    (resizedAt operator done doneBound shape newLen).2.lengths.getD i 0 =
                      rightOp.2.lengths.getD i 0 := by
                intro i hi
                by_cases same : i = done
                · rw [same]
                  have written :=
                    resizedAt_getD operator done
                      (by simpa [operator.2.lengths_length] using doneBound) newLen
                  simpa [resizedAt, newLen] using written
                · have kept := lengths_set_getD_ne operator.2.lengths done newLen i same
                  have earlier := prefixOk i (by omega)
                  simpa [resizedAt] using kept.trans earlier
              have sameLen :
                  (resizedAt operator done doneBound shape newLen).1.1.params.length =
                    operator.1.1.params.length := by
                simp [resizedAt]
              exact adopted.trans
                (inductionHypothesis (resizedAt operator done doneBound shape newLen)
                  (spliceChild operator done doneBound shape newLen children trees)
                  newIh ruleKept newCounts newPlain newArgRel (done + 1)
                  (by rw [sameLen]; omega) (by rw [sameLen]; omega) newPrefix)

/-- A non-bare operator whose parameters include a hash set. Lengths of those
sets are the head data the pattern congruence may change, by deleting one of
two equal children. -/
theorem set_apply_treeCong
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (sameRule : leftOp.1.1 = rightOp.1.1)
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
        leftOp.1.1.params leftOp.2.counts leftOp.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        leftOp.1.1.params rightOp.2.counts rightOp.2.lengths)) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  obtain ⟨countsEq, plainLengths⟩ :=
    recover_partial
      (fun direction => toPattern (leftChildren direction))
      (fun direction => toPattern (rightChildren direction))
      0 0 leftOp.1.1.params leftOp.2.counts leftOp.2.lengths rightOp.2.counts
      rightOp.2.lengths leftOp.2.counts_length leftOp.2.lengths_length
      (by rw [rightOp.2.counts_length,
          ← congrArg List.length (congrArg (fun rule => rule.params) sameRule)])
      (by rw [rightOp.2.lengths_length,
          ← congrArg List.length (congrArg (fun rule => rule.params) sameRule)])
      leftOp.2.counts_fixed
      (by
        intro index hypothesis
        exact rightOp.2.counts_fixed index
          (by simpa [congrArg (fun rule => rule.params) sameRule] using hypothesis))
      leftOp.2.lengths_fixed
      (by
        intro index hypothesis
        exact rightOp.2.lengths_fixed index
          (by simpa [congrArg (fun rule => rule.params) sameRule] using hypothesis))
      argRel
  exact set_apply_from labels uniqueBare rightOp rightChildren
    leftOp.1.1.params.length leftOp leftChildren ih sameRule countsEq plainLengths argRel
    0 (Nat.zero_le _) (Nat.le_refl _) (fun i hi => (Nat.not_lt_zero i hi).elim)

/-- A non-bare operator with a bag or a set parameter. The generators are the
segment permutation and the set deletion; this is the first encoding. -/
theorem bagset_from_rule
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (sameRule : leftOp.1.1 = rightOp.1.1)
    (argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
        leftOp.1.1.params leftOp.2.counts leftOp.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        leftOp.1.1.params rightOp.2.counts rightOp.2.lengths)) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  by_cases noSet : paramsHasSet leftOp.1.1.params = false
  · have heads :=
      recover_no_set
        (fun direction => toPattern (leftChildren direction))
        (fun direction => toPattern (rightChildren direction))
        0 leftOp.1.1.params leftOp.2.counts leftOp.2.lengths rightOp.2.counts
        rightOp.2.lengths leftOp.2.counts_length leftOp.2.lengths_length
        (by rw [rightOp.2.counts_length,
            ← congrArg List.length (congrArg (fun rule => rule.params) sameRule)])
        (by rw [rightOp.2.lengths_length,
            ← congrArg List.length (congrArg (fun rule => rule.params) sameRule)])
        leftOp.2.counts_fixed
        (by
          intro index hypothesis
          exact rightOp.2.counts_fixed index
            (by simpa [congrArg (fun rule => rule.params) sameRule] using hypothesis))
        leftOp.2.lengths_fixed
        (by
          intro index hypothesis
          exact rightOp.2.lengths_fixed index
            (by simpa [congrArg (fun rule => rule.params) sameRule] using hypothesis))
        noSet argRel
    obtain ⟨countsEq, lengthsEq⟩ := heads
    have opEq : leftOp = rightOp := by
      rcases leftOp with ⟨packedLeft, dataLeft⟩
      rcases rightOp with ⟨packedRight, dataRight⟩
      have packedEq : packedLeft = packedRight := Subtype.ext sameRule
      subst packedEq
      have dataEq : dataLeft = dataRight := headData_ext countsEq lengthsEq
      subst dataEq
      rfl
    subst opEq
    let operator := leftOp
    have advance :
        ∀ fuel done (current : Child language Γ sort operator),
          done + fuel = operator.1.1.params.length →
          TreeCong language
            (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
              operator rightChildren)
            (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
              operator current) →
          (∀ direction : Fin ((indexedSignature language).arity operator).length,
            direction.val <
                takenSlots operator.1.1.params operator.2.counts operator.2.lengths done →
              PatternCong (toPattern (leftChildren direction)) (toPattern (current direction))) →
          (∀ direction : Fin ((indexedSignature language).arity operator).length,
            takenSlots operator.1.1.params operator.2.counts operator.2.lengths done ≤
                direction.val →
              current direction = rightChildren direction) →
          TreeCong language
            (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
              operator leftChildren)
            (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
              operator rightChildren) := by
      intro fuel
      induction fuel with
      | zero =>
          intro done current sum rightToCurrent aligned suffix
          have doneAll : done = operator.1.1.params.length := by omega
          subst doneAll
          have covered :
              takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                  operator.1.1.params.length =
                ((indexedSignature language).arity operator).length := by
            rw [takenSlots_all _ _ _ operator.2.counts_length operator.2.lengths_length,
              expandSlots_length]
          have steps :
              ∀ direction, TreeCong language (leftChildren direction) (current direction) := by
            intro direction
            apply ih
            have bound :
                direction.val <
                  takenSlots operator.1.1.params operator.2.counts operator.2.lengths
                    operator.1.1.params.length := by
              rw [covered]
              exact direction.isLt
            exact aligned direction bound
          exact (treeCong_pointwise operator leftChildren current steps).trans
            (TreeCong.symm rightToCurrent)
      | succ fuel inductionHypothesis =>
          intro done current sum rightToCurrent aligned suffix
          have doneBound : done < operator.1.1.params.length := by omega
          obtain ⟨current', stepped, aligned', suffix'⟩ :=
            extend_alignment labels uniqueBare operator done doneBound leftChildren rightChildren
              current ih argRel rightToCurrent aligned suffix
          exact inductionHypothesis (done + 1) current' (by omega) stepped aligned' suffix'
    exact advance operator.1.1.params.length 0 rightChildren (by omega) (TreeCong.refl _)
      (by
        intro direction bound
        simp [takenSlots_zero] at bound)
      (by
        intro direction _
        rfl)
  · have _marked : paramsHasSet leftOp.1.1.params = true := by simpa using noSet
    exact set_apply_treeCong labels uniqueBare leftOp leftChildren rightOp rightChildren ih
      sameRule argRel

/-- A non-bare operator with a bag or a set parameter. The generators are the
segment permutation and the set deletion; this is the first encoding. -/
theorem bagset_apply_treeCong
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftShape : bareCollection? leftOp.1.1 = none)
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightShape : bareCollection? rightOp.1.1 = none)
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (related : PatternCong
      (nodeOf leftOp fun direction => toPattern (leftChildren direction))
      (nodeOf rightOp fun direction => toPattern (rightChildren direction)))
    (notPlain : paramsPlain leftOp.1.1.params = false) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  simp only [nodeOf, leftShape, rightShape] at related
  obtain ⟨label, _args, _args', leftEq, rightEq, _argRel⟩ :=
    patternCong_apply_args related
      (Or.inl ⟨leftOp.1.1.label,
        assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
          leftOp.1.1.params leftOp.2.counts leftOp.2.lengths, rfl⟩)
  simp only [Pattern.apply.injEq] at leftEq rightEq
  obtain ⟨leftLabel, leftArgs⟩ := leftEq
  obtain ⟨rightLabel, rightArgs⟩ := rightEq
  have sameLabel : leftOp.1.1.label = rightOp.1.1.label :=
    leftLabel.trans rightLabel.symm
  have sameRule : leftOp.1.1 = rightOp.1.1 :=
    List.inj_on_of_nodup_map (f := fun rule => rule.label) labels
      leftOp.1.2.1 rightOp.1.2.1 sameLabel
  have paramsEq : leftOp.1.1.params = rightOp.1.1.params :=
    congrArg (fun rule => rule.params) sameRule
  have argRel : List.Forall₂ PatternCong
      (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
        leftOp.1.1.params leftOp.2.counts leftOp.2.lengths)
      (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
        leftOp.1.1.params rightOp.2.counts rightOp.2.lengths) := by
    rw [← leftArgs, ← rightArgs] at _argRel
    have paramsShift :
        assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
            rightOp.1.1.params rightOp.2.counts rightOp.2.lengths =
          assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
            leftOp.1.1.params rightOp.2.counts rightOp.2.lengths :=
      congrArg
        (fun parameters =>
          assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
            parameters rightOp.2.counts rightOp.2.lengths)
        paramsEq.symm
    rw [paramsShift] at _argRel
    exact _argRel
  have _keptPlain : paramsPlain leftOp.1.1.params = false := notPlain
  exact bagset_from_rule labels uniqueBare leftOp leftChildren rightOp rightChildren ih sameRule
    argRel

/-- A non-bare operator reflects the pattern congruence as the tree congruence.
Binder and vector parameters contribute no quotient. -/
theorem applyBare_treeCong
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {Γ : List String} {sort : String}
    (leftOp : (indexedSignature language).Op sort)
    (leftShape : bareCollection? leftOp.1.1 = none)
    (leftChildren : Child language Γ sort leftOp)
    (rightOp : (indexedSignature language).Op sort)
    (rightShape : bareCollection? rightOp.1.1 = none)
    (rightChildren : Child language Γ sort rightOp)
    (ih : ∀ direction
        (other : Tree language
          ((polynomial (indexedSignature language)).src (Γ, sort) leftOp direction)),
        PatternCong (toPattern (leftChildren direction)) (toPattern other) →
          TreeCong language (leftChildren direction) other)
    (related : PatternCong
      (nodeOf leftOp fun direction => toPattern (leftChildren direction))
      (nodeOf rightOp fun direction => toPattern (rightChildren direction))) :
    TreeCong language
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        leftOp leftChildren)
      (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
        rightOp rightChildren) := by
  cases plain? : paramsPlain leftOp.1.1.params with
  | false =>
      exact bagset_apply_treeCong labels uniqueBare leftOp leftShape leftChildren
        rightOp rightShape rightChildren ih related plain?
  | true =>
      simp only [nodeOf, leftShape, rightShape] at related
      obtain ⟨label, _args, _args', leftEq, rightEq, argRel⟩ :=
        patternCong_apply_args related
          (Or.inl ⟨leftOp.1.1.label,
            assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
              leftOp.1.1.params leftOp.2.counts leftOp.2.lengths, rfl⟩)
      simp only [Pattern.apply.injEq] at leftEq rightEq
      obtain ⟨leftLabel, leftArgs⟩ := leftEq
      obtain ⟨rightLabel, rightArgs⟩ := rightEq
      have sameLabel : leftOp.1.1.label = rightOp.1.1.label :=
        leftLabel.trans rightLabel.symm
      have sameRule : leftOp.1.1 = rightOp.1.1 :=
        List.inj_on_of_nodup_map (f := fun rule => rule.label) labels
          leftOp.1.2.1 rightOp.1.2.1 sameLabel
      have paramsEq : leftOp.1.1.params = rightOp.1.1.params :=
        congrArg (fun rule => rule.params) sameRule
      have argRel' : List.Forall₂ PatternCong
          (assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
            leftOp.1.1.params leftOp.2.counts leftOp.2.lengths)
          (assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
            leftOp.1.1.params rightOp.2.counts rightOp.2.lengths) := by
        rw [← leftArgs, ← rightArgs] at argRel
        have paramsShift :
            assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
                rightOp.1.1.params rightOp.2.counts rightOp.2.lengths =
              assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
                leftOp.1.1.params rightOp.2.counts rightOp.2.lengths :=
          congrArg
            (fun parameters =>
              assemblePrinted (fun direction => toPattern (rightChildren direction)) 0
                parameters rightOp.2.counts rightOp.2.lengths)
            paramsEq.symm
        rw [paramsShift] at argRel
        exact argRel
      have heads :=
        plain_assemble
          (fun direction => toPattern (leftChildren direction))
          (fun direction => toPattern (rightChildren direction))
          0 leftOp.1.1.params leftOp.2.counts leftOp.2.lengths rightOp.2.counts
          rightOp.2.lengths leftOp.2.counts_length leftOp.2.lengths_length
          (by rw [rightOp.2.counts_length, ← paramsEq])
          (by rw [rightOp.2.lengths_length, ← paramsEq])
          leftOp.2.counts_fixed
          (by
            intro index hypothesis
            exact rightOp.2.counts_fixed index (by simpa [paramsEq] using hypothesis))
          leftOp.2.lengths_fixed
          (by
            intro index hypothesis
            exact rightOp.2.lengths_fixed index (by simpa [paramsEq] using hypothesis))
          plain? argRel'
      obtain ⟨countsEq, lengthsEq, pointwise⟩ := heads
      have opEq : leftOp = rightOp := by
        rcases leftOp with ⟨packedLeft, dataLeft⟩
        rcases rightOp with ⟨packedRight, dataRight⟩
        have packedEq : packedLeft = packedRight := Subtype.ext sameRule
        subst packedEq
        have dataEq : dataLeft = dataRight := headData_ext countsEq lengthsEq
        subst dataEq
        rfl
      subst opEq
      have steps :
          ∀ direction, TreeCong language (leftChildren direction) (rightChildren direction) := by
        intro direction
        apply ih
        have bound : direction.val <
            slotCount leftOp.1.1.params leftOp.2.counts leftOp.2.lengths := by
          simpa [expandSlots_length] using direction.isLt
        have atDir := pointwise direction.val bound
        simp only [Nat.zero_add] at atDir
        rw [nthPrinted_of_lt _ direction.isLt, nthPrinted_of_lt _ direction.isLt] at atDir
        rw [Fin.eta direction] at atDir
        exact atDir
      exact treeCong_pointwise leftOp leftChildren rightChildren steps

/-- A de Bruijn pattern is only congruent to itself. -/
theorem bvar_of_index {pattern : Pattern} {index : Nat}
    (head : bvarIndex? pattern = some index) : pattern = .bvar index := by
  cases pattern with
  | bvar index' =>
      simp only [bvarIndex?, Option.some.injEq] at head
      exact congrArg Pattern.bvar head
  | fvar _ => simp [bvarIndex?] at head
  | lambda _ _ => simp [bvarIndex?] at head
  | multiLambda _ _ _ => simp [bvarIndex?] at head
  | subst _ _ => simp [bvarIndex?] at head
  | apply _ _ => simp [bvarIndex?] at head
  | collection _ _ _ => simp [bvarIndex?] at head

/-- Printing reflects the pattern congruence into the tree congruence on a bare
hash bag, a variable, and, through the same induction, every other head. -/
theorem pattern_treeCong
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language)
    {index : List String × String} (left : Tree language index) :
    ∀ right : Tree language index,
      PatternCong (toPattern left) (toPattern right) →
        TreeCong language left right := by
  induction left with
  | pure variable_ =>
      intro right related
      cases right with
      | pure variable' =>
          rw [toPattern_pure, toPattern_pure] at related
          have sameIndex := patternCong_bvarIndex related
          simp only [bvarIndex?, Option.some.injEq] at sameIndex
          have variableEq := varIndex_injective variable_ variable' sameIndex
          subst variableEq
          exact TreeCong.refl _
      | liftBind operator _children =>
          rw [toPattern_pure, toPattern_liftBind] at related
          have heads := patternCong_bvarIndex related
          have notBvar : bvarIndex? (nodeOf operator fun direction =>
              toPattern (_children direction)) = none := by
            cases reading : bareCollection? operator.1.1 <;>
              simp [nodeOf, reading, bvarIndex?]
          rw [notBvar] at heads
          cases heads
  | liftBind operator children inductionHypothesis =>
      intro right related
      cases right with
      | pure variable_ =>
          rw [toPattern_liftBind, toPattern_pure] at related
          have heads := patternCong_bvarIndex related
          have notBvar : bvarIndex? (nodeOf operator fun direction =>
              toPattern (children direction)) = none := by
            cases reading : bareCollection? operator.1.1 <;>
              simp [nodeOf, reading, bvarIndex?]
          rw [notBvar] at heads
          cases heads
      | liftBind operator' children' =>
          rw [toPattern_liftBind, toPattern_liftBind] at related
          cases reading : bareCollection? operator.1.1 with
          | some pair =>
              obtain ⟨kind, element⟩ := pair
              cases kind with
              | hashBag =>
                  cases reading' : bareCollection? operator'.1.1 with
                  | some pair' =>
                      obtain ⟨kind', element'⟩ := pair'
                      have bagKind : kind' = .hashBag := by
                        have heads := patternCong_collectionHead related
                        simp only [nodeOf, reading, reading', collectionHead?,
                          Option.some.injEq, Prod.mk.injEq] at heads
                        exact heads.1.symm
                      subst bagKind
                      have sameElement : element' = element := by
                        have sameRule :=
                          uniqueBare operator.1.2.1 operator'.1.2.1
                            (operator.1.2.2.2.trans operator'.1.2.2.2.symm) reading reading'
                        have shapes := congrArg bareCollection? sameRule
                        simp only [reading, reading', Option.some.injEq, Prod.mk.injEq] at shapes
                        exact shapes.2.symm
                      subst sameElement
                      exact bareBag_treeCong labels uniqueBare operator reading children
                        operator' reading' children' inductionHypothesis related
                  | none =>
                      have heads := patternCong_collectionHead related
                      simp only [nodeOf, reading, reading', collectionHead?] at heads
                      cases heads
              | vec =>
                  cases reading' : bareCollection? operator'.1.1 with
                  | none =>
                      have heads := patternCong_collectionHead related
                      simp only [nodeOf, reading, reading', collectionHead?] at heads
                      cases heads
                  | some pair' =>
                      obtain ⟨kind', element'⟩ := pair'
                      have kindEq : kind' = .vec := by
                        have heads := patternCong_collectionHead related
                        simp only [nodeOf, reading, reading', collectionHead?,
                          Option.some.injEq, Prod.mk.injEq] at heads
                        exact heads.1.symm
                      subst kindEq
                      have sameElement : element' = element := by
                        have sameRule :=
                          uniqueBare operator.1.2.1 operator'.1.2.1
                            (operator.1.2.2.2.trans operator'.1.2.2.2.symm) reading reading'
                        have shapes := congrArg bareCollection? sameRule
                        simp only [reading, reading', Option.some.injEq, Prod.mk.injEq] at shapes
                        exact shapes.2.symm
                      subst sameElement
                      exact vecBare_treeCong labels uniqueBare operator reading children
                        operator' reading' children' inductionHypothesis related
              | hashSet =>
                  cases reading' : bareCollection? operator'.1.1 with
                  | none =>
                      have heads := patternCong_collectionHead related
                      simp only [nodeOf, reading, reading', collectionHead?] at heads
                      cases heads
                  | some pair' =>
                      obtain ⟨kind', element'⟩ := pair'
                      have kindEq : kind' = .hashSet := by
                        have heads := patternCong_collectionHead related
                        simp only [nodeOf, reading, reading', collectionHead?,
                          Option.some.injEq, Prod.mk.injEq] at heads
                        exact heads.1.symm
                      subst kindEq
                      have sameElement : element' = element := by
                        have sameRule :=
                          uniqueBare operator.1.2.1 operator'.1.2.1
                            (operator.1.2.2.2.trans operator'.1.2.2.2.symm) reading reading'
                        have shapes := congrArg bareCollection? sameRule
                        simp only [reading, reading', Option.some.injEq, Prod.mk.injEq] at shapes
                        exact shapes.2.symm
                      subst sameElement
                      exact setBare_treeCong labels uniqueBare operator reading children
                        operator' reading' children' inductionHypothesis related
          | none =>
              cases reading' : bareCollection? operator'.1.1 with
              | some _ =>
                  have heads := patternCong_applyLabel related
                  simp only [nodeOf, reading, reading', applyLabel?] at heads
                  cases heads
              | none =>
                  exact applyBare_treeCong labels uniqueBare operator reading children
                    operator' reading' children' inductionHypothesis related

/-- Closed object patterns modulo one bag permutation, or one deletion of a
duplicate set child, are the indexed trees modulo that same congruence. -/
noncomputable def collectionQuotientEquiv
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language) (sort : String) :
    Quotient (treeSetoid (language := language) sort) ≃
      Quotient (patternSetoid (language := language) sort) :=
  Quotient.congr (closedIndexedEquiv fragment labels uniqueBare sort)
    (fun left right =>
      ⟨fun related => treeCong_pattern related,
        fun related => pattern_treeCong labels uniqueBare left right related⟩)

end Mettapedia.GSLT.Poly.CollectionIndexedEquiv
