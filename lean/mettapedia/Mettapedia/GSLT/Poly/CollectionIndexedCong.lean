import Mettapedia.GSLT.Poly.CollectionIndexedEquiv

/-!
# Printing the indexed tree congruence

Permutation of one bag or set parameter, and deletion of one duplicate set
child, print as the same steps on patterns. The pattern quotient and the tree
quotient are therefore the same once both directions are proved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedEquiv

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Poly.BindingLanguage hiding toPattern
open Mettapedia.GSLT.Poly.BindingSignature
open Mettapedia.GSLT.Poly.CollectionIndexed
open IPFunctor

variable {language : LanguageDef}

/-! ## The tree congruence prints as the pattern congruence -/

theorem wrapBinders_cong (binders : List String) {left right : Pattern}
    (related : PatternCong left right) :
    PatternCong (wrapBinders binders left) (wrapBinders binders right) := by
  induction binders generalizing left right with
  | nil => simpa [wrapBinders] using related
  | cons _ binders inductionHypothesis =>
      simpa [wrapBinders] using inductionHypothesis (PatternCong.lambdaAt related)

theorem printArgument_cong (parameter : TermParam) (count : Nat) {left right : Pattern}
    (related : PatternCong left right) :
    PatternCong (printArgument parameter count left)
      (printArgument parameter count right) := by
  cases parameter with
  | simple _ type =>
      cases type <;>
        simpa [printArgument, slotBinders] using wrapBinders_cong _ related
  | abstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simpa [printArgument, slotBinders] using wrapBinders_cong _ related
      | arrow domain codomain =>
          cases domain <;> cases codomain <;>
            simpa [printArgument, slotBinders] using wrapBinders_cong _ related
      | multiBinder _ =>
          simpa [printArgument, slotBinders] using wrapBinders_cong _ related
      | collection _ _ =>
          simpa [printArgument, slotBinders] using wrapBinders_cong _ related
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simpa [printArgument] using PatternCong.multiLambdaAt related
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              cases inner with
              | base _ =>
                  cases codomain with
                  | base _ =>
                      simpa [printArgument] using PatternCong.multiLambdaAt related
                  | arrow _ _ =>
                      simpa [printArgument, slotBinders] using wrapBinders_cong _ related
                  | multiBinder _ =>
                      simpa [printArgument, slotBinders] using wrapBinders_cong _ related
                  | collection _ _ =>
                      simpa [printArgument, slotBinders] using wrapBinders_cong _ related
              | arrow _ _ =>
                  simpa [printArgument, slotBinders] using wrapBinders_cong _ related
              | multiBinder _ =>
                  simpa [printArgument, slotBinders] using wrapBinders_cong _ related
              | collection _ _ =>
                  simpa [printArgument, slotBinders] using wrapBinders_cong _ related
          | base _ =>
              simpa [printArgument, slotBinders] using wrapBinders_cong _ related
          | arrow _ _ =>
              simpa [printArgument, slotBinders] using wrapBinders_cong _ related
          | collection _ _ =>
              simpa [printArgument, slotBinders] using wrapBinders_cong _ related
      | multiBinder _ =>
          simpa [printArgument, slotBinders] using wrapBinders_cong _ related
      | collection _ _ =>
          simpa [printArgument, slotBinders] using wrapBinders_cong _ related

theorem forall2_pattern_of_eq {left right : List Pattern} (equal : left = right) :
    List.Forall₂ PatternCong left right := by
  subst equal
  induction left with
  | nil => exact List.Forall₂.nil
  | cons _ _ inductionHypothesis =>
      exact List.Forall₂.cons (PatternCong.refl _) inductionHypothesis

theorem apply_prefix_cong {label : String} (before left right : List Pattern)
    (pointwise : List.Forall₂ PatternCong left right) :
    PatternCong (.apply label (before ++ left)) (.apply label (before ++ right)) := by
  induction left generalizing before right with
  | nil =>
      have rightNil : right = [] := List.forall₂_nil_left_iff.mp pointwise
      subst rightNil
      simpa [List.append_nil] using PatternCong.refl (.apply label before)
  | cons head tail inductionHypothesis =>
      obtain ⟨rightHead, rightTail, headStep, tailPointwise, rightEq⟩ :=
        List.forall₂_cons_left_iff.mp pointwise
      subst rightEq
      apply PatternCong.trans
      · exact PatternCong.applyAt (before := before) headStep
      · simpa [List.append_assoc, List.singleton_append] using
          inductionHypothesis (before ++ [rightHead]) rightTail tailPointwise

theorem collection_prefix_cong {kind : CollType} {rest : Option String}
    (before left right : List Pattern) (pointwise : List.Forall₂ PatternCong left right) :
    PatternCong (.collection kind (before ++ left) rest)
      (.collection kind (before ++ right) rest) := by
  induction left generalizing before right with
  | nil =>
      have rightNil : right = [] := List.forall₂_nil_left_iff.mp pointwise
      subst rightNil
      simpa [List.append_nil] using PatternCong.refl (.collection kind before rest)
  | cons head tail inductionHypothesis =>
      obtain ⟨rightHead, rightTail, headStep, tailPointwise, rightEq⟩ :=
        List.forall₂_cons_left_iff.mp pointwise
      subst rightEq
      apply PatternCong.trans
      · exact PatternCong.collectionAt (before := before) headStep
      · simpa [List.append_assoc, List.singleton_append] using
          inductionHypothesis (before ++ [rightHead]) rightTail tailPointwise

theorem ofFn_forall2_eq {n : Nat} {left right : Fin n → Pattern}
    (agree : ∀ index, left index = right index) :
    List.Forall₂ PatternCong (List.ofFn left) (List.ofFn right) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (agree 0 ▸ PatternCong.refl _)
        (inductionHypothesis fun index => agree index.succ)

theorem ofFn_forall2_one {n : Nat} (left right : Fin n → Pattern) (changed : Fin n)
    (step : PatternCong (left changed) (right changed))
    (stable : ∀ index, index ≠ changed → left index = right index) :
    List.Forall₂ PatternCong (List.ofFn left) (List.ofFn right) := by
  induction n with
  | zero => exact changed.elim0
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ]
      cases changed using Fin.cases with
      | zero =>
          refine List.Forall₂.cons step ?_
          exact ofFn_forall2_eq fun index =>
            stable index.succ (Fin.succ_ne_zero index)
      | succ changed =>
          refine List.Forall₂.cons ?_ ?_
          · have headEq : left 0 = right 0 :=
              stable 0 (Ne.symm (Fin.succ_ne_zero changed))
            exact headEq ▸ PatternCong.refl _
          · exact inductionHypothesis (fun index => left index.succ)
              (fun index => right index.succ) changed (by simpa using step)
              fun index different => stable index.succ fun same =>
                different (Fin.succ_injective _ same)

theorem toPattern_segmentChild {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort) (start : Nat) {length : Nat}
    (index : Fin length)
    (fit : start + index.val < ((indexedSignature language).arity operator).length)
    (uniform :
      ((indexedSignature language).arity operator).get ⟨start + index.val, fit⟩ = ([], element))
    (children : Child language Γ sort operator) :
    toPattern (segmentChild operator start index fit uniform children) =
      toPattern (children ⟨start + index.val, fit⟩) := by
  have sourceEq :
      (polynomial (indexedSignature language)).src (Γ, sort) operator
          ⟨start + index.val, fit⟩ =
        (Γ, element) := by
    rw [polynomial_direction, uniform]
    rfl
  simpa [segmentChild, atElement] using
    toPattern_cast sourceEq (children ⟨start + index.val, fit⟩)

theorem toPattern_atElement {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort)
    (direction : Fin ((indexedSignature language).arity operator).length)
    (uniform : ((indexedSignature language).arity operator).get direction = ([], element))
    (children : Child language Γ sort operator) :
    toPattern (atElement operator direction uniform children) =
      toPattern (children direction) := by
  have sourceEq :
      (polynomial (indexedSignature language)).src (Γ, sort) operator direction = (Γ, element) := by
    rw [polynomial_direction, uniform]
    rfl
  simpa [atElement] using toPattern_cast sourceEq (children direction)

theorem segment_pattern_perm {Γ : List String} {sort element : String}
    (operator : (indexedSignature language).Op sort) (start length : Nat)
    (fitLength : start + length ≤ ((indexedSignature language).arity operator).length)
    (uniform : ∀ index : Fin length,
      ((indexedSignature language).arity operator).get ⟨start + index.val, by omega⟩ =
        ([], element))
    (left right : Child language Γ sort operator)
    (permuted : List.Perm
      (List.ofFn fun index : Fin length =>
        segmentChild operator start index (by omega) (uniform index) left)
      (List.ofFn fun index : Fin length =>
        segmentChild operator start index (by omega) (uniform index) right)) :
    List.Perm
      (List.ofFn fun index : Fin length =>
        nthPrinted (fun direction => toPattern (left direction)) (start + index.val))
      (List.ofFn fun index : Fin length =>
        nthPrinted (fun direction => toPattern (right direction)) (start + index.val)) := by
  have mapped :=
    List.Perm.map (fun tree => toPattern tree) permuted
  have printedLeft :
      List.ofFn (fun index : Fin length =>
          nthPrinted (fun direction => toPattern (left direction)) (start + index.val)) =
        List.map toPattern
          (List.ofFn fun index : Fin length =>
            segmentChild operator start index (by omega) (uniform index) left) := by
    rw [← List.ofFn_comp']
    refine ofFn_pointwise ?_
    intro index
    rw [toPattern_segmentChild, nthPrinted_of_lt]
  have printedRight :
      List.ofFn (fun index : Fin length =>
          nthPrinted (fun direction => toPattern (right direction)) (start + index.val)) =
        List.map toPattern
          (List.ofFn fun index : Fin length =>
            segmentChild operator start index (by omega) (uniform index) right) := by
    rw [← List.ofFn_comp']
    refine ofFn_pointwise ?_
    intro index
    rw [toPattern_segmentChild, nthPrinted_of_lt]
  exact printedLeft.symm ▸ printedRight.symm ▸ mapped

theorem ofFn_split_at {α : Type} {n : Nat} (values : Fin n → α) (cut : Nat) (bound : cut ≤ n)
    (leftBound : ∀ index : Fin cut, index.val < n)
    (rightBound : ∀ index : Fin (n - cut), cut + index.val < n) :
    List.ofFn values =
      List.ofFn (fun index : Fin cut => values ⟨index.val, leftBound index⟩) ++
        List.ofFn (fun index : Fin (n - cut) => values ⟨cut + index.val, rightBound index⟩) := by
  have sum : cut + (n - cut) = n := Nat.add_sub_of_le bound
  have recast :
      List.ofFn values =
        List.ofFn (fun index : Fin (cut + (n - cut)) => values (Fin.cast sum index)) := by
    have congru :=
      List.ofFn_congr sum (fun index : Fin (cut + (n - cut)) => values (Fin.cast sum index))
    have collapsed :
        (List.ofFn fun index : Fin n =>
            values (Fin.cast sum (Fin.cast sum.symm index))) =
          List.ofFn values := by
      refine ofFn_pointwise ?_
      intro index
      congr 1
    exact collapsed.symm.trans congru.symm
  rw [recast, List.ofFn_add]
  refine congrArg₂ HAppend.hAppend ?_ ?_
  · refine ofFn_pointwise ?_
    intro index
    congr 1
  · refine ofFn_pointwise ?_
    intro index
    congr 1

theorem shiftSlot_lt {n cut : Nat} (index : Fin (n - 1)) (room : cut + 1 < n) :
    (if index.val < cut then index.val else index.val + 1) < n := by
  by_cases lower : index.val < cut
  · rw [if_pos lower]
    have indexBound := index.isLt
    omega
  · rw [if_neg lower]
    have indexBound := index.isLt
    omega

theorem hashSet_drop_cong {n : Nat} (source : Fin n → Pattern) (target : Fin (n - 1) → Pattern)
    (cut : Nat) (room : cut + 1 < n)
    (duplicate : source ⟨cut, by omega⟩ = source ⟨cut + 1, room⟩)
    (shifted : ∀ index : Fin (n - 1),
      target index =
        source ⟨if index.val < cut then index.val else index.val + 1, shiftSlot_lt index room⟩) :
    PatternCong (.collection .hashSet (List.ofFn source) none)
      (.collection .hashSet (List.ofFn target) none) := by
  have cutLt : cut < n := by omega
  have beforeBound (index : Fin cut) : index.val < n := by
    have indexBound := index.isLt
    omega
  have afterBound (index : Fin (n - cut - 2)) : cut + (2 + index.val) < n := by
    have indexBound := index.isLt
    omega
  have tailBound (index : Fin (n - cut)) : cut + index.val < n := by
    have indexBound := index.isLt
    omega
  have targetTailBound (index : Fin (n - 1 - cut)) : cut + index.val < n - 1 := by
    have indexBound := index.isLt
    omega
  set before := List.ofFn fun index : Fin cut => source ⟨index.val, beforeBound index⟩
  set element := source ⟨cut, cutLt⟩
  set element' := source ⟨cut + 1, room⟩
  set after :=
    List.ofFn fun index : Fin (n - cut - 2) => source ⟨cut + (2 + index.val), afterBound index⟩
  have sourceSplit : List.ofFn source = before ++ element :: element' :: after := by
    have outer :=
      ofFn_split_at source cut (Nat.le_of_lt cutLt) beforeBound tailBound
    have twoLt (index : Fin 2) : index.val < n - cut := by
      have indexBound := index.isLt
      omega
    have restLt (index : Fin (n - cut - 2)) : 2 + index.val < n - cut := by
      have indexBound := index.isLt
      omega
    have tail :=
      ofFn_split_at (fun index : Fin (n - cut) => source ⟨cut + index.val, tailBound index⟩) 2
        (by omega) twoLt restLt
    rw [outer, tail]
    refine congrArg₂ HAppend.hAppend rfl ?_
    have appended : element :: element' :: after = [element, element'] ++ after := rfl
    rw [appended]
    refine congrArg₂ HAppend.hAppend ?_ ?_
    · rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
      apply congrArg₂ (fun left right => left :: right :: [])
      · apply congrArg source
        apply Fin.ext
        rfl
      · apply congrArg source
        apply Fin.ext
        rfl
    · refine ofFn_pointwise ?_
      intro index
      apply congrArg source
      apply Fin.ext
      rfl
  have duplicateElements : element = element' := by
    have leftEq : (⟨cut, cutLt⟩ : Fin n) = ⟨cut, by omega⟩ := Fin.ext rfl
    simpa [element, element', leftEq] using duplicate
  have targetSplit : List.ofFn target = before ++ element :: after := by
    have cutLe : cut ≤ n - 1 := by omega
    have headBound (index : Fin cut) : index.val < n - 1 := by
      have indexBound := index.isLt
      omega
    have outer := ofFn_split_at target cut cutLe headBound targetTailBound
    have oneLt (index : Fin 1) : index.val < n - 1 - cut := by
      have indexBound := index.isLt
      omega
    have restLt (index : Fin (n - 1 - cut - 1)) : 1 + index.val < n - 1 - cut := by
      have indexBound := index.isLt
      omega
    have tail :=
      ofFn_split_at (fun index : Fin (n - 1 - cut) =>
          target ⟨cut + index.val, targetTailBound index⟩) 1 (by omega) oneLt restLt
    rw [outer, tail]
    refine congrArg₂ HAppend.hAppend ?_ ?_
    · refine ofFn_pointwise ?_
      intro index
      rw [shifted]
      apply congrArg source
      apply Fin.ext
      show
        (if (⟨index.val, headBound index⟩ : Fin (n - 1)).val < cut then
            (⟨index.val, headBound index⟩ : Fin (n - 1)).val
          else (⟨index.val, headBound index⟩ : Fin (n - 1)).val + 1) = index.val
      rw [if_pos (by
        show (⟨index.val, headBound index⟩ : Fin (n - 1)).val < cut
        exact index.isLt)]
    · have appended : element :: after = [element] ++ after := rfl
      rw [appended]
      refine congrArg₂ HAppend.hAppend ?_ ?_
      · rw [duplicateElements]
        rw [List.ofFn_succ, List.ofFn_zero]
        apply congrArg (fun pattern => pattern :: [])
        rw [shifted]
        apply congrArg source
        apply Fin.ext
        simp only [Fin.val_zero]
        rw [if_neg (by omega : ¬ cut + 0 < cut)]
      · have lengthEq : n - 1 - cut - 1 = n - cut - 2 := by omega
        rw [List.ofFn_congr lengthEq]
        refine ofFn_pointwise ?_
        intro index
        rw [shifted]
        apply congrArg source
        apply Fin.ext
        show
          (if cut + (1 + (Fin.cast lengthEq.symm index).val) < cut then
              cut + (1 + (Fin.cast lengthEq.symm index).val)
            else cut + (1 + (Fin.cast lengthEq.symm index).val) + 1) =
            cut + (2 + index.val)
        simp only [Fin.val_cast]
        rw [if_neg (by omega : ¬ cut + (1 + index.val) < cut)]
        omega
  rw [sourceSplit, targetSplit, duplicateElements]
  exact PatternCong.setDup

theorem assemble_focus {total : Nat} (printed : Fin total → Pattern) (offset : Nat)
    (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (parameterIndex : Nat) (parameterBound : parameterIndex < parameters.length)
    {kind : CollType} {element : String}
    (shape :
      baseCollection? (parameters.get ⟨parameterIndex, parameterBound⟩) = some (kind, element))
    {segmentLength : Nat}
    (lengthAt : segmentLength = lengths.getD parameterIndex 0) :
    assemblePrinted printed offset parameters counts lengths =
      assemblePrinted printed offset (parameters.take parameterIndex)
          (counts.take parameterIndex) (lengths.take parameterIndex) ++
        .collection kind
            (List.ofFn fun index : Fin segmentLength =>
              nthPrinted printed
                (offset +
                    slotCount (parameters.take parameterIndex) (counts.take parameterIndex)
                      (lengths.take parameterIndex) +
                  index.val))
          none ::
          assemblePrinted printed
            (offset +
                slotCount (parameters.take parameterIndex) (counts.take parameterIndex)
                  (lengths.take parameterIndex) +
              segmentLength)
            (parameters.drop (parameterIndex + 1)) (counts.drop (parameterIndex + 1))
            (lengths.drop (parameterIndex + 1)) := by
  induction parameters generalizing counts lengths offset parameterIndex with
  | nil => simp at parameterBound
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
              cases parameterIndex with
              | zero =>
                  have headShape : baseCollection? parameter = some (kind, element) := by
                    simpa [List.getElem_cons_zero] using shape
                  have lengthEq : segmentLength = length := by
                    simpa [List.getD_cons_zero] using lengthAt
                  subst lengthEq
                  simp only [assemblePrinted, headShape, List.take_zero, List.nil_append, slotCount,
                    Nat.zero_add, Nat.add_zero, List.drop_succ_cons, List.drop_zero]
              | succ parameterIndex =>
                  have tailBound : parameterIndex < parameters.length := by
                    simp only [List.length_cons] at parameterBound
                    exact Nat.lt_of_succ_lt_succ parameterBound
                  have tailShape :
                      baseCollection? (parameters.get ⟨parameterIndex, tailBound⟩) =
                        some (kind, element) := by
                    simpa [List.getElem_cons_succ] using shape
                  have tailLengthAt : segmentLength = lengths.getD parameterIndex 0 := by
                    simpa [List.getD_cons_succ] using lengthAt
                  cases reading : baseCollection? parameter with
                  | some packed =>
                      simp only [assemblePrinted, List.take_succ_cons, List.drop_succ_cons,
                        slotCount, directionsOf, reading]
                      have tail :=
                        inductionHypothesis (offset + length) counts lengths tailCounts tailLengths
                          parameterIndex tailBound tailShape tailLengthAt
                      rw [tail]
                      simp [List.cons_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  | none =>
                      simp only [assemblePrinted, List.take_succ_cons, List.drop_succ_cons,
                        slotCount, directionsOf, reading]
                      have tail :=
                        inductionHypothesis (offset + 1) counts lengths tailCounts tailLengths
                          parameterIndex tailBound tailShape tailLengthAt
                      rw [tail]
                      simp [List.cons_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem assemblePrinted_one {total : Nat} (left right : Fin total → Pattern)
    (changed : Fin total) (step : PatternCong (left changed) (right changed))
    (stable : ∀ direction, direction ≠ changed → left direction = right direction)
    (offset : Nat) (parameters : List TermParam) (counts lengths : List Nat)
    (fit : offset + slotCount parameters counts lengths ≤ total)
    (inside : offset ≤ changed.val ∧
      changed.val < offset + slotCount parameters counts lengths) :
    List.Forall₂ PatternCong (assemblePrinted left offset parameters counts lengths)
      (assemblePrinted right offset parameters counts lengths) := by
  induction parameters generalizing counts lengths offset with
  | nil =>
      simp [slotCount] at inside
      omega
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil =>
          simp [slotCount] at inside
          omega
      | cons count counts =>
          cases lengths with
          | nil =>
              simp [slotCount] at inside
              omega
          | cons length lengths =>
              cases reading : baseCollection? parameter with
              | some packed =>
                  obtain ⟨kind, element⟩ := packed
                  simp only [assemblePrinted, reading]
                  have width :
                      slotCount (parameter :: parameters) (count :: counts) (length :: lengths) =
                        length + slotCount parameters counts lengths := by
                    simp [slotCount, directionsOf, reading]
                  by_cases here : changed.val < offset + length
                  · refine List.Forall₂.cons ?_ ?_
                    · have localBound : changed.val - offset < length := by omega
                      exact collection_prefix_cong [] _ _
                        (ofFn_forall2_one
                          (fun index : Fin length => nthPrinted left (offset + index.val))
                          (fun index : Fin length => nthPrinted right (offset + index.val))
                          ⟨changed.val - offset, localBound⟩
                          (by
                            have sumEq : offset + (changed.val - offset) = changed.val := by omega
                            have sumLt : offset + (changed.val - offset) < total := by
                              rw [width] at fit
                              omega
                            rw [nthPrinted_of_lt (bound := sumLt), nthPrinted_of_lt (bound := sumLt)]
                            have finEq :
                                (⟨offset + (changed.val - offset), sumLt⟩ : Fin total) =
                                  changed := by
                              apply Fin.ext
                              exact sumEq
                            simpa [finEq] using step)
                          (by
                            intro index different
                            have indexLt : offset + index.val < total := by
                              have indexBound := index.isLt
                              rw [width] at fit
                              omega
                            rw [nthPrinted_of_lt (bound := indexLt),
                              nthPrinted_of_lt (bound := indexLt)]
                            exact stable ⟨offset + index.val, indexLt⟩ (by
                              intro same
                              apply different
                              apply Fin.ext
                              have valueEq : offset + index.val = changed.val :=
                                congrArg Fin.val same
                              show index.val = changed.val - offset
                              omega)))
                    · have tailEq :=
                        assemblePrinted_congr left right (offset + length) parameters counts lengths
                          fun index lower upper => by
                            have indexNe : index ≠ changed.val := by omega
                            have indexLt : index < total := by
                              rw [width] at fit
                              omega
                            rw [nthPrinted_of_lt (bound := indexLt),
                              nthPrinted_of_lt (bound := indexLt)]
                            exact stable ⟨index, indexLt⟩ (by
                              intro same
                              exact indexNe (congrArg Fin.val same))
                      exact forall2_pattern_of_eq tailEq
                  · refine List.Forall₂.cons ?_ ?_
                    · have elementsEq :
                          List.ofFn (fun index : Fin length => nthPrinted left (offset + index.val)) =
                            List.ofFn (fun index : Fin length =>
                              nthPrinted right (offset + index.val)) := by
                        refine ofFn_pointwise ?_
                        intro index
                        have indexLt : offset + index.val < total := by
                          have indexBound := index.isLt
                          rw [width] at fit
                          omega
                        rw [nthPrinted_of_lt (bound := indexLt), nthPrinted_of_lt (bound := indexLt)]
                        exact stable ⟨offset + index.val, indexLt⟩ (by
                          intro same
                          have valueEq : offset + index.val = changed.val :=
                            congrArg Fin.val same
                          have indexBound := index.isLt
                          omega)
                      rw [elementsEq]
                      exact PatternCong.refl _
                    · exact inductionHypothesis (offset + length) counts lengths (by
                        rw [width] at fit
                        omega) (by
                        rw [width] at inside
                        omega)
              | none =>
                  simp only [assemblePrinted, reading]
                  have width :
                      slotCount (parameter :: parameters) (count :: counts) (length :: lengths) =
                        1 + slotCount parameters counts lengths := by
                    simp [slotCount, directionsOf, reading]
                  by_cases here : changed.val = offset
                  · refine List.Forall₂.cons ?_ ?_
                    · apply printArgument_cong
                      have offsetLt : offset < total := by
                        rw [width] at fit
                        omega
                      rw [nthPrinted_of_lt (bound := offsetLt), nthPrinted_of_lt (bound := offsetLt)]
                      have finEq : (⟨offset, offsetLt⟩ : Fin total) = changed := by
                        apply Fin.ext
                        exact here.symm
                      simpa [finEq] using step
                    · have tailEq :=
                        assemblePrinted_congr left right (offset + 1) parameters counts lengths
                          fun index lower upper => by
                            have indexNe : index ≠ changed.val := by omega
                            have indexLt : index < total := by
                              rw [width] at fit
                              omega
                            rw [nthPrinted_of_lt (bound := indexLt),
                              nthPrinted_of_lt (bound := indexLt)]
                            exact stable ⟨index, indexLt⟩ (by
                              intro same
                              exact indexNe (congrArg Fin.val same))
                      exact forall2_pattern_of_eq tailEq
                  · refine List.Forall₂.cons ?_ ?_
                    · have headEq : nthPrinted left offset = nthPrinted right offset := by
                        have offsetLt : offset < total := by
                          rw [width] at fit inside
                          omega
                        rw [nthPrinted_of_lt (bound := offsetLt), nthPrinted_of_lt (bound := offsetLt)]
                        exact stable ⟨offset, offsetLt⟩ (by
                          intro same
                          have valueEq : changed.val = offset := (congrArg Fin.val same).symm
                          exact here valueEq)
                      rw [headEq]
                      exact PatternCong.refl _
                    · exact inductionHypothesis (offset + 1) counts lengths (by
                        rw [width] at fit
                        omega) (by
                        rw [width] at inside
                        constructor
                        · omega
                        · omega)

theorem assemblePrinted_align {total total' : Nat}
    (printed : Fin total → Pattern) (printed' : Fin total' → Pattern)
    (offset offset' : Nat) (parameters : List TermParam) (counts lengths : List Nat)
    (agree : ∀ index : Nat, index < slotCount parameters counts lengths →
      nthPrinted printed (offset + index) = nthPrinted printed' (offset' + index)) :
    assemblePrinted printed offset parameters counts lengths =
      assemblePrinted printed' offset' parameters counts lengths := by
  induction parameters generalizing counts lengths offset offset' with
  | nil => simp [assemblePrinted]
  | cons parameter parameters inductionHypothesis =>
      cases counts with
      | nil => simp [assemblePrinted]
      | cons count counts =>
          cases lengths with
          | nil => simp [assemblePrinted]
          | cons length lengths =>
              cases reading : baseCollection? parameter with
              | some _packed =>
                  simp only [assemblePrinted, reading]
                  have width :
                      slotCount (parameter :: parameters) (count :: counts) (length :: lengths) =
                        length + slotCount parameters counts lengths := by
                    simp [slotCount, directionsOf, reading]
                  have childrenEq :
                      List.ofFn (fun index : Fin length => nthPrinted printed (offset + index.val)) =
                        List.ofFn (fun index : Fin length =>
                          nthPrinted printed' (offset' + index.val)) :=
                    ofFn_pointwise fun index => agree index.val (by
                      have indexBound := index.isLt
                      simp [width] at indexBound ⊢
                      omega)
                  have tailEq :=
                    inductionHypothesis (offset + length) (offset' + length) counts lengths
                      fun index bound => by
                        simpa [Nat.add_assoc] using
                          agree (length + index) (by
                            simp [width] at bound ⊢
                            omega)
                  simp [childrenEq, tailEq]
              | none =>
                  simp only [assemblePrinted, reading]
                  have width :
                      slotCount (parameter :: parameters) (count :: counts) (length :: lengths) =
                        1 + slotCount parameters counts lengths := by
                    simp [slotCount, directionsOf, reading]
                  have headEq : nthPrinted printed offset = nthPrinted printed' offset' :=
                    agree 0 (by simp [width])
                  have tailEq :=
                    inductionHypothesis (offset + 1) (offset' + 1) counts lengths fun index bound => by
                      simpa [Nat.add_assoc] using
                        agree (1 + index) (by
                          simp [width] at bound ⊢
                          omega)
                  simp [headEq, tailEq]

theorem slotCount_focus (parameters : List TermParam) (counts lengths : List Nat)
    (countsLength : counts.length = parameters.length)
    (lengthsLength : lengths.length = parameters.length)
    (parameterIndex : Nat) (parameterBound : parameterIndex < parameters.length)
    (collection : (baseCollection? (parameters.get ⟨parameterIndex, parameterBound⟩)).isSome) :
    slotCount parameters counts lengths =
      slotCount (parameters.take parameterIndex) (counts.take parameterIndex)
          (lengths.take parameterIndex) +
        lengths.getD parameterIndex 0 +
        slotCount (parameters.drop (parameterIndex + 1)) (counts.drop (parameterIndex + 1))
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
                  have headSome : (baseCollection? parameter).isSome := by
                    simpa [List.getElem_cons_zero] using collection
                  cases reading : baseCollection? parameter with
                  | none => simp [reading] at headSome
                  | some _packed =>
                      simp [slotCount, directionsOf, reading, List.take_zero, List.drop_succ_cons,
                        List.drop_zero]
              | succ parameterIndex =>
                  have tailBound : parameterIndex < parameters.length := by
                    simp at parameterBound
                    omega
                  have tailCollection :
                      (baseCollection? (parameters.get ⟨parameterIndex, tailBound⟩)).isSome := by
                    simpa [List.getElem_cons_succ] using collection
                  have tail :=
                    inductionHypothesis counts lengths tailCounts tailLengths parameterIndex
                      tailBound tailCollection
                  cases reading : baseCollection? parameter with
                  | some _packed =>
                      simp only [slotCount, directionsOf, reading, List.take_succ_cons,
                        List.drop_succ_cons, List.getD_cons_succ] at tail ⊢
                      omega
                  | none =>
                      simp only [slotCount, directionsOf, reading, List.take_succ_cons,
                        List.drop_succ_cons, List.getD_cons_succ] at tail ⊢
                      omega

theorem collectionShape_isSome {parameter : TermParam} {kind : CollType} {element : String}
    (shape : baseCollection? parameter = some (kind, element)) :
    (baseCollection? parameter).isSome = true := by
  rw [shape]
  rfl

theorem singleton_get_zero {α : Type} (value : α) (bound : 0 < [value].length) :
    [value].get ⟨0, bound⟩ = value := by
  have indexZero : (⟨0, bound⟩ : Fin [value].length) = (0 : Fin [value].length) := by
    apply Fin.ext
    rfl
  rw [indexZero]
  exact List.get_cons_zero

theorem setDeletion_pattern {Γ : List String} {sort element : String}
    {source target : (indexedSignature language).Op sort}
    (sourceChildren : Child language Γ sort source)
    (targetChildren : Child language Γ sort target)
    {removed : Fin ((indexedSignature language).arity source).length}
    {parameterIndex segmentStart : Nat}
    (deletion : SetDeletion language Γ sort element source target sourceChildren targetChildren
      removed parameterIndex segmentStart) :
    PatternCong
      (toPattern
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort)) source
          sourceChildren))
      (toPattern
        (IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort)) target
          targetChildren)) := by
  rw [toPattern_liftBind, toPattern_liftBind]
  cases reading : bareCollection? source.1.1 with
  | some packed =>
      obtain ⟨kindBare, _elementBare⟩ := packed
      have targetReading : bareCollection? target.1.1 = some (kindBare, _elementBare) := by
        simpa [deletion.sameRule] using reading
      obtain ⟨_name, paramsEq⟩ := bare_rule_params reading
      have parameterZero : parameterIndex = 0 := by
        have bound := deletion.parameterBound
        simp only [paramsEq, List.length_singleton] at bound
        omega
      subst parameterZero
      have startZero : segmentStart = 0 := by
        simpa [paramsEq, List.take_zero, slotCount] using deletion.segmentIsPrefix
      subst startZero
      obtain ⟨_countsOne, lengthsOne⟩ := bare_head source reading
      have sourceLen :
          ((indexedSignature language).arity source).length = source.2.lengths.getD 0 0 := by
        rw [lengthsOne, List.getD_cons_zero]
      have room : removed.val + 1 < ((indexedSignature language).arity source).length := by
        have inside := deletion.inSegment
        omega
      have kindSet : kindBare = .hashSet := by
        have shapeHead := deletion.parameterShape
        rw [List.get_of_eq paramsEq] at shapeHead
        have headEq :=
          singleton_get_zero (TermParam.simple _name (.collection kindBare (.base _elementBare)))
            (paramsEq ▸ deletion.parameterBound)
        simp only [headEq, baseCollection?, Option.some.injEq, Prod.mk.injEq] at shapeHead
        exact shapeHead.1
      subst kindSet
      simp only [nodeOf, reading, targetReading]
      have targetLen :
          ((indexedSignature language).arity target).length =
            ((indexedSignature language).arity source).length - 1 := by
        have drop := deletion.lengthDrop
        omega
      have duplicatePattern :
          toPattern (sourceChildren removed) =
            toPattern (sourceChildren ⟨removed.val + 1, deletion.successor⟩) := by
        have leftPrinted :=
          toPattern_atElement source removed deletion.removedDecl sourceChildren
        have rightPrinted :=
          toPattern_atElement source ⟨removed.val + 1, deletion.successor⟩ deletion.nextDecl
            sourceChildren
        have same := congrArg toPattern deletion.duplicate
        rw [leftPrinted, rightPrinted] at same
        exact same
      rw [List.ofFn_congr targetLen (fun direction => toPattern (targetChildren direction))]
      exact hashSet_drop_cong (fun direction => toPattern (sourceChildren direction))
        (fun index => toPattern (targetChildren (Fin.cast targetLen.symm index))) removed.val room
        duplicatePattern
        (by
          intro index
          obtain ⟨equal, keptEq⟩ := deletion.kept (Fin.cast targetLen.symm index)
          have printed := toPattern_cast equal (targetChildren (Fin.cast targetLen.symm index))
          rw [keptEq] at printed
          have dropEq :
              dropDirection removed.val removed.isLt (Fin.cast targetLen.symm index).val
                  (by
                    have indexBound := (Fin.cast targetLen.symm index).isLt
                    have lengthEq := deletion.lengthDrop
                    omega) =
                (⟨if index.val < removed.val then index.val else index.val + 1,
                    shiftSlot_lt index room⟩ :
                  Fin ((indexedSignature language).arity source).length) := by
            simp only [dropDirection, Fin.val_cast]
            split <;> apply Fin.ext <;> simp
          rw [dropEq] at printed
          exact printed.symm)
  | none =>
      have targetReading : bareCollection? target.1.1 = none := by
        simpa [deletion.sameRule] using reading
      simp only [nodeOf, reading, targetReading]
      let sourceGet := source.2.lengths.getD parameterIndex 0
      have sourcePositive : parameterIndex < source.2.lengths.length := by
        simpa [source.2.lengths_length] using deletion.parameterBound
      have targetGet :
          target.2.lengths.getD parameterIndex 0 = sourceGet - 1 := by
        rw [deletion.lengthsDrop, List.getD_eq_getElem?_getD, List.getElem?_set]
        simp [sourcePositive, sourceGet, List.getD_eq_getElem?_getD]
      have prefixLengths :
          target.2.lengths.take parameterIndex = source.2.lengths.take parameterIndex := by
        rw [deletion.lengthsDrop, List.take_set]
        refine List.set_eq_of_length_le ?_
        simp [List.length_take]
      have suffixLengths :
          target.2.lengths.drop (parameterIndex + 1) =
            source.2.lengths.drop (parameterIndex + 1) := by
        rw [deletion.lengthsDrop, List.drop_set]
        simp
      have sourceSplit :=
        slotCount_focus source.1.1.params source.2.counts source.2.lengths source.2.counts_length
          source.2.lengths_length parameterIndex deletion.parameterBound
          (collectionShape_isSome deletion.parameterShape)
      have sourceArity :
          ((indexedSignature language).arity source).length =
            slotCount source.1.1.params source.2.counts source.2.lengths := by
        simp [indexedSignature, expandSlots_length]
      have localDef : removed.val = segmentStart + (removed.val - segmentStart) := by
        have lower := deletion.inSegment.1
        omega
      have room : removed.val - segmentStart + 1 < sourceGet := by
        have upper := deletion.inSegment.2
        omega
      have focusSource :=
        assemble_focus (fun direction => toPattern (sourceChildren direction)) 0
          source.1.1.params source.2.counts source.2.lengths source.2.counts_length
          source.2.lengths_length parameterIndex deletion.parameterBound deletion.parameterShape rfl
      have targetParameterBound : parameterIndex < target.1.1.params.length := by
        simpa [deletion.sameRule] using deletion.parameterBound
      have focusTarget :=
        assemble_focus (fun direction => toPattern (targetChildren direction)) 0
          target.1.1.params target.2.counts target.2.lengths target.2.counts_length
          target.2.lengths_length parameterIndex targetParameterBound
          (by simpa [deletion.sameRule] using deletion.parameterShape) targetGet.symm
      have childShift (index : Fin ((indexedSignature language).arity target).length) :
          toPattern (targetChildren index) =
            toPattern (sourceChildren
              (dropDirection removed.val removed.isLt index.val
                (by
                  have indexBound := index.isLt
                  have lengthEq := deletion.lengthDrop
                  omega))) := by
        obtain ⟨equal, keptEq⟩ := deletion.kept index
        have printed := toPattern_cast equal (targetChildren index)
        rw [keptEq] at printed
        exact printed.symm
      have prefixEq :=
        assemblePrinted_align (fun direction => toPattern (targetChildren direction))
          (fun direction => toPattern (sourceChildren direction)) 0 0
          (source.1.1.params.take parameterIndex) (source.2.counts.take parameterIndex)
          (source.2.lengths.take parameterIndex)
          fun index bound => by
            have indexStart : index < segmentStart := by
              simpa [deletion.segmentIsPrefix] using bound
            have indexRemoved : index < removed.val := by
              have lower := deletion.inSegment.1
              omega
            have targetBound : index < ((indexedSignature language).arity target).length := by
              have lengthEq := deletion.lengthDrop
              omega
            have sourceBound : index < ((indexedSignature language).arity source).length := by
              have lengthEq := deletion.lengthDrop
              omega
            simp only [Nat.zero_add]
            rw [nthPrinted_of_lt (bound := targetBound), nthPrinted_of_lt (bound := sourceBound)]
            have shifted := childShift ⟨index, targetBound⟩
            simp only [dropDirection] at shifted
            rw [if_pos indexRemoved] at shifted
            apply Eq.trans shifted
            apply congrArg (fun direction => toPattern (sourceChildren direction))
            apply Fin.ext
            rfl
      have suffixEq :=
        assemblePrinted_align
          (fun direction => toPattern (targetChildren direction))
          (fun direction => toPattern (sourceChildren direction))
          (segmentStart + (sourceGet - 1)) (segmentStart + sourceGet)
          (source.1.1.params.drop (parameterIndex + 1))
          (source.2.counts.drop (parameterIndex + 1))
          (source.2.lengths.drop (parameterIndex + 1))
          fun index _bound => by
            have targetAt :
                segmentStart + (sourceGet - 1) + index <
                  ((indexedSignature language).arity target).length := by
              have split := sourceSplit
              have arityEq := sourceArity
              have lengthEq := deletion.lengthDrop
              have prefixNat := deletion.segmentIsPrefix
              have upper := deletion.inSegment.2
              omega
            have sourceAtBound :
                segmentStart + sourceGet + index <
                  ((indexedSignature language).arity source).length := by
              have split := sourceSplit
              have arityEq := sourceArity
              have prefixNat := deletion.segmentIsPrefix
              omega
            rw [nthPrinted_of_lt (bound := targetAt), nthPrinted_of_lt (bound := sourceAtBound)]
            have shifted := childShift ⟨segmentStart + (sourceGet - 1) + index, targetAt⟩
            have past : ¬ segmentStart + (sourceGet - 1) + index < removed.val := by
              have upper := deletion.inSegment.2
              have lower := deletion.inSegment.1
              omega
            simp only [dropDirection] at shifted
            rw [if_neg past] at shifted
            apply Eq.trans shifted
            apply congrArg (fun direction => toPattern (sourceChildren direction))
            apply Fin.ext
            show segmentStart + (sourceGet - 1) + index + 1 = segmentStart + sourceGet + index
            omega
      rw [focusSource, focusTarget]
      have startBase :
          0 + slotCount (source.1.1.params.take parameterIndex)
              (source.2.counts.take parameterIndex) (source.2.lengths.take parameterIndex) =
            segmentStart := by
        simpa [Nat.zero_add] using deletion.segmentIsPrefix.symm
      have targetStartBase :
          0 + slotCount (target.1.1.params.take parameterIndex)
              (target.2.counts.take parameterIndex) (target.2.lengths.take parameterIndex) =
            segmentStart := by
        simpa [deletion.sameRule, deletion.sameCounts, prefixLengths, Nat.zero_add] using
          deletion.segmentIsPrefix.symm
      rw [startBase, targetStartBase]
      simp only [← deletion.sameRule, ← deletion.sameCounts, prefixLengths, suffixLengths]
      rw [prefixEq, suffixEq]
      have duplicatePattern :
          toPattern (sourceChildren removed) =
            toPattern (sourceChildren ⟨removed.val + 1, deletion.successor⟩) := by
        have leftPrinted :=
          toPattern_atElement source removed deletion.removedDecl sourceChildren
        have rightPrinted :=
          toPattern_atElement source ⟨removed.val + 1, deletion.successor⟩ deletion.nextDecl
            sourceChildren
        have same := congrArg toPattern deletion.duplicate
        rw [leftPrinted, rightPrinted] at same
        exact same
      have collectionCong :=
        hashSet_drop_cong
          (fun index : Fin sourceGet =>
            nthPrinted (fun direction => toPattern (sourceChildren direction))
              (segmentStart + index.val))
          (fun index : Fin (sourceGet - 1) =>
            nthPrinted (fun direction => toPattern (targetChildren direction))
              (segmentStart + index.val))
          (removed.val - segmentStart) room
          (by
            have leftBound :
                segmentStart + (removed.val - segmentStart) <
                  ((indexedSignature language).arity source).length := by
              rw [← localDef]
              exact removed.isLt
            have rightBound :
                segmentStart + (removed.val - segmentStart + 1) <
                  ((indexedSignature language).arity source).length := by
              have sumEq :
                  segmentStart + (removed.val - segmentStart + 1) = removed.val + 1 := by
                omega
              rw [sumEq]
              exact deletion.successor
            rw [nthPrinted_of_lt (bound := leftBound), nthPrinted_of_lt (bound := rightBound)]
            have leftFin :
                (⟨segmentStart + (removed.val - segmentStart), leftBound⟩ :
                  Fin ((indexedSignature language).arity source).length) = removed := by
              apply Fin.ext
              exact localDef.symm
            have rightFin :
                (⟨segmentStart + (removed.val - segmentStart + 1), rightBound⟩ :
                  Fin ((indexedSignature language).arity source).length) =
                  ⟨removed.val + 1, deletion.successor⟩ := by
              apply Fin.ext
              show segmentStart + (removed.val - segmentStart + 1) = removed.val + 1
              omega
            rw [leftFin, rightFin]
            exact duplicatePattern)
          (by
            intro index
            by_cases lower : index.val < removed.val - segmentStart
            · simp only [if_pos lower]
              have pos : segmentStart + index.val < removed.val := by omega
              have targetBound :
                  segmentStart + index.val <
                    ((indexedSignature language).arity target).length := by
                have indexBound := index.isLt
                have lengthEq := deletion.lengthDrop
                have split := sourceSplit
                have arityEq := sourceArity
                have prefixNat := deletion.segmentIsPrefix
                omega
              have sourceBound :
                  segmentStart + index.val <
                    ((indexedSignature language).arity source).length := by
                have sumLt : segmentStart + index.val < removed.val := by omega
                exact Nat.lt_trans sumLt removed.isLt
              rw [nthPrinted_of_lt (bound := targetBound), nthPrinted_of_lt (bound := sourceBound)]
              have shifted := childShift ⟨segmentStart + index.val, targetBound⟩
              simp only [dropDirection] at shifted
              rw [if_pos pos] at shifted
              apply Eq.trans shifted
              apply congrArg (fun direction => toPattern (sourceChildren direction))
              apply Fin.ext
              rfl
            · simp only [if_neg lower]
              have neg : ¬ segmentStart + index.val < removed.val := by omega
              have targetBound :
                  segmentStart + index.val <
                    ((indexedSignature language).arity target).length := by
                have indexBound := index.isLt
                have lengthEq := deletion.lengthDrop
                have split := sourceSplit
                have arityEq := sourceArity
                have prefixNat := deletion.segmentIsPrefix
                omega
              have sourceBound :
                  segmentStart + (index.val + 1) <
                    ((indexedSignature language).arity source).length := by
                have indexBound := index.isLt
                have split := sourceSplit
                have arityEq := sourceArity
                have prefixNat := deletion.segmentIsPrefix
                omega
              rw [nthPrinted_of_lt (bound := targetBound), nthPrinted_of_lt (bound := sourceBound)]
              have shifted := childShift ⟨segmentStart + index.val, targetBound⟩
              simp only [dropDirection] at shifted
              rw [if_neg neg] at shifted
              apply Eq.trans shifted
              apply congrArg (fun direction => toPattern (sourceChildren direction))
              apply Fin.ext
              show segmentStart + index.val + 1 = segmentStart + (index.val + 1)
              omega)
      exact PatternCong.applyAt (before :=
        assemblePrinted (fun direction => toPattern (sourceChildren direction)) 0
          (source.1.1.params.take parameterIndex) (source.2.counts.take parameterIndex)
          (source.2.lengths.take parameterIndex)) collectionCong

/-- Printing sends the indexed tree congruence to the pattern congruence. -/
theorem treeCong_pattern {index : List String × String} {left right : Tree language index}
    (related : TreeCong language left right) :
    PatternCong (toPattern left) (toPattern right) := by
  induction related with
  | refl _ => exact PatternCong.refl _
  | symm _ inductionHypothesis => exact PatternCong.symm inductionHypothesis
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact PatternCong.trans inductionHypothesis inductionHypothesis'
  | congr operator leftChildren rightChildren changed _ stable inductionHypothesis =>
      rw [toPattern_liftBind, toPattern_liftBind]
      cases reading : bareCollection? operator.1.1 with
      | some packed =>
          simp only [nodeOf, reading]
          simpa using
            collection_prefix_cong [] _ _
              (ofFn_forall2_one (fun direction => toPattern (leftChildren direction))
                (fun direction => toPattern (rightChildren direction)) changed
                inductionHypothesis
                fun direction different =>
                  congrArg toPattern (stable direction different))
      | none =>
          simp only [nodeOf, reading]
          have fit :
              0 + slotCount operator.1.1.params operator.2.counts operator.2.lengths ≤
                ((indexedSignature language).arity operator).length := by
            rw [Nat.zero_add]
            simp [indexedSignature, expandSlots_length]
          have inside :
              0 ≤ changed.val ∧
                changed.val <
                  0 + slotCount operator.1.1.params operator.2.counts operator.2.lengths := by
            refine ⟨Nat.zero_le _, ?_⟩
            rw [Nat.zero_add]
            simpa [indexedSignature, expandSlots_length] using changed.isLt
          simpa using
            apply_prefix_cong [] _ _
              (assemblePrinted_one (fun direction => toPattern (leftChildren direction))
                (fun direction => toPattern (rightChildren direction)) changed
                inductionHypothesis
                (fun direction different =>
                  congrArg toPattern (stable direction different))
                0 operator.1.1.params operator.2.counts operator.2.lengths fit inside)
  | bagPerm operator start segmentWidth _fit kind bagOrSet parameterIndex parameterBound
      parameterShape segmentStart segmentLength uniform leftChildren rightChildren outside permuted =>
      rw [toPattern_liftBind, toPattern_liftBind]
      cases reading : bareCollection? operator.1.1 with
      | some packed =>
          obtain ⟨kindBare, elementBare⟩ := packed
          obtain ⟨_name, paramsEq⟩ := bare_rule_params reading
          have parameterZero : parameterIndex = 0 := by
            have bound := parameterBound
            simp only [paramsEq, List.length_singleton] at bound
            omega
          subst parameterZero
          have startZero : start = 0 := by
            simpa [paramsEq, List.take_zero, slotCount] using segmentStart
          subst startZero
          obtain ⟨_countsOne, lengthsOne⟩ := bare_head operator reading
          have widthFull :
              segmentWidth = ((indexedSignature language).arity operator).length := by
            rw [lengthsOne, List.getD_cons_zero] at segmentLength
            exact segmentLength
          subst widthFull
          have kindMatch : kindBare = kind := by
            have shapeHead := parameterShape
            rw [List.get_of_eq paramsEq] at shapeHead
            have headEq :=
              singleton_get_zero (TermParam.simple _name (.collection kindBare (.base elementBare)))
                (paramsEq ▸ parameterBound)
            simp only [headEq, baseCollection?, Option.some.injEq, Prod.mk.injEq] at shapeHead
            exact shapeHead.1
          subst kindMatch
          simp only [nodeOf, reading]
          have elementPerm :=
            segment_pattern_perm operator 0
              ((indexedSignature language).arity operator).length (by omega) uniform
              leftChildren rightChildren permuted
          have leftElements :
              List.ofFn (fun direction => toPattern (leftChildren direction)) =
                List.ofFn fun index : Fin ((indexedSignature language).arity operator).length =>
                  nthPrinted (fun direction => toPattern (leftChildren direction))
                    (0 + index.val) := by
            refine ofFn_pointwise ?_
            intro index
            rw [Nat.zero_add, nthPrinted_of_lt (bound := index.isLt)]
          have rightElements :
              List.ofFn (fun direction => toPattern (rightChildren direction)) =
                List.ofFn fun index : Fin ((indexedSignature language).arity operator).length =>
                  nthPrinted (fun direction => toPattern (rightChildren direction))
                    (0 + index.val) := by
            refine ofFn_pointwise ?_
            intro index
            rw [Nat.zero_add, nthPrinted_of_lt (bound := index.isLt)]
          rw [leftElements, rightElements]
          cases bagOrSet with
          | inl kindBag =>
              subst kindBag
              exact PatternCong.bagPerm elementPerm
          | inr kindSet =>
              subst kindSet
              exact PatternCong.setPerm elementPerm
      | none =>
          simp only [nodeOf, reading]
          have focusLeft :=
            assemble_focus (fun direction => toPattern (leftChildren direction)) 0
              operator.1.1.params operator.2.counts operator.2.lengths operator.2.counts_length
              operator.2.lengths_length parameterIndex parameterBound parameterShape
              segmentLength
          have focusRight :=
            assemble_focus (fun direction => toPattern (rightChildren direction)) 0
              operator.1.1.params operator.2.counts operator.2.lengths operator.2.counts_length
              operator.2.lengths_length parameterIndex parameterBound parameterShape
              segmentLength
          have prefixEq :=
            assemblePrinted_congr (fun direction => toPattern (leftChildren direction))
              (fun direction => toPattern (rightChildren direction)) 0
              (operator.1.1.params.take parameterIndex)
              (operator.2.counts.take parameterIndex) (operator.2.lengths.take parameterIndex)
              fun index _lower upper => by
                have indexStart : index < start := by
                  simpa [segmentStart, Nat.zero_add] using upper
                have inArity : index < ((indexedSignature language).arity operator).length := by
                  omega
                rw [nthPrinted_of_lt (bound := inArity), nthPrinted_of_lt (bound := inArity)]
                exact congrArg toPattern (outside ⟨index, inArity⟩ (Or.inl indexStart))
          have suffixStart :
              start + segmentWidth =
                0 +
                  slotCount (operator.1.1.params.take parameterIndex)
                    (operator.2.counts.take parameterIndex)
                    (operator.2.lengths.take parameterIndex) +
                segmentWidth := by
            simp [segmentStart]
          have suffixEq :=
            assemblePrinted_congr (fun direction => toPattern (leftChildren direction))
              (fun direction => toPattern (rightChildren direction)) (start + segmentWidth)
              (operator.1.1.params.drop (parameterIndex + 1))
              (operator.2.counts.drop (parameterIndex + 1))
              (operator.2.lengths.drop (parameterIndex + 1))
              fun index lower upper => by
                have indexAfter : start + segmentWidth ≤ index := lower
                have inArity : index < ((indexedSignature language).arity operator).length := by
                  have totalEq :
                      slotCount operator.1.1.params operator.2.counts operator.2.lengths =
                        ((indexedSignature language).arity operator).length := by
                    simp [indexedSignature, expandSlots_length]
                  have split :=
                    slotCount_focus operator.1.1.params operator.2.counts operator.2.lengths
                      operator.2.counts_length operator.2.lengths_length parameterIndex
                      parameterBound (collectionShape_isSome parameterShape)
                  omega
                rw [nthPrinted_of_lt (bound := inArity), nthPrinted_of_lt (bound := inArity)]
                exact congrArg toPattern (outside ⟨index, inArity⟩ (Or.inr indexAfter))
          have elementPerm :=
            segment_pattern_perm operator start segmentWidth (by omega) uniform leftChildren
              rightChildren permuted
          rw [focusLeft, focusRight]
          have startBase :
              (0 +
                  slotCount (operator.1.1.params.take parameterIndex)
                    (operator.2.counts.take parameterIndex)
                    (operator.2.lengths.take parameterIndex)) =
                start := by
            simp [segmentStart]
          rw [startBase]
          simp only [← prefixEq, suffixEq]
          cases bagOrSet with
          | inl kindBag =>
              subst kindBag
              exact PatternCong.applyAt (before :=
                assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
                  (operator.1.1.params.take parameterIndex)
                  (operator.2.counts.take parameterIndex)
                  (operator.2.lengths.take parameterIndex))
                (PatternCong.bagPerm elementPerm)
          | inr kindSet =>
              subst kindSet
              exact PatternCong.applyAt (before :=
                assemblePrinted (fun direction => toPattern (leftChildren direction)) 0
                  (operator.1.1.params.take parameterIndex)
                  (operator.2.counts.take parameterIndex)
                  (operator.2.lengths.take parameterIndex))
                (PatternCong.setPerm elementPerm)
  | setDup _source _target _sourceChildren _targetChildren _removed _parameterIndex
      _segmentStart deletion =>
      exact setDeletion_pattern _sourceChildren _targetChildren deletion

/-! ## Outer shape is a pattern invariant -/

/-- The de Bruijn index of a variable, and nothing else. -/
def bvarIndex? : Pattern → Option Nat
  | .bvar index => some index
  | _ => none

/-- The label of an application, and nothing else. -/
def applyLabel? : Pattern → Option String
  | .apply label _ => some label
  | _ => none

/-- Kind and tail of a collection, and nothing else. -/
def collectionHead? : Pattern → Option (CollType × Option String)
  | .collection kind _ rest => some (kind, rest)
  | _ => none

/-- Binder of a lambda, and nothing else. -/
def lambdaHead? : Pattern → Option (Option String)
  | .lambda binder _ => some binder
  | _ => none

/-- Arity and names of a multi-lambda, and nothing else. -/
def multiHead? : Pattern → Option (Nat × List String)
  | .multiLambda arity binders _ => some (arity, binders)
  | _ => none

theorem patternCong_bvarIndex {left right : Pattern} (related : PatternCong left right) :
    bvarIndex? left = bvarIndex? right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | bagPerm _ => rfl
  | setPerm _ => rfl
  | setDup => rfl
  | applyAt _ _ => rfl
  | lambdaAt _ _ => rfl
  | multiLambdaAt _ _ => rfl
  | collectionAt _ _ => rfl

theorem patternCong_applyLabel {left right : Pattern} (related : PatternCong left right) :
    applyLabel? left = applyLabel? right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | bagPerm _ => rfl
  | setPerm _ => rfl
  | setDup => rfl
  | applyAt _ _ => rfl
  | lambdaAt _ _ => rfl
  | multiLambdaAt _ _ => rfl
  | collectionAt _ _ => rfl

theorem patternCong_collectionHead {left right : Pattern} (related : PatternCong left right) :
    collectionHead? left = collectionHead? right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | bagPerm _ => rfl
  | setPerm _ => rfl
  | setDup => rfl
  | applyAt _ _ => rfl
  | lambdaAt _ _ => rfl
  | multiLambdaAt _ _ => rfl
  | collectionAt _ _ => rfl

theorem patternCong_lambdaHead {left right : Pattern} (related : PatternCong left right) :
    lambdaHead? left = lambdaHead? right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | bagPerm _ => rfl
  | setPerm _ => rfl
  | setDup => rfl
  | applyAt _ _ => rfl
  | lambdaAt _ _ => rfl
  | multiLambdaAt _ _ => rfl
  | collectionAt _ _ => rfl

theorem patternCong_multiHead {left right : Pattern} (related : PatternCong left right) :
    multiHead? left = multiHead? right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | bagPerm _ => rfl
  | setPerm _ => rfl
  | setDup => rfl
  | applyAt _ _ => rfl
  | lambdaAt _ _ => rfl
  | multiLambdaAt _ _ => rfl
  | collectionAt _ _ => rfl

theorem forall2_pattern_symm {left right : List Pattern}
    (pointwise : List.Forall₂ PatternCong left right) :
    List.Forall₂ PatternCong right left := by
  induction pointwise with
  | nil => exact List.Forall₂.nil
  | cons headRelated _ inductionHypothesis =>
      exact List.Forall₂.cons (PatternCong.symm headRelated) inductionHypothesis

theorem forall2_pattern_trans {left mid right : List Pattern}
    (first : List.Forall₂ PatternCong left mid) (second : List.Forall₂ PatternCong mid right) :
    List.Forall₂ PatternCong left right := by
  induction first generalizing right with
  | nil =>
      cases second
      exact List.Forall₂.nil
  | cons headRelated _ inductionHypothesis =>
      cases second with
      | cons headRelated' tailRelated' =>
          exact List.Forall₂.cons (PatternCong.trans headRelated headRelated')
            (inductionHypothesis tailRelated')

theorem forall2_pattern_replace {before after : List Pattern} {left right : Pattern}
    (step : PatternCong left right) :
    List.Forall₂ PatternCong (before ++ left :: after) (before ++ right :: after) := by
  induction before with
  | nil => exact List.Forall₂.cons step (forall2_pattern_of_eq rfl)
  | cons _ _ inductionHypothesis =>
      exact List.Forall₂.cons (PatternCong.refl _) inductionHypothesis

/-- An application stays an application of the same label, and the arguments
stay related pointwise. -/
theorem patternCong_apply_args {left right : Pattern} (related : PatternCong left right)
    (shaped : (∃ label args, left = .apply label args) ∨
      (∃ label args, right = .apply label args)) :
    ∃ label args args',
      left = .apply label args ∧ right = .apply label args' ∧
        List.Forall₂ PatternCong args args' := by
  induction related with
  | refl pattern =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨label, args, equal⟩ := existsLeft
          exact ⟨label, args, args, equal, equal, forall2_pattern_of_eq rfl⟩
      | inr existsRight =>
          obtain ⟨label, args, equal⟩ := existsRight
          exact ⟨label, args, args, equal, equal, forall2_pattern_of_eq rfl⟩
  | symm _ inductionHypothesis =>
      obtain ⟨label, args, args', rightEq, leftEq, pointwise⟩ :=
        inductionHypothesis shaped.symm
      exact ⟨label, args', args, leftEq, rightEq, forall2_pattern_symm pointwise⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨label, args, midArgs, leftEq, midEq, pointLeft⟩ :=
            inductionHypothesis (Or.inl existsLeft)
          obtain ⟨label', midArgs', rightArgs, midEq', rightEq, pointRight⟩ :=
            inductionHypothesis' (Or.inl ⟨label, midArgs, midEq⟩)
          have sameMid := midEq.symm.trans midEq'
          simp only [Pattern.apply.injEq] at sameMid
          obtain ⟨labels, argsEq⟩ := sameMid
          subst labels
          subst argsEq
          exact ⟨label, args, rightArgs, leftEq, rightEq,
            forall2_pattern_trans pointLeft pointRight⟩
      | inr existsRight =>
          obtain ⟨label, midArgs, rightArgs, midEq, rightEq, pointRight⟩ :=
            inductionHypothesis' (Or.inr existsRight)
          obtain ⟨label', args, midArgs', leftEq, midEq', pointLeft⟩ :=
            inductionHypothesis (Or.inr ⟨label, midArgs, midEq⟩)
          have sameMid := midEq'.symm.trans midEq
          simp only [Pattern.apply.injEq] at sameMid
          obtain ⟨labels, argsEq⟩ := sameMid
          subst labels
          subst argsEq
          exact ⟨label', args, rightArgs, leftEq, rightEq,
            forall2_pattern_trans pointLeft pointRight⟩
  | bagPerm _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, _, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, _, equal⟩ := existsRight
          cases equal
  | setPerm _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, _, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, _, equal⟩ := existsRight
          cases equal
  | setDup =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, _, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, _, equal⟩ := existsRight
          cases equal
  | applyAt step _ =>
      expose_names
      exact ⟨label, before ++ left_1 :: after, before ++ right_1 :: after, rfl, rfl,
        forall2_pattern_replace step⟩
  | lambdaAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, _, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, _, equal⟩ := existsRight
          cases equal
  | multiLambdaAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, _, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, _, equal⟩ := existsRight
          cases equal
  | collectionAt _ _ =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨_, _, equal⟩ := existsLeft
          cases equal
      | inr existsRight =>
          obtain ⟨_, _, equal⟩ := existsRight
          cases equal

/-- A lambda stays a lambda of the same binder. -/
theorem patternCong_lambda_body {left right : Pattern} (related : PatternCong left right)
    (shaped : (∃ binder body, left = .lambda binder body) ∨
      (∃ binder body, right = .lambda binder body)) :
    ∃ binder body body',
      left = .lambda binder body ∧ right = .lambda binder body' ∧ PatternCong body body' := by
  induction related with
  | refl pattern =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨binder, body, equal⟩ := existsLeft
          exact ⟨binder, body, body, equal, equal, PatternCong.refl body⟩
      | inr existsRight =>
          obtain ⟨binder, body, equal⟩ := existsRight
          exact ⟨binder, body, body, equal, equal, PatternCong.refl body⟩
  | symm _ inductionHypothesis =>
      obtain ⟨binder, body, body', rightEq, leftEq, step⟩ := inductionHypothesis shaped.symm
      exact ⟨binder, body', body, leftEq, rightEq, PatternCong.symm step⟩
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      cases shaped with
      | inl existsLeft =>
          obtain ⟨binder, body, midBody, leftEq, midEq, stepLeft⟩ :=
            inductionHypothesis (Or.inl existsLeft)
          obtain ⟨binder', midBody', rightBody, midEq', rightEq, stepRight⟩ :=
            inductionHypothesis' (Or.inl ⟨binder, midBody, midEq⟩)
          have sameMid := midEq.symm.trans midEq'
          simp only [Pattern.lambda.injEq] at sameMid
          obtain ⟨binders, bodies⟩ := sameMid
          subst binders
          subst bodies
          exact ⟨binder, body, rightBody, leftEq, rightEq, PatternCong.trans stepLeft stepRight⟩
      | inr existsRight =>
          obtain ⟨binder, midBody, rightBody, midEq, rightEq, stepRight⟩ :=
            inductionHypothesis' (Or.inr existsRight)
          obtain ⟨binder', body, midBody', leftEq, midEq', stepLeft⟩ :=
            inductionHypothesis (Or.inr ⟨binder, midBody, midEq⟩)
          have sameMid := midEq'.symm.trans midEq
          simp only [Pattern.lambda.injEq] at sameMid
          obtain ⟨binders, bodies⟩ := sameMid
          subst binders
          subst bodies
          exact ⟨binder', body, rightBody, leftEq, rightEq, PatternCong.trans stepLeft stepRight⟩
  | bagPerm _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, equal⟩ := existsRight; cases equal
  | setPerm _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, equal⟩ := existsRight; cases equal
  | setDup =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, equal⟩ := existsRight; cases equal
  | applyAt _ _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, equal⟩ := existsRight; cases equal
  | lambdaAt step _ =>
      expose_names
      exact ⟨binder, left_1, right_1, rfl, rfl, step⟩
  | multiLambdaAt _ _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, equal⟩ := existsRight; cases equal
  | collectionAt _ _ =>
      cases shaped with
      | inl existsLeft => obtain ⟨_, _, equal⟩ := existsLeft; cases equal
      | inr existsRight => obtain ⟨_, _, equal⟩ := existsRight; cases equal

/-! ## A vec language has nothing to quotient -/

theorem vecOnly_not_bag (vecOnly : VecOnly language) {sort : String}
    (operator : (indexedSignature language).Op sort) {parameterIndex : Nat}
    (parameterBound : parameterIndex < operator.1.1.params.length) {kind : CollType}
    {element : String}
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, parameterBound⟩) =
      some (kind, element))
    (bagOrSet : kind = .hashBag ∨ kind = .hashSet) : False := by
  have kindVec :=
    vecOnly operator.1.1 operator.1.2.1
      (operator.1.1.params.get ⟨parameterIndex, parameterBound⟩)
      (List.get_mem operator.1.1.params ⟨parameterIndex, parameterBound⟩) kind element shape
  cases bagOrSet with
  | inl kindBag =>
      subst kindBag
      cases kindVec
  | inr kindSet =>
      subst kindSet
      cases kindVec

theorem vecOnly_not_set (vecOnly : VecOnly language) {sort : String}
    (operator : (indexedSignature language).Op sort) {parameterIndex : Nat}
    (parameterBound : parameterIndex < operator.1.1.params.length) {element : String}
    (shape : baseCollection? (operator.1.1.params.get ⟨parameterIndex, parameterBound⟩) =
      some (.hashSet, element)) : False := by
  have kindVec :=
    vecOnly operator.1.1 operator.1.2.1
      (operator.1.1.params.get ⟨parameterIndex, parameterBound⟩)
      (List.get_mem operator.1.1.params ⟨parameterIndex, parameterBound⟩) .hashSet element shape
  cases kindVec

/-- In a vec language the tree congruence is equality. -/
theorem vec_treeCong_eq (vecOnly : VecOnly language) {index : List String × String}
    {left right : Tree language index} (related : TreeCong language left right) :
    left = right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | @congr Γ sort operator leftChildren rightChildren changed _ stable inductionHypothesis =>
      have childrenEq : leftChildren = rightChildren := by
        funext direction
        by_cases same : direction = changed
        · subst same
          exact inductionHypothesis
        · exact stable direction same
      exact congrArg
        (fun continuation : Child language Γ sort operator =>
          IFreeM.liftBind (P := polynomial (indexedSignature language)) (s := (Γ, sort))
            operator continuation)
        childrenEq
  | bagPerm operator _start _length _fit _kind bagOrSet parameterIndex parameterBound
      parameterShape _segmentStart _segmentLength _uniform _leftChildren _rightChildren
      _outside _permuted =>
      exact False.elim
        (vecOnly_not_bag vecOnly operator parameterBound parameterShape bagOrSet)
  | setDup source _target _sourceChildren _targetChildren _removed _parameterIndex
      _segmentStart deletion =>
      exact False.elim
        (vecOnly_not_set vecOnly source deletion.parameterBound deletion.parameterShape)

/-- Printing a vec language reflects the pattern congruence as the tree congruence. -/
theorem vec_pattern_treeCong
    (vecOnly : VecOnly language) (labels : (language.terms.map (·.label)).Nodup)
    (uniqueBare : UniqueBare language) {index : List String × String}
    {left right : Tree language index}
    (related : PatternCong (toPattern left) (toPattern right)) :
    TreeCong language left right := by
  have printedEq := vec_cong_eq related (Or.inl (toPattern_vecShaped vecOnly left))
  have treesEq := toPattern_injective labels uniqueBare left right printedEq
  subst treesEq
  exact TreeCong.refl left

/-- The tree quotient of a vec language is the indexed tree. -/
noncomputable def vecTreeQuotientEquiv (vecOnly : VecOnly language) (sort : String) :
    Quotient (treeSetoid (language := language) sort) ≃ Tree language ([], sort) where
  toFun := Quotient.lift id (fun _left _right related => vec_treeCong_eq vecOnly related)
  invFun := Quotient.mk (treeSetoid (language := language) sort)
  left_inv quotient := by
    induction quotient using Quotient.inductionOn with
    | _ element => rfl
  right_inv _ := rfl

/-- Closed vec patterns modulo the pattern congruence are the indexed trees
modulo the tree congruence, and both quotients are the trees themselves. -/
noncomputable def vecCongruenceEquiv
    (fragment : ∀ rule ∈ language.terms, FragmentRule rule)
    (labels : (language.terms.map (·.label)).Nodup) (uniqueBare : UniqueBare language)
    (vecOnly : VecOnly language) (sort : String) :
    Quotient (patternSetoid (language := language) sort) ≃
      Quotient (treeSetoid (language := language) sort) :=
  (vecQuotientEquiv fragment labels uniqueBare vecOnly sort).trans
    (vecTreeQuotientEquiv vecOnly sort).symm

end Mettapedia.GSLT.Poly.CollectionIndexedEquiv
