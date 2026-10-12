import Mettapedia.GSLT.Dedukti.LeanMinusOneVariable

/-!
# The value of a computed set of sublevels, at every valuation of the level variables

`conv_code_iff_normalSet` says that the conversion of the theory with explicit
level substitution, on the codes of levels, is equality of the sets of
sublevels that the rules compute.  `LeanMinusOneVariable` links those sets to
the values of the levels for at most one level variable.  This module gives
the values for every number of variables, in one direction: the computed set
has the value of the level.  The converse, that levels with one value at every
valuation have one computed set, is in `LeanMinusCanonicity`.

* `sublevelEval`, `setEval`: the value of a sublevel and of a set of sublevels
  at a valuation.  `C G c` is `c` and `V G x k` is `x + k` where every variable
  of the guard `G` is positive, and both are `0` elsewhere.  At a constant
  valuation they are the values of `LeanMinusOneVariable`
  (`sublevelValue_eq_sublevelEval`, `setValue_eq_setEval`).
* `Admissible valuation`: the sublevels on which the dominance test `leS` is
  sound at the valuation (`leSub_sound`).  A constant is at least `1`, and the
  variable of `V G x k` is positive wherever `G` holds.
* `InsertionSound valuation add`: what the proof uses of the insertion of a
  sublevel into a set.  It keeps the admissible sublevels and gives the maximum
  of the values.  The corrected `Add` has it at every valuation
  (`addSub_sound`).
* `normalSetWith add leaf`: the set computed for a level with the insertion
  `add` and the code `leaf` of a level variable.  `normalSet` is the case of the
  corrected `Add` and of the variable in its own guard
  (`normalSetWith_addSub_guardedLeaf`).  Its value is the value of the level at
  every valuation at which the leaves are admissible and have the values of the
  variables (`normalSetWith_spec`).

## Consequences

* **The computed set of every level has the value of the level**
  (`setEval_normalSet`).  Levels with equal computed sets are equivalent
  (`equiv_of_normalSet_eq`), and **convertible codes are codes of equivalent
  levels, for all levels** (`equiv_of_conv_code`): the direction "convertible
  ⇒ equivalent" of the paper's Theorem 2 in the theory with explicit level
  substitution, for any number of level variables.
* **The paper's code of a level variable has the empty guard**
  (`unguardedLeaf`).  It is admissible at the valuations at which the variable
  is positive, and at no other (`unguardedLeaf_admissible_iff`).  In the theory
  with explicit level substitution the paper's code `paperCode` reduces to the
  set computed with it (`paperCode_reduces_unguarded`,
  `conv_paperCode_explicit_iff`); that theory converts the paper's codes of
  `max 1 α` and `α` (`paperCode_max_one_var_conv_explicit`), and two levels with
  convertible paper codes have equal values at every valuation that is positive
  everywhere (`eval_eq_of_conv_paperCode_explicit`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Values -/

/-- A guard holds at a valuation when every variable of the guard is positive
there. -/
def guardHolds (valuation : Nat → Nat) (guard : List Nat) : Bool :=
  guard.all fun index => valuation index != 0

theorem guardHolds_iff {valuation : Nat → Nat} {guard : List Nat} :
    guardHolds valuation guard = true ↔ ∀ index ∈ guard, valuation index ≠ 0 := by
  simp [guardHolds]

/-- The value of a sublevel at a valuation: `C G c` is `c` and `V G x k` is
`x + k` where the guard `G` holds, and both are `0` elsewhere. -/
def sublevelEval (valuation : Nat → Nat) : Sublevel → Nat
  | .cst guard constant => if guardHolds valuation guard then constant else 0
  | .var guard index offset => if guardHolds valuation guard then valuation index + offset else 0

/-- The value of a set of sublevels: the maximum, `0` for the empty set. -/
def setEval (valuation : Nat → Nat) (set : List Sublevel) : Nat :=
  set.foldr (fun sublevel accumulated => max (sublevelEval valuation sublevel) accumulated) 0

theorem setEval_nil (valuation : Nat → Nat) : setEval valuation [] = 0 := rfl

theorem setEval_cons (valuation : Nat → Nat) (head : Sublevel) (rest : List Sublevel) :
    setEval valuation (head :: rest) = max (sublevelEval valuation head) (setEval valuation rest) :=
  rfl

theorem setEval_append (valuation : Nat → Nat) (first second : List Sublevel) :
    setEval valuation (first ++ second) = max (setEval valuation first) (setEval valuation second) := by
  induction first with
  | nil => simp [setEval_nil]
  | cons head rest ih => simp only [List.cons_append, setEval_cons, ih]; omega

/-- At a constant valuation, the value of a sublevel is its value for one
variable. -/
theorem sublevelValue_eq_sublevelEval (value : Nat) (sublevel : Sublevel) :
    sublevelValue value sublevel = sublevelEval (fun _ => value) sublevel := by
  cases sublevel with
  | cst guard constant =>
      by_cases zero : value = 0 <;> cases guard <;>
        simp [sublevelValue, sublevelEval, guardHolds, zero]
  | var guard index offset =>
      by_cases zero : value = 0 <;> cases guard <;>
        simp [sublevelValue, sublevelEval, guardHolds, zero]

/-- At a constant valuation, the value of a set is its value for one variable. -/
theorem setValue_eq_setEval (value : Nat) (set : List Sublevel) :
    setValue value set = setEval (fun _ => value) set := by
  induction set with
  | nil => rfl
  | cons head rest ih => rw [setValue_cons, setEval_cons, ih, sublevelValue_eq_sublevelEval]

/-! ## The dominance test is sound on admissible sublevels -/

/-- **A sublevel on which the dominance test is sound at a valuation**: a
constant is at least `1`, and the variable of `V G x k` is positive wherever
its guard `G` holds. -/
def Admissible (valuation : Nat → Nat) : Sublevel → Prop
  | .cst _ constant => 1 ≤ constant
  | .var guard index _ => guardHolds valuation guard = true → valuation index ≠ 0

/-- What `incl` accepts is an inclusion. -/
theorem inclNat_subset {first : List Nat} :
    ∀ {second : List Nat}, inclNat first second = true → ∀ index ∈ first, index ∈ second := by
  intro second
  induction second generalizing first with
  | nil =>
      intro included index member
      cases first with
      | nil => cases member
      | cons head rest => simp [inclNat] at included
  | cons head' rest' ih =>
      intro included index member
      cases first with
      | nil => cases member
      | cons head rest =>
          rcases outcome : cmpNat head head' with _ | _ | _
          · simp [inclNat, outcome] at included
          · simp only [inclNat, outcome] at included
            have same := cmpNat_eq_eq.mp outcome
            subst same
            rcases List.mem_cons.mp member with rfl | inRest
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih included index inRest)
          · simp only [inclNat, outcome] at included
            exact List.mem_cons_of_mem _ (ih included index member)

theorem guardHolds_of_inclNat {valuation : Nat → Nat} {small large : List Nat}
    (included : inclNat small large = true) (holds : guardHolds valuation large = true) :
    guardHolds valuation small = true :=
  guardHolds_iff.mpr fun index member =>
    guardHolds_iff.mp holds index (inclNat_subset included index member)

/-- **The dominance test is sound**: a sublevel that `leS` puts below an
admissible sublevel has at most its value. -/
theorem leSub_sound {valuation : Nat → Nat} {first second : Sublevel}
    (admissible : Admissible valuation second) (dominated : leSub first second = true) :
    sublevelEval valuation first ≤ sublevelEval valuation second := by
  cases first with
  | cst guard constant =>
      cases second with
      | cst guard' constant' =>
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at dominated
          simp only [sublevelEval]
          by_cases holds : guardHolds valuation guard = true
          · rw [if_pos holds, if_pos (guardHolds_of_inclNat dominated.1 holds)]
            exact dominated.2
          · rw [if_neg holds]
            exact Nat.zero_le _
      | var guard' index' offset' =>
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at dominated
          simp only [sublevelEval]
          by_cases holds : guardHolds valuation guard = true
          · have holds' := guardHolds_of_inclNat dominated.1 holds
            have positive := admissible holds'
            rw [if_pos holds, if_pos holds']
            omega
          · rw [if_neg holds]
            exact Nat.zero_le _
  | var guard index offset =>
      cases second with
      | cst guard' constant' => simp [leSub] at dominated
      | var guard' index' offset' =>
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at dominated
          obtain ⟨included, same, below⟩ := dominated
          subst same
          simp only [sublevelEval]
          by_cases holds : guardHolds valuation guard = true
          · rw [if_pos holds, if_pos (guardHolds_of_inclNat included holds)]
            omega
          · rw [if_neg holds]
            exact Nat.zero_le _

/-! ## Sorted insertion keeps the value -/

theorem cmpList_cmpNat_eq :
    ∀ {first second : List Nat}, cmpList cmpNat first second = .eq → first = second
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [cmpList] at same
  | _ :: _, [], same => by simp [cmpList] at same
  | head :: rest, head' :: rest', same => by
      rcases outcome : cmpNat head head' with _ | _ | _
      · simp [cmpList, outcome] at same
      · simp only [cmpList, outcome] at same
        rw [cmpNat_eq_eq.mp outcome, cmpList_cmpNat_eq same]
      · simp [cmpList, outcome] at same

/-- Sublevels that `cmpS` finds equal are equal. -/
theorem cmpSub_eq {first second : Sublevel} (same : cmpSub first second = .eq) : first = second := by
  cases first with
  | cst guard constant =>
      cases second with
      | var guard' index' offset' => simp [cmpSub] at same
      | cst guard' constant' =>
          rcases outcome : cmpList cmpNat guard guard' with _ | _ | _
          · simp [cmpSub, outcome] at same
          · simp only [cmpSub, outcome] at same
            rw [cmpList_cmpNat_eq outcome, cmpNat_eq_eq.mp same]
          · simp [cmpSub, outcome] at same
  | var guard index offset =>
      cases second with
      | cst guard' constant' => simp [cmpSub] at same
      | var guard' index' offset' =>
          rcases outcome : cmpList cmpNat guard guard' with _ | _ | _
          · simp [cmpSub, outcome] at same
          · simp only [cmpSub, outcome] at same
            rcases inner : cmpNat index index' with _ | _ | _
            · simp [inner] at same
            · simp only [inner] at same
              rw [cmpList_cmpNat_eq outcome, cmpNat_eq_eq.mp inner, cmpNat_eq_eq.mp same]
            · simp [inner] at same
          · simp [cmpSub, outcome] at same

theorem mem_insertSorted {α : Type} (compare : α → α → Ordering) (element : α) :
    ∀ (list : List α) (other : α), other ∈ insertSorted compare element list →
      other = element ∨ other ∈ list
  | [], other, member => by
      simp only [insertSorted, List.mem_singleton] at member
      exact Or.inl member
  | head :: rest, other, member => by
      rcases outcome : compare element head with _ | _ | _
      · simp only [insertSorted, outcome, List.mem_cons] at member
        rcases member with same | same | inRest
        · exact Or.inl same
        · exact Or.inr (List.mem_cons.mpr (Or.inl same))
        · exact Or.inr (List.mem_cons_of_mem _ inRest)
      · simp only [insertSorted, outcome] at member
        exact Or.inr member
      · simp only [insertSorted, outcome, List.mem_cons] at member
        rcases member with same | inInner
        · exact Or.inr (List.mem_cons.mpr (Or.inl same))
        · rcases mem_insertSorted compare element rest other inInner with same | inRest
          · exact Or.inl same
          · exact Or.inr (List.mem_cons_of_mem _ inRest)

/-- **Sorted insertion of a sublevel gives the maximum of the values.** -/
theorem setEval_insertSorted (valuation : Nat → Nat) (sublevel : Sublevel) :
    ∀ set : List Sublevel, setEval valuation (insertSorted cmpSub sublevel set) =
      max (sublevelEval valuation sublevel) (setEval valuation set)
  | [] => rfl
  | head :: rest => by
      rcases outcome : cmpSub sublevel head with _ | _ | _
      · simp only [insertSorted, outcome, setEval_cons]
      · simp only [insertSorted, outcome, setEval_cons]
        rw [cmpSub_eq outcome]
        omega
      · simp only [insertSorted, outcome, setEval_cons, setEval_insertSorted valuation sublevel rest]
        omega

/-! ## Insertions that keep the value -/

/-- **An insertion of a sublevel into a set that is sound at a valuation**: it
keeps the admissible sublevels, and the value of the result is the maximum of
the values. -/
structure InsertionSound (valuation : Nat → Nat)
    (add : Sublevel → List Sublevel → List Sublevel) : Prop where
  admissible : ∀ {sublevel : Sublevel} {set : List Sublevel}, Admissible valuation sublevel →
    (∀ other ∈ set, Admissible valuation other) → ∀ other ∈ add sublevel set, Admissible valuation other
  value : ∀ {sublevel : Sublevel} {set : List Sublevel}, Admissible valuation sublevel →
    (∀ other ∈ set, Admissible valuation other) →
      setEval valuation (add sublevel set) =
        max (sublevelEval valuation sublevel) (setEval valuation set)

theorem mem_addSub (sublevel : Sublevel) :
    ∀ (set : List Sublevel) (other : Sublevel), other ∈ addSub sublevel set →
      other = sublevel ∨ other ∈ set
  | [], other, member => by
      simp only [addSub, List.mem_singleton] at member
      exact Or.inl member
  | head :: rest, other, member => by
      simp only [addSub] at member
      split at member
      · exact Or.inr member
      · split at member
        · rcases mem_addSub sublevel rest other member with same | inRest
          · exact Or.inl same
          · exact Or.inr (List.mem_cons_of_mem _ inRest)
        · rcases mem_insertSorted cmpSub head _ other member with same | inInner
          · exact Or.inr (List.mem_cons.mpr (Or.inl same))
          · rcases mem_addSub sublevel rest other inInner with same | inRest
            · exact Or.inl same
            · exact Or.inr (List.mem_cons_of_mem _ inRest)

theorem setEval_addSub {valuation : Nat → Nat} {sublevel : Sublevel}
    (admissible : Admissible valuation sublevel) :
    ∀ {set : List Sublevel}, (∀ other ∈ set, Admissible valuation other) →
      setEval valuation (addSub sublevel set) =
        max (sublevelEval valuation sublevel) (setEval valuation set)
  | [], _ => rfl
  | head :: rest, admissibles => by
      have headAdmissible := admissibles head List.mem_cons_self
      have ih := setEval_addSub admissible (set := rest) fun other member =>
        admissibles other (List.mem_cons_of_mem _ member)
      simp only [addSub]
      by_cases dominated : leSub sublevel head = true
      · have below := leSub_sound headAdmissible dominated
        rw [if_pos dominated]
        simp only [setEval_cons]
        omega
      · rw [if_neg dominated]
        by_cases dominates : leSub head sublevel = true
        · have below := leSub_sound admissible dominates
          rw [if_pos dominates, ih]
          simp only [setEval_cons]
          omega
        · rw [if_neg dominates, setEval_insertSorted, ih]
          simp only [setEval_cons]
          omega

/-- **The corrected `Add` is sound at every valuation.** -/
theorem addSub_sound (valuation : Nat → Nat) : InsertionSound valuation addSub where
  admissible := fun {sublevel set} admissible admissibles other member => by
    rcases mem_addSub sublevel set other member with same | inSet
    · rw [same]
      exact admissible
    · exact admissibles other inSet
  value := fun admissible admissibles => setEval_addSub admissible admissibles

section Insertion

variable {valuation : Nat → Nat} {add : Sublevel → List Sublevel → List Sublevel}

/-- **Inserting the sublevels of a list one by one gives the maximum of the
values.** -/
theorem foldAdd_spec (sound : InsertionSound valuation add) :
    ∀ (list : List Sublevel) {accumulated : List Sublevel},
      (∀ other ∈ list, Admissible valuation other) →
      (∀ other ∈ accumulated, Admissible valuation other) →
        (∀ other ∈ list.foldl (fun accumulated' element => add element accumulated') accumulated,
          Admissible valuation other) ∧
        setEval valuation (list.foldl (fun accumulated' element => add element accumulated') accumulated) =
          max (setEval valuation list) (setEval valuation accumulated)
  | [], _, _, admissibles => ⟨admissibles, by simp [setEval_nil]⟩
  | head :: rest, accumulated, listAdmissible, admissibles => by
      have headAdmissible := listAdmissible head List.mem_cons_self
      obtain ⟨kept, value⟩ := foldAdd_spec sound rest (accumulated := add head accumulated)
        (fun other member => listAdmissible other (List.mem_cons_of_mem _ member))
        (sound.admissible headAdmissible admissibles)
      refine ⟨kept, ?_⟩
      rw [List.foldl_cons, value, sound.value headAdmissible admissibles, setEval_cons]
      omega

end Insertion

/-! ## Increments -/

theorem incrSub_admissible {valuation : Nat → Nat} {sublevel : Sublevel}
    (admissible : Admissible valuation sublevel) : Admissible valuation (incrSub sublevel) := by
  cases sublevel with
  | cst guard constant => exact Nat.le_add_left 1 constant
  | var guard index offset => exact admissible

/-- Incrementing every sublevel of a set adds one to its value, up to the
constant `1`. -/
theorem setEval_map_incrSub (valuation : Nat → Nat) :
    ∀ set : List Sublevel, max 1 (setEval valuation (set.map incrSub)) = setEval valuation set + 1
  | [] => rfl
  | head :: rest => by
      have ih := setEval_map_incrSub valuation rest
      rw [List.map_cons, setEval_cons, setEval_cons]
      cases head with
      | cst guard constant =>
          simp only [incrSub, sublevelEval]
          by_cases holds : guardHolds valuation guard = true
          · rw [if_pos holds, if_pos holds]
            omega
          · rw [if_neg holds, if_neg holds]
            omega
      | var guard index offset =>
          simp only [incrSub, sublevelEval]
          by_cases holds : guardHolds valuation guard = true
          · rw [if_pos holds, if_pos holds]
            omega
          · rw [if_neg holds, if_neg holds]
            omega

/-! ## Guards -/

theorem mem_insertSorted_cmpNat (element : Nat) :
    ∀ (list : List Nat) (other : Nat), other ∈ insertSorted cmpNat element list ↔
      other = element ∨ other ∈ list
  | [], other => by simp [insertSorted]
  | head :: rest, other => by
      rcases outcome : cmpNat element head with _ | _ | _
      · simp [insertSorted, outcome]
      · have same := cmpNat_eq_eq.mp outcome
        subst same
        simp [insertSorted, outcome]
      · simp only [insertSorted, outcome, List.mem_cons, mem_insertSorted_cmpNat element rest other]
        constructor
        · rintro (same | same | inRest)
          · exact Or.inr (Or.inl same)
          · exact Or.inl same
          · exact Or.inr (Or.inr inRest)
        · rintro (same | same | inRest)
          · exact Or.inr (Or.inl same)
          · exact Or.inl same
          · exact Or.inr (Or.inr inRest)

theorem mem_unionSorted_cmpNat :
    ∀ (first second : List Nat) (index : Nat), index ∈ unionSorted cmpNat first second ↔
      index ∈ first ∨ index ∈ second
  | [], second, index => by simp [unionSorted]
  | head :: rest, second, index => by
      simp only [unionSorted, mem_insertSorted_cmpNat, mem_unionSorted_cmpNat rest second index,
        List.mem_cons]
      exact or_assoc.symm

/-- The union of two guards holds exactly where both hold. -/
theorem guardHolds_union (valuation : Nat → Nat) (first second : List Nat) :
    guardHolds valuation (unionSorted cmpNat first second) =
      (guardHolds valuation first && guardHolds valuation second) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, guardHolds_iff, guardHolds_iff, guardHolds_iff]
  constructor
  · intro holds
    exact ⟨fun index member => holds index ((mem_unionSorted_cmpNat first second index).mpr (Or.inl member)),
      fun index member => holds index ((mem_unionSorted_cmpNat first second index).mpr (Or.inr member))⟩
  · rintro ⟨firstHolds, secondHolds⟩ index member
    rcases (mem_unionSorted_cmpNat first second index).mp member with inFirst | inSecond
    · exact firstHolds index inFirst
    · exact secondHolds index inSecond

/-- The value of `addguard u v`: the value of `u` where the guard of `v`
holds, and `0` elsewhere. -/
theorem sublevelEval_addguardSub (valuation : Nat → Nat) (first second : Sublevel) :
    sublevelEval valuation (addguardSub first second) =
      if guardHolds valuation (guardOfSub second) then sublevelEval valuation first else 0 := by
  cases first with
  | cst guard constant =>
      simp only [addguardSub, sublevelEval, guardHolds_union]
      cases guardHolds valuation guard <;> cases guardHolds valuation (guardOfSub second) <;> rfl
  | var guard index offset =>
      simp only [addguardSub, sublevelEval, guardHolds_union]
      cases guardHolds valuation guard <;> cases guardHolds valuation (guardOfSub second) <;> rfl

theorem addguardSub_admissible {valuation : Nat → Nat} {first : Sublevel}
    (admissible : Admissible valuation first) (second : Sublevel) :
    Admissible valuation (addguardSub first second) := by
  cases first with
  | cst guard constant => exact admissible
  | var guard index offset =>
      intro holds
      rw [guardHolds_union, Bool.and_eq_true] at holds
      exact admissible holds.1

/-- An admissible sublevel has the value `0` exactly where its guard fails. -/
theorem sublevelEval_eq_zero_iff {valuation : Nat → Nat} {sublevel : Sublevel}
    (admissible : Admissible valuation sublevel) :
    sublevelEval valuation sublevel = 0 ↔ guardHolds valuation (guardOfSub sublevel) = false := by
  cases sublevel with
  | cst guard constant =>
      have positive : 1 ≤ constant := admissible
      simp only [sublevelEval, guardOfSub]
      by_cases holds : guardHolds valuation guard = true
      · rw [if_pos holds, holds]
        simp
        omega
      · rw [if_neg holds]
        simpa using holds
  | var guard index offset =>
      simp only [sublevelEval, guardOfSub]
      by_cases holds : guardHolds valuation guard = true
      · have positive := admissible holds
        rw [if_pos holds, holds]
        simp
        omega
      · rw [if_neg holds]
        simpa using holds

/-- A set of admissible sublevels has the value `0` exactly where no guard
holds. -/
theorem setEval_eq_zero_iff {valuation : Nat → Nat} :
    ∀ {set : List Sublevel}, (∀ other ∈ set, Admissible valuation other) →
      (setEval valuation set = 0 ↔
        (set.any fun other => guardHolds valuation (guardOfSub other)) = false)
  | [], _ => by simp [setEval_nil]
  | head :: rest, admissibles => by
      have headZero := sublevelEval_eq_zero_iff (admissibles head List.mem_cons_self)
      have restZero := setEval_eq_zero_iff (set := rest) fun other member =>
        admissibles other (List.mem_cons_of_mem _ member)
      rw [setEval_cons, List.any_cons, Bool.or_eq_false_iff, ← headZero, ← restZero]
      omega

/-- The value of the copies of a sublevel guarded by the sublevels of a set:
its own value where some guard of the set holds, and `0` elsewhere. -/
theorem setEval_map_addguardSub (valuation : Nat → Nat) (sublevel : Sublevel) :
    ∀ set : List Sublevel, setEval valuation (set.map (addguardSub sublevel)) =
      if (set.any fun other => guardHolds valuation (guardOfSub other)) = true
        then sublevelEval valuation sublevel else 0
  | [] => rfl
  | head :: rest => by
      rw [List.map_cons, setEval_cons, setEval_map_addguardSub valuation sublevel rest,
        sublevelEval_addguardSub, List.any_cons]
      cases guardHolds valuation (guardOfSub head) <;>
        cases rest.any (fun other => guardHolds valuation (guardOfSub other)) <;> simp

/-- The value of all guarded copies of the sublevels of one set by those of
another. -/
theorem setEval_flatMap_addguardSub (valuation : Nat → Nat) (second : List Sublevel) :
    ∀ first : List Sublevel,
      setEval valuation (first.flatMap fun element => second.map (addguardSub element)) =
        if (second.any fun other => guardHolds valuation (guardOfSub other)) = true
          then setEval valuation first else 0
  | [] => by simp [setEval_nil]
  | head :: rest => by
      rw [List.flatMap_cons, setEval_append, setEval_map_addguardSub,
        setEval_flatMap_addguardSub valuation second rest, setEval_cons]
      split <;> simp

/-! ## The set computed for a level -/

/-- The set of `imax`, for an insertion `add`: nothing when the second set is
empty, and otherwise the second set with every copy of a sublevel of the first
guarded by a sublevel of the second. -/
def imaxSetWith (add : Sublevel → List Sublevel → List Sublevel) (first second : List Sublevel) :
    List Sublevel :=
  match second with
  | [] => []
  | _ :: _ =>
      (first.flatMap fun element => second.map (addguardSub element)).foldl
        (fun accumulated element => add element accumulated) second

/-- **The set of sublevels computed for a level**, with the insertion `add` in
the place of `Add` and the code `leaf` of the level variables. -/
def normalSetWith (add : Sublevel → List Sublevel → List Sublevel) (leaf : Nat → Sublevel) :
    LeanLevel → List Sublevel
  | .zero => []
  | .succ level => add (.cst [] 1) ((normalSetWith add leaf level).map incrSub)
  | .max first second =>
      (normalSetWith add leaf first).foldl (fun accumulated element => add element accumulated)
        (normalSetWith add leaf second)
  | .imax first second => imaxSetWith add (normalSetWith add leaf first) (normalSetWith add leaf second)
  | .param index => [leaf index]

section Computed

variable {valuation : Nat → Nat} {add : Sublevel → List Sublevel → List Sublevel}

theorem imaxSetWith_spec (sound : InsertionSound valuation add) {first second : List Sublevel}
    (firstAdmissible : ∀ other ∈ first, Admissible valuation other)
    (secondAdmissible : ∀ other ∈ second, Admissible valuation other) :
    (∀ other ∈ imaxSetWith add first second, Admissible valuation other) ∧
      setEval valuation (imaxSetWith add first second) =
        if setEval valuation second = 0 then 0
          else max (setEval valuation first) (setEval valuation second) := by
  cases second with
  | nil => exact ⟨fun other member => (by cases member), by simp [imaxSetWith, setEval_nil]⟩
  | cons head rest =>
      obtain ⟨kept, value⟩ := foldAdd_spec sound
        (first.flatMap fun element => (head :: rest).map (addguardSub element))
        (accumulated := head :: rest)
        (fun other member => by
          obtain ⟨element, elementMember, inner⟩ := List.mem_flatMap.mp member
          obtain ⟨guarding, _, same⟩ := List.mem_map.mp inner
          rw [← same]
          exact addguardSub_admissible (firstAdmissible element elementMember) guarding)
        secondAdmissible
      refine ⟨kept, ?_⟩
      have zero := setEval_eq_zero_iff secondAdmissible
      change setEval valuation (List.foldl _ _ _) = _
      rw [value, setEval_flatMap_addguardSub]
      by_cases holds : ((head :: rest).any fun other => guardHolds valuation (guardOfSub other)) = true
      · have positive : setEval valuation (head :: rest) ≠ 0 := fun isZero => by
          rw [zero.mp isZero] at holds
          cases holds
        rw [if_pos holds, if_neg positive]
      · have isZero : setEval valuation (head :: rest) = 0 :=
          zero.mpr (Bool.not_eq_true _ ▸ holds)
        rw [if_neg holds, if_pos isZero, isZero]
        rfl

/-- **The set computed for a level has the value of the level**, at every
valuation at which the insertion is sound and the codes of the variables are
admissible and have the values of the variables. -/
theorem normalSetWith_spec (sound : InsertionSound valuation add) {leaf : Nat → Sublevel}
    (admissible : ∀ index, Admissible valuation (leaf index))
    (value : ∀ index, sublevelEval valuation (leaf index) = valuation index) :
    ∀ level : LeanLevel,
      (∀ other ∈ normalSetWith add leaf level, Admissible valuation other) ∧
        setEval valuation (normalSetWith add leaf level) = level.eval valuation
  | .zero => ⟨fun other member => (by cases member), rfl⟩
  | .param index =>
      ⟨fun other member => by
          rw [List.mem_singleton.mp member]
          exact admissible index,
        by
          change max (sublevelEval valuation (leaf index)) 0 = valuation index
          rw [value]
          omega⟩
  | .succ level => by
      obtain ⟨kept, same⟩ := normalSetWith_spec sound admissible value level
      have one : Admissible valuation (.cst [] 1) := Nat.le_refl 1
      have incremented : ∀ other ∈ (normalSetWith add leaf level).map incrSub,
          Admissible valuation other := fun other member => by
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact incrSub_admissible (kept original originalMember)
      refine ⟨sound.admissible one incremented, ?_⟩
      change setEval valuation (add (.cst [] 1) _) = level.eval valuation + 1
      rw [sound.value one incremented, ← same, ← setEval_map_incrSub]
      rfl
  | .max first second => by
      obtain ⟨firstKept, firstSame⟩ := normalSetWith_spec sound admissible value first
      obtain ⟨secondKept, secondSame⟩ := normalSetWith_spec sound admissible value second
      obtain ⟨kept, same⟩ := foldAdd_spec sound (normalSetWith add leaf first) firstKept secondKept
      refine ⟨kept, ?_⟩
      change setEval valuation (List.foldl _ _ _) = max (first.eval valuation) (second.eval valuation)
      rw [same, firstSame, secondSame]
  | .imax first second => by
      obtain ⟨firstKept, firstSame⟩ := normalSetWith_spec sound admissible value first
      obtain ⟨secondKept, secondSame⟩ := normalSetWith_spec sound admissible value second
      obtain ⟨kept, same⟩ := imaxSetWith_spec sound firstKept secondKept
      refine ⟨kept, ?_⟩
      change setEval valuation (imaxSetWith add _ _) =
        if second.eval valuation = 0 then 0 else max (first.eval valuation) (second.eval valuation)
      rw [same, firstSame, secondSame]

end Computed

/-! ## The variable in its own guard: the corrected code -/

/-- The sublevel of the level variable numbered `index` in the corrected code:
`V {α} α 0`, the variable in its own guard. -/
def guardedLeaf (index : Nat) : Sublevel := .var [index] index 0

theorem guardedLeaf_admissible (valuation : Nat → Nat) (index : Nat) :
    Admissible valuation (guardedLeaf index) := by
  intro holds
  exact guardHolds_iff.mp holds index List.mem_cons_self

theorem sublevelEval_guardedLeaf (valuation : Nat → Nat) (index : Nat) :
    sublevelEval valuation (guardedLeaf index) = valuation index := by
  by_cases zero : valuation index = 0 <;> simp [guardedLeaf, sublevelEval, guardHolds, zero]

theorem imaxSet_eq_imaxSetWith (first second : List Sublevel) :
    imaxSet first second = imaxSetWith addSub first second := by
  cases second with
  | nil => rfl
  | cons head rest => exact guardedSet_eq_fold first (head :: rest) (head :: rest)

/-- **`normalSet` is the set computed with the corrected `Add` and the variable
in its own guard.** -/
theorem normalSetWith_addSub_guardedLeaf :
    ∀ level : LeanLevel, normalSetWith addSub guardedLeaf level = normalSet level
  | .zero => rfl
  | .param _ => rfl
  | .succ level => by
      change addSub (.cst [] 1) ((normalSetWith addSub guardedLeaf level).map incrSub) =
        succSet (normalSet level)
      rw [normalSetWith_addSub_guardedLeaf level]
      rfl
  | .max first second => by
      change List.foldl _ (normalSetWith addSub guardedLeaf second) (normalSetWith addSub guardedLeaf first) =
        maxSet (normalSet first) (normalSet second)
      rw [normalSetWith_addSub_guardedLeaf first, normalSetWith_addSub_guardedLeaf second]
      rfl
  | .imax first second => by
      change imaxSetWith addSub (normalSetWith addSub guardedLeaf first)
          (normalSetWith addSub guardedLeaf second) = imaxSet (normalSet first) (normalSet second)
      rw [normalSetWith_addSub_guardedLeaf first, normalSetWith_addSub_guardedLeaf second,
        imaxSet_eq_imaxSetWith]

/-- **The computed set of every level has the value of the level**, at every
valuation, with any number of level variables. -/
theorem setEval_normalSet (valuation : Nat → Nat) (level : LeanLevel) :
    setEval valuation (normalSet level) = level.eval valuation := by
  rw [← normalSetWith_addSub_guardedLeaf]
  exact (normalSetWith_spec (addSub_sound valuation) (guardedLeaf_admissible valuation)
    (sublevelEval_guardedLeaf valuation) level).2

/-- **Levels with equal computed sets are equivalent.** -/
theorem equiv_of_normalSet_eq {first second : LeanLevel} (same : normalSet first = normalSet second) :
    LeanLevel.Equiv first second := fun valuation => by
  rw [← setEval_normalSet valuation first, ← setEval_normalSet valuation second, same]

/-- **Convertible codes are codes of equivalent levels, for all levels**: the
direction "convertible ⇒ equivalent" of Theorem 2 in the theory with explicit
level substitution, with any number of level variables. -/
theorem equiv_of_conv_code {first second : LeanLevel}
    (convertible : Conv leanTheoryExplicit (code first) (code second)) : LeanLevel.Equiv first second :=
  equiv_of_normalSet_eq (conv_code_iff_normalSet.mp convertible)

/-! ## The empty guard: the paper's code of a variable -/

/-- The sublevel of the level variable numbered `index` in the paper's code:
`V ∅ α 0`, with the empty guard. -/
def unguardedLeaf (index : Nat) : Sublevel := .var [] index 0

/-- **The paper's code of a variable is admissible exactly where the variable
is positive.** -/
theorem unguardedLeaf_admissible_iff (valuation : Nat → Nat) (index : Nat) :
    Admissible valuation (unguardedLeaf index) ↔ valuation index ≠ 0 :=
  ⟨fun admissible => admissible rfl, fun positive _ => positive⟩

theorem sublevelEval_unguardedLeaf (valuation : Nat → Nat) (index : Nat) :
    sublevelEval valuation (unguardedLeaf index) = valuation index := by
  simp [unguardedLeaf, sublevelEval, guardHolds]

/-- **With the paper's code of a variable, the computed set has the value of the
level at every valuation that is positive everywhere**, for every insertion
that is sound there. -/
theorem setEval_unguarded {valuation : Nat → Nat} {add : Sublevel → List Sublevel → List Sublevel}
    (sound : InsertionSound valuation add) (positive : ∀ index, valuation index ≠ 0)
    (level : LeanLevel) :
    setEval valuation (normalSetWith add unguardedLeaf level) = level.eval valuation :=
  (normalSetWith_spec sound (fun index => (unguardedLeaf_admissible_iff valuation index).mpr (positive index))
    (sublevelEval_unguardedLeaf valuation) level).2

/-- **The paper's code of a level reduces, by the corrected rules, to the set
computed with the empty guard.** -/
theorem paperCode_reduces_unguarded :
    ∀ level : LeanLevel,
      Reduces pureTheoryExplicit (paperCode level) (normalCode (normalSetWith addSub unguardedLeaf level))
  | .zero => zero_reduces_pureExplicit
  | .param _ => .refl
  | .succ level =>
      (Reduces.app .refl (paperCode_reduces_unguarded level)).trans (succ_reduces _)
  | .max first second =>
      (Reduces.app (Reduces.app .refl (paperCode_reduces_unguarded first))
        (paperCode_reduces_unguarded second)).trans (max_reduces _ _)
  | .imax first second =>
      (Reduces.app (Reduces.app .refl (paperCode_reduces_unguarded first))
        (paperCode_reduces_unguarded second)).trans
        (by
          have reduced := imax_reduces (normalSetWith addSub unguardedLeaf first)
            (normalSetWith addSub unguardedLeaf second)
          rwa [imaxSet_eq_imaxSetWith] at reduced)

/-- **In the theory with explicit level substitution, conversion of the paper's
codes is equality of the sets computed with the empty guard.** -/
theorem conv_paperCode_explicit_iff {first second : LeanLevel} :
    Conv leanTheoryExplicit (paperCode first) (paperCode second) ↔
      normalSetWith addSub unguardedLeaf first = normalSetWith addSub unguardedLeaf second := by
  have rigid : ∀ name ∈ setConstructors, ¬ leanTheoryExplicit.Defines name :=
    setConstructors_rigid (by decide +kernel)
  have reduces (level : LeanLevel) : Reduces leanTheoryExplicit (paperCode level)
      (normalCode (normalSetWith addSub unguardedLeaf level)) :=
    (paperCode_reduces_unguarded level).mono pureTheoryExplicit_extends
  constructor
  · intro convertible
    by_contra distinct
    exact not_conv_of_normal leanTheoryExplicit_confluent
      (normalCode_normal leanTheoryExplicit_headed rigid _)
      (normalCode_normal leanTheoryExplicit_headed rigid _)
      (fun same => distinct (normalCode_injective same))
      (.trans _ _ _ (.symm _ _ (reduces first).conv) (.trans _ _ _ convertible (reduces second).conv))
  · intro same
    exact Joinable.conv ⟨_, reduces first, same ▸ reduces second⟩

/-- **The empty guard alone identifies `max 1 α` with `α`**: with the rule on
`Add` corrected, the paper's codes of the two levels are still convertible. -/
theorem paperCode_max_one_var_conv_explicit :
    Conv leanTheoryExplicit (paperCode maxOneVar) (paperCode alpha) :=
  conv_paperCode_explicit_iff.mpr (by decide)

/-- **Two levels whose paper codes the theory with explicit level substitution
converts have equal values at every valuation that is positive everywhere.** -/
theorem eval_eq_of_conv_paperCode_explicit {first second : LeanLevel}
    (convertible : Conv leanTheoryExplicit (paperCode first) (paperCode second))
    {valuation : Nat → Nat} (positive : ∀ index, valuation index ≠ 0) :
    first.eval valuation = second.eval valuation := by
  rw [← setEval_unguarded (addSub_sound valuation) positive first,
    ← setEval_unguarded (addSub_sound valuation) positive second,
    conv_paperCode_explicit_iff.mp convertible]

#print axioms leSub_sound
#print axioms addSub_sound
#print axioms normalSetWith_spec
#print axioms normalSetWith_addSub_guardedLeaf
#print axioms setEval_normalSet
#print axioms equiv_of_normalSet_eq
#print axioms equiv_of_conv_code
#print axioms paperCode_reduces_unguarded
#print axioms conv_paperCode_explicit_iff
#print axioms paperCode_max_one_var_conv_explicit
#print axioms eval_eq_of_conv_paperCode_explicit

end Mettapedia.GSLT.Dedukti.LeanMinus
