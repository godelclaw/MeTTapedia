import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagSplits
import Mettapedia.OSLF.StructuralModal.SeparatingConjunction
import Mettapedia.GSLT.Core.StepFree

/-!
# Finite bag observations in the shared native formula language

The carrier is a finite bag presented by a list. Equations identify precisely
permutations. This is the static observation of a completed answer collection;
it adds no operational transitions to the language that produced the answers.
Structural splitting is the ordinary multiset partition relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference

abbrev system : GSLT :=
  GSLT.equationOnly (List Pattern)
    ⟨List.Perm, ⟨List.Perm.refl, List.Perm.symm, List.Perm.trans⟩⟩

theorem equiv_iff (first second : List Pattern) :
    system.Equiv first second ↔ first.Perm second := Iff.rfl

theorem no_step (source target : List Pattern) : ¬ system.Step source target := id

def spatial : SpatialTheory system where
  Split index source left right := index = 0 ∧ (left ++ right).Perm source
  source_equiv same := by
    constructor
    · rintro ⟨declared, partition⟩
      exact ⟨declared, partition.trans same⟩
    · rintro ⟨declared, partition⟩
      exact ⟨declared, partition.trans same.symm⟩

def splitBackend : SplitBackend system (fun _ => True) where
  theory := spatial
  declared index := index == 0
  enumerate index items := if index = 0 then BagSplits.enumerate items else []
  sound index items parts member := by
    split at member
    · rename_i declared
      exact ⟨declared, Multiset.coe_eq_coe.mp (BagSplits.enumerate_sound member)⟩
    · simp at member
  coverage index items first second partition := by
    obtain ⟨declared, same⟩ := partition
    obtain ⟨pair, member, sameLeft, sameRight⟩ :=
      BagSplits.enumerate_complete (left := (first : Multiset Pattern))
        (right := (second : Multiset Pattern)) (Multiset.coe_eq_coe.mpr same)
    exact ⟨pair, by simp [declared, member],
      (Multiset.coe_eq_coe.mp sameLeft).symm, (Multiset.coe_eq_coe.mp sameRight).symm⟩
  components_admitted _ _ _ _ _ := ⟨trivial, trivial⟩

/-- Empty and singleton observations are the only primitive bag tests. -/
inductive Leaf where
  | emp
  | singleton (value : Pattern)
  deriving DecidableEq, Repr

def evalLeaf : Leaf → List Pattern → Bool
  | .emp, items => decide (items = [])
  | .singleton value, items => decide (items = [value])

def predicate : Leaf → EquationPredicate system
  | .emp =>
    ⟨fun items => (items : Multiset Pattern) = 0, by
      intro first second same
      change (first : Multiset Pattern) = 0 ↔ (second : Multiset Pattern) = 0
      rw [Multiset.coe_eq_coe.mpr same]⟩
  | .singleton value =>
    ⟨fun items => (items : Multiset Pattern) = {value}, by
      intro first second same
      change (first : Multiset Pattern) = {value} ↔ (second : Multiset Pattern) = {value}
      rw [Multiset.coe_eq_coe.mpr same]⟩

theorem evalLeaf_exact (leaf : Leaf) (items : List Pattern) :
    evalLeaf leaf items = true ↔ (predicate leaf).1 items := by
  cases leaf <;> simp [evalLeaf, predicate]

def tests : Leaf → Core.Test system (fun _ => True) := fun leaf =>
  .ofBoolean (predicate leaf) (evalLeaf leaf) (evalLeaf_exact leaf)

def backend : Core.Backend system (fun _ => True) where
  Receipt _ := Empty
  target _ receipt := receipt.elim
  frontier _ _ := []
  closed _ _ := true
  sound _ _ receipt _ := receipt.elim
  coverage _ _ _ _ impossible := impossible.elim
  target_admitted _ _ _ receipt _ := receipt.elim
  completionBudget _ := 0
  complete_at _ _ := rfl
  frontier_stable _ _ _ := rfl
  closed_stable _ _ _ := rfl
  spatial := splitBackend

/-- The exact answer packet: consume one singleton per requested occurrence
and require the remaining bag to be empty. -/
def packet : List Pattern → Core.Formula Leaf
  | [] => .atom .emp
  | value :: rest => .separating 0 (.atom (.singleton value)) (packet rest)

/-- A lower multiplicity bound: consume the requested copies and leave the
remainder unrestricted. -/
def atLeast (value : Pattern) : Nat → Core.Formula Leaf
  | 0 => .top
  | count + 1 => .separating 0 (.atom (.singleton value)) (atLeast value count)

def holds (formula : Core.Formula Leaf) (items : List Pattern) : Prop :=
  (Core.denotation tests formula spatial).1 items

theorem packet_iff (expected actual : List Pattern) :
    holds (packet expected) actual ↔ (actual : Multiset Pattern) = (expected : Multiset Pattern) := by
  induction expected generalizing actual with
  | nil =>
    simp [holds, packet, Core.denotation, tests, Core.Test.ofBoolean, predicate]
  | cons value rest ih =>
    change (∃ first second : List Pattern, (0 = 0 ∧ (first ++ second).Perm actual) ∧
      (first : Multiset Pattern) = {value} ∧ holds (packet rest) second) ↔ _
    constructor
    · rintro ⟨first, second, ⟨_, partition⟩, singleton, remaining⟩
      have restEq := (ih second).mp remaining
      calc
        (actual : Multiset Pattern) = (first : Multiset Pattern) + second :=
          (Multiset.coe_eq_coe.mpr partition).symm
        _ = {value} + (rest : Multiset Pattern) := by rw [singleton, restEq]
        _ = (value :: rest : List Pattern) := by simp
    · intro same
      exact ⟨[value], rest, ⟨rfl, Multiset.coe_eq_coe.mp same.symm⟩, rfl,
        (ih rest).mpr rfl⟩

theorem atLeast_iff (value : Pattern) (count : Nat) (actual : List Pattern) :
    holds (atLeast value count) actual ↔ count ≤ actual.count value := by
  induction count generalizing actual with
  | zero => simp [holds, atLeast, Core.denotation]
  | succ count ih =>
    change (∃ first second : List Pattern, (0 = 0 ∧ (first ++ second).Perm actual) ∧
      (first : Multiset Pattern) = {value} ∧ holds (atLeast value count) second) ↔ _
    constructor
    · rintro ⟨first, second, ⟨_, partition⟩, singleton, remaining⟩
      have countEq := congrArg (Multiset.count value)
        (Multiset.coe_eq_coe.mpr partition)
      have firstCount := congrArg (Multiset.count value) singleton
      have restBound := (ih second).mp remaining
      simp only [Multiset.coe_count, List.count_append, Multiset.count_singleton_self] at *
      omega
    · intro bound
      have positive : 0 < actual.count value := by omega
      have member : value ∈ actual := List.count_pos_iff.mp positive
      have partition : (value :: actual.erase value).Perm actual :=
        (List.perm_cons_erase member).symm
      refine ⟨[value], actual.erase value, ⟨rfl, partition⟩, rfl, (ih _).mpr ?_⟩
      have counts : (actual.erase value).count value = actual.count value - 1 :=
        List.count_erase_self
      omega

/-- Embed the static bag presentation into the existing structural predicate
semantics. Components remain bags, rather than bare element predicates. -/
def encode (items : List Pattern) : Pattern := .collection .hashBag items none

def collectionEquation : Pattern → Pattern → Prop
  | .collection .hashBag first none, .collection .hashBag second none => first.Perm second
  | _, _ => False

def onCollection (property : List Pattern → Prop) : Pattern → Prop
  | .collection .hashBag items none => property items
  | _ => False

theorem separating_iff_sepConj (left right : EquationPredicate system) (items : List Pattern) :
    (spatialPredicate spatial 0 left right).1 items ↔
      Mettapedia.OSLF.StructuralModal.SeparatingConjunction.SepConj
        collectionEquation .hashBag (onCollection left.1) (onCollection right.1) (encode items) := by
  change (∃ first second : List Pattern,
      (0 = 0 ∧ (first ++ second).Perm items) ∧ left.1 first ∧ right.1 second) ↔
    (∃ first second : List Pattern, items.Perm (first ++ second) ∧ left.1 first ∧ right.1 second)
  constructor
  · rintro ⟨first, second, ⟨_, same⟩, acceptsLeft, acceptsRight⟩
    exact ⟨first, second, same.symm, acceptsLeft, acceptsRight⟩
  · rintro ⟨first, second, same, acceptsLeft, acceptsRight⟩
    exact ⟨first, second, ⟨rfl, same.symm⟩, acceptsLeft, acceptsRight⟩

end Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel
