import Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetUniverses

/-!
# A plural family of admitted theories: well-founded against anti-founded

A theory is here a set of membership principles (`Principle`): the six set-forming principles
(extensionality, empty set, union, power set, separation, replacement), membership induction,
and the existence of a Quine atom. A theory is *admitted* at a universe level when some
carrier of that level with a membership relation satisfies all of it (`Admitted`).

**Two admitted theories with no common admitted extension.** The set-forming principles with
membership induction (`wellFounded`) hold in the hereditarily finite sets, and in the members
of every closed set that holds the empty set (`stage_wellFounded`). The set-forming principles
with a Quine atom (`antiFounded`) hold in the hypersets. Both theories are admitted
(`admitted_wellFounded`, `admitted_antiFounded`), and no admitted theory includes both
(`no_common_admitted_extension`), since membership induction refutes a Quine atom. So the
admitted theories are not directed, and none of them includes every other
(`no_greatest_admitted`). The admitted theories are exactly the parts of one of the two
(`admitted_iff`): the family has two maximal members, and their common part, the six
set-forming principles, decides neither membership induction nor the Quine atom.

**The stages of sets share one theory and one membership.** Every closed set holding the empty
set is admitted under the same theory, `wellFounded`, on one membership relation, and no set at all
has a Quine atom among its members (`no_quineAtom_among_members`). The principles that hold at
such a stage are exactly those of `wellFounded` (`stage_holds_iff`), and those that hold at the
hypersets are exactly those of `antiFounded` (`hypersets_holds_iff`): each model is one of the
two maximal members of the family.

**How the two sides are joined.**
* By restriction to the well-founded part, in every model: the accessible part of any carrier
  that satisfies the set-forming principles satisfies the well-founded theory
  (`bubble_wellFounded`, free of choice), and it is a transitive part of the carrier
  (`bubble_decorates`). So every stage admitted under the set-forming principles, the
  hypersets among them, restricts to a well-founded stage.
* On one membership relation, from the well-founded side: every transitive set is a transitive
  part of the hypersets, through the injective map that sends a set to its hyperset
  (`members_decorate_hypersets`).
* On one membership relation, from the anti-founded side: nothing. A carrier with a
  self-member has no membership-preserving map into a carrier without one
  (`not_exists_memHom_of_selfMember`); in particular the hypersets have none into the members
  of any set of any level (`hypersets_no_memHom_into_members`).
* With the memberships kept apart: every hyperset of one level is a set of the next level, and
  membership of hypersets is a relation on those sets that is not their membership: the code of
  the Quine atom is related to itself and is not a member of itself (`codeMem_quineAtom_self`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation ZFSetDependentProducts
open Mettapedia.SetTheory.Profiles
open Mettapedia.SetTheory.CarveOuts
open Mettapedia.SetTheory.AntiFoundation (memChild)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open scoped ZFSet

universe u v w

/-! ## Principles and admitted theories -/

/-- The membership principles from which the well-founded and the anti-founded profile are
drawn. -/
inductive Principle where
  | extensional
  | empty
  | union
  | power
  | separation
  | replacement
  | induction
  | quineAtom
  deriving DecidableEq, Repr

/-- What a principle says of a membership relation. -/
def Principle.Holds {S : Type v} (mem : Mem S) : Principle → Prop
  | .extensional => Extensional mem
  | .empty => HasEmpty mem
  | .union => HasUnion mem
  | .power => HasPower mem
  | .separation => HasSeparation mem
  | .replacement => HasReplacement mem
  | .induction => HasMemInduction mem
  | .quineAtom => HasQuineAtom mem

/-- Membership induction holds of Mathlib's sets. -/
example : Principle.Holds (fun x y : ZFSet.{u} => x ∈ y) .induction :=
  zfSet_memInduction

/-- Membership induction fails of the hypersets. -/
example : ¬ Principle.Holds (fun x y : HSet.{u} => x ∈ y) .induction :=
  hset_refutes_memInduction

/-- A theory, a set of principles, is admitted at a universe level when some carrier of that
level with a membership relation satisfies every principle of it. -/
def Admitted (T : Set Principle) : Prop :=
  ∃ (S : Type v) (mem : Mem S), ∀ p ∈ T, p.Holds mem

/-- A part of an admitted theory is admitted. -/
theorem Admitted.mono {T T' : Set Principle} (included : T ⊆ T') (admitted : Admitted.{v} T') :
    Admitted.{v} T := by
  obtain ⟨S, mem, holds⟩ := admitted
  exact ⟨S, mem, fun p hp => holds p (included hp)⟩

/-- The six set-forming principles. -/
def setForming : Set Principle :=
  {.extensional, .empty, .union, .power, .separation, .replacement}

/-- The set-forming principles with membership induction. -/
def wellFounded : Set Principle := insert .induction setForming

/-- The set-forming principles with a Quine atom. -/
def antiFounded : Set Principle := insert .quineAtom setForming

/-- Union is a set-forming principle; membership induction is not one. -/
example : Principle.union ∈ setForming ∧ Principle.induction ∉ setForming := by
  simp [setForming]

/-- The well-founded theory has membership induction and no Quine atom. -/
example : Principle.induction ∈ wellFounded ∧ Principle.quineAtom ∉ wellFounded := by
  simp [wellFounded, setForming]

/-- The anti-founded theory has a Quine atom and no membership induction. -/
example : Principle.quineAtom ∈ antiFounded ∧ Principle.induction ∉ antiFounded := by
  simp [antiFounded, setForming]

/-- The seven principles of a well-founded bubble are the well-founded theory. -/
theorem holds_wellFounded_of_bubbleLaws {S : Type v} {mem : Mem S} (laws : BubbleLaws mem) :
    ∀ p ∈ wellFounded, p.Holds mem := by
  intro p hp
  simp only [wellFounded, setForming, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact laws.induction
  · exact laws.extensional
  · exact laws.empty
  · exact laws.union
  · exact laws.power
  · exact laws.separation
  · exact laws.replacement

/-- The assumptions of the hyperset profile are the anti-founded theory. -/
theorem holds_antiFounded_of_assumptions {S : Type v} {mem : Mem S}
    (laws : HypersetAssumptions mem) : ∀ p ∈ antiFounded, p.Holds mem := by
  intro p hp
  simp only [antiFounded, setForming, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact laws.quineAtom
  · exact laws.extensional
  · exact laws.empty
  · exact laws.union
  · exact laws.power
  · exact laws.separation
  · exact laws.replacement

/-! ## The two theories are admitted, and no admitted theory includes both -/

/-- The well-founded theory is admitted: it holds in the hereditarily finite sets. -/
theorem admitted_wellFounded : Admitted.{u + 1} wellFounded :=
  ⟨_, _, holds_wellFounded_of_bubbleLaws hereditarilyFinite_bubbleLaws.{u}⟩

/-- The anti-founded theory is admitted: it holds in the hypersets. -/
theorem admitted_antiFounded : Admitted.{u + 1} antiFounded :=
  ⟨HSet.{u}, (· ∈ ·), holds_antiFounded_of_assumptions ClassicalHypersetCollection.assumptions⟩

/-- Membership induction and a Quine atom are not admitted together, at any level. -/
theorem not_admitted_induction_quineAtom :
    ¬ Admitted.{v} ({.induction, .quineAtom} : Set Principle) := by
  rintro ⟨S, mem, holds⟩
  exact noQuineAtom_of_induction (holds .induction (by simp)) (holds .quineAtom (by simp))

/-- **The well-founded and the anti-founded theory have no common admitted extension.** -/
theorem no_common_admitted_extension {T : Set Principle} (left : wellFounded ⊆ T)
    (right : antiFounded ⊆ T) : ¬ Admitted.{v} T := by
  intro admitted
  refine not_admitted_induction_quineAtom (admitted.mono ?_)
  intro p hp
  rcases hp with rfl | rfl
  · exact left (Set.mem_insert _ _)
  · exact right (Set.mem_insert _ _)

/-- **No admitted theory includes every admitted theory.** -/
theorem no_greatest_admitted :
    ¬ ∃ T : Set Principle, Admitted.{u + 1} T ∧ ∀ T', Admitted.{u + 1} T' → T' ⊆ T := by
  rintro ⟨T, admitted, greatest⟩
  exact no_common_admitted_extension (greatest _ admitted_wellFounded.{u})
    (greatest _ admitted_antiFounded.{u}) admitted

/-- The well-founded theory has every principle but the Quine atom. -/
theorem mem_wellFounded_iff {p : Principle} : p ∈ wellFounded ↔ p ≠ .quineAtom := by
  cases p <;> simp [wellFounded, setForming]

/-- The anti-founded theory has every principle but membership induction. -/
theorem mem_antiFounded_iff {p : Principle} : p ∈ antiFounded ↔ p ≠ .induction := by
  cases p <;> simp [antiFounded, setForming]

/-- **The admitted theories are the parts of the well-founded theory and the parts of the
anti-founded theory.** So the plural family of these theories has exactly two maximal members,
and their common part is the set-forming principles. -/
theorem admitted_iff {T : Set Principle} :
    Admitted.{u + 1} T ↔ T ⊆ wellFounded ∨ T ⊆ antiFounded := by
  constructor
  · intro admitted
    by_cases quine : Principle.quineAtom ∈ T
    · right
      intro p hp
      rw [mem_antiFounded_iff]
      rintro rfl
      refine not_admitted_induction_quineAtom (admitted.mono ?_)
      rintro q (rfl | rfl)
      · exact hp
      · exact quine
    · left
      intro p hp
      rw [mem_wellFounded_iff]
      rintro rfl
      exact quine hp
  · rintro (below | below)
    · exact admitted_wellFounded.mono below
    · exact admitted_antiFounded.mono below

/-! ## The stages of sets: one theory, one membership -/

/-- The members of a closed set holding the empty set form a transitive class. -/
theorem stage_transitiveClass {U : ZFSet.{u}} (hU : Closed U) (hEmpty : (∅ : ZFSet.{u}) ∈ U) :
    TransitiveClass (fun x : ZFSet.{u} => x ∈ U) where
  transitive hx hy := hU.transitive _ hx hy
  empty := hEmpty
  union := hU.union_mem
  power := hU.power_mem
  replacement f ha hf := hU.replacement_mem ha f hf

/-- **Every stage is admitted under the well-founded theory**: the members of a closed set
holding the empty set satisfy the set-forming principles and membership induction. -/
theorem stage_wellFounded {U : ZFSet.{u}} (hU : Closed U) (hEmpty : (∅ : ZFSet.{u}) ∈ U) :
    ∀ p ∈ wellFounded, p.Holds (fun x y : Elements U => x.1 ∈ y.1) :=
  holds_wellFounded_of_bubbleLaws (stage_transitiveClass hU hEmpty).bubbleLaws

/-- **No set has a Quine atom among its members.** -/
theorem no_quineAtom_among_members (U : ZFSet.{u}) :
    ¬ HasQuineAtom (fun x y : Elements U => x.1 ∈ y.1) := by
  rintro ⟨q, quine⟩
  exact ZFSet.mem_irrefl q.1 ((quine q).mpr rfl)

/-- **The theory of a stage of sets is the well-founded theory**: a principle holds of the
members of a closed set holding the empty set exactly when it is one of the set-forming
principles or membership induction. No principle separates two such stages. -/
theorem stage_holds_iff {U : ZFSet.{u}} (hU : Closed U) (hEmpty : (∅ : ZFSet.{u}) ∈ U)
    (p : Principle) : p.Holds (fun x y : Elements U => x.1 ∈ y.1) ↔ p ∈ wellFounded := by
  constructor
  · intro holds
    rw [mem_wellFounded_iff]
    rintro rfl
    exact no_quineAtom_among_members U holds
  · exact stage_wellFounded hU hEmpty p

/-- **The theory of the hypersets is the anti-founded theory.** -/
theorem hypersets_holds_iff (p : Principle) :
    p.Holds (fun x y : HSet.{u} => x ∈ y) ↔ p ∈ antiFounded := by
  constructor
  · intro holds
    rw [mem_antiFounded_iff]
    rintro rfl
    exact hset_refutes_memInduction holds
  · exact holds_antiFounded_of_assumptions ClassicalHypersetCollection.assumptions p

/-! ## The well-founded part of a model of the set-forming principles -/

section Bubble

variable {S : Type v} {mem : Mem S}

/-- **The accessible part of a model of the set-forming principles is a model of the
well-founded theory.** Each set formed from accessible sets is accessible, because its members
are members of accessible sets or accessible by construction; membership induction holds on
the accessible part of every membership. No use is made of the host's choice. -/
theorem bubble_wellFounded (laws : ∀ p ∈ setForming, p.Holds mem) :
    ∀ p ∈ wellFounded, p.Holds (bubbleMem mem) := by
  have extensional : Extensional mem := laws .extensional (by simp [setForming])
  have empty : HasEmpty mem := laws .empty (by simp [setForming])
  have union : HasUnion mem := laws .union (by simp [setForming])
  have power : HasPower mem := laws .power (by simp [setForming])
  have separation : HasSeparation mem := laws .separation (by simp [setForming])
  have replacement : HasReplacement mem := laws .replacement (by simp [setForming])
  intro p hp
  simp only [wellFounded, setForming, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bubble_memInduction mem
  · intro a b same
    refine Subtype.ext (extensional a.1 b.1 fun z => ?_)
    constructor
    · intro hz
      exact (same ⟨z, a.2.inv hz⟩).mp hz
    · intro hz
      exact (same ⟨z, b.2.inv hz⟩).mpr hz
  · obtain ⟨e, he⟩ := empty
    exact ⟨⟨e, Acc.intro e fun y hy => absurd hy (he y)⟩, fun z => he z.1⟩
  · intro a
    obtain ⟨s, hs⟩ := union a.1
    have accessible : Acc mem s := Acc.intro s fun z hz => by
      obtain ⟨y, hya, hzy⟩ := (hs z).mp hz
      exact (a.2.inv hya).inv hzy
    refine ⟨⟨s, accessible⟩, fun z => ?_⟩
    constructor
    · intro hz
      obtain ⟨y, hya, hzy⟩ := (hs z.1).mp hz
      exact ⟨⟨y, a.2.inv hya⟩, hya, hzy⟩
    · rintro ⟨y, hya, hzy⟩
      exact (hs z.1).mpr ⟨y.1, hya, hzy⟩
  · intro a
    obtain ⟨q, hq⟩ := power a.1
    have accessible : Acc mem q := Acc.intro q fun z hz =>
      Acc.intro z fun w hw => a.2.inv ((hq z).mp hz w hw)
    refine ⟨⟨q, accessible⟩, fun z => ?_⟩
    constructor
    · intro hz w hw
      exact (hq z.1).mp hz w.1 hw
    · intro included
      exact (hq z.1).mpr fun w hw => included ⟨w, z.2.inv hw⟩ hw
  · intro a P
    obtain ⟨b, hb⟩ := separation a.1 (fun z => ∃ hz : Acc mem z, P ⟨z, hz⟩)
    have accessible : Acc mem b := Acc.intro b fun z hz => a.2.inv ((hb z).mp hz).1
    refine ⟨⟨b, accessible⟩, fun z => ?_⟩
    constructor
    · intro hz
      obtain ⟨hza, _, holds⟩ := (hb z.1).mp hz
      exact ⟨hza, holds⟩
    · rintro ⟨hza, holds⟩
      exact (hb z.1).mpr ⟨hza, z.2, holds⟩
  · intro a R functional
    obtain ⟨b, hb⟩ := replacement a.1
      (fun x y => ∃ (hx : Acc mem x) (hy : Acc mem y), R ⟨x, hx⟩ ⟨y, hy⟩) (by
        intro x hx
        obtain ⟨y, hy, unique⟩ := functional ⟨x, a.2.inv hx⟩ hx
        refine ⟨y.1, ⟨a.2.inv hx, y.2, hy⟩, ?_⟩
        rintro y' ⟨_, hy', related⟩
        exact congrArg Subtype.val (unique ⟨y', hy'⟩ related))
    have accessible : Acc mem b := Acc.intro b fun y hy => by
      obtain ⟨_, _, _, hy', _⟩ := (hb y).mp hy
      exact hy'
    refine ⟨⟨b, accessible⟩, fun y => ?_⟩
    constructor
    · intro hy
      obtain ⟨x, hxa, hx, _, related⟩ := (hb y.1).mp hy
      exact ⟨⟨x, hx⟩, hxa, related⟩
    · rintro ⟨x, hxa, related⟩
      exact (hb y.1).mpr ⟨x.1, hxa, x.2, y.2, related⟩

/-- The accessible part is a transitive part of its carrier: the members of an accessible set
are the accessible sets that are its members. -/
theorem bubble_decorates :
    Decorates (memChild (bubbleMem mem)) mem (Subtype.val : Bubble mem → S) := by
  intro a y
  constructor
  · intro hy
    exact ⟨⟨y, a.2.inv hy⟩, hy, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact hb

end Bubble

/-! ## How the well-founded stages and the hypersets are joined -/

/-- **Every transitive set is a transitive part of the hypersets**: the members of the
hyperset of a member are the hypersets of its members. The map is injective
(`HSet.ofZFSet_injective`). -/
theorem members_decorate_hypersets {U : ZFSet.{u}} (hU : U.IsTransitive) :
    Decorates (memChild (fun x y : Elements U => x.1 ∈ y.1))
      (fun x y : HSet.{u} => x ∈ y) (fun x : Elements U => HSet.ofZFSet x.1) := by
  intro a y
  show y ∈ HSet.ofZFSet a.1 ↔ ∃ b : Elements U, b.1 ∈ a.1 ∧ y = HSet.ofZFSet b.1
  rw [HSet.mem_ofZFSet_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hU a.1 a.2 hz⟩, hz, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.1, hb, rfl⟩

/-- **A membership with a self-member has no membership-preserving map into one without.** -/
theorem not_exists_memHom_of_selfMember {A : Type v} {B : Type w} {memA : Mem A} {memB : Mem B}
    (self : ∃ q, memA q q) (irreflexive : ∀ b, ¬ memB b b) :
    ¬ ∃ f : A → B, ∀ x y, memA x y → memB (f x) (f y) := by
  rintro ⟨f, preserves⟩
  obtain ⟨q, hq⟩ := self
  exact irreflexive (f q) (preserves q q hq)

/-- **The hypersets have no membership-preserving map into the members of a set**, of any
level. -/
theorem hypersets_no_memHom_into_members (U : ZFSet.{v}) :
    ¬ ∃ f : HSet.{u} → Elements U, ∀ x y : HSet.{u}, x ∈ y → (f x).1 ∈ (f y).1 :=
  not_exists_memHom_of_selfMember (memA := fun x y : HSet.{u} => x ∈ y)
    (memB := fun x y : Elements U => x.1 ∈ y.1)
    ⟨HSet.quineAtom, HSet.quineAtom_mem_self⟩ (fun b => ZFSet.mem_irrefl b.1)

/-- **The interpreted membership is not the host's.** On the sets of the next level that code
the hypersets, the code of the Quine atom is related to itself by the membership of hypersets
and is not a member of itself. -/
theorem codeMem_quineAtom_self :
    codeMem (code HSet.quineAtom.{u}) (code HSet.quineAtom.{u}) ∧
      code HSet.quineAtom.{u} ∉ code HSet.quineAtom.{u} :=
  ⟨codeMem_code.mpr HSet.quineAtom_mem_self, ZFSet.mem_irrefl _⟩

#print axioms admitted_wellFounded
#print axioms admitted_antiFounded
#print axioms not_admitted_induction_quineAtom
#print axioms no_common_admitted_extension
#print axioms no_greatest_admitted
#print axioms admitted_iff
#print axioms stage_holds_iff
#print axioms hypersets_holds_iff
#print axioms stage_wellFounded
#print axioms no_quineAtom_among_members
#print axioms bubble_wellFounded
#print axioms bubble_decorates
#print axioms members_decorate_hypersets
#print axioms not_exists_memHom_of_selfMember
#print axioms hypersets_no_memHom_into_members
#print axioms codeMem_quineAtom_self

end Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
