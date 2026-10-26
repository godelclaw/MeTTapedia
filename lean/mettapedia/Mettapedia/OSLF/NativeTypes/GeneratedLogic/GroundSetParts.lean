import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HereditarySets
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts

/-!
# The parts of ground sets

A language read modulo its set laws splits a set into any two sets whose union it is: the parts may share members.
With the canonical forms of ground set languages (`canonical`: each member written once, in order), the splits of a
canonical set are listed by its coverings, which send each member to the first part, the second or both
(`coverings`).

- **The listing** (`groundParts`): the canonical forms of the two parts of each covering. A split of any presentation
  is matched by the covering that takes the members each part has, and the parts of a covering are sets of atoms
  again.
- **At the front door** (`groundPartsDecider`): with the presentations and coherence of ground set languages, a
  closed parts region decides splits as the language's semantics has it.
- **Sets of sets** (`hereditaryParts`): the same listing serves hereditary set languages, whose members are atoms
  and sets of hereditary terms; with no atoms they are the hereditarily finite sets. A flat set language, the
  membership language among them, decides splits at the front door (`flatPartsDecider`).

So bags (by deals), vectors (by cuts) and sets (by coverings) decide their splits through one contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_collection canon_apply arrange arrange_mem
  arrange_eq_of_presents members_map)

variable {relEnv : RelationEnv} {language : LanguageDef} {carrier : GrammarRule} {sort : String}

/-- **The splits of a canonical ground set**: the canonical forms of the two parts of each covering of its members. -/
def coveringSplits : Pattern → CollType → List (Pattern × Pattern)
  | .collection .hashSet values none, .hashSet =>
    (coverings values).map fun parts =>
      (BagForms.sortBags (.collection .hashSet parts.1 none), BagForms.sortBags (.collection .hashSet parts.2 none))
  | _, _ => []

theorem mem_coveringSplits {term : Pattern} {kind : CollType} {pair : Pattern × Pattern}
    (member : pair ∈ coveringSplits term kind) :
    ∃ values, term = .collection .hashSet values none ∧ kind = .hashSet ∧ ∃ parts ∈ coverings values,
      pair = (BagForms.sortBags (.collection .hashSet parts.1 none),
        BagForms.sortBags (.collection .hashSet parts.2 none)) := by
  unfold coveringSplits at member
  split at member
  · rename_i values
    obtain ⟨parts, inside, rfl⟩ := List.mem_map.mp member
    exact ⟨values, rfl, rfl, parts, inside, rfl⟩
  · cases member

theorem canon_of_atom {value : Pattern} (atom : ∃ label, value = token label ∧ AtomOf language sort label) :
    canon value = value := by
  obtain ⟨label, rfl, -⟩ := atom
  rw [token, canon_apply]
  rfl

theorem atomSet_of_sub {values part : List Pattern} (atoms : Atoms language sort values)
    (sub : ∀ value ∈ part, value ∈ values) : atomSet language sort (.collection .hashSet part none) = true :=
  atomSet_iff.mpr ⟨part, rfl, fun value member => atoms value (sub value member)⟩

/-- **Ground sets list their splits by coverings.** -/
def groundParts (lang : GroundSetLanguage language carrier sort) :
    PartsListing relEnv language BagForms.sortBags (atomSet language sort) where
  splits := coveringSplits
  empty := isEmptyCollection
  complete := by
    intro state kind first second admitted canonState split
    have canonical := canonical (relEnv := relEnv) lang
    obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
    have same := canonical.same admitted equivalent
    obtain ⟨values, rfl, atoms⟩ := atomSet_iff.mp admitted
    rw [canonState, BagForms.sortBags_eq, canon_collection] at same
    simp only [set, Pattern.collection.injEq, and_true] at same
    obtain ⟨rfl, arranged⟩ := same
    have inValues : ∀ value ∈ left ++ right, canon value ∈ values := fun value member => by
      rw [arranged, arrange_mem]
      exact List.mem_map_of_mem member
    have partAdmitted : ∀ part : List Pattern, (∀ value ∈ part, value ∈ left ++ right) →
        atomSet language sort (.collection .hashSet part none) = true := by
      intro part inside
      rw [← canonical.determined, BagForms.sortBags_eq, canon_collection]
      refine atomSet_of_sub atoms fun value member => ?_
      obtain ⟨original, member', rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
      exact inValues original (inside original member')
    refine ⟨partAdmitted left fun value member => List.mem_append_left _ member,
      partAdmitted right fun value member => List.mem_append_right _ member, ?_⟩
    have covered : ∀ value ∈ values,
        decide (value ∈ left.map canon) = true ∨ decide (value ∈ right.map canon) = true := by
      intro value member
      rw [arranged, arrange_mem, List.map_append, List.mem_append] at member
      simpa only [decide_eq_true_eq] using member
    have filtered : ∀ part : List Pattern, (∀ value ∈ part, value ∈ left ++ right) →
        BagForms.sortBags (.collection .hashSet (values.filter fun value => decide (value ∈ part.map canon)) none) =
          BagForms.sortBags (.collection .hashSet part none) := by
      intro part inside
      rw [BagForms.sortBags_eq, BagForms.sortBags_eq, canon_collection, canon_collection]
      congr 1
      apply arrange_eq_of_presents (kind := .hashSet)
      intro value
      have identity : (values.filter fun value => decide (value ∈ part.map canon)).map canon =
          values.filter fun value => decide (value ∈ part.map canon) :=
        List.map_congr_left (fun value member => canon_of_atom (atoms value (List.mem_filter.mp member).1))
          |>.trans (List.map_id _)
      rw [identity, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun found => found.2
      · intro found
        obtain ⟨original, member, rfl⟩ := List.mem_map.mp found
        exact ⟨inValues original (inside original member), found⟩
    simp only [set, coveringSplits, List.mem_map]
    exact ⟨_, filter_mem_coverings _ _ covered, by
      rw [filtered left fun value member => List.mem_append_left _ member,
        filtered right fun value member => List.mem_append_right _ member]⟩
  sound := by
    intro state kind pair admitted canonState member
    have canonical := canonical (relEnv := relEnv) lang
    obtain ⟨values, rfl, rfl, parts, inside, rfl⟩ := mem_coveringSplits member
    obtain ⟨values', same, atoms⟩ := atomSet_iff.mp admitted
    simp only [set, Pattern.collection.injEq, true_and, and_true] at same
    subst same
    obtain ⟨leftSub, rightSub, covered⟩ := mem_coverings_parts inside
    have canonEq : BagForms.sortBags (.collection .hashSet (parts.1 ++ parts.2) none) =
        BagForms.sortBags (.collection .hashSet values none) := by
      rw [BagForms.sortBags_eq, BagForms.sortBags_eq, canon_collection, canon_collection,
        arrange_eq_of_presents (kind := .hashSet) (members_map (fun value => ?_) canon)]
      rw [List.mem_append]
      exact ⟨fun found => found.elim (leftSub value) (rightSub value), covered value⟩
    have admittedBoth : atomSet language sort (.collection .hashSet (parts.1 ++ parts.2) none) = true := by
      rw [← canonical.determined, canonEq, canonical.determined]
      exact admitted
    exact ⟨.collection .hashSet parts.1 none, .collection .hashSet parts.2 none,
      ⟨canonical.object admitted, parts.1, parts.2, (canonical.equivalent_iff admitted admittedBoth).mpr canonEq.symm,
        rfl, rfl⟩,
      atomSet_of_sub atoms leftSub, atomSet_of_sub atoms rightSub, rfl, rfl⟩
  empty_iff := by
    intro state kind admitted canonState
    have canonical := canonical (relEnv := relEnv) lang
    rw [isEmptyCollection_iff]
    constructor
    · rintro rfl
      exact ⟨canonical.object admitted, Relation.EqvGen.refl _⟩
    · rintro ⟨-, equivalent⟩
      have same := canonical.same admitted equivalent
      rw [canonState, BagForms.sortBags_eq, canon_collection] at same
      rw [same]
      cases kind <;> simp [arrange, Mettapedia.OSLF.MeTTaIL.PatternLexOrder.sortLex]

/-- **Ground sets decide splits at the front door.** -/
def groundPartsDecider (lang : GroundSetLanguage language carrier sort) (fuel rounds : ℕ) :
    Decider relEnv language :=
  partsDecider (fuel := fuel) (presentations := setPresentations) (canonical lang) (coherent lang fuel)
    (groundParts lang) rounds


/-! ## Sets of sets -/

theorem canon_of_mem_set {values : List Pattern}
    (canonState : BagForms.sortBags (.collection .hashSet values none) = .collection .hashSet values none)
    {value : Pattern} (member : value ∈ values) : canon value = value := by
  rw [BagForms.sortBags_eq, canon_collection, Pattern.collection.injEq] at canonState
  rw [← canonState.2.1] at member
  obtain ⟨original, -, rfl⟩ := List.mem_map.mp ((arrange_mem _).mp member)
  exact Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent original

theorem hereditary_of_sub {values part : List Pattern}
    (inside : ∀ value ∈ values, Hereditary language sort value) (sub : ∀ value ∈ part, value ∈ values) :
    hereditary language sort (.collection .hashSet part none) = true :=
  (hereditary_iff _).mpr (Hereditary.members fun value member => inside value (sub value member))

/-- **Hereditary sets list their splits by coverings.** -/
def hereditaryParts (lang : HereditaryLanguage language carrier) :
    PartsListing relEnv language BagForms.sortBags (hereditary language carrier.category) where
  splits := coveringSplits
  empty := isEmptyCollection
  complete := by
    intro state kind first second admitted canonState split
    have canonical := hereditary_canonical (relEnv := relEnv) lang
    obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
    have same := canonical.same admitted equivalent
    rcases ((hereditary_iff _).mp admitted).cases with ⟨label, rfl, -⟩ | ⟨values, rfl, inside⟩
    · rw [canonState, BagForms.sortBags_eq, canon_collection] at same
      simp [token] at same
    rw [canonState, BagForms.sortBags_eq, canon_collection] at same
    simp only [set, Pattern.collection.injEq, and_true] at same
    obtain ⟨rfl, arranged⟩ := same
    have inValues : ∀ value ∈ left ++ right, canon value ∈ values := fun value member => by
      rw [arranged, arrange_mem]
      exact List.mem_map_of_mem member
    have partAdmitted : ∀ part : List Pattern, (∀ value ∈ part, value ∈ left ++ right) →
        hereditary language carrier.category (.collection .hashSet part none) = true := by
      intro part within
      rw [← canonical.determined, BagForms.sortBags_eq, canon_collection]
      refine hereditary_of_sub inside fun value member => ?_
      obtain ⟨original, member', rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
      exact inValues original (within original member')
    refine ⟨partAdmitted left fun value member => List.mem_append_left _ member,
      partAdmitted right fun value member => List.mem_append_right _ member, ?_⟩
    have covered : ∀ value ∈ values,
        decide (value ∈ left.map canon) = true ∨ decide (value ∈ right.map canon) = true := by
      intro value member
      rw [arranged, arrange_mem, List.map_append, List.mem_append] at member
      simpa only [decide_eq_true_eq] using member
    have filtered : ∀ part : List Pattern, (∀ value ∈ part, value ∈ left ++ right) →
        BagForms.sortBags (.collection .hashSet (values.filter fun value => decide (value ∈ part.map canon)) none) =
          BagForms.sortBags (.collection .hashSet part none) := by
      intro part within
      rw [BagForms.sortBags_eq, BagForms.sortBags_eq, canon_collection, canon_collection]
      congr 1
      apply arrange_eq_of_presents (kind := .hashSet)
      intro value
      have identity : (values.filter fun value => decide (value ∈ part.map canon)).map canon =
          values.filter fun value => decide (value ∈ part.map canon) :=
        List.map_congr_left (fun value member => canon_of_mem_set canonState (List.mem_filter.mp member).1)
          |>.trans (List.map_id _)
      rw [identity, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun found => found.2
      · intro found
        obtain ⟨original, member, rfl⟩ := List.mem_map.mp found
        exact ⟨inValues original (within original member), found⟩
    simp only [set, coveringSplits, List.mem_map]
    exact ⟨_, filter_mem_coverings _ _ covered, by
      rw [filtered left fun value member => List.mem_append_left _ member,
        filtered right fun value member => List.mem_append_right _ member]⟩
  sound := by
    intro state kind pair admitted canonState member
    have canonical := hereditary_canonical (relEnv := relEnv) lang
    obtain ⟨values, rfl, rfl, parts, inside, rfl⟩ := mem_coveringSplits member
    have members : ∀ value ∈ values, Hereditary language carrier.category value :=
      hereditary_set_iff.mp ((hereditary_iff _).mp admitted)
    obtain ⟨leftSub, rightSub, covered⟩ := mem_coverings_parts inside
    have canonEq : BagForms.sortBags (.collection .hashSet (parts.1 ++ parts.2) none) =
        BagForms.sortBags (.collection .hashSet values none) := by
      rw [BagForms.sortBags_eq, BagForms.sortBags_eq, canon_collection, canon_collection,
        arrange_eq_of_presents (kind := .hashSet) (members_map (fun value => ?_) canon)]
      rw [List.mem_append]
      exact ⟨fun found => found.elim (leftSub value) (rightSub value), covered value⟩
    have admittedBoth :
        hereditary language carrier.category (.collection .hashSet (parts.1 ++ parts.2) none) = true := by
      rw [← canonical.determined, canonEq, canonical.determined]
      exact admitted
    exact ⟨.collection .hashSet parts.1 none, .collection .hashSet parts.2 none,
      ⟨canonical.object admitted, parts.1, parts.2, (canonical.equivalent_iff admitted admittedBoth).mpr canonEq.symm,
        rfl, rfl⟩,
      hereditary_of_sub members leftSub, hereditary_of_sub members rightSub, rfl, rfl⟩
  empty_iff := by
    intro state kind admitted canonState
    have canonical := hereditary_canonical (relEnv := relEnv) lang
    rw [isEmptyCollection_iff]
    constructor
    · rintro rfl
      exact ⟨canonical.object admitted, Relation.EqvGen.refl _⟩
    · rintro ⟨-, equivalent⟩
      have same := canonical.same admitted equivalent
      rw [canonState, BagForms.sortBags_eq, canon_collection] at same
      rw [same]
      cases kind <;> simp [arrange, Mettapedia.OSLF.MeTTaIL.PatternLexOrder.sortLex]

/-- **A flat set language decides splits at the front door**, with the presentations and coherence of flat set
languages. -/
def flatPartsDecider {width : ℕ} (lang : FlatSetLanguage language carrier width) (fuel rounds : ℕ) :
    Decider relEnv language :=
  partsDecider (fuel := fuel) (presentations := copiesPresentations width) (hereditary_canonical lang.hereditary)
    (flat_coherent lang fuel) (hereditaryParts lang.hereditary) rounds

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
