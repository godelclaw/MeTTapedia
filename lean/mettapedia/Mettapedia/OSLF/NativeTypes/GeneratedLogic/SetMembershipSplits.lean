import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExtensional

/-!
# Deciding splits of hereditarily finite sets

A set splits into two sets whose union it is. The parts of a hereditarily finite set are its subsets, finitely many,
each presented by a sublist of a term's members, so a native type with splits looks at finitely many sets.

- **The parts region of a term** (`Region.withParts`): the subsets of the sets of its region. It is closed under
  membership and under parts (`withParts_partsClosed`), and its terms are the sets of the sublists of the members
  of the region's terms.
- **The decision** (`decideRegional`): the region decision run on the parts region. Splits go through the coverings
  of the members, each member in the first part, the second, or both.
- **It is exact** (`decideRegional_iff`): for every native type of the regional fragment, which adds splits and their
  duals to the modal fragment, it accepts a hereditary term exactly when the type holds there in the membership
  language.
- **The front door uses it as a certified decider** (`setDecider`, through `askWith`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The parts of a term's region**: the sets of the sublists of the members of its terms. -/
def partsOf (term : Pattern) : List Pattern :=
  (regionOf term).flatMap fun inner => (membersOf inner).sublists.map set

/-- The subsets of the sets of a term's region. -/
def zfParts (term : Pattern) : Set ZFSet.{0} := {part | ∃ y ∈ zfRegion term, part ⊆ y}

theorem zfOf_sublist_subset {values sub : List Pattern} (sublist : sub.Sublist values) :
    zfOf (set sub) ⊆ zfOfList values := by
  rw [zfOf_set, ZFSet.subset_def]
  intro z member
  obtain ⟨value, found, rfl⟩ := mem_zfOfList.mp member
  exact mem_zfOfList.mpr ⟨value, sublist.subset found, rfl⟩

variable {term : Pattern}

theorem partsOf_covers (holds : IsHF term) : ∀ part ∈ zfParts term, ∃ other ∈ partsOf term, zfOf other = part := by
  classical
  rintro part ⟨y, ⟨inner, inside, rfl⟩, sub⟩
  have innerHolds := hf_of_mem_regionOf holds inside
  rw [zfOf_eq_zfOfList innerHolds] at sub
  refine ⟨set ((membersOf inner).filter fun value => decide (zfOf value ∈ part)),
    List.mem_flatMap.mpr ⟨inner, inside, List.mem_map.mpr ⟨_, List.mem_sublists.mpr List.filter_sublist, rfl⟩⟩, ?_⟩
  rw [zfOf_set]
  exact zfOfList_filter_part (fun value _ => decide_eq_true_iff) sub

theorem partsOf_hereditary (holds : IsHF term) : ∀ other ∈ partsOf term, IsHF other := by
  intro other member
  obtain ⟨inner, inside, found⟩ := List.mem_flatMap.mp member
  obtain ⟨sub, subMember, rfl⟩ := List.mem_map.mp found
  exact .members fun value found =>
    hf_members (hf_of_mem_regionOf holds inside) value ((List.mem_sublists.mp subMember).subset found)

theorem partsOf_inside (holds : IsHF term) : ∀ other ∈ partsOf term, zfOf other ∈ zfParts term := by
  intro other member
  obtain ⟨inner, inside, found⟩ := List.mem_flatMap.mp member
  obtain ⟨sub, subMember, rfl⟩ := List.mem_map.mp found
  refine ⟨zfOf inner, ⟨inner, inside, rfl⟩, ?_⟩
  rw [zfOf_eq_zfOfList (hf_of_mem_regionOf holds inside)]
  exact zfOf_sublist_subset (List.mem_sublists.mp subMember)

theorem zfParts_closed (holds : IsHF term) : ∀ y ∈ zfParts term, ∀ z ∈ y, z ∈ zfParts term := by
  rintro part ⟨y, inside, sub⟩ z member
  exact ⟨z, zfRegion_closed holds y inside z (ZFSet.subset_def.mp sub member), ZFSet.subset_def.mpr fun _ found => found⟩

/-- **The parts region of a hereditary term.** -/
def Region.withParts (term : Pattern) (holds : IsHF term) : Region where
  sets := zfParts term
  terms := partsOf term
  closed := zfParts_closed holds
  finite := (List.finite_toSet ((partsOf term).map zfOf)).subset fun part inside => by
    obtain ⟨other, member, rfl⟩ := partsOf_covers holds part inside
    exact List.mem_map.mpr ⟨other, member, rfl⟩
  covers := partsOf_covers holds
  hereditary := partsOf_hereditary holds
  inside := partsOf_inside holds

/-- **The parts region is closed under parts.** -/
theorem withParts_partsClosed (holds : IsHF term) : PartsClosed (Region.withParts term holds).sets := by
  rintro part ⟨y, inside, sub⟩ smaller smallerSub
  exact ⟨y, inside, ZFSet.subset_def.mpr fun _ found => ZFSet.subset_def.mp sub (ZFSet.subset_def.mp smallerSub found)⟩

theorem self_mem_zfParts (term : Pattern) : zfOf term ∈ zfParts term :=
  ⟨zfOf term, self_mem_zfRegion term, ZFSet.subset_def.mpr fun _ found => found⟩

/-- **The decision of a regional native type** at a term: the region decision on the term's parts region. -/
def decideRegional (formula : Formula 0) (term : Pattern) : Bool := decideOn (partsOf term) formula Fin.elim0 term

/-- **The decision is exact**: it accepts a regional native type at a hereditary term exactly when the type holds
there. -/
theorem decideRegional_iff {formula : Formula 0} (regional : formula.regional = true) (holds : IsHF term) :
    decideRegional formula term = true ↔ Membership.sat Env.closed formula term :=
  (decideOn_iff_regional (Region.withParts term holds) formula regional (Or.inr (withParts_partsClosed holds))
    (agrees_closed _) term holds (self_mem_zfParts term)).trans
    (sat_iff_extensional (Formula.forward_of_regional formula regional) holds).symm

/-! ## A certified decider for the front door -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv) in
/-- **The parts-region decider of the membership language**: the regional native types of hereditary terms, decided
on parts regions. The front door's canonical regions hold reachable states, not parts, so this is how it answers
splits (`askWith`). -/
def setDecider : Decider RelationEnv.empty membership where
  decide formula term :=
    if formula.regional && hereditary membership hfRule.category term then some (decideRegional formula term) else none
  exact := by
    intro formula term answer decided
    by_cases fit : (formula.regional && hereditary membership hfRule.category term) = true
    · rw [if_pos fit] at decided
      obtain rfl := Option.some.inj decided
      obtain ⟨regional, hereditaryTerm⟩ := Bool.and_eq_true_iff.mp fit
      exact (decideRegional_iff regional ((hereditary_iff _).mp hereditaryTerm)).symm
    · rw [if_neg fit] at decided
      cases decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
