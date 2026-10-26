import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExactMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExtensional
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDerivations
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# The hereditarily finite sets as a structure of their own

Forward native types look only at what a set reaches through its members, so they read the same among the
hereditary terms and among all ZF sets (`sat_iff_extensional`). The past modalities, the counting of predecessors and
the quantifiers over a type look at sets that contain a given one, or at all sets, and the ZF sets have far more of
those than the hereditary terms denote. Read among the hereditarily finite sets instead, every native type agrees:

- **The hereditarily finite sets** (`IsHFSet`): the ZF sets denoted by hereditary terms. They are exactly the
  members of `V_ω` (`isHFSet_iff_mem_vonNeumann`): a term of height `h` denotes a subset of `V_h`, and `V_n` is
  denoted by an iterated power-set term. They are closed under members, parts and one-element sets
  (`hfSets_generated`), so they carry the relations among them (`HFSets`).
- **Denotation is an exact morphism** from the hereditary terms onto them (`toHFSets`): a bounded morphism (`toZF`)
  that is onto, and whose image's predecessors come from predecessors, since a hereditary term steps to every
  hereditary term whose set is a member of its own.
- **So every native type of a hereditary term, read among the hereditary terms, is the same native type of its set,
  read among the hereditarily finite sets** (`sat_iff_hfSets`), past modalities and quantifiers over a type
  included: `3` contains `2`, nothing empty contains a set, and every hereditarily finite set is well founded.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **A hereditarily finite set**: a ZF set denoted by a hereditary term. -/
def IsHFSet (z : ZFSet.{0}) : Prop := ∃ term, IsHF term ∧ zfOf term = z

theorem isHFSet_of_member {term : Pattern} (holds : IsHF term) {z : ZFSet.{0}} (member : z ∈ zfOf term) : IsHFSet z := by
  obtain ⟨values, same, inside⟩ := hf_set holds
  rw [same, zfOf_set] at member
  obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp member
  exact ⟨value, inside value valueMember, rfl⟩

theorem isHFSet_of_subset {term : Pattern} (holds : IsHF term) {z : ZFSet.{0}} (within : z ⊆ zfOf term) :
    IsHFSet z := by
  classical
  obtain ⟨values, same, inside⟩ := hf_set holds
  rw [same, zfOf_set] at within
  refine ⟨set (values.filter fun value => zfOf value ∈ z),
    .members fun value member => inside value (List.mem_of_mem_filter member), ?_⟩
  rw [zfOf_set]
  apply ZFSet.ext
  intro other
  rw [mem_zfOfList]
  constructor
  · rintro ⟨value, member, rfl⟩
    simpa using (List.mem_filter.mp member).2
  · intro isMember
    obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp (within isMember)
    exact ⟨value, List.mem_filter.mpr ⟨valueMember, by simpa using isMember⟩, rfl⟩

/-! ## The hereditarily finite sets are `V_ω` -/

/-- **A hereditary term of height `h` denotes a subset of `V_h`.** -/
theorem zfOf_subset_vonNeumann : ∀ (term : Pattern), IsHF term →
    zfOf term ⊆ ZFSet.vonNeumann ((height term : ℕ) : Ordinal)
  | term, holds => by
    intro z member
    obtain ⟨values, same, inside⟩ := hf_set holds
    have member' : z ∈ zfOfList values := by
      rw [← zfOf_set, ← same]
      exact member
    obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp member'
    have inMembers : value ∈ membersOf term := by
      rw [same]
      exact valueMember
    have lower := height_lt_of_mem inMembers
    exact ZFSet.mem_vonNeumann'.mpr ⟨(height value : ℕ), by exact_mod_cast lower,
      zfOf_subset_vonNeumann value (inside value valueMember)⟩
termination_by term => height term
decreasing_by exact height_lt_of_mem inMembers

/-- The sets of the sublists of a list, as one set term: its power set. -/
theorem zfOf_sublists (values : List Pattern) :
    zfOf (set (values.sublists.map set)) = ZFSet.powerset (zfOf (set values)) := by
  classical
  apply ZFSet.ext
  intro y
  rw [ZFSet.mem_powerset, zfOf_set, mem_zfOfList, zfOf_set]
  constructor
  · rintro ⟨_, member, rfl⟩
    obtain ⟨list, sublist, rfl⟩ := List.mem_map.mp member
    intro w inside
    rw [zfOf_set] at inside
    obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp inside
    exact mem_zfOfList.mpr ⟨value, (List.mem_sublists.mp sublist).subset valueMember, rfl⟩
  · intro within
    refine ⟨set (values.filter fun value => zfOf value ∈ y),
      List.mem_map.mpr ⟨_, List.mem_sublists.mpr List.filter_sublist, rfl⟩, ?_⟩
    rw [zfOf_set]
    apply ZFSet.ext
    intro other
    rw [mem_zfOfList]
    constructor
    · rintro ⟨value, member, rfl⟩
      simpa using (List.mem_filter.mp member).2
    · intro isMember
      obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp (within isMember)
      exact ⟨value, List.mem_filter.mpr ⟨valueMember, by simpa using isMember⟩, rfl⟩

/-- **Each finite stage `V_n` is denoted by a hereditary term**: the empty set, then power sets. -/
theorem vonNeumann_denoted : ∀ n : ℕ, ∃ term, IsHF term ∧ zfOf term = ZFSet.vonNeumann (n : Ordinal)
  | 0 => by
    refine ⟨set [], Hereditary.members (fun _ member => nomatch member), ?_⟩
    rw [Nat.cast_zero, ZFSet.vonNeumann_zero, zfOf_set]
    rfl
  | n + 1 => by
    obtain ⟨term, holds, same⟩ := vonNeumann_denoted n
    refine ⟨set ((membersOf term).sublists.map set), .members fun value member => ?_, ?_⟩
    · obtain ⟨list, sublist, rfl⟩ := List.mem_map.mp member
      exact .members fun other otherMember =>
        hf_members holds other ((List.mem_sublists.mp sublist).subset otherMember)
    · rw [zfOf_sublists, ← hf_eq_set holds, same, Nat.cast_succ, ZFSet.vonNeumann_add_one]

/-- **The hereditarily finite sets are exactly the members of `V_ω`.** -/
theorem isHFSet_iff_mem_vonNeumann (z : ZFSet.{0}) : IsHFSet z ↔ z ∈ ZFSet.vonNeumann Ordinal.omega0 := by
  constructor
  · rintro ⟨term, holds, rfl⟩
    exact ZFSet.mem_vonNeumann'.mpr ⟨(height term : ℕ), Ordinal.natCast_lt_omega0 _, zfOf_subset_vonNeumann term holds⟩
  · intro member
    obtain ⟨stage, below, within⟩ := ZFSet.mem_vonNeumann'.mp member
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp below
    obtain ⟨term, holds, same⟩ := vonNeumann_denoted n
    exact isHFSet_of_subset holds (same ▸ within)

/-- **The hereditarily finite sets are closed** under members, parts and the members of one-element sets. -/
theorem hfSets_generated : extensional.Generated IsHFSet where
  step := by
    rintro _ _ _ ⟨term, holds, rfl⟩ ⟨-, member⟩
    exact isHFSet_of_member holds member
  built _ built := built.elim
  split := by
    rintro _ _ first second ⟨term, holds, rfl⟩ ⟨-, union⟩
    exact ⟨isHFSet_of_subset holds fun z member => union ▸ ZFSet.mem_union.mpr (Or.inl member),
      isHFSet_of_subset holds fun z member => union ▸ ZFSet.mem_union.mpr (Or.inr member)⟩
  single := by
    rintro _ _ member ⟨term, holds, rfl⟩ ⟨-, isSingle⟩
    exact isHFSet_of_member holds (by rw [isSingle]; exact ZFSet.mem_singleton.mpr rfl)
  body _ body := body.elim
  multiBody _ body := body.elim
  apply holds _ := holds

/-- The hereditarily finite sets with the relations among them. -/
abbrev HFSets := NativeStructure.restrict hfSets_generated

/-- **Denotation is an exact morphism** from the hereditary terms onto the hereditarily finite sets. -/
def toHFSets : ExactMorphism HFNative HFSets where
  map term := ⟨zfOf term.1, term.1, term.2, rfl⟩
  step stepped := toZF.step stepped
  built built := toZF.built built |>.elim
  split split := toZF.split split
  empty empty := toZF.empty empty
  single single := toZF.single single
  body body := toZF.body body
  multiBody body := toZF.multiBody body
  bound bound := toZF.bound bound
  typed typed := toZF.typed typed
  named named := toZF.named named
  stepBack {_ _ target'} step := by
    obtain ⟨target, stepped, same⟩ := toZF.stepBack step
    exact ⟨target, stepped, Subtype.ext same⟩
  builtBack built := built.elim
  splitBack {_ _ first' second'} split := by
    obtain ⟨first, second, isSplit, sameFirst, sameSecond⟩ := toZF.splitBack split
    exact ⟨first, second, isSplit, Subtype.ext sameFirst, Subtype.ext sameSecond⟩
  emptyBack empty := toZF.emptyBack empty
  singleBack {_ _ member'} single := by
    obtain ⟨member, isSingle, same⟩ := toZF.singleBack single
    exact ⟨member, isSingle, Subtype.ext same⟩
  bodyBack body := body.elim
  multiBodyBack body := body.elim
  boundBack bound := toZF.boundBack bound
  typedBack typed := toZF.typedBack typed
  namedBack named := toZF.namedBack named
  sameIff first second := toZF.sameIff first second
  surjective := by
    rintro ⟨_, term, holds, rfl⟩
    exact ⟨⟨term, holds⟩, rfl⟩
  previousBack {source' label target} step := by
    obtain ⟨labelled, member⟩ := step
    obtain ⟨term, holds, same⟩ := source'.2
    refine ⟨⟨term, holds⟩, step_label_iff.mpr ⟨labelled, (member_step_iff holds target.2).mpr ?_⟩,
      Subtype.ext same⟩
    rw [same]
    exact member
  applyMap {element inner} body := by
    obtain ⟨-, name, equivalent⟩ := body
    exact (hf_not_lambda (hf_of_equivalent element.2 equivalent)).elim

/-- **Every native type of a hereditary term, read among the hereditary terms, is the same native type of its set,
read among the hereditarily finite sets**, past modalities, counting of predecessors and quantifiers over a type
included. -/
theorem sat_iff_hfSets (formula : Formula 0) (term : {term // IsHF term}) :
    HFNative.sat Env.closed formula term ↔ HFSets.sat Env.closed formula (toHFSets.map term) :=
  toHFSets.sat_iff formula (fun index => index.elim0) term

/-! ## Past modalities and quantifiers over a type -/

theorem two_hf : IsHF two := (hereditary_iff _).mp (by decide)

theorem zero_hf : IsHF zero := (hereditary_iff _).mp (by decide)

/-- **`3` contains `2`**: a past modality, read among the hereditary terms. -/
theorem three_contains_two : HFNative.sat Env.closed (.sometimeBefore .any (.is three)) ⟨two, two_hf⟩ := by
  refine (sat_iff_hfSets _ ⟨two, two_hf⟩).mpr ⟨⟨zfOf three, three, three_holds, rfl⟩, ⟨trivial, ?_⟩, three_holds, rfl⟩
  change zfOf two ∈ zfOf (set [zero, one, two])
  rw [zfOf_set]
  exact mem_zfOfList.mpr ⟨two, by simp, rfl⟩

/-- **Nothing empty contains a set.** -/
theorem nothing_empty_contains : ¬ HFNative.sat Env.closed (.sometimeBefore .any (.empty .hashSet)) ⟨zero, zero_hf⟩ := by
  intro holds
  obtain ⟨previous, ⟨-, member⟩, -, isEmpty⟩ := (sat_iff_hfSets _ ⟨zero, zero_hf⟩).mp holds
  change zfOf zero ∈ previous.1 at member
  rw [show previous.1 = ∅ from isEmpty] at member
  exact ZFSet.notMem_empty _ member

/-- **Every hereditarily finite set is well founded**: a quantifier over the type, with a least fixed point inside. -/
theorem every_hf_wellFounded :
    HFNative.sat Env.closed (.everyOf (.base "Set") (.mu (.necessarily .any (.var 0)))) ⟨zero, zero_hf⟩ := by
  refine (sat_iff_hfSets _ ⟨zero, zero_hf⟩).mpr fun witness _ closed isClosed => ?_
  suffices all : ∀ z : ZFSet.{0}, ∀ holds : IsHFSet z, (⟨z, holds⟩ : {z // IsHFSet z}) ∈ closed from
    all witness.1 witness.2
  intro z
  induction z using ZFSet.inductionOn with
  | h z ih =>
    intro holds
    refine isClosed _ fun next step => ?_
    obtain ⟨-, member⟩ := step
    exact ih next.1 member next.2

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
