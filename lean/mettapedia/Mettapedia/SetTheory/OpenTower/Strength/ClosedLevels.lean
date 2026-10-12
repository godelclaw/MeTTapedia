import Mettapedia.SetTheory.OpenTower.InternalTower

/-!
# Closed sets are levels of the von Neumann hierarchy

A closed set (`ZFSetUniverseClosure.Closed`: transitive, closed under union, power set and
replacement by arbitrary functions of the host) is the level of the von Neumann hierarchy at
its own rank (`closed_eq_vonNeumann`). The proof uses no hypothesis on cardinals: inside a
closed set the level at the rank of a member is a member (`vonNeumann_rank_mem`), by induction
on membership, replacement along the members and one union.

**The closed sets of one level are linearly ordered.** Two levels of the hierarchy are
comparable, so any two closed sets are related by membership or are equal
(`closed_trichotomy`), and one includes the other (`closed_subset_total`). Among closed sets,
membership is proper inclusion (`closed_mem_iff_ssubset`), and membership is a well-order
(`closedSets_isWellOrder`). So the class of stages of a level is a chain: directedness of the
stages is a consequence of linearity, and a tower of stages differs from the class of all
stages by its length only. Indexed by the ordinals of the level, the tower of least closed
sets reaches every set (`ordinalStage_cofinal`).

**Controls.**
* Closure is used: two transitive sets need not be comparable
  (`exists_incomparable_transitive`).
* Classical logic is used, and cannot be avoided: for the relational closure, which mentions
  no image, comparability of one closed set holding `∅` with every closed set decides every
  proposition (`em_of_closedRel_trichotomy`). That statement is free of the host's choice; the
  ones about `Closed` are not, because `Closed` itself mentions the replacement operation.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open InternalTower
open scoped ZFSet

universe u

variable {U V : ZFSet.{u}}

/-! ## Every closed set is a level -/

/-- Inside a closed set, the level of the hierarchy at the rank of a member is a member: the
level at the rank of `x` is the union of the power sets of the levels at the ranks of the
members of `x`, and those are collected by replacement along `x`. -/
theorem vonNeumann_rank_mem (hU : Closed U) : ∀ x : ZFSet.{u}, x ∈ U → V_ x.rank ∈ U := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    have values : ∀ y ∈ x, ZFSet.powerset (V_ y.rank) ∈ U := fun y hy =>
      hU.power_mem (ih y hy (hU.transitive x hx hy))
    have union := hU.union_mem
      (hU.replacement_mem hx (fun y => ZFSet.powerset (V_ y.rank)) values)
    have equal :
        ZFSet.sUnion (replacement x fun y => ZFSet.powerset (V_ y.rank)) = V_ x.rank := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_sUnion, ZFSet.mem_vonNeumann, ZFSet.lt_rank_iff]
      constructor
      · rintro ⟨w, hw, hz⟩
        obtain ⟨y, hy, rfl⟩ := mem_replacement.mp hw
        exact ⟨y, hy, ZFSet.subset_vonNeumann.mp (ZFSet.mem_powerset.mp hz)⟩
      · rintro ⟨y, hy, hzy⟩
        exact ⟨_, mem_replacement.mpr ⟨y, hy, rfl⟩,
          ZFSet.mem_powerset.mpr (ZFSet.subset_vonNeumann.mpr hzy)⟩
    rwa [equal] at union

/-- **A closed set is the level of the von Neumann hierarchy at its own rank.** -/
theorem closed_eq_vonNeumann (hU : Closed U) : U = V_ U.rank := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact ZFSet.subset_vonNeumann_self U hz
  · intro hz
    obtain ⟨x, hx, hzx⟩ := ZFSet.lt_rank_iff.mp (ZFSet.mem_vonNeumann.mp hz)
    exact hU.subset_mem (vonNeumann_rank_mem hU x hx) (ZFSet.subset_vonNeumann.mpr hzx)

/-! ## The closed sets of one level form a chain -/

/-- **Trichotomy.** Two closed sets are related by membership or are equal. -/
theorem closed_trichotomy (hU : Closed U) (hV : Closed V) : U ∈ V ∨ U = V ∨ V ∈ U := by
  have eU := closed_eq_vonNeumann hU
  have eV := closed_eq_vonNeumann hV
  rcases lt_trichotomy U.rank V.rank with h | h | h
  · left
    rw [eU, eV]
    exact ZFSet.vonNeumann_mem_vonNeumann_iff.mpr h
  · right; left
    rw [eU, eV, h]
  · right; right
    rw [eU, eV]
    exact ZFSet.vonNeumann_mem_vonNeumann_iff.mpr h

/-- **The closed sets of one level are linearly ordered by inclusion.** -/
theorem closed_subset_total (hU : Closed U) (hV : Closed V) : U ⊆ V ∨ V ⊆ U := by
  rcases closed_trichotomy hU hV with h | h | h
  · exact Or.inl (closed_subset_of_mem hV h)
  · exact Or.inl (h ▸ fun _ hx => hx)
  · exact Or.inr (closed_subset_of_mem hU h)

/-- Among closed sets, membership is proper inclusion. -/
theorem closed_mem_iff_ssubset (hU : Closed U) (hV : Closed V) : U ∈ V ↔ U ⊆ V ∧ U ≠ V := by
  constructor
  · intro h
    refine ⟨closed_subset_of_mem hV h, fun equal => ?_⟩
    rw [equal] at h
    exact ZFSet.mem_irrefl V h
  · rintro ⟨below, different⟩
    rcases closed_trichotomy hU hV with h | h | h
    · exact h
    · exact absurd h different
    · exact absurd (below h) (ZFSet.mem_irrefl V)

/-- **The closed sets of one level are well-ordered by membership.** -/
theorem closedSets_isWellOrder :
    IsWellOrder {U : ZFSet.{u} // Closed U} (fun U V => U.1 ∈ V.1) where
  wf := InvImage.wf (fun U : {U : ZFSet.{u} // Closed U} => U.1) ZFSet.mem_wf
  trichotomous U V notBelow notAbove := by
    rcases closed_trichotomy U.2 V.2 with h | h | h
    · exact absurd h notBelow
    · exact Subtype.ext h
    · exact absurd h notAbove

/-- **The tower of least closed sets indexed by the ordinals of the level reaches every set.**
Its stages are levels of the hierarchy of strictly increasing rank, so the stage at an ordinal
has at least that rank. -/
theorem ordinalStage_cofinal (h : CofinalInaccessibles.{u}) (N x : ZFSet.{u}) :
    ∃ α : Ordinal.{u}, x ∈ ordinalStage h N α := by
  have increasing : StrictMono fun α : Ordinal.{u} => (ordinalStage h N α).rank :=
    fun _ _ below => ZFSet.rank_lt_of_mem (ordinalStage_mem_of_lt h N below)
  refine ⟨Order.succ x.rank, ?_⟩
  rw [closed_eq_vonNeumann (ordinalStage_closed h N (Order.succ x.rank)), ZFSet.mem_vonNeumann]
  exact (Order.lt_succ x.rank).trans_le increasing.le_apply

/-! ## Controls -/

private theorem empty_ne_singleton_empty : (∅ : ZFSet.{u}) ≠ {∅} := by
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

/-- **Closure is used.** The transitive sets `{∅, {∅}, {{∅}}}` and `{∅, {∅}, {∅, {∅}}}` are not
comparable by inclusion. -/
theorem exists_incomparable_transitive :
    ∃ A B : ZFSet.{u}, A.IsTransitive ∧ B.IsTransitive ∧ ¬ A ⊆ B ∧ ¬ B ⊆ A := by
  refine ⟨{∅, {∅}, {{∅}}}, {∅, {∅}, {∅, {∅}}}, ?_, ?_, ?_, ?_⟩
  · intro y hy z hz
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact absurd hz (ZFSet.notMem_empty z)
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · exact Or.inr (Or.inl (ZFSet.mem_singleton.mp hz))
  · intro y hy z hz
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact absurd hz (ZFSet.notMem_empty z)
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · rcases ZFSet.mem_pair.mp hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  · intro below
    have member : ({{∅}} : ZFSet.{u}) ∈ ({∅, {∅}, {∅, {∅}}} : ZFSet.{u}) :=
      below (by simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, or_true])
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at member
    rcases member with h | h | h
    · have inside : ({∅} : ZFSet.{u}) ∈ ({{∅}} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
      rw [h] at inside
      exact ZFSet.notMem_empty _ inside
    · have inside : ({∅} : ZFSet.{u}) ∈ ({{∅}} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
      rw [h] at inside
      exact empty_ne_singleton_empty (ZFSet.mem_singleton.mp inside).symm
    · have inside : (∅ : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
      rw [← h] at inside
      exact empty_ne_singleton_empty (ZFSet.mem_singleton.mp inside)
  · intro below
    have member : ({∅, {∅}} : ZFSet.{u}) ∈ ({∅, {∅}, {{∅}}} : ZFSet.{u}) :=
      below (by simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, or_true])
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at member
    rcases member with h | h | h
    · have inside : (∅ : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
      rw [h] at inside
      exact ZFSet.notMem_empty _ inside
    · have inside : ({∅} : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inr rfl)
      rw [h] at inside
      exact empty_ne_singleton_empty (ZFSet.mem_singleton.mp inside).symm
    · have inside : (∅ : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
      rw [h] at inside
      exact empty_ne_singleton_empty (ZFSet.mem_singleton.mp inside)

/-- **Comparability of closed sets decides every proposition.** For the relational closure,
which mentions no image: if a closed set holding `∅` is comparable with every closed set, then
every proposition holds or fails. The closed set compared is the part of the given one cut out
by the proposition. No use is made of the host's choice. -/
theorem em_of_closedRel_trichotomy {W : ZFSet.{u}} (hW : ClosedRel W)
    (hEmpty : (∅ : ZFSet.{u}) ∈ W)
    (comparable : ∀ U : ZFSet.{u}, ClosedRel U → U ∈ W ∨ U = W ∨ W ∈ U) (p : Prop) :
    p ∨ ¬ p := by
  have closed : ClosedRel (ZFSet.sep (fun _ => p) W) := {
    transitive := fun y hy x hxy =>
      ZFSet.mem_sep.mpr ⟨hW.transitive y (ZFSet.mem_sep.mp hy).1 hxy, (ZFSet.mem_sep.mp hy).2⟩
    union_mem := fun ha =>
      ZFSet.mem_sep.mpr ⟨hW.union_mem (ZFSet.mem_sep.mp ha).1, (ZFSet.mem_sep.mp ha).2⟩
    power_mem := fun ha =>
      ZFSet.mem_sep.mpr ⟨hW.power_mem (ZFSet.mem_sep.mp ha).1, (ZFSet.mem_sep.mp ha).2⟩
    image_mem := fun ha hb image =>
      ZFSet.mem_sep.mpr ⟨hW.image_mem (ZFSet.mem_sep.mp ha).1
        (fun y hy => (ZFSet.mem_sep.mp (hb hy)).1) image, (ZFSet.mem_sep.mp ha).2⟩ }
  rcases comparable _ closed with h | h | h
  · right
    intro hp
    have same : ZFSet.sep (fun _ => p) W = W :=
      ZFSet.ext fun z => ⟨fun hz => (ZFSet.mem_sep.mp hz).1, fun hz => ZFSet.mem_sep.mpr ⟨hz, hp⟩⟩
    rw [same] at h
    exact ZFSet.mem_irrefl W h
  · left
    have member : (∅ : ZFSet.{u}) ∈ ZFSet.sep (fun _ => p) W := by
      rw [h]
      exact hEmpty
    exact (ZFSet.mem_sep.mp member).2
  · left
    exact (ZFSet.mem_sep.mp h).2

#print axioms vonNeumann_rank_mem
#print axioms closed_eq_vonNeumann
#print axioms closed_trichotomy
#print axioms closed_subset_total
#print axioms closed_mem_iff_ssubset
#print axioms closedSets_isWellOrder
#print axioms ordinalStage_cofinal
#print axioms exists_incomparable_transitive
#print axioms em_of_closedRel_trichotomy

end Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
