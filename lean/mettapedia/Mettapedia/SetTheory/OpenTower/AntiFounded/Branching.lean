import Mettapedia.SetTheory.OpenTower.AntiFounded.ClosedStages

/-!
# The anti-founded universes `B_κ`: hereditarily fewer than `κ` members

In a well-founded universe the size of a set is measured by its rank. A hyperset can have no
rank (`Ω = {Ω}`), so the measure here is *branching*: a hyperset has fewer than `κ` members
(`SmallMembers κ`) when a family indexed by a type of fewer than `κ` elements has exactly its
members as values, and it is *hereditarily* so (`HerSmall κ`) when every hyperset reached from
it by membership (`Below`) has fewer than `κ` members. `Ω` has one member and is hereditarily
so; the finite von Neumann ordinals are hereditarily finite; `ω` is not.

**The hereditarily small hypersets form a hyperset.** A hereditarily small hyperset is the
decoration of its tree of membership paths, a graph on the lists over a type of `κ` elements
(`exists_picture`). So separating the hyperset of all such graphs gives `branching κ`, whose
members are exactly the hereditarily small hypersets (`mem_branching`). For each `κ` this is a
set; no large-cardinal hypothesis is used.

**Which `branching κ` are closed stages.** `branching κ` is a closed stage exactly when `κ`
is `0`, `ℵ₀`, or inaccessible (`hclosed_branching_iff`): the same three cases as the closed sets
of `ZFSet` (`InaccessibleLevels.closed_iff`). Union needs regularity of `κ`, power set needs
`κ` to be a strong limit, replacement needs nothing. When it is closed and `κ ≠ 0`, its
well-founded part is exactly `V_κ` (`toZFSet_branching`).

**Controls.** `branching 0` is empty (`branching_zero`). `Ω` is a member of `branching ℵ₀`
(`quineAtom_mem_branching`), and the hyperset of `V_ω` is included in it but is not a member of
it (`ofZFSet_vonNeumann_omega_notMem_branching`): it has infinitely many members. For a finite
`κ ≥ 1`, `branching κ` is not closed (`hclosed_branching_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.SetTheory.OpenTower.Strength
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-! ## Small and hereditarily small hypersets -/

/-- `x` has fewer than `κ` members: a family indexed by a type of fewer than `κ` elements has
exactly the members of `x` as values. -/
def SmallMembers (κ : Cardinal.{u}) (x : HSet.{u}) : Prop :=
  ∃ (ι : Type u) (g : ι → HSet.{u}), #ι < κ ∧ ∀ y, y ∈ x ↔ ∃ i, g i = y

/-- `z` is reached from `x` by finitely many membership steps. -/
def Below (x z : HSet.{u}) : Prop :=
  Relation.ReflTransGen (fun a b : HSet.{u} => b ∈ a) x z

/-- Every hyperset reached from `x` by membership has fewer than `κ` members. -/
def HerSmall (κ : Cardinal.{u}) (x : HSet.{u}) : Prop :=
  ∀ z, Below x z → SmallMembers κ z

variable {κ μ : Cardinal.{u}} {x y z : HSet.{u}}

theorem SmallMembers.mono (h : κ ≤ μ) (hx : SmallMembers κ x) : SmallMembers μ x :=
  let ⟨ι, g, hι, hg⟩ := hx
  ⟨ι, g, hι.trans_le h, hg⟩

theorem HerSmall.mono (h : κ ≤ μ) (hx : HerSmall κ x) : HerSmall μ x :=
  fun z hz => (hx z hz).mono h

theorem HerSmall.smallMembers (hx : HerSmall κ x) : SmallMembers κ x :=
  hx x .refl

theorem HerSmall.mem (hx : HerSmall κ x) (hy : y ∈ x) : HerSmall κ y :=
  fun z hz => hx z (.head hy hz)

/-- A hyperset is hereditarily small when it has few members and its members are hereditarily
small. -/
theorem herSmall_iff : HerSmall κ x ↔ SmallMembers κ x ∧ ∀ y ∈ x, HerSmall κ y := by
  constructor
  · exact fun h => ⟨h.smallMembers, fun y hy => h.mem hy⟩
  · rintro ⟨hs, hm⟩ z hz
    rcases Relation.ReflTransGen.cases_head hz with rfl | ⟨y, hy, hyz⟩
    · exact hs
    · exact hm y hy z hyz

/-- Fewer members than a member's subsets: a subset of `x` has at most the members of `x`. -/
theorem SmallMembers.subset (hx : SmallMembers κ x) (hyx : y ⊆ x) : SmallMembers κ y := by
  obtain ⟨ι, g, hι, hg⟩ := hx
  refine ⟨{i // g i ∈ y}, fun i => g i.1, (mk_subtype_le _).trans_lt hι, fun w => ?_⟩
  constructor
  · intro hw
    obtain ⟨i, rfl⟩ := (hg w).mp (HSet.subset_iff.mp hyx hw)
    exact ⟨⟨i, hw⟩, rfl⟩
  · rintro ⟨⟨i, hi⟩, rfl⟩
    exact hi

/-- The values of a function on the members of `a` are at most as many as the members. -/
theorem SmallMembers.image {a b : HSet.{u}} (ha : SmallMembers κ a) {f : HSet.{u} → HSet.{u}}
    (hb : ∀ y, y ∈ b ↔ ∃ x ∈ a, f x = y) : SmallMembers κ b := by
  obtain ⟨ι, g, hι, hg⟩ := ha
  refine ⟨ι, fun i => f (g i), hι, fun y => ?_⟩
  rw [hb]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := (hg x).mp hx
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨g i, (hg _).mpr ⟨i, rfl⟩, rfl⟩

/-- **Union needs regularity.** Fewer than `κ` members, each with fewer than `κ` members, have
fewer than `κ` members together when `κ` is regular. -/
theorem SmallMembers.sUnion (hreg : κ.IsRegular) (hx : SmallMembers κ x)
    (hm : ∀ y ∈ x, SmallMembers κ y) : SmallMembers κ (HSet.sUnion x) := by
  obtain ⟨ι, g, hι, hg⟩ := hx
  have hgi : ∀ i, SmallMembers κ (g i) := fun i => hm _ ((hg _).mpr ⟨i, rfl⟩)
  choose ι' g' hι' hg' using hgi
  refine ⟨Σ i, ι' i, fun p => g' p.1 p.2, ?_, fun y => ?_⟩
  · rw [mk_sigma]
    exact sum_lt_of_isRegular hreg hι hι'
  · rw [HSet.mem_sUnion]
    constructor
    · rintro ⟨w, hw, hyw⟩
      obtain ⟨i, rfl⟩ := (hg w).mp hw
      obtain ⟨j, rfl⟩ := (hg' i _).mp hyw
      exact ⟨⟨i, j⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨g i, (hg _).mpr ⟨i, rfl⟩, (hg' i _).mpr ⟨j, rfl⟩⟩

/-- **Power set needs a strong limit.** The subsets of a hyperset with fewer than `κ` members
are fewer than `κ` when `2 ^ μ < κ` for every `μ < κ`. -/
theorem SmallMembers.powerset (hlim : κ.IsStrongLimit) (hx : SmallMembers κ x) :
    SmallMembers κ (HSet.powerset x) := by
  obtain ⟨ι, g, hι, hg⟩ := hx
  refine ⟨Set ι, fun S => HSet.sep (fun y => ∃ i ∈ S, g i = y) x, ?_, fun y => ?_⟩
  · rw [mk_set]
    exact hlim.isStrongPrelimit hι
  · rw [HSet.mem_powerset]
    constructor
    · intro hy
      refine ⟨{i | g i ∈ y}, ?_⟩
      ext w
      rw [HSet.mem_sep]
      constructor
      · rintro ⟨_, i, hi, rfl⟩
        exact hi
      · intro hw
        have hwx := HSet.subset_iff.mp hy hw
        obtain ⟨i, rfl⟩ := (hg w).mp hwx
        exact ⟨hwx, i, hw, rfl⟩
    · rintro ⟨S, rfl⟩
      exact HSet.subset_iff.mpr fun w hw => (HSet.mem_sep.mp hw).1

/-! ## A hereditarily small hyperset is pictured on lists over `κ` -/

/-- The members of a hyperset with fewer than `κ` members, listed partially by a type of `κ`
elements, at fewer than `κ` places. -/
theorem SmallMembers.exists_enum (h : SmallMembers κ x) :
    ∃ e : κ.ord.ToType → Option HSet.{u},
      (∀ y, y ∈ x ↔ ∃ t, e t = some y) ∧ #{t // e t ≠ none} < κ := by
  classical
  obtain ⟨ι, g, hι, hg⟩ := h
  have size : #ι ≤ #κ.ord.ToType := by
    rw [mk_ord_toType]
    exact hι.le
  obtain ⟨emb⟩ := (Cardinal.le_def _ _).mp size
  refine ⟨fun t => if h : ∃ i, emb i = t then some (g h.choose) else none, fun y => ?_, ?_⟩
  swap
  · have hit : ∀ t : {t // (if h : ∃ i, emb i = t then some (g h.choose) else none) ≠ none},
        ∃ i, emb i = t.1 := by
      rintro ⟨t, ht⟩
      by_contra none
      exact ht (dif_neg none)
    choose φ hφ using hit
    have injective : Function.Injective φ := fun t t' e =>
      Subtype.ext ((hφ t).symm.trans ((congrArg emb e).trans (hφ t')))
    exact (mk_le_of_injective injective).trans_lt hι
  rw [hg]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨emb i, ?_⟩
    have h : ∃ i', emb i' = emb i := ⟨i, rfl⟩
    simp only [dif_pos h, emb.injective h.choose_spec]
  · rintro ⟨t, ht⟩
    by_cases h : ∃ i, emb i = t
    · simp only [dif_pos h] at ht
      exact ⟨_, Option.some.inj ht⟩
    · simp only [dif_neg h] at ht
      cases ht

section Unfolding

variable (κ : Cardinal.{u}) (x : HSet.{u})

/-- A chosen partial listing of the members of a hyperset with fewer than `κ` members. -/
noncomputable def enumOf (z : HSet.{u}) : κ.ord.ToType → Option HSet.{u} := by
  classical
  exact if h : SmallMembers κ z then Classical.choose h.exists_enum else fun _ => none

theorem enumOf_spec {z : HSet.{u}} (h : SmallMembers κ z) :
    ∀ y, y ∈ z ↔ ∃ t, enumOf κ z t = some y := by
  classical
  simp only [enumOf, dif_pos h]
  exact (Classical.choose_spec h.exists_enum).1

/-- The listing names a member at fewer than `κ` places. -/
theorem enumOf_support {z : HSet.{u}} (h : SmallMembers κ z) :
    #{t // enumOf κ z t ≠ none} < κ := by
  classical
  simp only [enumOf, dif_pos h]
  exact (Classical.choose_spec h.exists_enum).2

theorem enumOf_eq_none {z : HSet.{u}} (h : ¬ SmallMembers κ z) (t : κ.ord.ToType) :
    enumOf κ z t = none := by
  classical
  simp only [enumOf, dif_neg h]

/-- The hyperset at the end of a membership path from `x`, the path read from its last step. -/
noncomputable def unfoldValue : List κ.ord.ToType → Option HSet.{u}
  | [] => some x
  | t :: l => (unfoldValue l).bind fun z => enumOf κ z t

/-- The tree of membership paths: a path steps to its extensions that still name a member. -/
def unfoldEdge (l l' : List κ.ord.ToType) : Prop :=
  ∃ t, l' = t :: l ∧ unfoldValue κ x l' ≠ none

/-- Every hyperset at the end of a path is reached from `x` by membership. -/
theorem below_of_unfoldValue :
    ∀ {l : List κ.ord.ToType} {z : HSet.{u}}, unfoldValue κ x l = some z → Below x z
  | [], z, h => by
    have equal : x = z := Option.some.inj h
    subst equal
    exact .refl
  | t :: l, z, h => by
    obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.mp h
    have below := below_of_unfoldValue hw
    by_cases hs : SmallMembers κ w
    · exact below.tail ((enumOf_spec κ hs z).mpr ⟨t, hz⟩)
    · rw [enumOf_eq_none κ hs] at hz
      cases hz

/-- The ends of the paths decorate the tree of paths. -/
theorem isDecoration_unfold (hx : HerSmall κ x) :
    HSet.IsDecoration (unfoldEdge κ x) fun l => (unfoldValue κ x l).getD ∅ := by
  intro l y
  show y ∈ (unfoldValue κ x l).getD ∅ ↔
    ∃ l', unfoldEdge κ x l l' ∧ (unfoldValue κ x l').getD ∅ = y
  cases hl : unfoldValue κ x l with
  | none =>
    rw [Option.getD_none]
    constructor
    · intro h
      exact absurd h (HSet.notMem_empty y)
    · rintro ⟨l', ⟨t, rfl, hne⟩, _⟩
      exact absurd (by simp only [unfoldValue, hl, Option.bind_none]) hne
  | some z =>
    rw [Option.getD_some]
    have hs : SmallMembers κ z := hx z (below_of_unfoldValue κ x hl)
    have step : ∀ t, unfoldValue κ x (t :: l) = enumOf κ z t := fun t => by
      simp only [unfoldValue, hl, Option.bind_some]
    rw [enumOf_spec κ hs]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t :: l, ⟨t, rfl, ?_⟩, ?_⟩
      · rw [step, ht]
        exact Option.some_ne_none y
      · rw [step, ht, Option.getD_some]
    · rintro ⟨l', ⟨t, rfl, hne⟩, rfl⟩
      rw [step] at hne ⊢
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
      exact ⟨t, by rw [hw, Option.getD_some]⟩

/-- **A hereditarily small hyperset is pictured on the lists over a type of `κ` elements.** -/
theorem exists_picture (hx : HerSmall κ x) :
    ∃ r : List κ.ord.ToType → List κ.ord.ToType → Prop, HSet.decorate r [] = x := by
  refine ⟨unfoldEdge κ x, ?_⟩
  have equal := congrFun (isDecoration_unfold κ x hx).eq_decorate []
  rw [← equal]
  rfl

end Unfolding

/-! ## The hyperset `B_κ` -/

/-- `B_κ`: the hyperset of the hereditarily small hypersets, cut out of the pictures on the
lists over a type of `κ` elements. -/
noncomputable def branching (κ : Cardinal.{u}) : HSet.{u} :=
  HSet.sep (HerSmall κ)
    (HSet.range fun r : List κ.ord.ToType → List κ.ord.ToType → Prop =>
      AccessiblePointedGraph.generated r [])

/-- **The members of `B_κ` are exactly the hereditarily small hypersets.** -/
theorem mem_branching : y ∈ branching κ ↔ HerSmall κ y := by
  rw [branching, HSet.mem_sep, HSet.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨r, hr⟩ := exists_picture κ y h
    exact ⟨⟨r, hr⟩, h⟩

theorem branching_mono (h : κ ≤ μ) : branching κ ⊆ branching μ :=
  HSet.subset_iff.mpr fun _ hy => mem_branching.mpr ((mem_branching.mp hy).mono h)

/-- No hyperset has fewer than `0` members. -/
theorem not_smallMembers_zero (x : HSet.{u}) : ¬ SmallMembers 0 x :=
  fun ⟨_, _, hι, _⟩ => lt_irrefl _ (zero_le.trans_lt hι)

theorem branching_zero : branching (0 : Cardinal.{u}) = ∅ :=
  HSet.eq_empty_iff.mpr fun _ hy =>
    not_smallMembers_zero _ (mem_branching.mp hy).smallMembers

/-- The hyperset with no members has fewer than any nonzero number of members. -/
theorem smallMembers_empty (hκ : κ ≠ 0) : SmallMembers κ (∅ : HSet.{u}) :=
  ⟨PEmpty, PEmpty.elim, by rw [mk_pempty]; exact pos_iff_ne_zero.mpr hκ,
    fun y => ⟨fun h => absurd h (HSet.notMem_empty y), fun ⟨i, _⟩ => i.elim⟩⟩

theorem herSmall_empty (hκ : κ ≠ 0) : HerSmall κ (∅ : HSet.{u}) := by
  rw [herSmall_iff]
  exact ⟨smallMembers_empty hκ, fun y hy => absurd hy (HSet.notMem_empty y)⟩

/-! ## Closure -/

/-- **`B_κ` is a closed stage when `κ` is a regular strong limit.** -/
theorem hclosed_branching_of_isRegular (hreg : κ.IsRegular) (hlim : κ.IsStrongLimit) :
    HClosed (branching κ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact mem_branching.mpr ((mem_branching.mp hx).mem hy)
  · intro x hx
    have hx := mem_branching.mp hx
    refine mem_branching.mpr (herSmall_iff.mpr ⟨?_, fun y hy => ?_⟩)
    · exact hx.smallMembers.sUnion hreg fun y hy => (hx.mem hy).smallMembers
    · obtain ⟨w, hw, hyw⟩ := HSet.mem_sUnion.mp hy
      exact (hx.mem hw).mem hyw
  · intro x hx
    have hx := mem_branching.mp hx
    refine mem_branching.mpr (herSmall_iff.mpr ⟨hx.smallMembers.powerset hlim, fun y hy => ?_⟩)
    have hyx := HSet.mem_powerset.mp hy
    exact herSmall_iff.mpr ⟨hx.smallMembers.subset hyx,
      fun w hw => hx.mem (HSet.subset_iff.mp hyx hw)⟩
  · rintro a b ha hb ⟨f, hf⟩
    exact mem_branching.mpr (herSmall_iff.mpr ⟨(mem_branching.mp ha).smallMembers.image hf,
      fun y hy => mem_branching.mp (hb hy)⟩)

/-! ## The well-founded hypersets that are small -/

/-- A set has fewer than `κ` members exactly when its hyperset does. -/
theorem smallMembers_ofZFSet_iff {w : ZFSet.{u}} :
    SmallMembers κ (HSet.ofZFSet w) ↔ w.card < κ := by
  constructor
  · rintro ⟨ι, g, hι, hg⟩
    have hit : ∀ s : Shrink.{u} w, ∃ i, g i = HSet.ofZFSet ((equivShrink w).symm s).1 :=
      fun s => (hg _).mp (HSet.ofZFSet_mem_ofZFSet_iff.mpr ((equivShrink w).symm s).2)
    choose φ hφ using hit
    have injective : Function.Injective φ := by
      intro s s' equal
      have same := (hφ s).symm.trans ((congrArg g equal).trans (hφ s'))
      exact (equivShrink w).symm.injective (Subtype.ext (HSet.ofZFSet_injective same))
    exact (mk_le_of_injective injective).trans_lt hι
  · intro hw
    refine ⟨Shrink.{u} w, fun s => HSet.ofZFSet ((equivShrink w).symm s).1, hw, fun y => ?_⟩
    rw [HSet.mem_ofZFSet_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨equivShrink w ⟨v, hv⟩, by simp only [Equiv.symm_apply_apply]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ((equivShrink w).symm s).2, rfl⟩

/-- Below the hyperset of an ordinal there are only the hypersets of smaller ordinals. -/
theorem below_ofZFSet_toZFSet {α : Ordinal.{u}} {z : HSet.{u}}
    (h : Below (HSet.ofZFSet α.toZFSet) z) : ∃ β ≤ α, z = HSet.ofZFSet β.toZFSet := by
  induction h with
  | refl => exact ⟨α, le_rfl, rfl⟩
  | tail _ hmem ih =>
    obtain ⟨β, hβ, rfl⟩ := ih
    obtain ⟨w, hw, rfl⟩ := HSet.mem_ofZFSet_iff.mp hmem
    obtain ⟨γ, hγ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hw
    exact ⟨γ, hγ.le.trans hβ, rfl⟩

/-- The hyperset of an ordinal with fewer than `κ` predecessors is hereditarily small. -/
theorem herSmall_ofZFSet_toZFSet {α : Ordinal.{u}} (h : α.card < κ) :
    HerSmall κ (HSet.ofZFSet α.toZFSet) := by
  intro z hz
  obtain ⟨β, hβ, rfl⟩ := below_ofZFSet_toZFSet hz
  rw [smallMembers_ofZFSet_iff, Ordinal.card_toZFSet]
  exact (Ordinal.card_le_card hβ).trans_lt h

/-! ## Which `B_κ` are closed -/

/-- When `B_κ` is a closed stage, the rank of its well-founded part has `κ` elements. -/
theorem rank_card_toZFSet_branching (h : HClosed (branching κ)) :
    (HSet.toZFSet (branching κ)).rank.card = κ := by
  have hW := h.closed_toZFSet
  apply le_antisymm
  · by_contra above
    have member := toZFSet_ord_mem hW (not_le.mp above)
    rw [mem_toZFSet_iff, mem_branching] at member
    have fewer := smallMembers_ofZFSet_iff.mp member.smallMembers
    rw [Ordinal.card_toZFSet, card_ord] at fewer
    exact lt_irrefl _ fewer
  · by_contra below
    set ν := (HSet.toZFSet (branching κ)).rank.card
    have hν : ν < κ := not_le.mp below
    have member : ν.ord.toZFSet ∈ HSet.toZFSet (branching κ) := by
      rw [mem_toZFSet_iff, mem_branching]
      exact herSmall_ofZFSet_toZFSet (by rw [card_ord]; exact hν)
    have fewer := card_lt_card_rank hW member
    rw [Ordinal.card_toZFSet, card_ord] at fewer
    exact lt_irrefl _ fewer

/-- **`B_κ` is a closed stage exactly when `κ` is `0`, `ℵ₀` or inaccessible.** -/
theorem hclosed_branching_iff :
    HClosed (branching κ) ↔ κ = 0 ∨ κ = ℵ₀ ∨ κ.IsInaccessible := by
  constructor
  · intro h
    by_cases hκ : κ = 0
    · exact Or.inl hκ
    right
    have hW := h.closed_toZFSet
    have hEmpty : (∅ : ZFSet.{u}) ∈ HSet.toZFSet (branching κ) := by
      rw [mem_toZFSet_iff, HSet.ofZFSet_empty, mem_branching]
      exact herSmall_empty hκ
    have key := rank_card_toZFSet_branching h
    rcases (omega_le_rank hW hEmpty).eq_or_lt with same | above
    · left
      rw [← key, ← same, Ordinal.card_omega0]
    · right
      rw [← key]
      exact isInaccessible_card_rank hW above
  · rintro (rfl | rfl | hκ)
    · rw [branching_zero]
      exact hclosed_empty
    · exact hclosed_branching_of_isRegular isRegular_aleph0 isStrongLimit_aleph0
    · exact hclosed_branching_of_isRegular hκ.isRegular hκ.isStrongLimit

/-- **The well-founded part of a closed `B_κ` is `V_κ`**: for `κ` equal to `0`, `ℵ₀` or an
inaccessible cardinal. -/
theorem toZFSet_branching (h : HClosed (branching κ)) :
    HSet.toZFSet (branching κ) = V_ κ.ord := by
  have hW := h.closed_toZFSet
  rw [closed_eq_vonNeumann hW, ← ord_card_rank hW, rank_card_toZFSet_branching h]

/-! ## Controls -/

theorem below_quineAtom {z : HSet.{u}} (h : Below HSet.quineAtom z) : z = HSet.quineAtom := by
  induction h with
  | refl => rfl
  | tail _ hmem ih =>
    subst ih
    exact HSet.mem_quineAtom.mp hmem

/-- `Ω` has one member. -/
theorem smallMembers_quineAtom (hκ : 1 < κ) : SmallMembers κ HSet.quineAtom.{u} :=
  ⟨PUnit, fun _ => HSet.quineAtom, by rw [mk_punit]; exact hκ,
    fun y => ⟨fun h => ⟨PUnit.unit, (HSet.mem_quineAtom.mp h).symm⟩,
      fun ⟨_, h⟩ => h ▸ HSet.quineAtom_mem_self⟩⟩

/-- `Ω` is a member of `B_ℵ₀`. -/
theorem quineAtom_mem_branching : HSet.quineAtom.{u} ∈ branching ℵ₀ :=
  mem_branching.mpr fun z hz => by
    rw [below_quineAtom hz]
    exact smallMembers_quineAtom one_lt_aleph0

/-- `Ω` is not well-founded, so `B_ℵ₀` is not the hyperset of a set. -/
theorem branching_aleph0_ne_ofZFSet (w : ZFSet.{u}) : branching ℵ₀ ≠ HSet.ofZFSet w := by
  intro equal
  have member := quineAtom_mem_branching.{u}
  rw [equal] at member
  exact HSet.not_wf_quineAtom ((HSet.wf_ofZFSet w).mem member)

/-- The hyperset of `V_ω` is included in `B_ℵ₀`. -/
theorem ofZFSet_vonNeumann_omega_subset_branching :
    HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u}) ⊆ branching ℵ₀ := by
  have equal := toZFSet_branching (κ := (ℵ₀ : Cardinal.{u}))
    (hclosed_branching_iff.mpr (Or.inr (Or.inl rfl)))
  rw [ord_aleph0] at equal
  rw [← equal]
  exact ofZFSet_toZFSet_subset _

/-- The hyperset of `V_ω` has infinitely many members, so it is not a member of `B_ℵ₀`,
although it is included in it. -/
theorem ofZFSet_vonNeumann_omega_notMem_branching :
    HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u}) ∉ branching ℵ₀ := by
  intro member
  have fewer := smallMembers_ofZFSet_iff.mp (mem_branching.mp member).smallMembers
  rw [ZFSet.card_vonNeumann, preBeth_omega] at fewer
  exact lt_irrefl _ fewer

/-- For a finite `κ ≥ 1`, `B_κ` is not a closed stage: `2` is neither `0`, `ℵ₀` nor
inaccessible. -/
example : ¬ HClosed (branching (2 : Cardinal.{u})) := by
  rw [hclosed_branching_iff]
  rintro (h | h | h)
  · exact two_ne_zero h
  · exact (natCast_lt_aleph0 (n := 2)).ne h
  · exact (h.aleph0_lt.trans (natCast_lt_aleph0 (n := 2))).false

#print axioms mem_branching
#print axioms hclosed_branching_iff
#print axioms toZFSet_branching
#print axioms ofZFSet_vonNeumann_omega_notMem_branching

end Mettapedia.SetTheory.OpenTower.AntiFounded
