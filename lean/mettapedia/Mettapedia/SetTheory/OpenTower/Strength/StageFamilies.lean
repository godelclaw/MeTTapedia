import Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
import Mettapedia.SetTheory.OpenTower.ExternalTower
import Mettapedia.SetTheory.CarveOuts.HereditarilyFinite

/-!
# Families of stages: one model, a tower, the class of all stages

Three shapes of a top made of closed sets of one level are compared here: one closed set, a
tower of closed sets indexed by the natural numbers, and the class of all closed sets.

**Two observers of a family of sets.** A family is *cofinal* when every set of the level lies
in one of its members (`Cofinal`), and *collected* when one set of the level has every member
of the family as a member (`Collected`). No family is both (`not_collected_of_cofinal`, by
foundation alone, with no use of choice). A family indexed by a small type is collected
(`collected_range`), so it is not cofinal (`not_cofinal_range`). Under the named hypothesis the
closed sets are cofinal, hence not collected (`closedSets_not_collected`), and the members of a
cofinal family of transitive sets bound every small family of sets
(`Cofinal.small_family_bounded`).

**Towers.** A `StageChain` is a sequence of closed sets, each a member of the next. Its union
is never closed (`StageChain.iUnion_not_closed`): replacement along `ω` would collect the
stages into one member. So the union of a tower is not itself a closed set. This is a statement
about closure under external functions, not about first-order models: the union of a tower can
satisfy every first-order replacement instance. (Below a Mahlo cardinal `K`, the levels elementary
in `V_K` form a club containing inaccessibles; the union of an `ω`-sequence of such inaccessible
levels is again elementary in `V_K`, hence a model of ZFC, and it is not closed.)
Under the hypothesis every closed set is the first stage of a tower (`chainFrom`,
`stageChain_chainFrom`), and every tower lies inside one closed set
(`InternalTower.small_family_bounded`).

**One model does not host itself.** The members of a closed set do not inject into the members
of any of its members (`not_injective_members_into_member`). This is Cantor's theorem for a set
that has every subset of that member as a member (`not_injective_of_subsets_mem`, free of
choice). In a tower the carrier of each stage is a member of the next stage.

**The law "every set lies in a closed set", read inside a model.** `UniverseLawInside W` says
that every member of `W` lies in a closed member of `W`. Among closed sets it fails exactly in
those that are the least closed set around one of their members
(`not_universeLawInside_iff`). It fails in the hereditarily finite sets and in every least
closed set, and it holds in the image of a level one level up when the lower level has
cofinally many inaccessibles. So the law does not separate the class of stages from every
single model.

**A greatest stage, exactly.** Because closed sets are linearly ordered, a greatest closed set
fails to exist exactly when every closed set is a member of another
(`not_exists_greatest_iff`). That is implied by the named hypothesis and does not use it.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Strength.StageFamilies

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation ZFSetDependentProducts ZFSetUniverseLift
open InternalTower ExternalTower
open ClosedLevels
open Mettapedia.SetTheory.CarveOuts
open scoped ZFSet

universe u v

variable {U V W : ZFSet.{u}}

/-! ## Cofinal and collected families -/

/-- A family of sets is cofinal in its level when every set of the level is a member of a
member of the family. -/
def Cofinal (𝔖 : Set ZFSet.{u}) : Prop :=
  ∀ x : ZFSet.{u}, ∃ U ∈ 𝔖, x ∈ U

/-- A family of sets is collected when one set of the level has every member of the family as
a member. -/
def Collected (𝔖 : Set ZFSet.{u}) : Prop :=
  ∃ s : ZFSet.{u}, ∀ U ∈ 𝔖, U ∈ s

/-- The family of all sets is cofinal: every set is a member of its singleton. -/
example : Cofinal (Set.univ : Set ZFSet.{u}) :=
  fun x => ⟨{x}, trivial, ZFSet.mem_singleton.mpr rfl⟩

/-- **A cofinal family is not collected.** The collecting set would be a member of a member of
the family, which is a member of it. -/
theorem not_collected_of_cofinal {𝔖 : Set ZFSet.{u}} (cofinal : Cofinal 𝔖) : ¬ Collected 𝔖 := by
  rintro ⟨s, collects⟩
  obtain ⟨U, hU, member⟩ := cofinal s
  exact ZFSet.mem_asymm member (collects U hU)

/-- A family indexed by a small type is collected, by the set of its values. -/
theorem collected_range {ι : Type v} [Small.{u} ι] (S : ι → ZFSet.{u}) :
    Collected (Set.range S) :=
  ⟨ZFSet.range S, by
    rintro _ ⟨i, rfl⟩
    exact ZFSet.mem_range_self i⟩

/-- The family of all sets is not collected. -/
example : ¬ Collected (Set.univ : Set ZFSet.{u}) :=
  not_collected_of_cofinal fun x => ⟨{x}, trivial, ZFSet.mem_singleton.mpr rfl⟩

/-- A family indexed by a small type is not cofinal. In particular no tower indexed by the
natural numbers is. -/
theorem not_cofinal_range {ι : Type v} [Small.{u} ι] (S : ι → ZFSet.{u}) :
    ¬ Cofinal (Set.range S) :=
  fun cofinal => not_collected_of_cofinal cofinal (collected_range S)

/-- One set is collected, hence not cofinal. -/
theorem not_cofinal_singleton (W : ZFSet.{u}) : ¬ Cofinal ({W} : Set ZFSet.{u}) := by
  intro cofinal
  refine not_collected_of_cofinal cofinal ⟨{W}, ?_⟩
  rintro _ rfl
  exact ZFSet.mem_singleton.mpr rfl

/-- The members of a cofinal family of transitive sets bound every small family of sets. -/
theorem Cofinal.small_family_bounded {𝔖 : Set ZFSet.{u}} (cofinal : Cofinal 𝔖)
    (transitive : ∀ U ∈ 𝔖, U.IsTransitive) {ι : Type v} [Small.{u} ι] (S : ι → ZFSet.{u}) :
    ∃ U ∈ 𝔖, ∀ i, S i ∈ U := by
  obtain ⟨U, hU, member⟩ := cofinal (ZFSet.range S)
  exact ⟨U, hU, fun i => transitive U hU _ member (ZFSet.mem_range_self i)⟩

/-- **The class of stages is not collected**: under the named hypothesis every set lies in a
closed set, so no set of the level has every closed set as a member. -/
theorem closedSets_not_collected (h : CofinalInaccessibles.{u}) :
    ¬ Collected {U : ZFSet.{u} | Closed U} :=
  not_collected_of_cofinal (exists_stage_containing h)

/-! ## A greatest stage, exactly -/

/-- **No greatest closed set exactly when every closed set is a member of another.** Uses the
linear order of closed sets and no hypothesis on cardinals. -/
theorem not_exists_greatest_iff :
    (¬ ∃ W : ZFSet.{u}, Closed W ∧ ∀ U, Closed U → U ⊆ W) ↔
      ∀ U : ZFSet.{u}, Closed U → ∃ V, Closed V ∧ U ∈ V := by
  constructor
  · intro none U hU
    by_contra terminal
    refine none ⟨U, hU, fun V hV => ?_⟩
    rcases closed_trichotomy hU hV with member | same | member
    · exact absurd ⟨V, hV, member⟩ terminal
    · exact same ▸ fun _ hx => hx
    · exact closed_subset_of_mem hU member
  · rintro later ⟨W, hW, greatest⟩
    obtain ⟨V, hV, member⟩ := later W hW
    exact ZFSet.mem_irrefl W (greatest V hV member)

/-! ## Towers of stages -/

/-- A tower of stages: a sequence of closed sets, each a member of the next. -/
structure StageChain (s : ℕ → ZFSet.{u}) : Prop where
  /-- Every stage is closed. -/
  closed : ∀ n, Closed (s n)
  /-- Every stage is a member of the next. -/
  mem_succ : ∀ n, s n ∈ s (n + 1)

/-- The tower of least closed sets over a set is a tower of stages. -/
theorem stageChain_stage (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    StageChain (stage h N) :=
  ⟨stage_closed h N, stage_mem_succ h N⟩

/-- A constant sequence is not a tower of stages. -/
theorem not_stageChain_const (W : ZFSet.{u}) : ¬ StageChain fun _ : ℕ => W :=
  fun chain => ZFSet.mem_irrefl W (chain.mem_succ 0)

namespace StageChain

variable {s : ℕ → ZFSet.{u}} (chain : StageChain s)
include chain

/-- An earlier stage of a tower is a member of every later one. -/
theorem mem_of_lt {m n : ℕ} (hmn : m < n) : s m ∈ s n := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | rfl
    · exact (chain.closed (n + 1)).transitive _ (chain.mem_succ n) (ih hlt)
    · exact chain.mem_succ m

/-- The stages of a tower are pairwise different. -/
theorem injective : Function.Injective s := by
  intro m n equal
  rcases lt_trichotomy m n with hlt | same | hgt
  · have member := chain.mem_of_lt hlt
    rw [equal] at member
    exact absurd member (ZFSet.mem_irrefl _)
  · exact same
  · have member := chain.mem_of_lt hgt
    rw [equal] at member
    exact absurd member (ZFSet.mem_irrefl _)

/-- From its third stage on, a tower holds `ω`. -/
theorem omega_mem : ZFSet.omega ∈ s 2 :=
  (chain.closed 2).subset_mem (chain.mem_succ 1)
    (omega_subset_of_closed (chain.closed 1) ((chain.closed 1).empty_mem (chain.mem_succ 0)))

/-- **The union of a tower of stages is not a stage.** Replacement along `ω` would collect
every stage into one member of the union, hence into a member of some stage, which would then
be a member of itself. -/
theorem iUnion_not_closed : ¬ Closed (ZFSet.iUnion s) := by
  classical
  intro closedUnion
  have stage_mem : ∀ n, s n ∈ ZFSet.iUnion s := fun n =>
    ZFSet.mem_iUnion.mpr ⟨n + 1, chain.mem_succ n⟩
  let index : ZFSet.{u} → ℕ := fun x =>
    if hx : ∃ n, natCode.{u} n = x then Classical.choose hx else 0
  have index_natCode : ∀ n, index (natCode.{u} n) = n := by
    intro n
    have hx : ∃ m, natCode.{u} m = natCode.{u} n := ⟨n, rfl⟩
    simp only [index, dif_pos hx]
    exact natCode_injective (Classical.choose_spec hx)
  have image := closedUnion.replacement_mem (ZFSet.mem_iUnion.mpr ⟨2, chain.omega_mem⟩)
    (fun x => s (index x)) (fun x _ => stage_mem (index x))
  obtain ⟨k, hk⟩ := ZFSet.mem_iUnion.mp image
  have member : s k ∈ replacement ZFSet.omega (fun x => s (index x)) :=
    mem_replacement.mpr ⟨natCode.{u} k, mem_omega_iff.mpr ⟨k, rfl⟩, by
      simp only [index_natCode]⟩
  exact ZFSet.mem_irrefl _ ((chain.closed k).transitive _ hk member)

end StageChain

/-- The tower over a closed set: the set itself, then the least closed set around the previous
stage. -/
noncomputable def chainFrom (h : CofinalInaccessibles.{u}) (W : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => W
  | n + 1 => univOf h (chainFrom h W n)

/-- **Every closed set is the first stage of a tower of stages**, under the named
hypothesis. -/
theorem stageChain_chainFrom (h : CofinalInaccessibles.{u}) (hW : Closed W) :
    StageChain (chainFrom h W) where
  closed n := by
    cases n with
    | zero => exact hW
    | succ n => exact univOf_closed h _
  mem_succ _ := mem_univOf h _

/-- The tower over a set starts at the set. -/
example (h : CofinalInaccessibles.{u}) (W : ZFSet.{u}) : chainFrom h W 0 = W := rfl

/-- The second stage of the tower over a set is not the set. -/
example (h : CofinalInaccessibles.{u}) (W : ZFSet.{u}) : chainFrom h W 1 ≠ W :=
  univOf_ne_self h W

/-! ## One model does not host itself -/

/-- **A set that has every subset of one of its members as a member does not inject into that
member**: such an injection would embed the subsets of the member into the member, against
Cantor's theorem. No use is made of the host's choice. -/
theorem not_injective_of_subsets_mem {c : ZFSet.{u}}
    (subsets : ∀ b : ZFSet.{u}, b ⊆ c → b ∈ W) :
    ¬ ∃ f : Elements W → Elements c, Function.Injective f := by
  rintro ⟨f, injective⟩
  let part : Set (Elements c) → Elements W := fun S =>
    ⟨ZFSet.sep (fun x => ∃ hx : x ∈ c, (⟨x, hx⟩ : Elements c) ∈ S) c,
      subsets _ ZFSet.sep_subset⟩
  have part_injective : Function.Injective part := by
    intro S T equal
    have sets : ZFSet.sep (fun x => ∃ hx : x ∈ c, (⟨x, hx⟩ : Elements c) ∈ S) c =
        ZFSet.sep (fun x => ∃ hx : x ∈ c, (⟨x, hx⟩ : Elements c) ∈ T) c :=
      congrArg Subtype.val equal
    ext x
    constructor
    · intro hx
      have member : x.1 ∈ ZFSet.sep (fun x => ∃ hx : x ∈ c, (⟨x, hx⟩ : Elements c) ∈ S) c :=
        ZFSet.mem_sep.mpr ⟨x.2, x.2, hx⟩
      rw [sets] at member
      obtain ⟨_, _, inT⟩ := ZFSet.mem_sep.mp member
      exact inT
    · intro hx
      have member : x.1 ∈ ZFSet.sep (fun x => ∃ hx : x ∈ c, (⟨x, hx⟩ : Elements c) ∈ T) c :=
        ZFSet.mem_sep.mpr ⟨x.2, x.2, hx⟩
      rw [← sets] at member
      obtain ⟨_, _, inS⟩ := ZFSet.mem_sep.mp member
      exact inS
  exact Function.cantor_injective (fun S => f (part S)) (injective.comp part_injective)

/-- **The members of a closed set do not inject into the members of one of its members.** -/
theorem not_injective_members_into_member (hW : Closed W) {c : ZFSet.{u}} (hc : c ∈ W) :
    ¬ ∃ f : Elements W → Elements c, Function.Injective f :=
  not_injective_of_subsets_mem fun _ below => hW.subset_mem hc below

/-! ## The law "every set lies in a closed set", inside a model -/

/-- Every member of `W` lies in a closed member of `W`: the law "every set lies in a closed
set", read inside `W`. -/
def UniverseLawInside (W : ZFSet.{u}) : Prop :=
  ∀ x ∈ W, ∃ V ∈ W, x ∈ V ∧ Closed V

/-- **Where the law fails.** Among closed sets, the law fails exactly in those that are the
least closed set around one of their members. -/
theorem not_universeLawInside_iff (hW : Closed W) :
    ¬ UniverseLawInside W ↔ ∃ N ∈ W, ∀ V : ZFSet.{u}, Closed V → N ∈ V → W ⊆ V := by
  constructor
  · intro fails
    by_contra none
    apply fails
    intro x hx
    by_contra noStage
    refine none ⟨x, hx, fun V hV hxV => ?_⟩
    rcases closed_trichotomy hV hW with member | same | member
    · exact absurd ⟨V, member, hxV, hV⟩ noStage
    · exact same ▸ fun _ hz => hz
    · exact closed_subset_of_mem hV member
  · rintro ⟨N, hN, least⟩ law
    obtain ⟨V, hVW, hNV, hV⟩ := law N hN
    exact ZFSet.mem_irrefl V (least V hV hNV hVW)

/-- The law holds inside the empty set, which has no member. -/
example : UniverseLawInside (∅ : ZFSet.{u}) :=
  fun x hx => absurd hx (ZFSet.notMem_empty x)

/-- The law holds inside the image of a level one level up, when the lower level has
cofinally many inaccessibles. -/
example (h : CofinalInaccessibles.{u}) : UniverseLawInside carrierCode.{u} :=
  fun _ hM => image_members_in_closed_members h hM

/-- The law fails inside the hereditarily finite sets, with no hypothesis. -/
example : ¬ UniverseLawInside (V_ Ordinal.omega0 : ZFSet.{u}) := by
  intro law
  obtain ⟨V, hV, hEmpty, closed⟩ := law ∅ empty_mem_vonNeumann_omega
  exact no_closed_universe_in_hereditarilyFinite ⟨V, hV, hEmpty, closed⟩

/-- The law fails inside every least closed set. -/
example (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) : ¬ UniverseLawInside (univOf h N) :=
  fun law => no_closed_member_around h N (law N (mem_univOf h N))

#print axioms not_collected_of_cofinal
#print axioms collected_range
#print axioms not_cofinal_range
#print axioms not_cofinal_singleton
#print axioms Cofinal.small_family_bounded
#print axioms closedSets_not_collected
#print axioms not_exists_greatest_iff
#print axioms StageChain.injective
#print axioms StageChain.iUnion_not_closed
#print axioms stageChain_chainFrom
#print axioms not_injective_of_subsets_mem
#print axioms not_injective_members_into_member
#print axioms not_universeLawInside_iff

end Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
