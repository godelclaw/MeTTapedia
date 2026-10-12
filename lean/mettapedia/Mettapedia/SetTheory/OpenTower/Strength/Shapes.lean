import Mettapedia.SetTheory.OpenTower.Strength.StageFamilies

/-!
# The order among the shapes of the top

Three shapes of a top made of closed sets of one level, as families of sets:

* **one fixed model** (`IsFixedModel`): the family whose only member is a closed set holding
  the empty set;
* **a linear open tower** (`IsLinearTower`): the stages of a tower of stages indexed by the
  natural numbers;
* **a cofinal family of stages** (`IsCofinalFamily`): a family of closed sets in which every
  set of the level lies.

Two relations between families are read as arrows. A family is a *part* of another when it is
included in it: the larger restricts to the smaller. A family is *hosted by* another when each
of its members is a member of a member of the other (`HostedBy`): the first is modelled inside
the second.

**Parts.** Under the named hypothesis every fixed model is a part of a linear tower
(`IsFixedModel.exists_isLinearTower`), and every linear tower is a part of the cofinal family
of all closed sets (`IsLinearTower.subset_closedSets`, `isCofinalFamily_closedSets`); the tower
of least closed sets is the beginning of the tower indexed by the ordinals of the level
(`ordinalStage_natCast`), which is itself a cofinal family (`isCofinalFamily_ordinalStage`).
Nothing goes back: a linear tower is a part of no fixed model
(`IsLinearTower.not_subset_of_isFixedModel`), and a cofinal family is a part of no collected
family (`IsCofinalFamily.not_subset_of_collected`), in particular of no linear tower and of no
fixed model. A cofinal family is a chain (`IsCofinalFamily.subset_total`), so it differs from
a linear tower by its length, not by the shape of its order.

**Hosting.** A linear tower and a cofinal family host themselves
(`IsLinearTower.hostedBy_self`, `IsCofinalFamily.hostedBy_self`); a fixed model does not
(`IsFixedModel.not_hostedBy_self`). Under the hypothesis every linear tower is hosted by a
fixed model (`IsLinearTower.exists_isFixedModel_hosting`), and no cofinal family is hosted by
a collected family (`IsCofinalFamily.not_hostedBy_of_collected`).

**One level up.** The image of a level one level up is a fixed model (`isFixedModel_image`),
and its closed members are exactly the lifts of the closed sets of the level
(`mem_image_closed_iff`). So the cofinal family of one level is the family of stages inside one
fixed model of the next level: the separation of the two shapes is relative to the level.

The plural family of admitted theories stands above the three: every stage of each of them is
admitted under one theory on one membership relation
(`AdmittedTheories.stage_wellFounded`), and the anti-founded theory, admitted at the hypersets,
has no stage among them and no membership-preserving map into them
(`AdmittedTheories.no_quineAtom_among_members`,
`AdmittedTheories.hypersets_no_memHom_into_members`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Strength.Shapes

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation ZFSetUniverseLift ZFSetLiftedUniverseClosure
open InternalTower ExternalTower
open ClosedLevels StageFamilies
open Mettapedia.SetTheory.CarveOuts
open scoped ZFSet

universe u

variable {𝔖 𝔗 : Set ZFSet.{u}}

/-! ## The three shapes -/

/-- One fixed model: the family whose only member is a closed set holding the empty set. -/
def IsFixedModel (𝔖 : Set ZFSet.{u}) : Prop :=
  ∃ W : ZFSet.{u}, Closed W ∧ (∅ : ZFSet.{u}) ∈ W ∧ 𝔖 = {W}

/-- A linear open tower: the stages of a tower of stages. -/
def IsLinearTower (𝔖 : Set ZFSet.{u}) : Prop :=
  ∃ s : ℕ → ZFSet.{u}, StageChain s ∧ 𝔖 = Set.range s

/-- A cofinal family of stages: a family of closed sets in which every set of the level
lies. -/
def IsCofinalFamily (𝔖 : Set ZFSet.{u}) : Prop :=
  (∀ U ∈ 𝔖, Closed U) ∧ Cofinal 𝔖

/-- The hereditarily finite sets are a fixed model, with no hypothesis. -/
theorem isFixedModel_hereditarilyFinite :
    IsFixedModel ({V_ Ordinal.omega0} : Set ZFSet.{u}) :=
  ⟨_, vonNeumann_omega_closed, empty_mem_vonNeumann_omega, rfl⟩

/-- The family whose only member is the empty set is not a fixed model: a model holds the
empty set. -/
example : ¬ IsFixedModel ({∅} : Set ZFSet.{u}) := by
  rintro ⟨W, -, hEmpty, same⟩
  have equal : (∅ : ZFSet.{u}) = W := Set.singleton_eq_singleton_iff.mp same
  rw [← equal] at hEmpty
  exact ZFSet.notMem_empty _ hEmpty

/-- The tower of least closed sets over a set is a linear tower. -/
theorem isLinearTower_stage (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    IsLinearTower (Set.range (stage h N)) :=
  ⟨stage h N, stageChain_stage h N, rfl⟩

/-- Under the named hypothesis the closed sets of a level are a cofinal family. -/
theorem isCofinalFamily_closedSets (h : CofinalInaccessibles.{u}) :
    IsCofinalFamily {U : ZFSet.{u} | Closed U} :=
  ⟨fun _ hU => hU, exists_stage_containing h⟩

/-- **The tower indexed by the ordinals of the level is a cofinal family.** -/
theorem isCofinalFamily_ordinalStage (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    IsCofinalFamily (Set.range (ordinalStage h N)) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro _ ⟨α, rfl⟩
    exact ordinalStage_closed h N α
  · obtain ⟨α, member⟩ := ordinalStage_cofinal h N x
    exact ⟨_, ⟨α, rfl⟩, member⟩

/-! ## Collected families, and the linear order of a cofinal family -/

/-- A fixed model is collected, by the singleton of its one member. -/
theorem IsFixedModel.collected (fixed : IsFixedModel 𝔖) : Collected 𝔖 := by
  obtain ⟨W, -, -, rfl⟩ := fixed
  exact ⟨{W}, fun U hU => ZFSet.mem_singleton.mpr hU⟩

/-- A linear tower is collected, by the set of its stages. -/
theorem IsLinearTower.collected (tower : IsLinearTower 𝔖) : Collected 𝔖 := by
  obtain ⟨s, -, rfl⟩ := tower
  exact collected_range s

/-- **A cofinal family is a chain**: any two of its members are comparable by inclusion. -/
theorem IsCofinalFamily.subset_total (cofinal : IsCofinalFamily 𝔖) {U V : ZFSet.{u}}
    (hU : U ∈ 𝔖) (hV : V ∈ 𝔖) : U ⊆ V ∨ V ⊆ U :=
  closed_subset_total (cofinal.1 U hU) (cofinal.1 V hV)

/-- A family with one member is not a linear tower: the stages of a tower differ. -/
example (W : ZFSet.{u}) : ¬ IsLinearTower ({W} : Set ZFSet.{u}) := by
  rintro ⟨s, chain, same⟩
  have first : s 0 = W := by
    have member : s 0 ∈ ({W} : Set ZFSet.{u}) := same ▸ ⟨0, rfl⟩
    exact member
  have second : s 1 = W := by
    have member : s 1 ∈ ({W} : Set ZFSet.{u}) := same ▸ ⟨1, rfl⟩
    exact member
  exact absurd (chain.injective (first.trans second.symm)) (by decide)

/-- A family indexed by the natural numbers is not a cofinal family. -/
example (s : ℕ → ZFSet.{u}) : ¬ IsCofinalFamily (Set.range s) :=
  fun cofinal => not_cofinal_range s cofinal.2

/-! ## Parts -/

/-- **Every fixed model is a part of a linear tower**, under the named hypothesis: it is the
first stage of the tower over it. -/
theorem IsFixedModel.exists_isLinearTower (h : CofinalInaccessibles.{u})
    (fixed : IsFixedModel 𝔖) : ∃ 𝔗 : Set ZFSet.{u}, IsLinearTower 𝔗 ∧ 𝔖 ⊆ 𝔗 := by
  obtain ⟨W, hW, -, rfl⟩ := fixed
  refine ⟨Set.range (chainFrom h W), ⟨_, stageChain_chainFrom h hW, rfl⟩, ?_⟩
  rintro _ rfl
  exact ⟨0, rfl⟩

/-- Every linear tower is a part of the family of all closed sets. -/
theorem IsLinearTower.subset_closedSets (tower : IsLinearTower 𝔖) :
    𝔖 ⊆ {U : ZFSet.{u} | Closed U} := by
  obtain ⟨s, chain, rfl⟩ := tower
  rintro _ ⟨n, rfl⟩
  exact chain.closed n

/-- **A linear tower is a part of no fixed model.** -/
theorem IsLinearTower.not_subset_of_isFixedModel (tower : IsLinearTower 𝔖)
    (fixed : IsFixedModel 𝔗) : ¬ 𝔖 ⊆ 𝔗 := by
  obtain ⟨s, chain, rfl⟩ := tower
  obtain ⟨W, -, -, rfl⟩ := fixed
  intro included
  have first : s 0 = W := included ⟨0, rfl⟩
  have second : s 1 = W := included ⟨1, rfl⟩
  exact absurd (chain.injective (first.trans second.symm)) (by decide)

/-- **A cofinal family is a part of no collected family**, in particular of no linear tower and
of no fixed model. -/
theorem IsCofinalFamily.not_subset_of_collected (cofinal : IsCofinalFamily 𝔖)
    (collected : Collected 𝔗) : ¬ 𝔖 ⊆ 𝔗 := by
  intro included
  obtain ⟨c, collects⟩ := collected
  exact not_collected_of_cofinal cofinal.2 ⟨c, fun U hU => collects U (included hU)⟩

/-- **The tower of least closed sets is the beginning of the tower indexed by the ordinals.** -/
theorem ordinalStage_natCast (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    ordinalStage h N (n : Ordinal.{u}) = stage h N n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have below : ordinalStage h N (n : Ordinal.{u}) ⊆ stage h N n := by
      rw [ordinalStage_eq]
      refine univOf_minimal h ?_ (stage_closed h N n)
      cases n with
      | zero =>
        refine (stage_closed h N 0).subset_mem
          ((stage_closed h N 0).singleton_mem (base_mem_stage_zero h N)) ?_
        intro z hz
        rcases ZFSet.mem_insert_iff.mp hz with same | hz
        · exact ZFSet.mem_singleton.mpr same
        · obtain ⟨β, -⟩ := ZFSet.mem_range.mp hz
          exact absurd β.2 (by simp)
      | succ m =>
        have top : insert (stage h N m) (stage h N m) ∈ stage h N (m + 1) :=
          closed_insert_mem (stage_closed h N (m + 1)) (stage_mem_succ h N m)
            (stage_mem_succ h N m)
        refine (stage_closed h N (m + 1)).subset_mem top ?_
        intro z hz
        rcases ZFSet.mem_insert_iff.mp hz with same | hz
        · rw [same]
          exact ZFSet.mem_insert_of_mem _ (base_mem_stage h N m)
        · obtain ⟨β, rfl⟩ := ZFSet.mem_range.mp hz
          obtain ⟨k, hk⟩ :=
            Ordinal.lt_omega0.mp (β.2.trans (Ordinal.natCast_lt_omega0 (m + 1)))
          have small : k < m + 1 := by
            have bound := β.2
            rw [Set.mem_Iio, hk] at bound
            exact Nat.cast_lt.mp bound
          rw [hk, ih k small]
          rcases Nat.lt_succ_iff_lt_or_eq.mp small with lower | rfl
          · exact ZFSet.mem_insert_of_mem _ (stage_mem_of_lt h N lower)
          · exact ZFSet.mem_insert _ _
    have above : stage h N n ⊆ ordinalStage h N (n : Ordinal.{u}) := by
      cases n with
      | zero =>
        exact univOf_minimal h (base_mem_ordinalStage h N _) (ordinalStage_closed h N _)
      | succ m =>
        refine univOf_minimal h ?_ (ordinalStage_closed h N _)
        rw [← ih m (Nat.lt_succ_self m)]
        exact ordinalStage_mem_of_lt h N (Nat.cast_lt.mpr (Nat.lt_succ_self m))
    exact ZFSet.ext fun z => ⟨fun hz => below hz, fun hz => above hz⟩

/-! ## Hosting -/

/-- A family is hosted by another when each of its members is a member of a member of the
other. -/
def HostedBy (𝔖 𝔗 : Set ZFSet.{u}) : Prop :=
  ∀ U ∈ 𝔖, ∃ V ∈ 𝔗, U ∈ V

/-- A linear tower hosts itself: each stage is a member of the next. -/
theorem IsLinearTower.hostedBy_self (tower : IsLinearTower 𝔖) : HostedBy 𝔖 𝔖 := by
  obtain ⟨s, chain, rfl⟩ := tower
  rintro _ ⟨n, rfl⟩
  exact ⟨_, ⟨n + 1, rfl⟩, chain.mem_succ n⟩

/-- A cofinal family hosts itself. -/
theorem IsCofinalFamily.hostedBy_self (cofinal : IsCofinalFamily 𝔖) : HostedBy 𝔖 𝔖 :=
  fun U _ => cofinal.2 U

/-- **A fixed model does not host itself.** -/
theorem IsFixedModel.not_hostedBy_self (fixed : IsFixedModel 𝔖) : ¬ HostedBy 𝔖 𝔖 := by
  obtain ⟨W, -, -, rfl⟩ := fixed
  intro hosted
  obtain ⟨V, hV, member⟩ := hosted W rfl
  rw [Set.mem_singleton_iff.mp hV] at member
  exact ZFSet.mem_irrefl W member

/-- **Every linear tower is hosted by a fixed model**, under the named hypothesis: a closed set
that has every stage as a member. -/
theorem IsLinearTower.exists_isFixedModel_hosting (h : CofinalInaccessibles.{u})
    (tower : IsLinearTower 𝔖) : ∃ 𝔗 : Set ZFSet.{u}, IsFixedModel 𝔗 ∧ HostedBy 𝔖 𝔗 := by
  obtain ⟨s, -, rfl⟩ := tower
  obtain ⟨W, hW, bound⟩ := small_family_bounded h s
  refine ⟨{W}, ⟨W, hW, hW.empty_mem (bound 0), rfl⟩, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact ⟨W, rfl, bound n⟩

/-- **No cofinal family is hosted by a collected family**, in particular by a linear tower or
by a fixed model: the union of the collecting set would collect the cofinal family. -/
theorem IsCofinalFamily.not_hostedBy_of_collected (cofinal : IsCofinalFamily 𝔖)
    (collected : Collected 𝔗) : ¬ HostedBy 𝔖 𝔗 := by
  intro hosted
  obtain ⟨c, collects⟩ := collected
  refine not_collected_of_cofinal cofinal.2 ⟨ZFSet.sUnion c, fun U hU => ?_⟩
  obtain ⟨V, hV, member⟩ := hosted U hU
  exact ZFSet.mem_sUnion.mpr ⟨V, collects V hV, member⟩

/-! ## One level up -/

/-- **The closed members of the image of a level are the lifts of its closed sets.** -/
theorem mem_image_closed_iff {V : ZFSet.{u + 1}} :
    V ∈ carrierCode.{u} ∧ Closed V ↔ ∃ U : ZFSet.{u}, Closed U ∧ lift U = V := by
  constructor
  · rintro ⟨hV, closed⟩
    obtain ⟨U, rfl⟩ := mem_carrierCode.mp hV
    exact ⟨U, closed_of_lift closed, rfl⟩
  · rintro ⟨U, closed, rfl⟩
    exact ⟨mem_carrierCode.mpr ⟨U, rfl⟩, closed_lift closed⟩

/-- The image of a level, one level up, is a fixed model, with no hypothesis. -/
theorem isFixedModel_image : IsFixedModel ({carrierCode.{u}} : Set ZFSet.{u + 1}) :=
  ⟨_, carrierCode_closed, carrierCode_closed.empty_mem omega_mem_image, rfl⟩

#print axioms isFixedModel_hereditarilyFinite
#print axioms isCofinalFamily_ordinalStage
#print axioms IsCofinalFamily.subset_total
#print axioms IsFixedModel.exists_isLinearTower
#print axioms IsLinearTower.subset_closedSets
#print axioms IsLinearTower.not_subset_of_isFixedModel
#print axioms IsCofinalFamily.not_subset_of_collected
#print axioms ordinalStage_natCast
#print axioms IsLinearTower.hostedBy_self
#print axioms IsCofinalFamily.hostedBy_self
#print axioms IsFixedModel.not_hostedBy_self
#print axioms IsLinearTower.exists_isFixedModel_hosting
#print axioms IsCofinalFamily.not_hostedBy_of_collected
#print axioms mem_image_closed_iff
#print axioms isFixedModel_image

end Mettapedia.SetTheory.OpenTower.Strength.Shapes
