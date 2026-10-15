import Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.Cardinal

/-!
# The closed sets are the levels at inaccessible cardinals

A closed set is a level of the von Neumann hierarchy (`ClosedLevels.closed_eq_vonNeumann`).
This module says which levels: the closed sets of one level of `ZFSet` are the empty set, the
hereditarily finite sets `V_ω`, and the levels `V_κ` at inaccessible cardinals `κ`
(`closed_iff`). One direction is the existing closure of inaccessible rank segments. For the
other, replacement along a member bounds every family of ranks indexed by its members
(`exists_bound_of_mem`), so a member has fewer members than the rank has predecessors
(`card_lt_card_rank`); hence the rank is an initial ordinal (`ord_card_rank`), regular, and
closed under cardinal exponentiation (`isInaccessible_card_rank`).

**The named hypothesis is the cofinal family.** Cofinally many inaccessibles at a level is
the same statement as "every set of the level lies in a closed set"
(`cofinalInaccessibles_iff_cofinal`). So the cofinal family of stages exists at a level
exactly when the hypothesis holds there: the hypothesis is not an extra assumption on that
option, it is the option.

**Where the law "every set lies in a closed set" holds inside a model.** Inside the level at
an inaccessible `κ` it holds exactly when the inaccessibles below `κ` are unbounded below `κ`
(`universeLawInside_vonNeumann_iff`). It fails in the hereditarily finite sets and at the
least inaccessible, and at every inaccessible that is not a limit of inaccessibles.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open InternalTower
open ClosedLevels StageFamilies
open Mettapedia.SetTheory.CarveOuts
open scoped ZFSet Cardinal Ordinal

universe u

variable {U : ZFSet.{u}}

/-! ## Membership in a closed set is a bound on the rank -/

/-- The members of a closed set are the sets of smaller rank. -/
theorem mem_iff_rank_lt (hU : Closed U) {x : ZFSet.{u}} : x ∈ U ↔ x.rank < U.rank := by
  constructor
  · exact ZFSet.rank_lt_of_mem
  · intro below
    have member := ZFSet.mem_vonNeumann.mpr below
    rwa [← closed_eq_vonNeumann hU] at member

/-- **Replacement bounds ranks.** A family of ordinals below the rank of a closed set, indexed
by the members of one of its members, is bounded below the rank. -/
theorem exists_bound_of_mem (hU : Closed U) {x : ZFSet.{u}} (hx : x ∈ U)
    (g : ZFSet.{u} → Ordinal.{u}) (hg : ∀ y ∈ x, g y < U.rank) :
    ∃ β < U.rank, ∀ y ∈ x, g y < β := by
  have image := hU.replacement_mem hx (fun y => V_ (g y)) (fun y hy =>
    (mem_iff_rank_lt hU).mpr (by rw [ZFSet.rank_vonNeumann]; exact hg y hy))
  refine ⟨_, ZFSet.rank_lt_of_mem image, fun y hy => ?_⟩
  have member : V_ (g y) ∈ replacement x (fun y => V_ (g y)) :=
    mem_replacement.mpr ⟨y, hy, rfl⟩
  have below := ZFSet.rank_lt_of_mem member
  rwa [ZFSet.rank_vonNeumann] at below

/-- A member of a closed set has fewer members than the rank of the closed set has
predecessors: otherwise its members would index every ordinal below the rank. -/
theorem card_lt_card_rank (hU : Closed U) {x : ZFSet.{u}} (hx : x ∈ U) :
    x.card < U.rank.card := by
  classical
  by_contra notLess
  have atLeast : U.rank.card ≤ x.card := not_lt.mp notLess
  have positive : 0 < U.rank := pos_of_gt (ZFSet.rank_lt_of_mem hx)
  have sizes : #(Set.Iio U.rank) ≤ #x := by
    rw [Cardinal.mk_Iio_ordinal, ZFSet.cardinalMk_coe_sort]
    exact Cardinal.lift_le.mpr atLeast
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp sizes
  let g : ZFSet.{u} → Ordinal.{u} := fun y =>
    if h : ∃ a : Set.Iio U.rank, (e a : ZFSet.{u}) = y then
      ((Classical.choose h : Set.Iio U.rank) : Ordinal.{u})
    else 0
  have hg : ∀ y ∈ x, g y < U.rank := by
    intro y _
    by_cases h : ∃ a : Set.Iio U.rank, (e a : ZFSet.{u}) = y
    · simp only [g, dif_pos h]
      exact (Classical.choose h).2
    · simp only [g, dif_neg h]
      exact positive
  obtain ⟨β, hβ, bound⟩ := exists_bound_of_mem hU hx g hg
  have value : g (e ⟨β, hβ⟩) = β := by
    have h : ∃ a : Set.Iio U.rank, (e a : ZFSet.{u}) = e ⟨β, hβ⟩ := ⟨⟨β, hβ⟩, rfl⟩
    simp only [g, dif_pos h]
    have same : Classical.choose h = ⟨β, hβ⟩ :=
      e.injective (Subtype.ext (Classical.choose_spec h))
    rw [same]
  have below := bound (e ⟨β, hβ⟩) (e ⟨β, hβ⟩).2
  rw [value] at below
  exact lt_irrefl _ below

/-- The rank of a closed set is an initial ordinal. -/
theorem ord_card_rank (hU : Closed U) : U.rank.card.ord = U.rank := by
  refine le_antisymm (Cardinal.ord_card_le _) (not_lt.mp fun below => ?_)
  have member : U.rank.card.ord.toZFSet ∈ U :=
    (mem_iff_rank_lt hU).mpr (by rw [Ordinal.rank_toZFSet]; exact below)
  have fewer := card_lt_card_rank hU member
  rw [Ordinal.card_toZFSet, Cardinal.card_ord] at fewer
  exact lt_irrefl _ fewer

/-- The von Neumann ordinal of a cardinal below the number of ranks of a closed set is a
member of it. -/
theorem toZFSet_ord_mem (hU : Closed U) {μ : Cardinal.{u}} (hμ : μ < U.rank.card) :
    μ.ord.toZFSet ∈ U := by
  refine (mem_iff_rank_lt hU).mpr ?_
  rw [Ordinal.rank_toZFSet, ← ord_card_rank hU]
  exact Cardinal.ord_lt_ord.mpr hμ

/-- **A closed set of rank above `ω` has an inaccessible number of ranks.** -/
theorem isInaccessible_card_rank (hU : Closed U) (hω : ω < U.rank) :
    U.rank.card.IsInaccessible := by
  have initial := ord_card_rank hU
  refine ⟨?_, ?_, ?_⟩
  · have below := Cardinal.lt_ord.mp (initial.symm ▸ hω)
    simpa using below
  · rw [initial]
    have key : Cardinal.lift.{u + 1} U.rank.card ≤ Order.cof (Set.Iio U.rank) := by
      refine Order.le_cof_iff.mpr fun s cofinal => ?_
      by_contra notLess
      obtain ⟨μ, hμ, size⟩ := Cardinal.lt_lift_iff.mp (not_le.mp notLess)
      have member := toZFSet_ord_mem hU hμ
      have sizes : #(μ.ord.toZFSet : ZFSet.{u}) = #s := by
        rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet, Cardinal.card_ord, size]
      obtain ⟨e⟩ := Cardinal.eq.mp sizes
      classical
      let g : ZFSet.{u} → Ordinal.{u} := fun y =>
        if h : y ∈ μ.ord.toZFSet then (((e ⟨y, h⟩ : s) : Set.Iio U.rank) : Ordinal.{u}) else 0
      have hg : ∀ y ∈ μ.ord.toZFSet, g y < U.rank := by
        intro y hy
        simp only [g, dif_pos hy]
        exact (e ⟨y, hy⟩).1.2
      obtain ⟨β, hβ, bound⟩ := exists_bound_of_mem hU member g hg
      obtain ⟨b, hb, above⟩ := cofinal ⟨β, hβ⟩
      have below := bound (e.symm ⟨b, hb⟩).1 (e.symm ⟨b, hb⟩).2
      simp only [g, dif_pos (e.symm ⟨b, hb⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply]
        at below
      exact lt_irrefl _ (below.trans_le above)
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof] at key
    exact Cardinal.lift_le.mp key
  · intro μ hμ
    have fewer := card_lt_card_rank hU (hU.power_mem (toZFSet_ord_mem hU hμ))
    rwa [ZFSet.card_powerset, Ordinal.card_toZFSet, Cardinal.card_ord] at fewer

/-- A nonempty closed set has rank at least `ω`. -/
theorem omega_le_rank (hU : Closed U) {x : ZFSet.{u}} (hx : x ∈ U) : ω ≤ U.rank := by
  by_contra below
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (not_le.mp below)
  have smaller := ZFSet.rank_lt_of_mem (powerset_iterate_mem hU (hU.empty_mem hx) n)
  rw [rank_powerset_iterate, hn] at smaller
  exact lt_irrefl _ smaller

/-! ## The classification -/

/-- **The closed sets of a level are the empty set, the hereditarily finite sets, and the
levels of the von Neumann hierarchy at inaccessible cardinals.** -/
theorem closed_iff (U : ZFSet.{u}) :
    Closed U ↔ U = ∅ ∨ U = V_ ω ∨ ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ U = V_ κ.ord := by
  constructor
  · intro hU
    by_cases empty : U = ∅
    · exact Or.inl empty
    · right
      obtain ⟨x, hx⟩ : ∃ x, x ∈ U := by
        by_contra none
        exact empty ((ZFSet.eq_empty U).mpr fun y hy => none ⟨y, hy⟩)
      rcases (omega_le_rank hU hx).eq_or_lt with same | above
      · left
        rw [closed_eq_vonNeumann hU, ← same]
      · right
        refine ⟨U.rank.card, isInaccessible_card_rank hU above, ?_⟩
        rw [ord_card_rank hU]
        exact closed_eq_vonNeumann hU
  · rintro (rfl | rfl | ⟨κ, hκ, rfl⟩)
    · exact closed_empty
    · exact vonNeumann_omega_closed
    · exact inaccessible_closed hκ

/-! ## The named hypothesis, read through the classification -/

/-- **Cofinally many inaccessibles is the statement that every set lies in a closed set.** -/
theorem cofinalInaccessibles_iff_cofinal :
    CofinalInaccessibles.{u} ↔ Cofinal {U : ZFSet.{u} | Closed U} := by
  constructor
  · exact exists_stage_containing
  · intro cofinal α
    obtain ⟨U, hU, member⟩ := cofinal (V_ (Order.succ (max α ω)))
    have rankBelow : Order.succ (max α ω) < U.rank := by
      have below := ZFSet.rank_lt_of_mem member
      rwa [ZFSet.rank_vonNeumann] at below
    have aboveOmega : ω < U.rank :=
      ((le_max_right α ω).trans_lt (Order.lt_succ _)).trans rankBelow
    refine ⟨U.rank.card, isInaccessible_card_rank hU aboveOmega, ?_⟩
    rw [ord_card_rank hU]
    exact ((le_max_left α ω).trans_lt (Order.lt_succ _)).trans rankBelow

/-- **Where the law "every set lies in a closed set" holds inside a model.** Inside the level
at an inaccessible cardinal, the law holds exactly when the inaccessibles below that cardinal
are unbounded below it. -/
theorem universeLawInside_vonNeumann_iff {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    UniverseLawInside (V_ κ.ord) ↔
      ∀ α < κ.ord, ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ α < μ.ord ∧ μ < κ := by
  have limit := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
  have omegaBelow : ω < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.mpr hκ.aleph0_lt
  constructor
  · intro law α hα
    have member : V_ (Order.succ (max α ω)) ∈ V_ κ.ord :=
      ZFSet.vonNeumann_mem_vonNeumann_iff.mpr (limit.succ_lt (max_lt hα omegaBelow))
    obtain ⟨V, hV, inside, closed⟩ := law _ member
    have rankBelow : Order.succ (max α ω) < V.rank := by
      have below := ZFSet.rank_lt_of_mem inside
      rwa [ZFSet.rank_vonNeumann] at below
    have aboveOmega : ω < V.rank :=
      ((le_max_right α ω).trans_lt (Order.lt_succ _)).trans rankBelow
    refine ⟨V.rank.card, isInaccessible_card_rank closed aboveOmega, ?_, ?_⟩
    · rw [ord_card_rank closed]
      exact ((le_max_left α ω).trans_lt (Order.lt_succ _)).trans rankBelow
    · rw [← Cardinal.ord_lt_ord, ord_card_rank closed]
      exact ZFSet.mem_vonNeumann.mp hV
  · intro unbounded x hx
    obtain ⟨μ, hμ, above, below⟩ := unbounded x.rank (ZFSet.mem_vonNeumann.mp hx)
    exact ⟨V_ μ.ord, ZFSet.vonNeumann_mem_vonNeumann_iff.mpr (Cardinal.ord_lt_ord.mpr below),
      ZFSet.mem_vonNeumann.mpr above, inaccessible_closed hμ⟩

#print axioms mem_iff_rank_lt
#print axioms exists_bound_of_mem
#print axioms card_lt_card_rank
#print axioms ord_card_rank
#print axioms isInaccessible_card_rank
#print axioms closed_iff
#print axioms cofinalInaccessibles_iff_cofinal
#print axioms universeLawInside_vonNeumann_iff

end Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
