import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeHolonomy

/-!
# Exact residue of adjacent-pair relational holonomy

The fixed-point-free relational obstruction has two genuinely different
forms.  Its fourfold composite may be empty, so that the four inhabited side
relations do not even concatenate around the cell.  Otherwise the composite
is inhabited and every completed return changes its starting witness.

This distinction is needed before any permutation-sign or monodromy argument:
an empty relation is not a permutation.  No geometric or wall-exclusion
consequence is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The fourfold composite is empty.  In the obstruction theorem below the
four side relations are separately inhabited, so this says that their local
witnesses fail to concatenate into even one clockwise path. -/
def HasRelationalBreak
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) : Prop :=
  ¬ RelationNonempty
    (fourStepRelationalHolonomy north east south west)

/-- The proper holonomy residue: at least one clockwise path completes, but
every completed path changes its north-west witness. -/
def HasNonemptyFixedPointFreeRelationalHolonomy
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) : Prop :=
  RelationNonempty
      (fourStepRelationalHolonomy north east south west) ∧
    ∀ start finish,
      fourStepRelationalHolonomy north east south west start finish →
        start ≠ finish

/-- A fixed-point-free relational obstruction is exactly either an empty
fourfold composite or an inhabited composite all of whose returns move their
starting witness.  The side-inhabitation hypotheses are retained literally
in both branches. -/
theorem hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) :
    HasFixedPointFreeRelationalHolonomy north east south west ↔
      RelationNonempty north ∧
        RelationNonempty east ∧
        RelationNonempty south ∧
        RelationNonempty west ∧
        (HasRelationalBreak north east south west ∨
          HasNonemptyFixedPointFreeRelationalHolonomy
            north east south west) := by
  constructor
  · rintro ⟨hnorth, heast, hsouth, hwest, hnoSection⟩
    refine ⟨hnorth, heast, hsouth, hwest, ?_⟩
    by_cases hcomposite : RelationNonempty
        (fourStepRelationalHolonomy north east south west)
    · right
      refine ⟨hcomposite, ?_⟩
      intro start finish hpath heq
      subst finish
      exact hnoSection ⟨start, hpath⟩
    · exact Or.inl hcomposite
  · rintro ⟨hnorth, heast, hsouth, hwest, hbreak | hproper⟩
    · refine ⟨hnorth, heast, hsouth, hwest, ?_⟩
      rintro ⟨start, hpath⟩
      exact hbreak ⟨start, start, hpath⟩
    · refine ⟨hnorth, heast, hsouth, hwest, ?_⟩
      rintro ⟨start, hpath⟩
      exact hproper.2 start start hpath rfl

/-- The concrete adjacent-pair lifting obstruction splits into a relational
break and a proper nonempty holonomy residue. -/
theorem hasSharedWitnessObstruction_iff_exists_break_or_nonemptyHolonomy
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestBase : DeletionColoring northwest)
    (northeastBase : DeletionColoring northeast)
    (southeastBase : DeletionColoring southeast)
    (southwestBase : DeletionColoring southwest) :
    HasSharedWitnessObstruction
        (overlapKempeCellStateSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase)
        (compatibleOverlapKempeCycleSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase) ↔
      ∃ state : OverlapKempeCellState, state.IsCornerCoherent ∧
        RelationNonempty
          (overlapStateWitnessRelation northwest northeast
            northwestBase northeastBase state.north) ∧
        RelationNonempty
          (overlapStateWitnessRelation northeast southeast
            northeastBase southeastBase state.east) ∧
        RelationNonempty
          (overlapStateWitnessRelation southeast southwest
            southeastBase southwestBase state.south) ∧
        RelationNonempty
          (overlapStateWitnessRelation southwest northwest
            southwestBase northwestBase state.west) ∧
        (HasRelationalBreak
            (overlapStateWitnessRelation northwest northeast
              northwestBase northeastBase state.north)
            (overlapStateWitnessRelation northeast southeast
              northeastBase southeastBase state.east)
            (overlapStateWitnessRelation southeast southwest
              southeastBase southwestBase state.south)
            (overlapStateWitnessRelation southwest northwest
              southwestBase northwestBase state.west) ∨
          HasNonemptyFixedPointFreeRelationalHolonomy
            (overlapStateWitnessRelation northwest northeast
              northwestBase northeastBase state.north)
            (overlapStateWitnessRelation northeast southeast
              northeastBase southeastBase state.east)
            (overlapStateWitnessRelation southeast southwest
              southeastBase southwestBase state.south)
            (overlapStateWitnessRelation southwest northwest
              southwestBase northwestBase state.west)) := by
  rw [hasSharedWitnessObstruction_iff_exists_fixedPointFreeHolonomy]
  constructor
  · rintro ⟨state, hcoherent, hholonomy⟩
    exact ⟨state, hcoherent,
      (hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty
        _ _ _ _).1 hholonomy⟩
  · rintro ⟨state, hcoherent, hresidue⟩
    exact ⟨state, hcoherent,
      (hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty
        _ _ _ _).2 hresidue⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing aliases for the refined relational residue. -/

alias GoertzelV24AdjacentPairOverlapKempeHolonomyResidue.hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty

alias GoertzelV24AdjacentPairOverlapKempeHolonomyResidue.hasSharedWitnessObstruction_iff_exists_break_or_nonemptyHolonomy :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasSharedWitnessObstruction_iff_exists_break_or_nonemptyHolonomy

end Mettapedia.GraphTheory.FourColor
