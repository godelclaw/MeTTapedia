import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeLifting

/-!
# Relational holonomy of adjacent-pair overlap states

A compatible cycle of four pairwise overlap states need not have one shared
colouring at each corner.  This file identifies the exact finite obstruction.
For a fixed side state, its concrete witnesses form a relation between the two
corner colouring fibres.  The four side relations compose to a relation from
the north-west fibre to itself.  A shared-witness cell exists exactly when this
four-step relation has a fixed point.

Consequently, failure of shared-witness lifting is equivalent to a coherent
state whose four side relations are nonempty but whose relational holonomy is
fixed-point-free.  No geometric or wall-exclusion consequence is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The fourfold composite of heterogeneous relations around a clockwise
cell.  It is a relation from the north-west carrier back to itself. -/
def fourStepRelationalHolonomy
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) :
    Northwest → Northwest → Prop :=
  fun start finish => ∃ northeast southeast southwest,
    north start northeast ∧
      east northeast southeast ∧
      south southeast southwest ∧
      west southwest finish

/-- A four-relation cell has a section when its clockwise composite has a
fixed point. -/
def HasRelationalSection
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) : Prop :=
  ∃ northwest,
    fourStepRelationalHolonomy north east south west northwest northwest

/-- A relation has at least one concrete pair of witnesses. -/
def RelationNonempty {A B : Type*} (relation : A → B → Prop) : Prop :=
  ∃ first second, relation first second

/-- The exact algebraic obstruction left by pairwise support: every side
relation is inhabited, but their clockwise composite has no fixed point. -/
def HasFixedPointFreeRelationalHolonomy
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) : Prop :=
  RelationNonempty north ∧
    RelationNonempty east ∧
    RelationNonempty south ∧
    RelationNonempty west ∧
    ¬ HasRelationalSection north east south west

/-- The colouring carrier at one adjacent-pair deletion. -/
abbrev DeletionColoring (data : AdjacentPairData G) :=
  (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).EdgeColoring Color

/-- The concrete witnesses of one fixed finite overlap state. -/
def overlapStateWitnessRelation
    (source target : AdjacentPairData G)
    (sourceBase : DeletionColoring source)
    (targetBase : DeletionColoring target)
    (state : OverlapKempeState) :
    DeletionColoring source → DeletionColoring target → Prop :=
  fun sourceColoring targetColoring =>
    sourceColoring ∈
        (DeletedAdjacentPairGraph G source.firstVertex
          source.secondVertex).EdgeKempeClosure sourceBase ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
        sourceColoring ∧
      targetColoring ∈
        (DeletedAdjacentPairGraph G target.firstVertex
          target.secondVertex).EdgeKempeClosure targetBase ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex)
        targetColoring ∧
      state = overlapKempeState source target sourceColoring targetColoring

/-- Membership in one pairwise support is exactly inhabitation of its
concrete witness relation. -/
theorem mem_overlapKempeStateSupport_iff_relationNonempty
    (source target : AdjacentPairData G)
    (sourceBase : DeletionColoring source)
    (targetBase : DeletionColoring target)
    (state : OverlapKempeState) :
    state ∈ overlapKempeStateSupport source target sourceBase targetBase ↔
      RelationNonempty
        (overlapStateWitnessRelation source target sourceBase targetBase state) := by
  constructor
  · rintro ⟨sourceColoring, hsourceMem, hsourceTait,
      targetColoring, htargetMem, htargetTait, hstate⟩
    exact ⟨sourceColoring, targetColoring,
      hsourceMem, hsourceTait, htargetMem, htargetTait, hstate⟩
  · rintro ⟨sourceColoring, targetColoring,
      hsourceMem, hsourceTait, htargetMem, htargetTait, hstate⟩
    exact ⟨sourceColoring, hsourceMem, hsourceTait,
      targetColoring, htargetMem, htargetTait, hstate⟩

/-- A fixed four-side state is realised by shared corner colourings exactly
when its four concrete side relations have a relational section. -/
theorem mem_overlapKempeCellStateSupport_iff_hasRelationalSection
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestBase : DeletionColoring northwest)
    (northeastBase : DeletionColoring northeast)
    (southeastBase : DeletionColoring southeast)
    (southwestBase : DeletionColoring southwest)
    (state : OverlapKempeCellState) :
    state ∈ overlapKempeCellStateSupport
        northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase ↔
      HasRelationalSection
        (overlapStateWitnessRelation northwest northeast
          northwestBase northeastBase state.north)
        (overlapStateWitnessRelation northeast southeast
          northeastBase southeastBase state.east)
        (overlapStateWitnessRelation southeast southwest
          southeastBase southwestBase state.south)
        (overlapStateWitnessRelation southwest northwest
          southwestBase northwestBase state.west) := by
  constructor
  · rintro ⟨northwestColoring, hnorthwestMem, hnorthwestTait,
      northeastColoring, hnortheastMem, hnortheastTait,
      southeastColoring, hsoutheastMem, hsoutheastTait,
      southwestColoring, hsouthwestMem, hsouthwestTait, rfl⟩
    exact ⟨northwestColoring, northeastColoring, southeastColoring,
      southwestColoring,
      ⟨hnorthwestMem, hnorthwestTait, hnortheastMem, hnortheastTait, rfl⟩,
      ⟨hnortheastMem, hnortheastTait, hsoutheastMem, hsoutheastTait, rfl⟩,
      ⟨hsoutheastMem, hsoutheastTait, hsouthwestMem, hsouthwestTait, rfl⟩,
      ⟨hsouthwestMem, hsouthwestTait, hnorthwestMem, hnorthwestTait, rfl⟩⟩
  · rintro ⟨northwestColoring, northeastColoring, southeastColoring,
      southwestColoring, hnorth, heast, hsouth, hwest⟩
    rcases hnorth with
      ⟨hnorthwestMem, hnorthwestTait, hnortheastMem, hnortheastTait,
        hnorthState⟩
    rcases heast with
      ⟨_, _, hsoutheastMem, hsoutheastTait, heastState⟩
    rcases hsouth with
      ⟨_, _, hsouthwestMem, hsouthwestTait, hsouthState⟩
    rcases hwest with ⟨_, _, _, _, hwestState⟩
    refine ⟨northwestColoring, hnorthwestMem, hnorthwestTait,
      northeastColoring, hnortheastMem, hnortheastTait,
      southeastColoring, hsoutheastMem, hsoutheastTait,
      southwestColoring, hsouthwestMem, hsouthwestTait, ?_⟩
    rcases state with ⟨northState, eastState, southState, westState⟩
    simp only at hnorthState heastState hsouthState hwestState ⊢
    subst northState
    subst eastState
    subst southState
    subst westState
    rfl

/-- Failure of the concrete lift at one pairwise-compatible state is exactly
a fixed-point-free relational holonomy on four inhabited side relations. -/
theorem mem_pairwise_not_mem_realized_iff_fixedPointFreeHolonomy
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestBase : DeletionColoring northwest)
    (northeastBase : DeletionColoring northeast)
    (southeastBase : DeletionColoring southeast)
    (southwestBase : DeletionColoring southwest)
    (state : OverlapKempeCellState) :
    state ∈ compatibleOverlapKempeCycleSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase ∧
        state ∉ overlapKempeCellStateSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase ↔
      state.IsCornerCoherent ∧
        HasFixedPointFreeRelationalHolonomy
          (overlapStateWitnessRelation northwest northeast
            northwestBase northeastBase state.north)
          (overlapStateWitnessRelation northeast southeast
            northeastBase southeastBase state.east)
          (overlapStateWitnessRelation southeast southwest
            southeastBase southwestBase state.south)
          (overlapStateWitnessRelation southwest northwest
            southwestBase northwestBase state.west) := by
  rw [mem_overlapKempeCellStateSupport_iff_hasRelationalSection]
  constructor
  · rintro ⟨⟨hnorth, heast, hsouth, hwest, hcoherent⟩, hnoSection⟩
    refine ⟨hcoherent, ?_, ?_, ?_, ?_, hnoSection⟩
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        northwest northeast northwestBase northeastBase state.north).1 hnorth
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        northeast southeast northeastBase southeastBase state.east).1 heast
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        southeast southwest southeastBase southwestBase state.south).1 hsouth
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        southwest northwest southwestBase northwestBase state.west).1 hwest
  · rintro ⟨hcoherent, hnorth, heast, hsouth, hwest, hnoSection⟩
    refine ⟨⟨?_, ?_, ?_, ?_, hcoherent⟩, hnoSection⟩
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        northwest northeast northwestBase northeastBase state.north).2 hnorth
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        northeast southeast northeastBase southeastBase state.east).2 heast
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        southeast southwest southeastBase southwestBase state.south).2 hsouth
    · exact (mem_overlapKempeStateSupport_iff_relationNonempty
        southwest northwest southwestBase northwestBase state.west).2 hwest

/-- The global lifting obstruction is equivalently the existence of one
coherent finite state carrying fixed-point-free relational holonomy. -/
theorem hasSharedWitnessObstruction_iff_exists_fixedPointFreeHolonomy
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
        HasFixedPointFreeRelationalHolonomy
          (overlapStateWitnessRelation northwest northeast
            northwestBase northeastBase state.north)
          (overlapStateWitnessRelation northeast southeast
            northeastBase southeastBase state.east)
          (overlapStateWitnessRelation southeast southwest
            southeastBase southwestBase state.south)
          (overlapStateWitnessRelation southwest northwest
            southwestBase northwestBase state.west) := by
  constructor
  · rintro ⟨state, hpairwise, hnotRealized⟩
    exact ⟨state,
      (mem_pairwise_not_mem_realized_iff_fixedPointFreeHolonomy
        northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase state).1
        ⟨hpairwise, hnotRealized⟩⟩
  · rintro ⟨state, hholonomy⟩
    exact ⟨state,
      (mem_pairwise_not_mem_realized_iff_fixedPointFreeHolonomy
        northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase state).2
        hholonomy⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing aliases for the relational-holonomy interface. -/

alias GoertzelV24AdjacentPairOverlapKempeHolonomy.mem_overlapKempeCellStateSupport_iff_hasRelationalSection :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.mem_overlapKempeCellStateSupport_iff_hasRelationalSection

alias GoertzelV24AdjacentPairOverlapKempeHolonomy.mem_pairwise_not_mem_realized_iff_fixedPointFreeHolonomy :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.mem_pairwise_not_mem_realized_iff_fixedPointFreeHolonomy

alias GoertzelV24AdjacentPairOverlapKempeHolonomy.hasSharedWitnessObstruction_iff_exists_fixedPointFreeHolonomy :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasSharedWitnessObstruction_iff_exists_fixedPointFreeHolonomy

end Mettapedia.GraphTheory.FourColor
