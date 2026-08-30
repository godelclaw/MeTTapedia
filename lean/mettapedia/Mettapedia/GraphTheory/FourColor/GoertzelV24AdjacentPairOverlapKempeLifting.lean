import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeCell

/-!
# When pairwise overlap states support shared corner witnesses

The four-side overlap relation remembers only a finite boundary observation at
each corner.  Pairwise compatibility therefore need not identify the concrete
colourings used by the two incident sides.  This file isolates the exact
positive condition under which the naive compatible cycle does lift: the
finite boundary observation must separate the proper colourings in each of the
four selected Kempe orbits.

No wall-exclusion or geometric flatness claim is made.  The theorem is a
consumer-facing criterion for any later argument that proves orbit separation,
or replaces the observation by a quotient with unique fibres.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The finite boundary observation separates all proper colourings in the
selected Kempe orbit.  Membership and the nonzero condition are both explicit
because a Kempe closure may contain intermediate colourings using zero. -/
def BoundaryKempeStateSeparatesOrbit
    (data : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) : Prop :=
  ∀ firstColoring,
    firstColoring ∈
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeKempeClosure base →
    IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        firstColoring →
    ∀ secondColoring,
      secondColoring ∈
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).EdgeKempeClosure base →
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          secondColoring →
      boundaryKempeState data firstColoring =
          boundaryKempeState data secondColoring →
      firstColoring = secondColoring

/-- An explicit nontrivial fibre of the finite boundary observation inside one
proper Kempe orbit. -/
def HasBoundaryKempeStateCollision
    (data : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) : Prop :=
  ∃ firstColoring,
    firstColoring ∈
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeKempeClosure base ∧
    IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        firstColoring ∧
    ∃ secondColoring,
      secondColoring ∈
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).EdgeKempeClosure base ∧
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          secondColoring ∧
      boundaryKempeState data firstColoring =
          boundaryKempeState data secondColoring ∧
      firstColoring ≠ secondColoring

/-- Failure of orbit separation is exactly a concrete collision in one finite
boundary-state fibre. -/
theorem hasBoundaryKempeStateCollision_iff_not_separatesOrbit
    (data : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) :
    HasBoundaryKempeStateCollision data base ↔
      ¬ BoundaryKempeStateSeparatesOrbit data base := by
  classical
  constructor
  · rintro ⟨firstColoring, hfirstMem, hfirstTait,
      secondColoring, hsecondMem, hsecondTait, hstate, hne⟩ hseparates
    exact hne (hseparates firstColoring hfirstMem hfirstTait
      secondColoring hsecondMem hsecondTait hstate)
  · intro hnot
    unfold BoundaryKempeStateSeparatesOrbit at hnot
    push Not at hnot
    rcases hnot with
      ⟨firstColoring, hfirstMem, hfirstTait,
        secondColoring, hsecondMem, hsecondTait, hstate, hne⟩
    exact ⟨firstColoring, hfirstMem, hfirstTait,
      secondColoring, hsecondMem, hsecondTait, hstate, hne⟩

/-- If the boundary observation has singleton proper fibres in all four corner
orbits, every pairwise-compatible cycle has one shared choice of concrete
corner witnesses. -/
theorem hasSharedWitnessLifting_of_boundaryKempeStateSeparatesOrbits
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestBase :
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex).EdgeColoring Color)
    (northeastBase :
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex).EdgeColoring Color)
    (southeastBase :
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex).EdgeColoring Color)
    (southwestBase :
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex).EdgeColoring Color)
    (hnorthwest : BoundaryKempeStateSeparatesOrbit northwest northwestBase)
    (hnortheast : BoundaryKempeStateSeparatesOrbit northeast northeastBase)
    (hsoutheast : BoundaryKempeStateSeparatesOrbit southeast southeastBase)
    (hsouthwest : BoundaryKempeStateSeparatesOrbit southwest southwestBase) :
    HasSharedWitnessLifting
      (overlapKempeCellStateSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase)
      (compatibleOverlapKempeCycleSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase) := by
  intro state hstate
  rcases hstate with ⟨hnorth, heast, hsouth, hwest, hcoherent⟩
  rcases hnorth with
    ⟨northwestNorth, hnorthwestNorthMem, hnorthwestNorthTait,
      northeastNorth, hnortheastNorthMem, hnortheastNorthTait, hnorth⟩
  rcases heast with
    ⟨northeastEast, hnortheastEastMem, hnortheastEastTait,
      southeastEast, hsoutheastEastMem, hsoutheastEastTait, heast⟩
  rcases hsouth with
    ⟨southeastSouth, hsoutheastSouthMem, hsoutheastSouthTait,
      southwestSouth, hsouthwestSouthMem, hsouthwestSouthTait, hsouth⟩
  rcases hwest with
    ⟨southwestWest, hsouthwestWestMem, hsouthwestWestTait,
      northwestWest, hnorthwestWestMem, hnorthwestWestTait, hwest⟩
  change state.north.targetBoundary = state.east.sourceBoundary ∧
      state.east.targetBoundary = state.south.sourceBoundary ∧
      state.south.targetBoundary = state.west.sourceBoundary ∧
      state.west.targetBoundary = state.north.sourceBoundary at hcoherent
  rw [hnorth, heast, hsouth, hwest] at hcoherent
  have hnortheastEq : northeastNorth = northeastEast :=
    hnortheast northeastNorth hnortheastNorthMem hnortheastNorthTait
      northeastEast hnortheastEastMem hnortheastEastTait hcoherent.1
  have hsoutheastEq : southeastEast = southeastSouth :=
    hsoutheast southeastEast hsoutheastEastMem hsoutheastEastTait
      southeastSouth hsoutheastSouthMem hsoutheastSouthTait hcoherent.2.1
  have hsouthwestEq : southwestSouth = southwestWest :=
    hsouthwest southwestSouth hsouthwestSouthMem hsouthwestSouthTait
      southwestWest hsouthwestWestMem hsouthwestWestTait hcoherent.2.2.1
  have hnorthwestEq : northwestNorth = northwestWest :=
    hnorthwest northwestNorth hnorthwestNorthMem hnorthwestNorthTait
      northwestWest hnorthwestWestMem hnorthwestWestTait hcoherent.2.2.2.symm
  subst northeastEast
  subst southeastSouth
  subst southwestWest
  subst northwestWest
  refine ⟨northwestNorth, hnorthwestNorthMem, hnorthwestNorthTait,
    northeastNorth, hnortheastNorthMem, hnortheastNorthTait,
    southeastEast, hsoutheastEastMem, hsoutheastEastTait,
    southwestSouth, hsouthwestSouthMem, hsouthwestSouthTait, ?_⟩
  cases state
  simp_all [overlapKempeCellState]

/-- Consequently, if shared-witness lifting fails, at least one corner has a
nontrivial proper boundary-state fibre.  This identifies the exact local debt;
it does not claim that every collision produces a global obstruction. -/
theorem exists_corner_boundaryKempeStateCollision_of_not_sharedWitnessLifting
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestBase :
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex).EdgeColoring Color)
    (northeastBase :
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex).EdgeColoring Color)
    (southeastBase :
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex).EdgeColoring Color)
    (southwestBase :
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex).EdgeColoring Color)
    (hlifting : ¬ HasSharedWitnessLifting
      (overlapKempeCellStateSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase)
      (compatibleOverlapKempeCycleSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase)) :
    HasBoundaryKempeStateCollision northwest northwestBase ∨
      HasBoundaryKempeStateCollision northeast northeastBase ∨
      HasBoundaryKempeStateCollision southeast southeastBase ∨
      HasBoundaryKempeStateCollision southwest southwestBase := by
  classical
  by_contra hnone
  push Not at hnone
  have hnorthwestSeparates :
      BoundaryKempeStateSeparatesOrbit northwest northwestBase := by
    by_contra hnot
    exact hnone.1
      ((hasBoundaryKempeStateCollision_iff_not_separatesOrbit
        northwest northwestBase).2 hnot)
  have hnortheastSeparates :
      BoundaryKempeStateSeparatesOrbit northeast northeastBase := by
    by_contra hnot
    exact hnone.2.1
      ((hasBoundaryKempeStateCollision_iff_not_separatesOrbit
        northeast northeastBase).2 hnot)
  have hsoutheastSeparates :
      BoundaryKempeStateSeparatesOrbit southeast southeastBase := by
    by_contra hnot
    exact hnone.2.2.1
      ((hasBoundaryKempeStateCollision_iff_not_separatesOrbit
        southeast southeastBase).2 hnot)
  have hsouthwestSeparates :
      BoundaryKempeStateSeparatesOrbit southwest southwestBase := by
    by_contra hnot
    exact hnone.2.2.2
      ((hasBoundaryKempeStateCollision_iff_not_separatesOrbit
        southwest southwestBase).2 hnot)
  exact hlifting
    (hasSharedWitnessLifting_of_boundaryKempeStateSeparatesOrbits
      northwest northeast southeast southwest
      northwestBase northeastBase southeastBase southwestBase
      hnorthwestSeparates hnortheastSeparates
      hsoutheastSeparates hsouthwestSeparates)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing aliases for the lifting criterion. -/

alias GoertzelV24AdjacentPairOverlapKempeLifting.hasBoundaryKempeStateCollision_iff_not_separatesOrbit :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasBoundaryKempeStateCollision_iff_not_separatesOrbit

alias GoertzelV24AdjacentPairOverlapKempeLifting.hasSharedWitnessLifting_of_boundaryKempeStateSeparatesOrbits :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasSharedWitnessLifting_of_boundaryKempeStateSeparatesOrbits

alias GoertzelV24AdjacentPairOverlapKempeLifting.exists_corner_boundaryKempeStateCollision_of_not_sharedWitnessLifting :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.exists_corner_boundaryKempeStateCollision_of_not_sharedWitnessLifting

end Mettapedia.GraphTheory.FourColor
