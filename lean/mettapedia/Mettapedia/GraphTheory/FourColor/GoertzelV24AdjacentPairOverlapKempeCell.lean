import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeState

/-!
# Coherent composition of four adjacent-pair overlap relations

Pairwise overlap supports cannot be composed merely by matching their finite
boundary observations: two occurrences of the same observation may be
witnessed by different colourings of the intermediate deletion.  This file
records the first exact two-dimensional object.  A cell state is evaluated
from one actual colouring at each of four corners, and neighbouring overlap
states reuse that same corner colouring.

The realised cell support is finite, nonempty for proper base colourings, and
independent of the chosen representatives of the four Kempe orbits.  Every
realised cell projects to the four pairwise overlap supports and its adjacent
boundary observations agree.  Only inclusion in the corresponding naive
compatible cycle is claimed; the converse would require a genuine lifting
theorem and is deliberately not assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- Four clockwise pairwise observations around one relational cell. -/
structure OverlapKempeCellState where
  north : OverlapKempeState
  east : OverlapKempeState
  south : OverlapKempeState
  west : OverlapKempeState
deriving DecidableEq

/-- A product code exhibiting that the cell observation space is finite. -/
abbrev OverlapKempeCellStateCode :=
  OverlapKempeState × OverlapKempeState ×
    OverlapKempeState × OverlapKempeState

/-- Forget the field labels of a cell state. -/
def overlapKempeCellStateEquiv :
    OverlapKempeCellState ≃ OverlapKempeCellStateCode where
  toFun state := (state.north, state.east, state.south, state.west)
  invFun code :=
    { north := code.1
      east := code.2.1
      south := code.2.2.1
      west := code.2.2.2 }
  left_inv state := by cases state; rfl
  right_inv code := by rcases code with ⟨_, _, _, _⟩; rfl

noncomputable instance overlapKempeCellStateFintype :
    Fintype OverlapKempeCellState :=
  Fintype.ofEquiv OverlapKempeCellStateCode overlapKempeCellStateEquiv.symm

/-- Adjacent sides of a cell carry literally equal observations of their
shared corner deletion. -/
def OverlapKempeCellState.IsCornerCoherent
    (state : OverlapKempeCellState) : Prop :=
  state.north.targetBoundary = state.east.sourceBoundary ∧
    state.east.targetBoundary = state.south.sourceBoundary ∧
    state.south.targetBoundary = state.west.sourceBoundary ∧
    state.west.targetBoundary = state.north.sourceBoundary

/-- Evaluate the clockwise cell observation on four concrete colourings.
The same colouring is used by the two sides meeting at each corner. -/
def overlapKempeCellState
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestColoring :
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex).EdgeColoring Color)
    (northeastColoring :
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex).EdgeColoring Color)
    (southeastColoring :
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex).EdgeColoring Color)
    (southwestColoring :
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex).EdgeColoring Color) :
    OverlapKempeCellState where
  north := overlapKempeState northwest northeast
    northwestColoring northeastColoring
  east := overlapKempeState northeast southeast
    northeastColoring southeastColoring
  south := overlapKempeState southeast southwest
    southeastColoring southwestColoring
  west := overlapKempeState southwest northwest
    southwestColoring northwestColoring

/-- Concrete cell evaluation is coherent at all four corners by
construction. -/
theorem overlapKempeCellState_isCornerCoherent
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestColoring :
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex).EdgeColoring Color)
    (northeastColoring :
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex).EdgeColoring Color)
    (southeastColoring :
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex).EdgeColoring Color)
    (southwestColoring :
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex).EdgeColoring Color) :
    OverlapKempeCellState.IsCornerCoherent
      (overlapKempeCellState northwest northeast southeast southwest
        northwestColoring northeastColoring southeastColoring southwestColoring) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The canonical finite cell relation realised by one proper colouring at
each corner, with each colouring drawn from its selected Kempe orbit. -/
def overlapKempeCellStateSupport
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
        southwest.secondVertex).EdgeColoring Color) :
    Set OverlapKempeCellState :=
  {state | ∃ northwestColoring,
      northwestColoring ∈
        (DeletedAdjacentPairGraph G northwest.firstVertex
          northwest.secondVertex).EdgeKempeClosure northwestBase ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G northwest.firstVertex
          northwest.secondVertex) northwestColoring ∧
      ∃ northeastColoring,
        northeastColoring ∈
          (DeletedAdjacentPairGraph G northeast.firstVertex
            northeast.secondVertex).EdgeKempeClosure northeastBase ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G northeast.firstVertex
            northeast.secondVertex) northeastColoring ∧
        ∃ southeastColoring,
          southeastColoring ∈
            (DeletedAdjacentPairGraph G southeast.firstVertex
              southeast.secondVertex).EdgeKempeClosure southeastBase ∧
          IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G southeast.firstVertex
              southeast.secondVertex) southeastColoring ∧
          ∃ southwestColoring,
            southwestColoring ∈
              (DeletedAdjacentPairGraph G southwest.firstVertex
                southwest.secondVertex).EdgeKempeClosure southwestBase ∧
            IsTaitEdgeColoring
              (DeletedAdjacentPairGraph G southwest.firstVertex
                southwest.secondVertex) southwestColoring ∧
            state = overlapKempeCellState
              northwest northeast southeast southwest
              northwestColoring northeastColoring
              southeastColoring southwestColoring}

/-- Replacing any of the four base colourings by a reachable representative
does not change the realised cell relation. -/
theorem overlapKempeCellStateSupport_eq_of_mem
    (northwest northeast southeast southwest : AdjacentPairData G)
    {northwestBase northwestRepresentative :
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex).EdgeColoring Color}
    {northeastBase northeastRepresentative :
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex).EdgeColoring Color}
    {southeastBase southeastRepresentative :
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex).EdgeColoring Color}
    {southwestBase southwestRepresentative :
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex).EdgeColoring Color}
    (hnorthwest : northwestRepresentative ∈
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex).EdgeKempeClosure northwestBase)
    (hnortheast : northeastRepresentative ∈
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex).EdgeKempeClosure northeastBase)
    (hsoutheast : southeastRepresentative ∈
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex).EdgeKempeClosure southeastBase)
    (hsouthwest : southwestRepresentative ∈
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex).EdgeKempeClosure southwestBase) :
    overlapKempeCellStateSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase =
      overlapKempeCellStateSupport northwest northeast southeast southwest
        northwestRepresentative northeastRepresentative
        southeastRepresentative southwestRepresentative := by
  have hnorthwestClosure :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem hnorthwest
  have hnortheastClosure :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem hnortheast
  have hsoutheastClosure :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem hsoutheast
  have hsouthwestClosure :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem hsouthwest
  simp only [overlapKempeCellStateSupport, hnorthwestClosure,
    hnortheastClosure, hsoutheastClosure, hsouthwestClosure]

/-- Proper base colourings themselves realise a coherent cell state. -/
theorem overlapKempeCellStateSupport_nonempty
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
    (hnorthwest : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G northwest.firstVertex
        northwest.secondVertex) northwestBase)
    (hnortheast : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G northeast.firstVertex
        northeast.secondVertex) northeastBase)
    (hsoutheast : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G southeast.firstVertex
        southeast.secondVertex) southeastBase)
    (hsouthwest : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G southwest.firstVertex
        southwest.secondVertex) southwestBase) :
    (overlapKempeCellStateSupport northwest northeast southeast southwest
      northwestBase northeastBase southeastBase southwestBase).Nonempty := by
  refine ⟨overlapKempeCellState northwest northeast southeast southwest
    northwestBase northeastBase southeastBase southwestBase, ?_⟩
  exact ⟨northwestBase, SimpleGraph.mem_edgeKempeClosure_self _, hnorthwest,
    northeastBase, SimpleGraph.mem_edgeKempeClosure_self _, hnortheast,
    southeastBase, SimpleGraph.mem_edgeKempeClosure_self _, hsoutheast,
    southwestBase, SimpleGraph.mem_edgeKempeClosure_self _, hsouthwest, rfl⟩

/-- The pairwise-compatible cycle obtained by forgetting that neighbouring
sides were witnessed by the same concrete corner colourings. -/
def compatibleOverlapKempeCycleSupport
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
        southwest.secondVertex).EdgeColoring Color) :
    Set OverlapKempeCellState :=
  {state |
    state.north ∈ overlapKempeStateSupport
      northwest northeast northwestBase northeastBase ∧
    state.east ∈ overlapKempeStateSupport
      northeast southeast northeastBase southeastBase ∧
    state.south ∈ overlapKempeStateSupport
      southeast southwest southeastBase southwestBase ∧
    state.west ∈ overlapKempeStateSupport
      southwest northwest southwestBase northwestBase ∧
    state.IsCornerCoherent}

/-- Exact cell composition implies pairwise compatibility.  The reverse
inclusion is intentionally not asserted: its pairwise witnesses need not
choose one common colouring at a corner. -/
theorem overlapKempeCellStateSupport_subset_compatibleCycleSupport
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
        southwest.secondVertex).EdgeColoring Color) :
    overlapKempeCellStateSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase ⊆
      compatibleOverlapKempeCycleSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase := by
  intro state hstate
  rcases hstate with
    ⟨northwestColoring, hnorthwestMem, hnorthwestTait,
      northeastColoring, hnortheastMem, hnortheastTait,
      southeastColoring, hsoutheastMem, hsoutheastTait,
      southwestColoring, hsouthwestMem, hsouthwestTait, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨northwestColoring, hnorthwestMem, hnorthwestTait,
      northeastColoring, hnortheastMem, hnortheastTait, rfl⟩
  · exact ⟨northeastColoring, hnortheastMem, hnortheastTait,
      southeastColoring, hsoutheastMem, hsoutheastTait, rfl⟩
  · exact ⟨southeastColoring, hsoutheastMem, hsoutheastTait,
      southwestColoring, hsouthwestMem, hsouthwestTait, rfl⟩
  · exact ⟨southwestColoring, hsouthwestMem, hsouthwestTait,
      northwestColoring, hnorthwestMem, hnorthwestTait, rfl⟩
  · exact overlapKempeCellState_isCornerCoherent
      northwest northeast southeast southwest
      northwestColoring northeastColoring southeastColoring southwestColoring

/-- The exact missing converse: every pairwise-compatible observation has
one choice of concrete corner witnesses shared by its two incident sides. -/
def HasSharedWitnessLifting
    (realized pairwise : Set OverlapKempeCellState) : Prop :=
  pairwise ⊆ realized

/-- A finite observation witnessing failure of shared-corner lifting.  This
is only an obstruction datum; calling it a geometric holonomy requires a
separate theorem relating the observation to an embedded region. -/
def HasSharedWitnessObstruction
    (realized pairwise : Set OverlapKempeCellState) : Prop :=
  ∃ state, state ∈ pairwise ∧ state ∉ realized

/-- Shared-witness lifting either holds or has one explicit finite-state
obstruction.  This logical dichotomy proves neither route-specific horn. -/
theorem sharedWitnessLifting_or_obstruction
    (realized pairwise : Set OverlapKempeCellState) :
    HasSharedWitnessLifting realized pairwise ∨
      HasSharedWitnessObstruction realized pairwise := by
  classical
  by_cases hlifts : pairwise ⊆ realized
  · exact Or.inl hlifts
  · exact Or.inr (Set.not_subset.mp hlifts)

/-- Once exact composition is known to project into the pairwise cycle,
equality is equivalent to the shared-witness lifting obligation. -/
theorem eq_iff_hasSharedWitnessLifting_of_subset
    {realized pairwise : Set OverlapKempeCellState}
    (hsubset : realized ⊆ pairwise) :
    realized = pairwise ↔ HasSharedWitnessLifting realized pairwise := by
  constructor
  · intro heq
    simpa [HasSharedWitnessLifting, heq]
  · intro hlifts
    exact Set.Subset.antisymm hsubset hlifts

/-- For the four adjacent-pair orbit relations, the desired equality with
the naive compatible cycle is exactly shared-witness lifting. -/
theorem overlapKempeCellStateSupport_eq_compatibleCycleSupport_iff
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
        southwest.secondVertex).EdgeColoring Color) :
    overlapKempeCellStateSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase =
      compatibleOverlapKempeCycleSupport northwest northeast southeast southwest
        northwestBase northeastBase southeastBase southwestBase ↔
      HasSharedWitnessLifting
        (overlapKempeCellStateSupport northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase)
        (compatibleOverlapKempeCycleSupport northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase) :=
  eq_iff_hasSharedWitnessLifting_of_subset
    (overlapKempeCellStateSupport_subset_compatibleCycleSupport
      northwest northeast southeast southwest
      northwestBase northeastBase southeastBase southwestBase)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing aliases for the cell-composition interface. -/

alias GoertzelV24AdjacentPairOverlapKempeCell.overlapKempeCellStateSupport_eq_of_mem :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeCellStateSupport_eq_of_mem

alias GoertzelV24AdjacentPairOverlapKempeCell.overlapKempeCellStateSupport_nonempty :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeCellStateSupport_nonempty

alias GoertzelV24AdjacentPairOverlapKempeCell.overlapKempeCellStateSupport_subset_compatibleCycleSupport :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeCellStateSupport_subset_compatibleCycleSupport

alias GoertzelV24AdjacentPairOverlapKempeCell.sharedWitnessLifting_or_obstruction :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.sharedWitnessLifting_or_obstruction

alias GoertzelV24AdjacentPairOverlapKempeCell.overlapKempeCellStateSupport_eq_compatibleCycleSupport_iff :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeCellStateSupport_eq_compatibleCycleSupport_iff

end Mettapedia.GraphTheory.FourColor
