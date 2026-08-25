import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteStepReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellColorSplice

/-!
# A colouring-parametric tracked boundary rebase

The first executable boundary-rebase receipt was extracted at the ambient web
colouring.  That is enough to certify one source path, but not enough for the
source's transfer word: a positive entry of the literal Cell `Count` may carry
a different compatible Cell colouring.

This file removes that specialization from the tracked half of the rebase.
The successor graph, unchanged core, local residual, component graph, and
bounded twenty-eight-edge code all take an arbitrary colour function.  Their
ambient specializations are definitionally the earlier constructions.  The
closure theorem is proved at that generality, so later code may instantiate it
with the exact prefix--Cell splice rather than silently returning to the
ambient colouring.

This is only the tracked half.  It does not yet package the colour-parametric
five-field output receipt or compute a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryRebaseTrackedColorParametricEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The successor regional tracked graph, evaluated at an arbitrary colour
function rather than the ambient web colouring. -/
noncomputable def successorTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- The unchanged old/new core at an arbitrary colour function. -/
noncomputable def coreTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph web.annular.RS
    (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset
      hnext)
    color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

theorem coreTrackedGraphForColorAt_le_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    coreTrackedGraphForColorAt corridor hunique offset hnext color pair <=
      successorTrackedGraphForColorAt corridor hunique offset hnext color
        pair := by
  apply regionalTrackedEdgeGraph_mono
  intro edge hedge
  rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff corridor
    hunique offset hnext] at hedge
  exact (Finset.mem_sdiff.mp hedge).1

/-- The part of the successor graph not already supplied by the unchanged
core. -/
noncomputable def localTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  supResidual
    (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (⊥ : SimpleGraph G.edgeSet)

theorem core_sup_localTrackedForColor_eq_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    coreTrackedGraphForColorAt corridor hunique offset hnext color pair ⊔
        localTrackedGraphForColorAt corridor hunique offset hnext color pair =
      successorTrackedGraphForColorAt corridor hunique offset hnext color
        pair := by
  have h := sup_sup_supResidual_eq
    (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (⊥ : SimpleGraph G.edgeSet)
    (coreTrackedGraphForColorAt_le_successor corridor hunique offset hnext
      color pair) bot_le
  simpa [localTrackedGraphForColorAt] using h

theorem localTrackedGraphForColorAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    (localTrackedGraphForColorAt corridor hunique offset hnext color pair
      ).support <=
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨other, hadj⟩
  have hresidual := (supResidual_adj
    (successorTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (⊥ : SimpleGraph G.edgeSet) edge other).1 hadj
  have hwhole := hresidual.1
  have hnotCore := hresidual.2.1
  have hchanged : edge ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext ∨
      other ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
    by_contra hnot
    have hedgeNot : edge ∉
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
      fun h => hnot (Or.inl h)
    have hotherNot : other ∉
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
      fun h => hnot (Or.inr h)
    apply hnotCore
    refine ⟨hwhole.1, ?_, ?_⟩
    · rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        corridor hunique offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.1, hedgeNot⟩
    · rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        corridor hunique offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.2, hotherNot⟩
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ edge).2
  rcases hchanged with hedgeChanged | hotherChanged
  · exact Or.inl hedgeChanged
  · exact Or.inr ⟨other, hotherChanged, hwhole.1.1⟩

/-- The inherited component relation restricted to the finite collar. -/
noncomputable def trackedCoreComponentGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet where
  Adj left right :=
    left ≠ right ∧
      left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique
        offset hnext ∧
      right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique
        offset hnext ∧
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable left right
  symm := ⟨by
    rintro left right ⟨hne, hleft, hright, hreach⟩
    exact ⟨hne.symm, hright, hleft, hreach.symm⟩⟩
  loopless := ⟨by intro edge hadj; exact hadj.1 rfl⟩

theorem trackedCoreComponentGraphForColorAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair) :
    (trackedCoreComponentGraphForColorAt corridor hunique offset hnext color
      pair).support <=
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨other, hadj⟩
  exact hadj.2.1

theorem trackedCoreComponentGraphForColorAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair)
    (left right : G.edgeSet)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext) :
    (trackedCoreComponentGraphForColorAt corridor hunique offset hnext color
      pair).Reachable left right ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable left right := by
  constructor
  · intro hreach
    have hpath := (SimpleGraph.reachable_iff_reflTransGen left right).mp hreach
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {first second} _ =>
        (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
          ).Reachable first second)
      hpath (fun _ => SimpleGraph.Reachable.rfl)
      (fun hadj => hadj.2.2.2)
      (fun _ _ hfirst hsecond => hfirst.trans hsecond)
  · intro hreach
    by_cases heq : left = right
    · subst right
      exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable (show
        (trackedCoreComponentGraphForColorAt corridor hunique offset hnext
          color pair).Adj left right from
          ⟨heq, hleft, hright, hreach⟩)

/-- Bounded two-factor tracked code at an arbitrary colour function. -/
noncomputable def trackedCollarCodeForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) :
    BoundedCarrierGraphFamilyCode 28 4 (TrackedColorPair × Bool) :=
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    28 4
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight corridor
      hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique offset
      hnext)
    (fun family => if family.2 then
      localTrackedGraphForColorAt corridor hunique offset hnext color family.1
    else
      trackedCoreComponentGraphForColorAt corridor hunique offset hnext color
        family.1)

theorem trackedCollarCodeForColorAt_false_reachable_iff_core
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext}) :
    ((trackedCollarCodeForColorAt corridor hunique offset hnext color).graph
      (pair, false)).Reachable
        (carrierCoordinate _ left) (carrierCoordinate _ right) ↔
      (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable left.1 right.1 := by
  have hcode := boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    28 4
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight corridor
      hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique offset
      hnext)
    (fun family : TrackedColorPair × Bool => if family.2 then
      localTrackedGraphForColorAt corridor hunique offset hnext color family.1
    else
      trackedCoreComponentGraphForColorAt corridor hunique offset hnext color
        family.1)
    (pair, false)
    (by simpa using
      (trackedCoreComponentGraphForColorAt_support_subset_collar corridor
        hunique offset hnext color pair))
    left right
  simp only [Bool.false_eq_true, if_false] at hcode
  rw [trackedCoreComponentGraphForColorAt_reachable_iff corridor hunique offset
    hnext color pair left.1 right.1 left.2 right.2] at hcode
  simpa [trackedCollarCodeForColorAt] using hcode

theorem trackedCollarCodeForColorAt_true_reachable_iff_local
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext}) :
    ((trackedCollarCodeForColorAt corridor hunique offset hnext color).graph
      (pair, true)).Reachable
        (carrierCoordinate _ left) (carrierCoordinate _ right) ↔
      (localTrackedGraphForColorAt corridor hunique offset hnext color pair
        ).Reachable left.1 right.1 := by
  have hcode := boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    28 4
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight corridor
      hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique offset
      hnext)
    (fun family : TrackedColorPair × Bool => if family.2 then
      localTrackedGraphForColorAt corridor hunique offset hnext color family.1
    else
      trackedCoreComponentGraphForColorAt corridor hunique offset hnext color
        family.1)
    (pair, true)
    (by simpa using
      (localTrackedGraphForColorAt_support_subset_collar corridor hunique offset
        hnext color pair))
    left right
  simpa [trackedCollarCodeForColorAt] using hcode

set_option maxHeartbeats 800000 in
/-- Successor reachability for an arbitrary colour function is exactly the
closure of the two bounded coded factors. -/
theorem successorTrackedForColor_reachable_iff_collarCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color) (pair : TrackedColorPair)
    (left right : G.edgeSet)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext) :
    (successorTrackedGraphForColorAt corridor hunique offset hnext color pair
      ).Reachable left right ↔
      Relation.ReflTransGen
        (fun first second : Fin
            (trackedCollarCodeForColorAt corridor hunique offset hnext color
              ).vertexCount.val =>
          ((trackedCollarCodeForColorAt corridor hunique offset hnext color
            ).graph (pair, false)).Reachable first second ∨
          ((trackedCollarCodeForColorAt corridor hunique offset hnext color
            ).graph (pair, true)).Reachable first second)
        (carrierCoordinate _ ⟨left, hleft⟩)
        (carrierCoordinate _ ⟨right, hright⟩) := by
  let carrier :=
    sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext
  let coordinate := carrierCoordinate carrier
  rw [← core_sup_localTrackedForColor_eq_successor corridor hunique offset
    hnext color pair]
  have hsup := reachable_sup_iff_subtype_componentClosure
    (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (localTrackedGraphForColorAt corridor hunique offset hnext color pair)
    (fun edge => edge ∈ carrier) left right hleft hright (by
      intro x middle y _hx hmiddleY _hcore hlocal
      apply localTrackedGraphForColorAt_support_subset_collar corridor hunique
        offset hnext color pair
      exact SimpleGraph.mem_support_of_reachable hmiddleY hlocal)
  rw [hsup]
  have hstep (first second : {edge // edge ∈ carrier}) :
        (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
            ).Reachable first.1 second.1 ∨
          (localTrackedGraphForColorAt corridor hunique offset hnext color pair
            ).Reachable first.1 second.1 ↔
        ((trackedCollarCodeForColorAt corridor hunique offset hnext color
          ).graph (pair, false)).Reachable
            (coordinate first) (coordinate second) ∨
          ((trackedCollarCodeForColorAt corridor hunique offset hnext color
            ).graph (pair, true)).Reachable
              (coordinate first) (coordinate second) := by
    constructor
    · rintro (hcore | hlocal)
      · exact Or.inl
          ((trackedCollarCodeForColorAt_false_reachable_iff_core corridor
            hunique offset hnext color pair first second).2 hcore)
      · exact Or.inr
          ((trackedCollarCodeForColorAt_true_reachable_iff_local corridor
            hunique offset hnext color pair first second).2 hlocal)
    · rintro (hcore | hlocal)
      · exact Or.inl
          ((trackedCollarCodeForColorAt_false_reachable_iff_core corridor
            hunique offset hnext color pair first second).1 hcore)
      · exact Or.inr
          ((trackedCollarCodeForColorAt_true_reachable_iff_local corridor
            hunique offset hnext color pair first second).1 hlocal)
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
  · intro hclosure
    have hlift : Relation.ReflTransGen
        (fun first second : {edge // edge ∈ carrier} =>
          (coreTrackedGraphForColorAt corridor hunique offset hnext color pair
              ).Reachable first.1 second.1 ∨
            (localTrackedGraphForColorAt corridor hunique offset hnext color
              pair).Reachable first.1 second.1)
        (coordinate.symm (coordinate ⟨left, hleft⟩))
        (coordinate.symm (coordinate ⟨right, hright⟩)) :=
      Relation.ReflTransGen.lift coordinate.symm
        (fun first second h => by
          rw [← Equiv.apply_symm_apply coordinate first,
            ← Equiv.apply_symm_apply coordinate second] at h
          exact
            (hstep (coordinate.symm first) (coordinate.symm second)).2 h)
        hclosure
    simpa only [Equiv.symm_apply_apply] using hlift

/-- At the ambient web colouring the generalized code is definitionally the
previously proved code. -/
@[simp]
theorem trackedCollarCodeForColorAt_ambient
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    trackedCollarCodeForColorAt corridor hunique offset hnext coloring =
      sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique offset
        hnext := by
  simp only [trackedCollarCodeForColorAt,
    sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt,
    localTrackedGraphForColorAt,
    sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt,
    successorTrackedGraphForColorAt,
    sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt,
    coreTrackedGraphForColorAt,
    sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt,
    trackedCoreComponentGraphForColorAt,
    sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt]

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric

end Mettapedia.GraphTheory.FourColor
