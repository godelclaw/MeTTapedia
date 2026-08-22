import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollar
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupResidual

/-!
# Exact facial recurrence through the actual rebase collar

The preceding module bounds the support on which a literal boundary rebase can
change facial adjacency.  This file turns that locality statement into an exact
component recurrence.  The successor regional face graph is the union of its
unchanged core and a canonical local residual supported on the at-most-
twenty-four-dart collar.  Reachability between collar darts is therefore the
closure of whole-core moves and local-residual moves on that finite interface.

This is still a semantic recurrence on actual darts.  It does not yet encode
the collar in `Fin 24`, recover the core-component relation from the predecessor
receipt, or construct the graph-free successor profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFaceCollarRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The successor regional face graph for one actual boundary rebase. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph web.annular.RS.D :=
  faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))

/-- The unchanged facial graph after removing the literal switch edges. -/
noncomputable def sourceLocalLayerBoundaryRebaseCoreFaceGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph web.annular.RS.D :=
  faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerBoundaryRebaseFaceCoreRegionAt corridor hunique offset hnext)

/-- The canonical successor facial residue not already present in the common
core. -/
noncomputable def sourceLocalLayerBoundaryRebaseLocalFaceGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph web.annular.RS.D :=
  supResidual
    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset hnext)
    ⊥

theorem sourceLocalLayerBoundaryRebaseCoreFaceGraphAt_le_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset hnext ≤
      sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset hnext := by
  intro left right hadj
  simp only [sourceLocalLayerBoundaryRebaseCoreFaceGraphAt,
    sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt,
    faceRegionalDartGraph_adj] at hadj ⊢
  refine ⟨hadj.1, hadj.2.1, ?_, ?_⟩
  · have hmem := hadj.2.2.1
    rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
      corridor hunique offset hnext] at hmem
    exact (Finset.mem_sdiff.mp hmem).1
  · have hmem := hadj.2.2.2
    rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
      corridor hunique offset hnext] at hmem
    exact (Finset.mem_sdiff.mp hmem).1

/-- The successor graph is exactly its unchanged core plus the canonical local
residue. -/
theorem sourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset hnext ⊔
        sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset hnext =
      sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset hnext := by
  have h := sup_sup_supResidual_eq
    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset hnext)
    (⊥ : SimpleGraph web.annular.RS.D)
    (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt_le_successor corridor hunique
      offset hnext)
    bot_le
  simpa [sourceLocalLayerBoundaryRebaseLocalFaceGraphAt] using h

/-- Every dart touched by the genuinely local successor factor belongs to the
one-step facial collar. -/
theorem sourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset hnext).support ⊆
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨other, hadj⟩
  have hresidual := (supResidual_adj
    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset hnext)
    ⊥ dart other).1 hadj
  have hwhole := hresidual.1
  have hnotCore := hresidual.2.1
  have hchanged : web.annular.RS.edgeOf dart ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext ∨
      web.annular.RS.edgeOf other ∈
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
    by_contra hnot
    have hdartNot : web.annular.RS.edgeOf dart ∉
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
      fun h => hnot (Or.inl h)
    have hotherNot : web.annular.RS.edgeOf other ∉
        sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext :=
      fun h => hnot (Or.inr h)
    apply hnotCore
    simp only [sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt,
      sourceLocalLayerBoundaryRebaseCoreFaceGraphAt,
      faceRegionalDartGraph_adj] at hwhole ⊢
    refine ⟨hwhole.1, hwhole.2.1, ?_, ?_⟩
    · rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        corridor hunique offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.2.1, hdartNot⟩
    · rw [sourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        corridor hunique offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.2.2, hotherNot⟩
  rcases hchanged with hdartChanged | hotherChanged
  · exact
      sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar corridor
        hunique offset hnext (by simpa using hdartChanged)
  · exact
      (sourceLocalLayerBoundaryRebaseFaceCollarAt_of_adj_of_changed corridor
        hunique offset hnext
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)) hwhole.symm
        hotherChanged).2

/-- Exact successor reachability on the finite collar: alternate whole-core
component moves with moves in the local residual. -/
theorem sourceLocalLayerBoundaryRebaseSuccessor_reachable_iff_collarComponentClosure
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : web.annular.RS.D)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext) :
    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset
      hnext).Reachable left right ↔
      Relation.ReflTransGen
        (fun first second : Subtype (fun dart =>
            dart ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
              offset hnext) =>
          (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
            hnext).Reachable first.1 second.1 ∨
          (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset
            hnext).Reachable first.1 second.1)
        ⟨left, hleft⟩ ⟨right, hright⟩ := by
  rw [← sourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor corridor
    hunique offset hnext]
  apply reachable_sup_iff_subtype_componentClosure
  intro x middle y _hx hmiddleY _hcore hlocal
  apply sourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
    corridor hunique offset hnext
  exact SimpleGraph.mem_support_of_reachable hmiddleY hlocal

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
