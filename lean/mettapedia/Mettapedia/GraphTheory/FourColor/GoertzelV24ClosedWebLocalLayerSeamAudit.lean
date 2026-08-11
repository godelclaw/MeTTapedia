import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerBoundary

/-!
# Audit of the local Cell-3 layer seam

The two paths constructed from one Cell-3 tile are genuine local open-layer
data.  They must not be silently promoted to the closed retained-vertex splice:
at their first local corner the two crossed primal edges share an endpoint.

This is not a failure of the source route.  Addendum XXVII takes profiles on
completed simple transversals or layer boundaries; the local tile is one
generator from which such a boundary must be assembled.  Recording the corner
fact here makes that distinction available to the later assembly proof.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSeamAuditEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The two first crossed edges of a source-local Cell-3 layer share the
literal corner immediately before the outgoing rung. -/
theorem SourceLocalLayerPairWitness.exists_common_first_crossing_endpoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    ∃ vertex,
      vertex ∈ web.annular.RS.endpoints
        (dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          witness.toLocalLayerPair.firstWalk
          ⟨0, by simp [LocalLayerPair.firstWalk]⟩) ∧
      vertex ∈ web.annular.RS.endpoints
        (dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          witness.toLocalLayerPair.secondWalk
          ⟨0, by simp [LocalLayerPair.secondWalk]⟩) := by
  let RS := web.annular.RS
  let beforeDart := faceCycleDart RS witness.placement.root witness.before.1
  let vertex := RS.vertOf (RS.phi beforeDart)
  refine ⟨vertex, ?_, ?_⟩
  · rw [witness.firstWalk_crossingEdge_zero_eq_beforeEdge]
    rw [RS.mem_endpoints_iff]
    refine ⟨RS.alpha beforeDart, RS.mem_dartsOn.2 ?_, ?_⟩
    · exact RS.edge_alpha beforeDart
    · simp [vertex]
  · rw [witness.secondWalk_crossingEdge_zero_eq_beforeThirdEdge]
    rw [RS.mem_endpoints_iff]
    refine ⟨RS.rho (RS.phi beforeDart), RS.mem_dartsOn.2 rfl, ?_⟩
    simpa [vertex] using
      (RS.vert_rho (RS.phi beforeDart)).trans
        (RS.vert_phi_eq_vert_alpha beforeDart)

/-- A local Cell-3 tile cannot itself meet the endpoint-disjointness premise
of the *closed* retained-vertex splice: its first matched crossings meet at
the source corner proved above.  The source's primary operation remains the
open-tangle splice; a later global layer assembly supplies the completed
boundary needed for a closed specialization. -/
theorem SourceLocalLayerPairWitness.not_matchedCrossingsVertexDisjoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    ¬ GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation
        (witness.toLocalLayerPair.separatedLocalLayerPair hunique) := by
  let pair := witness.toLocalLayerPair.separatedLocalLayerPair hunique
  change ¬ GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.MatchedCrossingsVertexDisjoint
    web.annular.cellulation.rotation pair
  intro hseparated
  rcases witness.exists_common_first_crossing_endpoint with
    ⟨vertex, hleft, hright⟩
  let step : Fin pair.left.walk.length :=
    ⟨0, by simp [pair, LocalLayerPair.separatedLocalLayerPair,
      LocalLayerPair.firstLayer, LocalLayerPair.firstWalk]⟩
  have hleft' : vertex ∈ web.annular.RS.endpoints
      (pair.left.crossingEdge hunique step) := by
    simpa [pair, step, LocalLayerPair.separatedLocalLayerPair,
      LocalLayerPair.firstLayer, SimpleDualCrosscut.crossingEdge] using hleft
  have hzeroRight : Fin.cast pair.length_eq step =
      (⟨0, by simp [pair, LocalLayerPair.separatedLocalLayerPair,
        LocalLayerPair.secondLayer, LocalLayerPair.secondWalk]⟩ : Fin pair.right.walk.length) := by
    apply Fin.ext
    rfl
  have hright' : vertex ∈ web.annular.RS.endpoints
      (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) := by
    rw [hzeroRight]
    simpa [pair, LocalLayerPair.separatedLocalLayerPair,
      LocalLayerPair.secondLayer, SimpleDualCrosscut.crossingEdge] using hright
  exact hseparated step vertex vertex hleft' hright' rfl

/-- The canonical Cell-3 local layer pair is therefore an open interface
generator, not itself the endpoint-disjoint closed splice boundary. -/
theorem sourceLocalLayerPair_not_matchedCrossingsVertexDisjoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    ¬ GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.MatchedCrossingsVertexDisjoint
      web.annular.cellulation.rotation
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair hunique) := by
  simpa [sourceLocalLayerPair, localLayerPairOfCorridor] using
    SourceLocalLayerPairWitness.not_matchedCrossingsVertexDisjoint
      (localLayerPairWitnessOfCorridor corridor hunique leftInterior hnext)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
