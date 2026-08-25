import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPrefixState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorUpdate

/-!
# Exterior-component edge caps after adjoining one literal Cell

The cumulative weighted facial state is updated by the Cell graph and its
residual seam.  Both added graph factors are supported on the bounded rolling
interface, so the update changes only direct interface adjacency and literal
interface presence.  Strictly exterior components and their capped edge
supports remain unchanged.

The main theorem identifies the executable update with the exact weighted
factor of the literal pre-rebase regional face graph.  No boundary-deletion
mask is enumerated.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPreRebaseState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceDeletionStableCappedPreRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Update the weighted prefix factor with the literal Cell adjacency and the
newly present Cell edges. -/
noncomputable def sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    SourceLocalLayerSerialFaceDeletionStableCappedPrefixState :=
  let prefixState :=
    sourceLocalLayerSerialFaceDeletionStableCappedPrefixStateAt corridor
      hunique offset hcell
  { vertexCount := prefixState.vertexCount
    code := fun _ =>
      addInterfaceAdjacencyAndPresence (prefixState.code ())
        (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset
          hcell)
        (fun slot => decide
          (web.annular.RS.edgeOf
              (((carrierCoordinate
                (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
                  offset)).symm slot).1) ∈
            sourceLocalLayerCellRegionAt corridor hunique offset)) }

/-- The weighted finite update is exactly the pre-rebase regional face
factor, including every strict-exterior component's cap at five distinct
primal edges. -/
theorem sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt_code_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (sourceLocalLayerSerialFaceDeletionStableCappedPreRebaseStateAt corridor
        hunique offset hcell).code () =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        dartAt := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let dartAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  let prefixRegion :=
    sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
  let cellRegion := sourceLocalLayerCellRegionAt corridor hunique offset
  let prefixGraph := faceRegionalDartGraph web.annular.RS prefixRegion
  let localGraph := sourceLocalLayerSerialFaceLocalGraphAt corridor hunique
    offset
  have hupdate := addInterfaceAdjacencyAndPresence_exact_code_eq
    prefixGraph localGraph dartAt
    (sourceLocalLayerSerialFaceLocalGraph_support_subset_range corridor hunique
      offset)
    (fun dart => web.annular.RS.edgeOf dart ∈ prefixRegion)
    (fun dart => web.annular.RS.edgeOf dart ∈ cellRegion)
    Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
    web.annular.RS.edgeOf
    (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell)
    (sourceLocalLayerSerialFaceLocalAdjacency_exact corridor hunique offset
      hcell)
  change addInterfaceAdjacencyAndPresence
      (exactInterfaceExteriorLabelCapCode prefixGraph dartAt
        (fun dart => web.annular.RS.edgeOf dart ∈ prefixRegion)
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
        web.annular.RS.edgeOf)
      (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell)
      (fun slot => decide
        (web.annular.RS.edgeOf (dartAt slot) ∈ cellRegion)) = _
  unfold exactFaceInterfaceExteriorLabelCapCode
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset, sup_assoc]
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
    hunique offset]
  simpa only [prefixGraph, localGraph, prefixRegion, cellRegion,
    sourceLocalLayerSerialFaceLocalGraphAt, Finset.mem_union] using hupdate

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableCappedPreRebaseState

end Mettapedia.GraphTheory.FourColor
