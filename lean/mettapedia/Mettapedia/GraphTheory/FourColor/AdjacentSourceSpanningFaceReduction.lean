import Mettapedia.GraphTheory.FourColor.AdjacentSourceSplice
import Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFace

/-!
# Strict source-splice reconstruction from arbitrary smaller target witnesses

When the actual smaller source has two-sided faces and a face touching
every vertex, spanning-face calibration extracts the source witness from
any smaller target Tait colouring. The existing coupled splice repair then
restores both deleted vertices, preserves the target map class and removes
exactly six target vertices in the reduction direction. Complete faithful
GSLT sweeps receive actual reconstructed colouring witnesses.

The smaller source's geometric face condition is explicit. No universal
occurrence, recursive preservation of that condition, unchanged polygon
colours, or Kempe history from the arbitrary input is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentSourceSpanningFaceReduction

open _root_.SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RotationCutDartDecomposition GoertzelV24DeletedRegionRotationSplice
open GoertzelV24CyclicBoundaryClosure
open AdjacentSourceSplice DualTruncateColoring

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (graphData : Data G) (data : AdjacentPairData G)
  (hcubic : graphData.toRotationSystem.IsCubic)
  (hrotation : VertexRotationCyclic graphData.toRotationSystem)
  (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
  (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
  (hconnected : G.Connected)
  (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected)
  (hsmallTwoSided : OrbitFacesTwoSided (smaller graphData data hcubic hrotation))
  (face : DualTruncateSpanningFace.SpanningFace (smaller graphData data hcubic hrotation))
  (input : (rotation (smaller graphData data hcubic hrotation)).EdgeColoring Color)
  (hinput : (rotation (smaller graphData data hcubic hrotation)).IsTaitEdgeColoring input)

/-- The smaller source witness is derived from the supplied arbitrary
target witness, rather than supplied separately. -/
def sourceWitness : ThreeVertexColoring (smaller graphData data hcubic hrotation) :=
  DualTruncateSpanningFace.sourceColouring _
    (smaller_spherical graphData data hcubic hrotation hsphere htwoSided hconnected hretained)
    hsmallTwoSided (smaller_connected graphData data hcubic hrotation hretained)
    (smaller_rotation graphData data hcubic hrotation) input hinput face

/-- The extracted witness jointly preserves every original source-edge
observation of the smaller target. -/
theorem smaller_cross_preserved (dart : (smaller graphData data hcubic hrotation).D) :
    colouring (smaller graphData data hcubic hrotation)
      (sourceWitness graphData data hcubic hrotation hsphere htwoSided hconnected hretained
        hsmallTwoSided face input hinput) (.inl ((smaller graphData data hcubic hrotation).edgeOf dart)) =
          input (.inl ((smaller graphData data hcubic hrotation).edgeOf dart)) :=
  DualTruncateSpanningFace.preserves_cross _
    (smaller_spherical graphData data hcubic hrotation hsphere htwoSided hconnected hretained)
    hsmallTwoSided (smaller_connected graphData data hcubic hrotation hretained)
    (smaller_rotation graphData data hcubic hrotation) input hinput face
      ((smaller graphData data hcubic hrotation).edgeOf dart)

/-- Complete coupled reconstruction of the original source. -/
def restoredSource : ThreeVertexColoring graphData.toRotationSystem :=
  AdjacentSourceSplice.sourceColouring graphData data hcubic hrotation
    (sourceWitness graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput) hsphere htwoSided hconnected hretained

/-- Geometry, full size accounting and actual colouring reconstruction
now hold for every smaller target Tait witness on the spanning-face domain. -/
theorem strict_reconstruction :
    BridgelessSphericalCubicMapData
        (rotation (smaller graphData data hcubic hrotation)) ∧
      Fintype.card (smaller graphData data hcubic hrotation).D + 6 =
        Fintype.card graphData.toRotationSystem.D ∧
      (rotation graphData.toRotationSystem).IsTaitEdgeColoring
        (colouring graphData.toRotationSystem
          (restoredSource graphData data hcubic hrotation hsphere htwoSided hconnected hretained
            hsmallTwoSided face input hinput)) :=
  reduction_reconstruction graphData data hcubic hrotation
    (sourceWitness graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput) hsphere htwoSided hconnected hretained

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

include hsphere htwoSided hconnected hretained hsmallTwoSided face input hinput in
/-- The arbitrary input supplies genuine compatible witnesses on every
complete faithful construction route of the original target. -/
theorem every_complete_sweep (order : List graphData.toRotationSystem.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic graphData.toRotationSystem)
        (DualTruncateConstructionGSLT.rotationCyclic graphData.toRotationSystem)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  AdjacentSourceSplice.every_complete_sweep graphData data hcubic hrotation
    (sourceWitness graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput) hsphere htwoSided hconnected hretained order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.AdjacentSourceSpanningFaceReduction
