import Mettapedia.GraphTheory.FourColor.AdjacentSourceSpanningFaceReduction
import Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseGSLT
import Mettapedia.GraphTheory.FourColor.DualTruncateCornerCoherence

/-!
# Strict splice reconstruction through an actual repair history

Calibrate an arbitrary smaller target Tait witness on the spanning-face
domain, execute three physical face-phase region stages, and extract the
source witness from the resulting coherent field. The actual coupled splice
then restores the two deleted source vertices. All cross-edge observations
survive the normalization, and the strict reduction removes six target
vertices. Recognition and recursive coverage remain separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentSourceFacePhaseReduction

open _root_.SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RotationCutDartDecomposition GoertzelV24DeletedRegionRotationSplice
open GoertzelV24CyclicBoundaryClosure
open AdjacentSourceSplice DualTruncateColoring
open Mettapedia.GSLT.Ultrainfinite

noncomputable section
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

local notation "R" => smaller graphData data hcubic hrotation
local notation "W" => AdjacentSourceSpanningFaceReduction.sourceWitness graphData data hcubic hrotation
  hsphere htwoSided hconnected hretained hsmallTwoSided face input hinput

def initial : DualTruncateFacePhaseKempe.State R W where
  colouring := input
  tait := hinput
  compatible := by
    intro d
    exact (AdjacentSourceSpanningFaceReduction.smaller_cross_preserved graphData data hcubic
      hrotation hsphere htwoSided hconnected hretained hsmallTwoSided face input hinput d).symm.trans
        (star_colour_zero R (W).colour d)

local notation "S" => initial graphData data hcubic hrotation hsphere htwoSided hconnected
  hretained hsmallTwoSided face input hinput

def history : Route (DualTruncateFacePhaseGSLT.Event R W) S
    (DualTruncateFacePhaseKempe.normalize R W S) := DualTruncateFacePhaseGSLT.repair R W S

theorem history_length :
    (history graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput).length = 3 := rfl

theorem terminal_coherent : DualTruncateCornerCoherence.Coherent R
    (DualTruncateCornerSemantics.corner R (DualTruncateFacePhaseKempe.normalize R W S).colouring) := by
  have hcorner (d : (R).D) :
      DualTruncateCornerSemantics.corner R (DualTruncateFacePhaseKempe.normalize R W S).colouring d =
        (W).colour ((R).vertOf d) :=
    (add_eq_zero_iff_eq _ _).1 (DualTruncateFacePhaseKempe.normalize_error R W S d)
  intro d e hv
  rw [hcorner d, hcorner e, hv]

/-- Extract the actual source witness from the terminal physical field. -/
def repairedSource : ThreeVertexColoring R :=
  DualTruncateCornerCoherence.sourceColouring R
    (DualTruncateCornerSemantics.corner R (DualTruncateFacePhaseKempe.normalize R W S).colouring)
    (DualTruncateCornerSemantics.corners_valid R _ (DualTruncateFacePhaseKempe.normalize R W S).tait)
    (terminal_coherent graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput)

theorem terminal_cross_preserved (dart : (R).D) :
    (DualTruncateFacePhaseKempe.normalize R W S).colouring (.inl ((R).edgeOf dart)) =
      input (.inl ((R).edgeOf dart)) :=
  DualTruncateFacePhaseKempe.normalize_cross_preserved R W S ((R).edgeOf dart)

def restoredSource : ThreeVertexColoring graphData.toRotationSystem :=
  AdjacentSourceSplice.sourceColouring graphData data hcubic hrotation
    (repairedSource graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput) hsphere htwoSided hconnected hretained

/-- Reconstruction consumes the witness extracted after the physical route. -/
theorem strict_reconstruction :
    BridgelessSphericalCubicMapData (rotation R) ∧
      Fintype.card (R).D + 6 = Fintype.card graphData.toRotationSystem.D ∧
      (rotation graphData.toRotationSystem).IsTaitEdgeColoring
        (colouring graphData.toRotationSystem
          (restoredSource graphData data hcubic hrotation hsphere htwoSided hconnected hretained
            hsmallTwoSided face input hinput)) :=
  reduction_reconstruction graphData data hcubic hrotation
    (repairedSource graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput) hsphere htwoSided hconnected hretained

/-- One consumer includes the legal history, complete size accounting and
the reconstructed actual colouring. -/
theorem operational_reconstruction :
    DualTruncateFacePhaseGSLT.PhysicalHistory R W
        (history graphData data hcubic hrotation hsphere htwoSided hconnected hretained
          hsmallTwoSided face input hinput) ∧
      (history graphData data hcubic hrotation hsphere htwoSided hconnected hretained
        hsmallTwoSided face input hinput).length = 3 ∧
      BridgelessSphericalCubicMapData (rotation R) ∧
      Fintype.card (R).D + 6 = Fintype.card graphData.toRotationSystem.D ∧
      (rotation graphData.toRotationSystem).IsTaitEdgeColoring
        (colouring graphData.toRotationSystem
          (restoredSource graphData data hcubic hrotation hsphere htwoSided hconnected hretained
            hsmallTwoSided face input hinput)) :=
  ⟨DualTruncateFacePhaseGSLT.physical_history R W _, rfl,
    strict_reconstruction graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput⟩

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

include hsphere htwoSided hconnected hretained hsmallTwoSided face input hinput in
/-- Complete construction routes receive witnesses after physical repair
and coupled strict-splice reconstruction. -/
theorem every_complete_sweep (order : List graphData.toRotationSystem.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic graphData.toRotationSystem)
        (DualTruncateConstructionGSLT.rotationCyclic graphData.toRotationSystem)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  AdjacentSourceSplice.every_complete_sweep graphData data hcubic hrotation
    (repairedSource graphData data hcubic hrotation hsphere htwoSided hconnected hretained
      hsmallTwoSided face input hinput) hsphere htwoSided hconnected hretained order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.AdjacentSourceFacePhaseReduction
