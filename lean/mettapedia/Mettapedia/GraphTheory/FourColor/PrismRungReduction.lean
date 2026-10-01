import Mettapedia.GraphTheory.FourColor.PrismRungGeometry

/-!
# All-width operational prism rung reduction

At every rim width at least three, the canonical rung splice is a literal
capped ladder with a spanning face. The original and smaller geometries
are proved, so an arbitrary smaller target Tait witness enters the shared
physical phase repair and coupled insertion. Exactly six expanded target
vertices disappear. No additional colour table is used.
-/

namespace Mettapedia.GraphTheory.FourColor.PrismRungReduction

open PrismRungCoordinates DualTruncateColoring
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)

abbrev original := (graphData m hm).toRotationSystem
local notation "S" => original m hm
local notation "R" => PrismRungSplice.smaller m hm

variable (input : (rotation R).EdgeColoring Color)
  (hinput : (rotation R).IsTaitEdgeColoring input)

def witness (input : (rotation R).EdgeColoring Color)
    (hinput : (rotation R).IsTaitEdgeColoring input) : ThreeVertexColoring R := AdjacentSourceSpanningFaceReduction.sourceWitness
  (graphData m hm) (pair m hm) (graph_cubic m hm) (graph_rotation m hm)
  (PrismRungGeometry.graph_spherical m hm) (PrismRungGeometry.graph_twoSided m hm)
  (PrismRungGeometry.connected m) (PrismRungSplice.retained_connected m hm)
  (PrismRungSplice.twoSided m hm) (PrismRungSplice.spanningFace m hm) input hinput

def history (input : (rotation R).EdgeColoring Color)
    (hinput : (rotation R).IsTaitEdgeColoring input) := AdjacentSourceFacePhaseReduction.history
  (graphData m hm) (pair m hm) (graph_cubic m hm) (graph_rotation m hm)
  (PrismRungGeometry.graph_spherical m hm) (PrismRungGeometry.graph_twoSided m hm)
  (PrismRungGeometry.connected m) (PrismRungSplice.retained_connected m hm)
  (PrismRungSplice.twoSided m hm) (PrismRungSplice.spanningFace m hm) input hinput

def restoredSource (input : (rotation R).EdgeColoring Color)
    (hinput : (rotation R).IsTaitEdgeColoring input) : ThreeVertexColoring S := AdjacentSourceFacePhaseReduction.restoredSource
  (graphData m hm) (pair m hm) (graph_cubic m hm) (graph_rotation m hm)
  (PrismRungGeometry.graph_spherical m hm) (PrismRungGeometry.graph_twoSided m hm)
  (PrismRungGeometry.connected m) (PrismRungSplice.retained_connected m hm)
  (PrismRungSplice.twoSided m hm) (PrismRungSplice.spanningFace m hm) input hinput

/-- All source dart identities are retained by the expanded target counts. -/
theorem target_counts : Fintype.card (R).D = 6*m ∧ Fintype.card (S).D = 6*(m+1) := by
  constructor
  · rw [← Fintype.card_congr (PrismRungSplice.spliceDartEquiv m hm)]
    simp only [CappedLadderRotation.Dart,CappedLadderRotation.Vertex,
      Fintype.card_prod,Fintype.card_fin]
    omega
  · change Fintype.card (graph m).Dart = _
    rw [← Fintype.card_congr (dartEquiv m hm)]
    simp only [PrismRungCoordinates.Dart,PrismRungCoordinates.Vertex,CappedLadderRotation.Vertex,Fintype.card_prod,Fintype.card_fin]
    omega

/-- One shared operational law supplies physical repair, valid smaller
geometry, exact strict decrease and reconstruction at every prism width. -/
theorem operational_reconstruction (input : (rotation R).EdgeColoring Color)
    (hinput : (rotation R).IsTaitEdgeColoring input) :
    DualTruncateFacePhaseGSLT.PhysicalHistory R (witness m hm input hinput)
        (history m hm input hinput) ∧
      (history m hm input hinput).length = 3 ∧
      BridgelessSphericalCubicMapData (rotation R) ∧
      Fintype.card (R).D + 6 = Fintype.card (S).D ∧
      (rotation S).IsTaitEdgeColoring (DualTruncateColoring.colouring S (restoredSource m hm input hinput)) :=
  AdjacentSourceFacePhaseReduction.operational_reconstruction
    (graphData m hm) (pair m hm) (graph_cubic m hm) (graph_rotation m hm)
    (PrismRungGeometry.graph_spherical m hm) (PrismRungGeometry.graph_twoSided m hm)
    (PrismRungGeometry.connected m) (PrismRungSplice.retained_connected m hm)
    (PrismRungSplice.twoSided m hm) (PrismRungSplice.spanningFace m hm) input hinput

/-- The repaired witness supports every complete faithful construction
sweep of the actual restored expanded prism. -/
theorem every_complete_sweep (input : (rotation R).EdgeColoring Color)
    (hinput : (rotation R).IsTaitEdgeColoring input) (order : List (S).D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d,visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic S) (DualTruncateConstructionGSLT.rotationCyclic S)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  AdjacentSourceFacePhaseReduction.every_complete_sweep
    (graphData m hm) (pair m hm) (graph_cubic m hm) (graph_rotation m hm)
    (PrismRungGeometry.graph_spherical m hm) (PrismRungGeometry.graph_twoSided m hm)
    (PrismRungGeometry.connected m) (PrismRungSplice.retained_connected m hm)
    (PrismRungSplice.twoSided m hm) (PrismRungSplice.spanningFace m hm)
    input hinput order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.PrismRungReduction
