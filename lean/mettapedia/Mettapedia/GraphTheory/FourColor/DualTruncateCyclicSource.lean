import Mettapedia.GraphTheory.FourColor.CubicPairDeletionConnectivity
import Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring

/-!
# Source colours supplied by geometric cut constraints

Cyclic edge-connectivity at least four and simple primal degree three derive
the retained connectivity needed by the coupled colouring argument. The
result supplies genuine source colours, literal target Tait colourings and
compatible witnesses along every complete target construction sweep.

No source colouring or per-deletion connectivity certificate is a theorem
input. Inverse recognition and spherical target coverage remain separate.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource

open DualTruncateColoring DualTruncateStructuralColoring
open GoertzelV24FaceDualConnectedness GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- The same equal source choice is retained at a specified nonadjacent
neighbour pair. The cut theorem supplies its connected deletion. -/
theorem source_of_cyclic_pair
    (hregular : (rotationPrimalGraph RS).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph RS) 4)
    {a b r : V} (hab : a ≠ b) (hnadj : ¬(rotationPrimalGraph RS).Adj a b)
    (ha : (rotationPrimalGraph RS).Adj r a)
    (hb : (rotationPrimalGraph RS).Adj r b) :
    ∃ c : ThreeVertexColoring RS, c.colour a = c.colour b := by
  obtain ⟨c, hc⟩ := CoupledThreeColouring.colouring_of_connected_pair
    (rotationPrimalGraph RS) (fun v =>
      (SimpleGraph.degree_instance_independent (G := rotationPrimalGraph RS) v _ _).trans_le
        (le_of_eq (hregular v))) hab hnadj ha hb
    (CubicPairDeletionConnectivity.pairDeletion_connected
      (rotationPrimalGraph RS) hregular hcyclic a b hab)
  exact ⟨ofPrimalColouring RS c, congrArg palette hc⟩

/-- The geometric source class supplies its own three-colouring witness. -/
theorem source
    (hregular : (rotationPrimalGraph RS).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph RS) 4)
    (hconn : (rotationPrimalGraph RS).Connected)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y) :
    Nonempty (ThreeVertexColoring RS) := by
  obtain ⟨c⟩ := CubicPairDeletionConnectivity.colourable_three_of_cyclic_connectivity
    (rotationPrimalGraph RS) hregular hcyclic hconn hnot
  exact ⟨ofPrimalColouring RS c⟩

/-- A source cut condition yields an actual target edge colouring. -/
theorem tait
    (hregular : (rotationPrimalGraph RS).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph RS) 4)
    (hconn : (rotationPrimalGraph RS).Connected)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y) :
    RotationSystemTaitColorable (rotation RS) := by
  obtain ⟨c⟩ := source RS hregular hcyclic hconn hnot
  exact DualTruncateConstructionGSLT.tait RS c

/-- Every complete faithful construction sweep receives compatible actual
colouring witnesses from the same source structure. -/
theorem every_complete_sweep
    (hregular : (rotationPrimalGraph RS).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph RS) 4)
    (hconn : (rotationPrimalGraph RS).Connected)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y)
    (order : List RS.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic RS) (DualTruncateConstructionGSLT.rotationCyclic RS)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := source RS hregular hcyclic hconn hnot
  exact DualTruncateConstructionGSLT.supported_encoded_route RS c order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource
