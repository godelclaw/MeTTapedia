import Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring
import Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate

/-!
# A structural coupled-colouring consumer on the cube

The eight-vertex cube is supplied as a genuine cubic rotation. Deleting
neighbours 1 and 3 of vertex 0 leaves a connected graph. The shared source
colour is obtained from that structure, without a saved source colour word.
The uniform reconstruction colours the 24-vertex dual-and-truncate map and
supplies compatible witnesses on every complete construction sweep.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample

open CubicRotationByteCertificate DualTruncateColoring
open DualTruncateStructuralColoring GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
def code : CubicRotationByteCertificate.Code 8 12 where
  neighbours := { size := 24, pages := fun _ => ByteArray.mk #[
      1,0,4,0,3,0,2,0,5,0,0,0,3,0,6,0,1,0,0,0,7,0,2,0,
      7,0,0,0,5,0,4,0,1,0,6,0,5,0,2,0,7,0,6,0,3,0,4,0] }
  mates := { size := 24, pages := fun _ => ByteArray.mk #[
      5,0,13,0,9,0,8,0,16,0,0,0,11,0,19,0,3,0,2,0,22,0,6,0,
      23,0,1,0,15,0,14,0,4,0,18,0,17,0,7,0,21,0,20,0,10,0,12,0] }
  edges := { size := 24, pages := fun _ => ByteArray.mk #[
      0,0,2,0,1,0,3,0,4,0,0,0,5,0,6,0,3,0,1,0,7,0,5,0,
      9,0,2,0,8,0,8,0,4,0,10,0,10,0,6,0,11,0,11,0,7,0,9,0] }
  representatives := { size := 12, pages := fun _ => ByteArray.mk #[
      0,0,2,0,1,0,3,0,4,0,6,0,7,0,10,0,14,0,12,0,17,0,20,0] }

theorem valid : code.Valid := by decide +kernel

abbrev source : RotationSystem.{0,0,0} (Fin 8) (Fin 12) := code.rotation valid
abbrev graph := rotationPrimalGraph source

instance : DecidableRel graph.Adj := fun v w =>
  inferInstanceAs (Decidable (∃ d : Position 8, d.1 = v ∧ (code.mate d).1 = w))

abbrev retained := graph.induce {v | v ≠ (1 : Fin 8) ∧ v ≠ (3 : Fin 8)}

def root : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨0, by decide, by decide⟩
def two : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨2, by decide, by decide⟩
def four : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨4, by decide, by decide⟩
def five : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨5, by decide, by decide⟩
def six : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨6, by decide, by decide⟩
def seven : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨7, by decide, by decide⟩

/-- Actual retained paths discharge the structural connectivity obligation. -/
theorem retained_reachable (v : CoupledThreeColouring.Retained (1 : Fin 8) 3) :
    retained.Reachable root v := by
  have h04 : retained.Adj root four := by decide +kernel
  have h45 : retained.Adj four five := by decide +kernel
  have h56 : retained.Adj five six := by decide +kernel
  have h47 : retained.Adj four seven := by decide +kernel
  have h62 : retained.Adj six two := by decide +kernel
  have h05 := h04.reachable.trans h45.reachable
  have h06 := h05.trans h56.reachable
  rcases v with ⟨v, hv⟩
  fin_cases v
  · exact .refl _
  · exact (hv.1 rfl).elim
  · exact h06.trans h62.reachable
  · exact (hv.2 rfl).elim
  · exact h04.reachable
  · exact h05
  · exact h06
  · exact h04.reachable.trans h47.reachable

theorem retained_connected : retained.Connected := by
  exact { preconnected := fun u v => (retained_reachable u).symm.trans (retained_reachable v)
          nonempty := ⟨root⟩ }

theorem pair_nonadjacent : ¬graph.Adj 1 3 := by decide +kernel
theorem root_adj_one : graph.Adj 0 1 := by decide +kernel
theorem root_adj_three : graph.Adj 0 3 := by decide +kernel

/-- The source witness is derived rather than stored as finite colour data. -/
theorem source_shared_colouring :
    ∃ c : ThreeVertexColoring source, c.colour 1 = c.colour 3 :=
  source_of_connected_pair source (code.cubic valid) (by decide)
    pair_nonadjacent root_adj_one root_adj_three retained_connected

theorem target_tait : RotationSystemTaitColorable (rotation source) :=
  tait_of_connected_pair source (code.cubic valid) (by decide)
    pair_nonadjacent root_adj_one root_adj_three retained_connected

theorem target_counts : Fintype.card source.D = 24 ∧
    Fintype.card (Edge source) = 36 := by decide +kernel

theorem every_complete_sweep (order : List source.D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic source) (DualTruncateConstructionGSLT.rotationCyclic source)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  supported_route_of_connected_pair source (code.cubic valid) (by decide)
    pair_nonadjacent root_adj_one root_adj_three retained_connected order hn he hcover

/-- Cubicity alone cannot supply three source vertex colours: the complete
four-vertex source is a genuine exception. -/
theorem complete_four_not_three_colourable :
    ¬(SimpleGraph.completeGraph (Fin 4)).Colorable 3 := by
  intro h
  have hc := h.card_le_of_pairwise_adj (fun i : Fin 4 => i) (fun _ _ hne => hne)
  norm_num at hc

end
end Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample
