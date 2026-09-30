import Mettapedia.GraphTheory.CoupledThreeColouring
import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT

/-!
# Structural source choices for dual-and-truncate reconstruction

A connected retained source graph supplies the ordered coupled-colouring
argument. The resulting witness is translated to the three nonzero Klein
colours, then consumed by the literal vertex-to-edge reconstruction and its
faithful construction routes. Source colour words are not hypotheses of
these theorems.

The source domain is explicit: either a suitable pair of neighbours leaves
a connected graph, or every two-vertex deletion does and the source is
connected and noncomplete. Inverse recognition, spherical geometry and
coverage of arbitrary target maps remain separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring

open DualTruncateColoring GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- The simple primal graph records exactly the distinct opposite vertices. -/
theorem primal_neighbours (v : V) :
    (rotationPrimalGraph RS).neighborFinset v =
      (RS.dartsAt v).image (fun d => RS.vertOf (RS.alpha d)) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, rotationPrimalGraph_adj_iff,
    Finset.mem_image, RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Parallel edges may collapse in the simple primal graph, so the degree
bound is an inequality. Every colouring edge still has its actual dart. -/
theorem primal_degree_le_three (h : RS.IsCubic) (v : V) :
    (rotationPrimalGraph RS).degree v ≤ 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, primal_neighbours RS v]
  exact Finset.card_image_le.trans (le_of_eq (h v))

def palette (i : Fin 3) : Color :=
  if i = 0 then red else if i = 1 then blue else purple

theorem palette_nonzero (i : Fin 3) : palette i ≠ 0 := by
  fin_cases i <;> decide

theorem palette_injective : Function.Injective palette := by
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim ((by decide : ¬_) he)

/-- The graph colouring is interpreted on every genuine source edge. -/
def ofPrimalColouring (c : (rotationPrimalGraph RS).Coloring (Fin 3)) :
    ThreeVertexColoring RS where
  colour v := palette (c v)
  nonzero v := palette_nonzero (c v)
  proper d := palette_injective.ne (c.valid ⟨d, rfl, rfl⟩)

/-- Connectivity supplies the source witness while retaining the equal
choice at the two interacting insertions. -/
theorem source_of_connected_pair (h : RS.IsCubic) {a b r : V}
    (hab : a ≠ b) (hnadj : ¬(rotationPrimalGraph RS).Adj a b)
    (ha : (rotationPrimalGraph RS).Adj r a)
    (hb : (rotationPrimalGraph RS).Adj r b)
    (hconn : ((rotationPrimalGraph RS).induce {v | v ≠ a ∧ v ≠ b}).Connected) :
    ∃ c : ThreeVertexColoring RS, c.colour a = c.colour b := by
  obtain ⟨c, hc⟩ := CoupledThreeColouring.colouring_of_connected_pair
    (rotationPrimalGraph RS) (by
      intro v
      exact (SimpleGraph.degree_instance_independent (G := rotationPrimalGraph RS) v _ _).trans_le
        (primal_degree_le_three RS h v)) hab hnadj ha hb hconn
  exact ⟨ofPrimalColouring RS c, congrArg palette hc⟩

/-- The source choices are derived wholly from the stated graph structure. -/
theorem source_of_pairDeletionConnected (h : RS.IsCubic)
    (hconn : (rotationPrimalGraph RS).Connected)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y)
    (hdelete : ∀ a b : V, a ≠ b →
      ((rotationPrimalGraph RS).induce {v | v ≠ a ∧ v ≠ b}).Connected) :
    Nonempty (ThreeVertexColoring RS) := by
  obtain ⟨c⟩ := CoupledThreeColouring.colourable_of_pairDeletionConnected
    (rotationPrimalGraph RS) (by
      intro v
      exact (SimpleGraph.degree_instance_independent (G := rotationPrimalGraph RS) v _ _).trans_le
        (primal_degree_le_three RS h v)) hconn hnot hdelete
  exact ⟨ofPrimalColouring RS c⟩

/-- A single suitable connected deletion suffices for target reconstruction. -/
theorem tait_of_connected_pair (h : RS.IsCubic) {a b r : V}
    (hab : a ≠ b) (hnadj : ¬(rotationPrimalGraph RS).Adj a b)
    (ha : (rotationPrimalGraph RS).Adj r a)
    (hb : (rotationPrimalGraph RS).Adj r b)
    (hconn : ((rotationPrimalGraph RS).induce {v | v ≠ a ∧ v ≠ b}).Connected) :
    RotationSystemTaitColorable (rotation RS) := by
  obtain ⟨c, _⟩ := source_of_connected_pair RS h hab hnadj ha hb hconn
  exact DualTruncateConstructionGSLT.tait RS c

/-- The same structural source choices supply every complete target sweep. -/
theorem supported_route_of_connected_pair (h : RS.IsCubic) {a b r : V}
    (hab : a ≠ b) (hnadj : ¬(rotationPrimalGraph RS).Adj a b)
    (ha : (rotationPrimalGraph RS).Adj r a)
    (hb : (rotationPrimalGraph RS).Adj r b)
    (hconn : ((rotationPrimalGraph RS).induce {v | v ≠ a ∧ v ≠ b}).Connected)
    (order : List RS.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic RS) (DualTruncateConstructionGSLT.rotationCyclic RS)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 := by
  obtain ⟨c, _⟩ := source_of_connected_pair RS h hab hnadj ha hb hconn
  exact DualTruncateConstructionGSLT.supported_encoded_route RS c order hn he hcover

/-- The literal target receives an actual colouring from source geometry. -/
theorem tait_of_pairDeletionConnected (h : RS.IsCubic)
    (hconn : (rotationPrimalGraph RS).Connected)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y)
    (hdelete : ∀ a b : V, a ≠ b →
      ((rotationPrimalGraph RS).induce {v | v ≠ a ∧ v ≠ b}).Connected) :
    RotationSystemTaitColorable (rotation RS) := by
  obtain ⟨c⟩ := source_of_pairDeletionConnected RS h hconn hnot hdelete
  exact DualTruncateConstructionGSLT.tait RS c

/-- All intermediate choices on every complete sweep are reconstructed from
the same structurally derived source witness. -/
theorem supported_route_of_pairDeletionConnected (h : RS.IsCubic)
    (hconn : (rotationPrimalGraph RS).Connected)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y)
    (hdelete : ∀ a b : V, a ≠ b →
      ((rotationPrimalGraph RS).induce {v | v ≠ a ∧ v ≠ b}).Connected)
    (order : List RS.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic RS) (DualTruncateConstructionGSLT.rotationCyclic RS)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := source_of_pairDeletionConnected RS h hconn hnot hdelete
  exact DualTruncateConstructionGSLT.supported_encoded_route RS c order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring
