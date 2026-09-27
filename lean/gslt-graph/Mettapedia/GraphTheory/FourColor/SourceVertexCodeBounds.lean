import Mettapedia.GraphTheory.FourColor.SourceVertexCodePlanar
import Mettapedia.GraphTheory.FourColor.VertexCodeUnboundedMass

/-!
# Conservative bounds for source vertex-code sweeps

The finite-machine base needs a bound on every interface occurring in the
source sweep, not merely on its terminal interface.  A boundary dart is a dart
of the ambient rotation system, so every frontier has at most `|D|` ports.  For
a cubic source `|D| = 3 |V|`.  This gives a deliberately conservative but
source-derived width bound for the complete trace.

This file does not construct the exact closure certificate required by the
direct Count base.  It proves only that every bounded source is represented by
a viable run inside one finite width envelope.
-/

namespace Mettapedia.GraphTheory.FourColor.SourceVertexCodeBounds

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open SourceVertexCodeTrace SourceVertexCodePlanar
open TubeSlab.VertexTransfer
open VertexCodeSourceGeometry VertexCodeTrace VertexCodeUnboundedMass

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E}

/-- If a sweep covers every ambient vertex, its retained-vertex subtype is
equivalent to the original vertex carrier. -/
def retainedVertexFullEquiv {keep : V → Prop} (hcover : ∀ v, keep v) :
    {v : V // keep v} ≃ V where
  toFun v := v.1
  invFun v := ⟨v, hcover v⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- A model of a complete sweep has exactly one decoded vertex for each
ambient source vertex. -/
theorem model_vertex_card {keep : V → Prop}
    {W I : Type*} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I]
    {T : GoertzelV24OpenTangleComposition.TwoSidedOpenTangleData
      W I (Fin 0) (Fin 0)}
    {mi : Fin 0 ≃ BoundaryDart RS keep}
    (M : Model T mi) (hcover : ∀ v, keep v) :
    Fintype.card W = Fintype.card V := by
  exact Fintype.card_congr (M.vertex.trans (retainedVertexFullEquiv hcover))

/-- Every frontier is literally a subtype of the ambient dart carrier. -/
theorem boundaryDart_card_le (keep : V → Prop) :
    Fintype.card (BoundaryDart RS keep) ≤ Fintype.card RS.D := by
  exact Fintype.card_le_of_injective
    (fun d : BoundaryDart RS keep => d.1.1)
    (fun _ _ h => Subtype.ext (Subtype.ext h))

/-- Widening a trace envelope preserves membership. -/
theorem within_mono {b c r : ℕ} {t : Trace r}
    (h : Within b t) (hbc : b ≤ c) : Within c t := by
  induction t with
  | first a ha =>
      exact le_trans h hbc
  | step t a ha ih =>
      exact ⟨ih h.1, le_trans h.2 hbc⟩

/-- Every interface of the recursively constructed source sweep is bounded by
the total number of ambient darts. -/
theorem encodeOrder_within_darts (hc : RS.IsCubic)
    (hcyc : VertexRotationCyclic RS) :
    ∀ (order : List V) (hn : order.Nodup) (he : order ≠ [])
      {r : ℕ} (mo : Fin r ≃ BoundaryDart RS (visited order)),
      Within (Fintype.card RS.D) (encodeOrder hc hcyc order hn he mo).trace
  | [], _, he, _, _ => (he rfl).elim
  | [v], _, _, r, mo => by
      change r ≤ Fintype.card RS.D
      rw [← Fintype.card_fin r, Fintype.card_congr mo]
      exact boundaryDart_card_le (RS := RS) _
  | v :: w :: rest, hn, _, r, mo => by
      change
        Within (Fintype.card RS.D)
          (encodeOrder hc hcyc (w :: rest) (List.nodup_cons.mp hn).2
            (by simp) (coordinates (visited (w :: rest)))).trace ∧
        r ≤ Fintype.card RS.D
      constructor
      · exact encodeOrder_within_darts hc hcyc (w :: rest)
          (List.nodup_cons.mp hn).2 (by simp)
          (coordinates (visited (w :: rest)))
      · rw [← Fintype.card_fin r, Fintype.card_congr mo]
        exact boundaryDart_card_le (RS := RS) _

/-- Cubicity turns the ambient-dart envelope into the explicit width `3|V|`. -/
theorem encodeOrder_within_three_mul_vertices (hc : RS.IsCubic)
    (hcyc : VertexRotationCyclic RS) (order : List V) (hn : order.Nodup)
    (he : order ≠ []) {r : ℕ}
    (mo : Fin r ≃ BoundaryDart RS (visited order)) :
    Within (3 * Fintype.card V) (encodeOrder hc hcyc order hn he mo).trace := by
  rw [← RS.card_darts_eq_three_times_card_vertices hc]
  exact encodeOrder_within_darts hc hcyc order hn he mo

/-- A complete source in the minimality class has one closed, viable trace in
the explicit `3|V|` envelope.  This packages coverage, semantic pruning, and
the width bound without claiming an exact closure count. -/
theorem class_covered_within
    (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ t : Trace 0,
      Nonempty (Model t.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      VertexCodeLosslessPruning.prefixesViable t = true ∧
      Within (3 * Fintype.card V) t ∧
      Fintype.card t.Vertex = Fintype.card V := by
  have hn : (completeOrder (V := V)).Nodup := Finset.nodup_toList _
  have he : completeOrder (V := V) ≠ [] := by
    intro h
    have hm := (visited_iff_mem _ _).mp (visited_complete (RS.vertOf RS.outer))
    rw [h] at hm
    exact List.not_mem_nil hm
  let e := encodeClosed hclass.spherical.cubic hclass.vertexRotationCyclic
    completeOrder hn he visited_complete
  refine ⟨e.trace, ⟨e.model⟩, ?_, ?_, ?_⟩
  · exact source_prefixes_viable hclass.spherical hclass.primalConnected
      hclass.vertexRotationCyclic completeOrder hn he visited_complete
  · exact encodeOrder_within_three_mul_vertices hclass.spherical.cubic
      hclass.vertexRotationCyclic completeOrder hn he
      (terminalCoordinates completeOrder visited_complete)
  · exact model_vertex_card e.model visited_complete

/-- If the source has at most `N` vertices, the same witness lies in the
uniform width-`3N` envelope used by a bounded base computation. -/
theorem class_covered_within_vertex_bound {N : ℕ}
    (hclass : BridgelessSphericalCubicMapData RS)
    (hcard : Fintype.card V ≤ N) :
    ∃ t : Trace 0,
      Nonempty (Model t.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      VertexCodeLosslessPruning.prefixesViable t = true ∧
      Within (3 * N) t ∧
      Fintype.card t.Vertex ≤ N := by
  obtain ⟨t, hmodel, hv, hw, ht⟩ := class_covered_within hclass
  exact ⟨t, hmodel, hv, within_mono hw (Nat.mul_le_mul_left 3 hcard),
    ht.le.trans hcard⟩

end
end Mettapedia.GraphTheory.FourColor.SourceVertexCodeBounds
