import Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatch
import Mettapedia.GraphTheory.FourColor.DualTruncateCornerCoherence
import Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample

/-!
# A genuine exterior-preserving patch witness with varying corners

In the twenty-four-vertex cube expansion, select the fourteen target
vertices incident to source vertices zero, one and two. The retained
corner state reconstructs a Tait colouring while fixing all ten exterior
vertices and every incident exterior edge. Its nonzero cyclic difference
proves that this particular witness cannot be collapsed to source vertex
colours. This does not exclude other compatible source-colouring choices.

The small flat corner word is a diagnostic witness, not a source-colouring
supplier or a certificate used by the general patch theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample

open DualTruncateColoring DualTruncateCornerSemantics DualTruncateCornerCoherence
open DualTruncateOpenPatch CubicRotationByteCertificate

noncomputable section

abbrev source := DualTruncateCoupledExample.source
abbrev target := rotation source

/-- The cube's bipartition gives the initial exterior colours. -/
def baseColour (v : Fin 8) : Color :=
  if v.val % 2 = v.val / 4 then blue else red

def baseSource : ThreeVertexColoring source where
  colour := baseColour
  nonzero v := by unfold baseColour; split <;> simp
  proper := by decide +kernel

def base : Edge source → Color := edgeColour source baseColour

def selected (v : Fin 8) : Prop := v.val < 3
def keep : source.D → Prop := vertexRegion source selected

instance : DecidablePred keep := by unfold keep vertexRegion selected; infer_instance

theorem closed (d : source.D) : keep (source.alpha d) ↔ keep d :=
  vertexRegion_closed source selected d

theorem exterior_stars (d : source.D) (_ : ¬keep d) : Star source base d :=
  star_of_tait source (DualTruncateColoring.colouring source baseSource)
    (colouring_nonzero source baseSource) d

/-- Polygon-corner colours, indexed by the actual source dart positions. -/
def cornerWord : ByteArray := ByteArray.mk #[
  1,3,3, 3,1,1, 1,3,3, 3,1,1, 1,1,1, 2,2,2, 1,1,1, 2,2,2]

def patchCorners (d : source.D) : Color := wordColour cornerWord (index d)

theorem patch_summary : Summary source keep base patchCorners := by
  have hbase : corner source base = fun d => baseColour (source.vertOf d) := by
    funext d
    exact star_colour_two source baseColour d
  unfold Summary
  rw [hbase]
  unfold Visible DualTruncateCornerSemantics.Balanced
  decide +kernel

theorem patch_valid : Valid source patchCorners :=
  summary_valid source closed exterior_stars patch_summary

/-- Reconstruct through the exact fixed-exterior equivalence. -/
def repaired : {c : target.EdgeColoring Color //
    target.IsTaitEdgeColoring c ∧ Extends source keep base c} :=
  (extensionEquiv source closed exterior_stars).symm ⟨patchCorners,patch_summary⟩

theorem repaired_tait : target.IsTaitEdgeColoring repaired.val := repaired.property.1

theorem exterior_fixed : Extends source keep base repaired.val := repaired.property.2

theorem repaired_corners : corner source repaired.val = patchCorners :=
  corner_edgeColours source patchCorners

theorem selected_target_vertices : (Finset.univ.filter keep).card = 14 := by decide +kernel

theorem exterior_target_vertices : (Finset.univ.filter (fun d => ¬keep d)).card = 10 := by
  decide +kernel

theorem internal_polygon_variables :
    (Finset.univ.filter (fun d : source.D => keep d ∧ keep (source.phi.symm d))).card = 10 := by
  decide +kernel

theorem internal_cross_variables :
    (Finset.univ.filter (fun e : Fin 12 => keep (DualTruncateCoupledExample.code.representative e))).card = 7 := by
  decide +kernel

/-- The exact retained witness has a cyclic difference that a source
vertex-colouring summary would erase. -/
theorem difference_nonzero : difference source patchCorners (0,0) = blue := by
  decide +kernel

theorem not_coherent : ¬Coherent source patchCorners := by
  intro hc
  have hzero := difference_zero_of_coherent source hc (0,0)
  rw [difference_nonzero] at hzero
  exact blue_ne_zero hzero

theorem no_matching_source_witness :
    ¬ ∃ c : ThreeVertexColoring source,
      ∀ d, c.colour (source.vertOf d) = patchCorners d := by
  rw [source_witness_iff source patchCorners patch_valid]
  exact not_coherent

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

theorem every_complete_sweep (order : List source.D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic source) (DualTruncateConstructionGSLT.rotationCyclic source)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateOpenPatch.every_complete_sweep source closed exterior_stars patch_summary
    order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample
