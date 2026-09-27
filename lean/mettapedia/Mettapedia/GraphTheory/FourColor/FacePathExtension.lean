import Mettapedia.GraphTheory.FourColor.FaceColourTransfer
import Mettapedia.GraphTheory.FourColor.FaceRegionMissingColour
import Mettapedia.GraphTheory.FourColor.OrderedPathExtension

/-!
# Exact extension classification for a facial construction

Every attachment endpoint has a unique missing colour, derived from the
actual old incidence. One new edge requires equal missing colours, two
new edges require different missing colours, and three or more new edges
always extend a fixed proper old colouring. The final theorems construct
the path from the spherical map rather than assuming an arc supplier.
-/

namespace Mettapedia.GraphTheory.FourColor.FacePathExtension

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut PhysicalForkCodeFaces
open PermutationSingleExitArc FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)
variable (b : Arc
  (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))

/-- Cubic incidence supplies both endpoint colours for every proper old
colouring; no extension or support-richness hypothesis is used. -/
theorem endpoint_colours (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ r s : Fin 3,
      (∀ q, q ∉ profile data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces) a (path data e outer ambient ho b).first ↔ q = r) ∧
      (∀ q, q ∉ profile data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces) a (path data e outer ambient ho b).last ↔ q = s) := by
  let p := path data e outer ambient ho b
  have hC := cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic
  obtain ⟨r, hr, hur⟩ := FaceRegionMissingColour.existsUnique_missing hC ambient.spherical.cubic
    (first_old data e ambient outer ho b) (Finset.mem_sdiff.mp p.firstEdge_mem).2
    p.firstEdge_incident ha
  obtain ⟨s, hs, hus⟩ := FaceRegionMissingColour.existsUnique_missing hC ambient.spherical.cubic
    (last_old data e ambient outer ho b) (Finset.mem_sdiff.mp p.lastEdge_mem).2
    p.lastEdge_incident ha
  exact ⟨r, s, fun q => ⟨hur q, fun h => h.symm ▸ hr⟩,
    fun q => ⟨hus q, fun h => h.symm ▸ hs⟩⟩

/-- Exact classification, with the two endpoint colours constructed from
the given proper colouring of the old patch. -/
theorem extension_classification (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ r s : Fin 3,
      (∀ q, q ∉ profile data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces) a (path data e outer ambient ho b).first ↔ q = r) ∧
      (∀ q, q ∉ profile data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces) a (path data e outer ambient ho b).last ↔ q = s) ∧
      ((∃ d : G.edgeSet → Fin 3,
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) d ∧
          ∀ x ∈ edges data.toRotationSystem S.faces, d x = a x) ↔
        ((exposedEdges data e).card = 1 ∧ r = s) ∨
          ((exposedEdges data e).card = 2 ∧ r ≠ s) ∨ 3 ≤ (exposedEdges data e).card) := by
  obtain ⟨r, s, hr, hs⟩ := endpoint_colours data e outer ambient ho b a ha
  refine ⟨r, s, hr, hs, ?_⟩
  rw [FaceColourTransfer.extension_iff data e outer ambient ho b a ha]
  change (∃ c, (path data e outer ambient ho b).Consecutive c ∧
    (path data e outer ambient ho b).EndpointCompatible (edges data.toRotationSystem S.faces) a c) ↔ _
  rw [(path data e outer ambient ho b).endpoint_extension_iff _ a r s hr hs,
    path_length data e outer ambient ho b]

include ambient in
/-- Every actual event has this classified transfer law. The geometric
path and all missing-colour witnesses are supplied by the source map. -/
theorem exists_classified_transfer :
    ∃ p : OrderedEdgePath.Path data.toRotationSystem.endpoints (exposedEdges data e),
      p.length = (exposedEdges data e).card ∧
      ∀ a : G.edgeSet → Fin 3,
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a →
        ∃ r s : Fin 3,
          (∀ q, q ∉ profile data.toRotationSystem.endpoints
            (edges data.toRotationSystem S.faces) a p.first ↔ q = r) ∧
          (∀ q, q ∉ profile data.toRotationSystem.endpoints
            (edges data.toRotationSystem S.faces) a p.last ↔ q = s) ∧
          ((∃ d : G.edgeSet → Fin 3,
            Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) d ∧
              ∀ x ∈ edges data.toRotationSystem S.faces, d x = a x) ↔
            ((exposedEdges data e).card = 1 ∧ r = s) ∨
              ((exposedEdges data e).card = 2 ∧ r ≠ s) ∨ 3 ≤ (exposedEdges data e).card) := by
  obtain ⟨oR, hR, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e oR ambient hR
  exact ⟨path data e oR ambient hR arc, path_length data e oR ambient hR arc,
    extension_classification data e oR ambient hR arc⟩

include ambient in
/-- Adding at least three new edges always preserves every old edge
colour. The theorem assumes only the actual event and the old witness. -/
theorem extends_of_three_le (hlen : 3 ≤ (exposedEdges data e).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ d : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) d ∧
        ∀ x ∈ edges data.toRotationSystem S.faces, d x = a x := by
  obtain ⟨_, _, h⟩ := exists_classified_transfer data e ambient
  obtain ⟨_, _, _, _, hiff⟩ := h a ha
  exact hiff.mpr (Or.inr (Or.inr hlen))

end
end Mettapedia.GraphTheory.FourColor.FacePathExtension
