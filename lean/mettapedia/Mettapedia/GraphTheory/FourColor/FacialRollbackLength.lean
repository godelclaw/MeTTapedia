import Mettapedia.GraphTheory.FourColor.LongPathKempeLifting
import Mettapedia.GraphTheory.FourColor.FaceKempeRepair

/-!
# Only short facial rollbacks can escape an old Kempe class

For a facial path with at least three edges, every smaller history lifts
to any specified proper reconstruction on the old retained edges. Such
a rollback cannot create reachability between previously separated old
colourings. The path, degree bounds, and attachment conditions are all
constructed from the spherical facial event.
-/

namespace Mettapedia.GraphTheory.FourColor.FacialRollbackLength

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut PhysicalForkCodeFaces
open PermutationSingleExitArc FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
include ambient

/-- Every smaller physical history can be reproduced on the old patch,
ending with all retained colours of the specified old reconstruction. -/
theorem long_route_lifts (hlong : 3 ≤ (exposedEdges data e).card)
    {C D : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces)).Coloring (Fin 3)}
    (history : History C D)
    (old target : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces ∪ exposedEdges data e)).Coloring (Fin 3))
    (hold : ∀ x ∈ edges data.toRotationSystem S.faces, old x = C x)
    (htarget : ∀ x ∈ edges data.toRotationSystem S.faces, target x = D x) :
    ∃ final : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces ∪ exposedEdges data e)).Coloring (Fin 3),
      Nonempty (History old final) ∧
        ∀ x ∈ edges data.toRotationSystem S.faces ∪ exposedEdges data e, final x = target x := by
  obtain ⟨oR, hR, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e oR ambient hR
  let p := path data e oR ambient hR arc
  have hC := cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic
  apply LongPathKempeLifting.history_lifts p (edges data.toRotationSystem S.faces) ?_
    (by rwa [path_length]) (FaceColourTransfer.shores_disjoint data e) ?_ ?_
    history old target hold htarget
  · intro x hx y hy v hvx hvy
    obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
    have hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) :=
      mem_touched.mpr ⟨d, hdv, (data.toRotationSystem.mem_dartsOn.mp hd).symm ▸ hx⟩
    exact shared_vertex data e ambient oR hR arc hv hy hvy
  · exact le_of_eq (FaceRegionMissingColour.incident_card_two hC ambient.spherical.cubic
      (first_old data e ambient oR hR arc) (Finset.mem_sdiff.mp p.firstEdge_mem).2
      p.firstEdge_incident)
  · exact le_of_eq (FaceRegionMissingColour.incident_card_two hC ambient.spherical.cubic
      (last_old data e ambient oR hR arc) (Finset.mem_sdiff.mp p.lastEdge_mem).2
      p.lastEdge_incident)

/-- A rollback which really connects previously unreachable reconstructed
colourings must delete at most two edges. This is a necessary condition,
not a claim that every short rollback succeeds. -/
theorem escape_requires_short
    {C D : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces)).Coloring (Fin 3)}
    (history : History C D)
    (old target : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces ∪ exposedEdges data e)).Coloring (Fin 3))
    (hold : ∀ x ∈ edges data.toRotationSystem S.faces, old x = C x)
    (htarget : ∀ x ∈ edges data.toRotationSystem S.faces, target x = D x)
    (escape : ¬ ∃ final : (graph data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces ∪ exposedEdges data e)).Coloring (Fin 3),
      Nonempty (History old final) ∧
        ∀ x ∈ edges data.toRotationSystem S.faces ∪ exposedEdges data e, final x = target x) :
    (exposedEdges data e).card ≤ 2 := by
  by_contra h
  exact escape (long_route_lifts data e ambient (by omega) history old target hold htarget)

/-- Any smaller history which escapes an old Kempe class must leave
the image of reconstruction. This holds for every actual facial event:
long paths cannot escape, and short reconstructible histories lift. -/
theorem escape_leaves_reconstruction_image
    {C D : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces)).Coloring (Fin 3)}
    (history : History C D)
    (old target : (graph data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces ∪ exposedEdges data e)).Coloring (Fin 3))
    (hold : ∀ x ∈ edges data.toRotationSystem S.faces, old x = C x)
    (htarget : ∀ x ∈ edges data.toRotationSystem S.faces, target x = D x)
    (escape : ¬ ∃ final : (graph data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces ∪ exposedEdges data e)).Coloring (Fin 3),
      Nonempty (History old final) ∧
        ∀ x ∈ edges data.toRotationSystem S.faces ∪ exposedEdges data e, final x = target x) :
    ¬ Nonempty (Route
      (ShortPathKempeLifting.ImageStep (inc := data.toRotationSystem.endpoints)
        (S := exposedEdges data e) (edges data.toRotationSystem S.faces))
      ⟨C, old, hold⟩ ⟨D, target, htarget⟩) := by
  have hshort := escape_requires_short data e ambient history old target hold htarget escape
  rintro ⟨imageHistory⟩
  obtain ⟨final, hfinal, hagree⟩ := FaceKempeRepair.reconstructible_route_lifts
    data e ambient hshort imageHistory old hold
  obtain ⟨oR, hR, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e oR ambient hR
  let p := path data e oR ambient hR arc
  obtain ⟨m, n, hm, hn⟩ := FacePathExtension.endpoint_colours
    data e oR ambient hR arc D (proper _ _ D)
  apply escape
  refine ⟨final, hfinal, ?_⟩
  exact p.extension_unique_of_length_le_two (by rwa [path_length])
    (edges data.toRotationSystem S.faces) (FaceColourTransfer.shores_disjoint data e)
    D final target m n hm hn (proper _ _ final) (proper _ _ target) hagree htarget

end
end Mettapedia.GraphTheory.FourColor.FacialRollbackLength
