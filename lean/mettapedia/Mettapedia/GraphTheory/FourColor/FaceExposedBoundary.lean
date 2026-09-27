import Mettapedia.GraphTheory.FourColor.FaceAttachmentBoundary
import Mettapedia.GraphTheory.FourColor.FaceRegionComplement

/-!
# The newly exposed boundary is one ordered arc

On the actual new patch, select exactly those outer darts whose original
edges were added by the facial event. Their endpoint set is computed on
the original graph. The complementary-region Euler law gives one more
vertex than edge, which forces one contiguous arc of the actual new
boundary permutation.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceExposedBoundary

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionComplement
open FaceRegionBoundary FaceRegionPatch FaceRegionStepBoundary
open PhysicalForkCodeCut PhysicalForkCodeFaces PermutationSingleExitArc

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))

def exposedDarts : Finset (Dart data.toRotationSystem (edges data.toRotationSystem R.faces)) :=
  (outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer)).filter
    fun d => data.toRotationSystem.edgeOf d.val ∈ exposedEdges data e

theorem mem_exposedDarts (d : Dart data.toRotationSystem (edges data.toRotationSystem R.faces)) :
    d ∈ exposedDarts data e outer ↔
      d ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer) ∧
      data.toRotationSystem.edgeOf d.val ∈ exposedEdges data e := by
  exact Finset.mem_filter

theorem exposed_successors_on_outer :
    exposedDarts data e outer ∪ (exposedDarts data e outer).image
        (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi ⊆
      outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer) := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · exact ((mem_exposedDarts data e outer d).mp hd).1
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact (outer_phi_iff x).mpr ((mem_exposedDarts data e outer x).mp hx).1

variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)

include ambient ho

theorem exposed_edge_image :
    (exposedDarts data e outer).image (fun d => data.toRotationSystem.edgeOf d.val) =
      exposedEdges data e := by
  ext a
  constructor
  · intro ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    exact ((mem_exposedDarts data e outer d).mp hd).2
  · intro ha
    obtain ⟨d, hd, hda⟩ := (mem_orbitFaceBoundary_iff data.toRotationSystem e.face a).mp
      (Finset.mem_sdiff.mp ha).1
    have had : data.toRotationSystem.edgeOf (data.toRotationSystem.alpha d) ∈ exposedEdges data e := by
      rw [data.toRotationSystem.edge_alpha, hda]
      exact ha
    let d' : Dart data.toRotationSystem (edges data.toRotationSystem R.faces) :=
      ⟨data.toRotationSystem.alpha d, exposed_mem_new data e had⟩
    refine Finset.mem_image.mpr ⟨d', Finset.mem_filter.mpr ⟨?_, had⟩, ?_⟩
    · apply (mem_outerDarts_iff data R.faces ambient outer ho R.inside R.outside d').mpr
      exact exposed_alpha_outside data ambient e d ((mem_orbitFaceDarts_iff _ _ _).mp hd)
        (hda.symm ▸ ha)
    · exact (data.toRotationSystem.edge_alpha d).trans hda

theorem exposed_vertex_image :
    touched data.toRotationSystem (exposedEdges data e) =
      (exposedDarts data e outer ∪ (exposedDarts data e outer).image
        (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi).image
        (fun d => data.toRotationSystem.vertOf d.val) := by
  let T := toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer
  ext v
  constructor
  · intro hv
    obtain ⟨d, hdv, hd⟩ := mem_touched.mp hv
    rw [← exposed_edge_image data e outer ambient ho] at hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    rcases data.toRotationSystem.edge_fiber_two_cases rfl hxd.symm with heq | heq
    · rw [heq] at hdv
      exact Finset.mem_image.mpr ⟨x, Finset.mem_union_left _ hx, hdv⟩
    · rw [heq] at hdv
      exact Finset.mem_image.mpr ⟨T.phi x,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩),
        (congrArg Subtype.val (T.vert_phi_eq_vert_alpha x)).trans hdv⟩
  · intro hv
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hd with hd | hd
    · exact mem_touched.mpr ⟨d.val, rfl, ((mem_exposedDarts data e outer d).mp hd).2⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      refine mem_touched.mpr ⟨data.toRotationSystem.alpha x.val,
        (congrArg Subtype.val (T.vert_phi_eq_vert_alpha x)).symm, ?_⟩
      rw [data.toRotationSystem.edge_alpha]
      exact ((mem_exposedDarts data e outer x).mp hx).2

theorem exposed_darts_card : (exposedDarts data e outer).card = (exposedEdges data e).card := by
  rw [← exposed_edge_image data e outer ambient ho]
  exact (Finset.card_image_of_injOn ((outer_edges_injective data ambient R outer ho).mono
    (Finset.filter_subset _ _))).symm

theorem exposed_successor_count :
    (exposedDarts data e outer ∪ (exposedDarts data e outer).image
        (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi).card =
      (exposedDarts data e outer).card + 1 := by
  have hi : Set.InjOn
      (fun d : Dart data.toRotationSystem (edges data.toRotationSystem R.faces) =>
        data.toRotationSystem.vertOf d.val)
      ((exposedDarts data e outer ∪ (exposedDarts data e outer).image
        (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi) :
        Finset (Dart data.toRotationSystem (edges data.toRotationSystem R.faces))) := by
    intro d hd x hx hv
    exact FaceRegionBoundary.outer_simple outer
      (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) ho
      (exposed_successors_on_outer data e outer hd)
      (exposed_successors_on_outer data e outer hx) (Subtype.ext hv)
  have hv := Finset.card_image_of_injOn hi
  rw [← exposed_vertex_image data e outer ambient ho, exposed_count data ambient e,
    ← exposed_darts_card data e outer ambient ho] at hv
  exact hv.symm

/-- The new edges occur consecutively in the actual new boundary order.
Both boundary neighbours are outside the new-edge arc. -/
theorem exists_exposed_arc :
    Nonempty (Arc (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
      (exposedDarts data e outer)) := by
  apply exists_arc_of_union_card _ _ ?_ (exposed_successor_count data e outer ambient ho)
  intro d hd x hx
  have hd' := ((mem_exposedDarts data e outer d).mp hd).1
  have hx' := ((mem_exposedDarts data e outer x).mp hx).1
  have hdf := (mem_orbitFaceDarts_iff _ _ _).mp hd'
  have hxf := (mem_orbitFaceDarts_iff _ _ _).mp hx'
  exact @Quotient.exact _ (Perm.SameCycle.setoid
    (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi) d x
    (hdf.trans hxf.symm)

end
end Mettapedia.GraphTheory.FourColor.FaceExposedBoundary
