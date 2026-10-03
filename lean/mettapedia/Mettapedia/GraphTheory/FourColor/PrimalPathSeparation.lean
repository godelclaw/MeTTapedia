import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceParityCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport

/-!
# Closed-walk face potentials separate disjoint vertex paths

The separating walk need not be simple. Its mod-two edge multiplicities
give a face potential on a cellular sphere, and a vertex-disjoint path
preserves that potential between any incident endpoint faces. This allows
a fixed return through a patch to close an exterior path even when the
exterior path visits other boundary vertices.
-/

namespace Mettapedia.GraphTheory.FourColor.PrimalPathSeparation

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24FaceCutTransport GoertzelV24FaceCutVertexAvoidingTransport
open GoertzelV24WalkCycleParity GoertzelV24OrbitFaceParityBoundary
open GoertzelV24PrimalCycleSpace SimpleGraph SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Any two endpoint dart sides have the same label along a walk whose
vertices have no incident cut edge. Degrees are unrestricted. -/
theorem labels_eq_along_walk (data : Data G)
    (rotation : VertexRotationCyclic data.toRotationSystem)
    {A : Type*} (labels : OrbitFace data.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (exactCut : ∀ d, labels (dartOrbitFace data.toRotationSystem d) ≠
      labels (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)) ↔
        cut (data.toRotationSystem.edgeOf d))
    {u v : V} (walk : G.Walk u v)
    (avoid : ∀ x ∈ walk.support, ∀ d : G.Dart, d.fst = x →
      ¬cut (data.toRotationSystem.edgeOf d))
    (first last : G.Dart) (hfirst : first.fst = u) (hlast : last.fst = v) :
    labels (dartOrbitFace data.toRotationSystem first) =
      labels (dartOrbitFace data.toRotationSystem last) := by
  induction walk generalizing first last with
  | nil =>
      exact labels_eq_of_same_vertex_of_all_edges_not_cut
        data.toRotationSystem rotation labels cut exactCut first last
        (hlast.trans hfirst.symm) (fun d hd => avoid _ (by simp) d (hd.trans hfirst))
  | @cons u w v edge tail ih =>
      let d : G.Dart := ⟨(u, w), edge⟩
      have turn := labels_eq_of_same_vertex_of_all_edges_not_cut
        data.toRotationSystem rotation labels cut exactCut first d hfirst.symm
        (fun e he => avoid u (by simp) e (he.trans hfirst))
      have cross := labels_eq_alpha_of_not_cut data.toRotationSystem labels cut exactCut d
        (avoid u (by simp) d rfl)
      have rest := ih (fun x hx e he => avoid x (by simp [hx]) e he)
        d.symm last rfl hlast
      exact turn.trans (cross.trans rest)

/-- Face potentials of a closed walk are constant along every vertex-disjoint
walk. The two endpoint faces may be chosen using local patch triangles. -/
theorem labels_eq_of_disjoint_walk (data : Data G)
    (rotation : VertexRotationCyclic data.toRotationSystem)
    {r u v : V} (closed : G.Walk r r) (walk : G.Walk u v)
    (disjoint : ∀ x ∈ walk.support, x ∉ closed.support)
    (labels : OrbitFace data.toRotationSystem → F2)
    (potential : orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
      walkEdgeParity closed)
    (first last : G.Dart) (hfirst : first.fst = u) (hlast : last.fst = v) :
    labels (dartOrbitFace data.toRotationSystem first) =
      labels (dartOrbitFace data.toRotationSystem last) := by
  let cut : G.edgeSet → Prop := fun e => walkEdgeParity closed e = 1
  have exactCut : ∀ d, labels (dartOrbitFace data.toRotationSystem d) ≠
      labels (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)) ↔
        cut (data.toRotationSystem.edgeOf d) := by
    intro d
    rw [← f2_add_eq_one_iff_ne, ← orbitFaceParityBoundaryLinearMap_apply_edgeOf, potential]
  apply labels_eq_along_walk data rotation labels cut exactCut walk _ first last hfirst hlast
  intro x hx d hd hcut
  have absent : (data.toRotationSystem.edgeOf d).1 ∉ closed.edges := by
    intro hedge
    apply disjoint x hx
    rw [← hd]
    exact closed.fst_mem_support_of_mem_edges hedge
  have zero := walkEdgeParity_apply_eq_zero_of_not_mem_edges closed
    (data.toRotationSystem.edgeOf d) absent
  exact zero_ne_one (zero.symm.trans hcut)

end
end Mettapedia.GraphTheory.FourColor.PrimalPathSeparation
