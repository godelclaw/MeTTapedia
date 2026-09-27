import Mettapedia.GraphTheory.FourColor.FaceRegionBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided

/-!
# A facial bond constructs an actual plane patch

Both connected sides of a facial bipartition have a complete simple primal
contour. The exterior darts in the literal retained-edge map form exactly
one face: membership propagates across every edge of that contour. All
degree-two vertices lie on this outer face, so the plane-patch curvature
theorems apply with no assumed disk, boundary word or patch Euler equation.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionPatch

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open GoertzelV24BridgelessFaceTwoSided PhysicalForkCodeFaces
open FaceRegionDegree EdgeShoreRotation PlanePatchCurvature FaceRegionBoundary
open FaceRegionConnectivity SphericalDistanceContours FaceDistanceFrontiers

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E} {R : Finset (OrbitFace RS)}

/-- Boundary membership expressed on the original vertex carrier. -/
def OnOuter (outer : Dart RS (edges RS R)) (v : V) : Prop :=
  ∃ d : Dart RS (edges RS R), RS.vertOf d.val = v ∧
    d ∈ outerDarts (toMap RS (edges RS R) outer)

theorem onOuter_across_outside (hC : Cubic3 RS)
    (outer d : Dart RS (edges RS R))
    (ho : dartOrbitFace RS outer.val ∉ R) (hd : dartOrbitFace RS d.val ∉ R) :
    OnOuter outer (RS.vertOf d.val) ↔ OnOuter outer (RS.vertOf (RS.alpha d.val)) := by
  let next := (toMap RS (edges RS R) outer).phi d
  have hn : dartOrbitFace RS next.val ∉ R := (outside_phi_iff outer d).mpr hd
  have hv : RS.vertOf next.val = RS.vertOf (RS.alpha d.val) :=
    congrArg Subtype.val ((toMap RS (edges RS R) outer).vert_phi_eq_vert_alpha d)
  constructor
  · rintro ⟨e, he, hem⟩
    have hed := outside_vertex_injective hC e d (outer_dart_outside outer ho hem) hd he
    subst e
    exact ⟨next, hv, (outer_phi_iff (RS := toMap RS (edges RS R) outer) d).mpr hem⟩
  · rintro ⟨e, he, hem⟩
    have hen := outside_vertex_injective hC e next (outer_dart_outside outer ho hem) hn
      (he.trans hv.symm)
    have hnm : next ∈ outerDarts (toMap RS (edges RS R) outer) := hen ▸ hem
    exact ⟨d, rfl, (outer_phi_iff (RS := toMap RS (edges RS R) outer) d).mp hnm⟩

theorem onOuter_across_cut (hC : Cubic3 RS) (outer : Dart RS (edges RS R))
    (ho : dartOrbitFace RS outer.val ∉ R) (d : RS.D)
    (hcut : (dartOrbitFace RS d ∈ R ∧ dartOrbitFace RS (RS.alpha d) ∉ R) ∨
      (dartOrbitFace RS d ∉ R ∧ dartOrbitFace RS (RS.alpha d) ∈ R)) :
    OnOuter outer (RS.vertOf d) ↔ OnOuter outer (RS.vertOf (RS.alpha d)) := by
  rcases hcut with h | h
  · have ha : dartOrbitFace RS (RS.alpha (RS.alpha d)) ∈ R := by
      simpa only [RS.alpha_involutive] using h.1
    have hh := onOuter_across_outside hC outer
      ⟨RS.alpha d, (edge_mem_iff RS R _).mpr (Or.inr ha)⟩ ho h.2
    simpa only [RS.alpha_involutive] using hh.symm
  · exact onOuter_across_outside hC outer
      ⟨d, (edge_mem_iff RS R _).mpr (Or.inr h.2)⟩ ho h.1

section Graph

open _root_.SimpleGraph SimpleGraphDartRotation
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) (F : Finset (OrbitFace data.toRotationSystem))
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem F))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ F)

include ambient ho

theorem onOuter_along_cut_walk {u v : V} (p : G.Walk u v)
    (hcut : ∀ d : data.toRotationSystem.D,
      (data.toRotationSystem.edgeOf d).val ∈ p.edges →
        (dartOrbitFace data.toRotationSystem d ∈ F ∧
          dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉ F) ∨
        (dartOrbitFace data.toRotationSystem d ∉ F ∧
          dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ F)) :
    OnOuter outer u ↔ OnOuter outer v := by
  induction p with
  | nil => rfl
  | @cons u v w hadj p ih =>
    let d : G.Dart := ⟨(u, v), hadj⟩
    have hh := onOuter_across_cut
      (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) outer ho d
      (hcut d (by simp [SimpleGraph.Walk.edges_cons, d]))
    exact hh.trans (ih (fun e he => hcut e (by
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inr he)))

/-- Completeness of the primal contour forces all exterior occurrences
into the chosen outer face. Other exterior components are not assumed away. -/
theorem mem_outerDarts_iff
    (hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected)
    (hFc : ((orbitFaceDualGraph data).induce (F : Set _)ᶜ).Connected)
    (d : Dart data.toRotationSystem (edges data.toRotationSystem F)) :
    d ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) ↔
      dartOrbitFace data.toRotationSystem d.val ∉ F := by
  refine ⟨outer_dart_outside outer ho, ?_⟩
  intro hd
  have htwo := GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
    data.toRotationSystem ambient
  obtain ⟨root, cycle, _, hexact⟩ :=
    FacialBondPrimalCycle.exists_cycle_of_facial_bond data ambient htwo F hF hFc
  have hcut (e : data.toRotationSystem.D)
      (he : (data.toRotationSystem.edgeOf e).val ∈ cycle.edges) :=
    (boundary_ne_zero_iff_separates data htwo F e).mp ((hexact _).mp he)
  have hin (e : Dart data.toRotationSystem (edges data.toRotationSystem F))
      (he : dartOrbitFace data.toRotationSystem e.val ∉ F) :
      data.toRotationSystem.vertOf e.val ∈ cycle.support := by
    have hc := (edge_mem_iff _ _ e.val).mp e.property |>.resolve_left he
    have hm := (hexact _).mpr
      ((boundary_ne_zero_iff_separates data htwo F e.val).mpr (Or.inr ⟨he, hc⟩))
    exact cycle.fst_mem_support_of_mem_edges hm
  have path_iff (e : Dart data.toRotationSystem (edges data.toRotationSystem F))
      (he : dartOrbitFace data.toRotationSystem e.val ∉ F) :
      OnOuter outer root ↔ OnOuter outer (data.toRotationSystem.vertOf e.val) := by
    exact onOuter_along_cut_walk data F ambient outer ho
      (cycle.takeUntil _ (hin e he)) (fun a ha =>
        hcut a (cycle.edges_takeUntil_subset_edges (hin e he) ha))
  have hroot : OnOuter outer root := (path_iff outer ho).mpr
    ⟨outer, rfl, (mem_orbitFaceDarts_iff _ _ _).mpr rfl⟩
  obtain ⟨e, he, hem⟩ := (path_iff d hd).mp hroot
  have hed := outside_vertex_injective
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) e d
    (outer_dart_outside outer ho hem) hd he
  exact hed ▸ hem

/-- A connected facial side with connected complement is literally a
plane patch in the restricted rotation system. All patch fields are derived. -/
theorem patch
    (hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected)
    (hFc : ((orbitFaceDualGraph data).induce (F : Set _)ᶜ).Connected) :
    Patch (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) := by
  obtain ⟨hc, hr, he, hd⟩ := retained_geometry data F ambient hF outer
  have hC := cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic
  refine ⟨hc, hr, he, outer_simple outer hC ho, fun v _ => hd v, ?_⟩
  intro v hv
  rcases hd v with htwo | hthree
  · obtain ⟨d, hdv, hdf⟩ := outside_at_vertex_of_degree_two outer hC ambient.spherical.cubic v htwo
    have hm := (mem_outerDarts_iff data F ambient outer ho hF hFc d).mpr hdf
    exact (hv (Finset.mem_image.mpr ⟨d, hm, Subtype.ext hdv⟩)).elim
  · exact hthree

/-- Boundary vertices are precisely the original mixed vertices. -/
theorem boundaryVertices_iff_mixed
    (hF : ((orbitFaceDualGraph data).induce (F : Set _)).Connected)
    (hFc : ((orbitFaceDualGraph data).induce (F : Set _)ᶜ).Connected)
    (v : Vertex data.toRotationSystem (edges data.toRotationSystem F)) :
    v ∈ boundaryVertices (toMap data.toRotationSystem (edges data.toRotationSystem F) outer) ↔
      Mixed (vertexFaces data) (F : Set _) v.val := by
  constructor
  · rintro hv
    obtain ⟨d, hd, hdv⟩ := Finset.mem_image.mp hv
    have hout := outer_dart_outside outer ho hd
    have hin := (edge_mem_iff_sectors _ _ d.val).mp d.property |>.resolve_left hout
    have hdv' := congrArg Subtype.val hdv
    exact ⟨⟨_, ⟨_, (data.toRotationSystem.vert_rho d.val).trans hdv', rfl⟩, hin⟩,
      ⟨_, ⟨_, hdv', rfl⟩, hout⟩⟩
  · rintro ⟨⟨f, ⟨d, hd, hdf⟩, hf⟩, ⟨g, ⟨e, he, heg⟩, hg⟩⟩
    obtain ⟨a, ha, haf⟩ := exists_outside_at_vertex
      (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) v.val
      ⟨d, hd, hdf ▸ hf⟩ ⟨e, he, heg ▸ hg⟩
    exact Finset.mem_image.mpr ⟨a,
      (mem_outerDarts_iff data F ambient outer ho hF hFc a).mpr haf, Subtype.ext ha⟩

end Graph
end
end Mettapedia.GraphTheory.FourColor.FaceRegionPatch
