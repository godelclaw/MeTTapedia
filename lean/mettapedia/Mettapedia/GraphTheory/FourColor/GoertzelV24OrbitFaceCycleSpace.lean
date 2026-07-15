import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleSpace
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceCycleSpace

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- With two distinct dart-side faces at every edge, membership toggles along
a facial orbit are in bijection with that face's edges incident to a fixed
vertex. -/
theorem togglesOn_card_eq_incidentEdges_inter_faceEdges_of_twoSided
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (representative : RS.D) (vertex : V) :
    (RS.togglesOn vertex representative).card =
      (RS.incidentEdges vertex ∩ RS.faceEdges representative).card := by
  classical
  refine Finset.card_bij (fun dart _ => RS.edgeOf dart) ?_ ?_ ?_
  · intro dart hdart
    rcases (RS.mem_togglesOn_iff).1 hdart with ⟨horbit, htoggle⟩
    have hedgeFace : RS.edgeOf dart ∈ RS.faceEdges representative :=
      (RS.mem_faceEdges_iff).2 ⟨dart, horbit, rfl⟩
    have hvertex :
        (RS.vertOf dart = vertex ∧ RS.vertOf (RS.phi dart) ≠ vertex) ∨
          (RS.vertOf dart ≠ vertex ∧ RS.vertOf (RS.phi dart) = vertex) := by
      by_cases hleft : RS.vertOf dart = vertex
      · by_cases hrightRaw : RS.vertOf (RS.rho (RS.alpha dart)) = vertex
        · exact (htoggle (by
            simp [RotationSystem.phi_apply, hleft, hrightRaw])).elim
        · have hright : RS.vertOf (RS.phi dart) ≠ vertex := by
            intro h
            exact hrightRaw (by simpa [RotationSystem.phi_apply] using h)
          exact Or.inl ⟨hleft, hright⟩
      · by_cases hrightRaw : RS.vertOf (RS.rho (RS.alpha dart)) = vertex
        · have hright : RS.vertOf (RS.phi dart) = vertex := by
            simpa [RotationSystem.phi_apply] using hrightRaw
          exact Or.inr ⟨hleft, hright⟩
        · exact (htoggle (by
            simp [RotationSystem.phi_apply, hleft, hrightRaw])).elim
    have hedgeIncident : RS.edgeOf dart ∈ RS.incidentEdges vertex := by
      rcases hvertex with ⟨hleft, _⟩ | ⟨_, hright⟩
      · exact (RS.mem_incidentEdges_iff).2 ⟨dart, rfl, hleft⟩
      · exact (RS.mem_incidentEdges_iff).2
          ⟨RS.alpha dart, RS.edge_alpha dart,
            (RS.vert_phi_eq_vert_alpha dart).symm.trans hright⟩
    exact Finset.mem_inter.2 ⟨hedgeIncident, hedgeFace⟩
  · intro left hleft right hright hedge
    have hleftOrbit := (RS.mem_togglesOn_iff).1 hleft |>.1
    have hrightOrbit := (RS.mem_togglesOn_iff).1 hright |>.1
    rcases RS.edge_fiber_two_cases
        (e := RS.edgeOf left) (d := left) (y := right)
        rfl (by simpa using hedge.symm) with heq | heq
    · exact heq.symm
    · exfalso
      apply htwoSided left
      have hleftFace :
          dartOrbitFace RS left = dartOrbitFace RS representative := by
        apply Quotient.sound
        exact ((RS.mem_faceOrbit).1 hleftOrbit).symm
      have hrightFace :
          dartOrbitFace RS right = dartOrbitFace RS representative := by
        apply Quotient.sound
        exact ((RS.mem_faceOrbit).1 hrightOrbit).symm
      rw [← heq]
      exact hleftFace.trans hrightFace.symm
  · intro edge hedge
    have hedgeIncident : edge ∈ RS.incidentEdges vertex :=
      (Finset.mem_inter.1 hedge).1
    have hedgeFace : edge ∈ RS.faceEdges representative :=
      (Finset.mem_inter.1 hedge).2
    rcases (RS.mem_faceEdges_iff).1 hedgeFace with
      ⟨faceDart, hfaceOrbit, hfaceEdge⟩
    rcases (RS.mem_incidentEdges_iff).1 hedgeIncident with
      ⟨vertexDart, hvertexEdge, hvertex⟩
    rcases RS.edge_fiber_two_cases
        (e := RS.edgeOf faceDart) (d := faceDart) (y := vertexDart)
        rfl (by rw [hfaceEdge, ← hvertexEdge]) with heq | heq
    · have hleft : RS.vertOf faceDart = vertex := by
        rw [← heq]
        exact hvertex
      have hright : RS.vertOf (RS.phi faceDart) ≠ vertex := by
        intro hright
        have hvalpha : RS.vertOf (RS.alpha faceDart) = vertex := by
          rw [← RS.vert_phi_eq_vert_alpha faceDart]
          exact hright
        exact RS.no_self_loops faceDart (hleft.trans hvalpha.symm)
      have hrightRaw : RS.vertOf (RS.rho (RS.alpha faceDart)) ≠ vertex := by
        intro h
        exact hright (by simpa [RotationSystem.phi_apply] using h)
      refine ⟨faceDart, (RS.mem_togglesOn_iff).2 ⟨hfaceOrbit, ?_⟩,
        hfaceEdge⟩
      simp [RotationSystem.phi_apply, hleft, hrightRaw]
    · have hright : RS.vertOf (RS.alpha faceDart) = vertex := by
        rw [← heq]
        exact hvertex
      have hleft : RS.vertOf faceDart ≠ vertex := by
        intro hleft
        exact RS.no_self_loops faceDart (hleft.trans hright.symm)
      have hphi : RS.vertOf (RS.phi faceDart) = vertex :=
        (RS.vert_phi_eq_vert_alpha faceDart).trans hright
      have hphiRaw : RS.vertOf (RS.rho (RS.alpha faceDart)) = vertex := by
        simpa [RotationSystem.phi_apply] using hphi
      refine ⟨faceDart, (RS.mem_togglesOn_iff).2 ⟨hfaceOrbit, ?_⟩,
        hfaceEdge⟩
      simp [RotationSystem.phi_apply, hleft, hphiRaw]

/-- Every simple quotient facial boundary has even degree at each vertex. -/
theorem incidentEdges_inter_orbitFaceBoundary_card_even
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (face : OrbitFace RS) (vertex : V) :
    Even ((RS.incidentEdges vertex ∩ orbitFaceBoundary RS face).card) := by
  rcases exists_dartOrbitFace_eq RS face with ⟨representative, hface⟩
  rw [← hface, orbitFaceBoundary_dartOrbitFace_eq_faceEdges]
  rw [← togglesOn_card_eq_incidentEdges_inter_faceEdges_of_twoSided
    RS htwoSided representative vertex]
  exact RS.togglesOn_card_even representative vertex

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For graph-backed rotations, the stored incident-edge predicate is exactly
membership of the vertex in the underlying `Sym2` graph edge. -/
theorem mem_toRotationSystem_incidentEdges_iff
    (data : Data G) (vertex : V) (edge : G.edgeSet) :
    edge ∈ data.toRotationSystem.incidentEdges vertex ↔
      vertex ∈ (edge.1 : Sym2 V) := by
  constructor
  · intro hedge
    rcases (data.toRotationSystem.mem_incidentEdges_iff).1 hedge with
      ⟨dart, hdartEdge, hdartVertex⟩
    have hedgeValue : dart.edge = edge.1 :=
      congrArg Subtype.val hdartEdge
    rw [← hedgeValue, ← hdartVertex]
    simp [SimpleGraph.Dart.edge]
  · intro hedge
    rcases (Sym2.mem_iff_exists).1 hedge with ⟨other, hedgeValue⟩
    have hadj : G.Adj vertex other := by
      rw [← SimpleGraph.mem_edgeSet G, ← hedgeValue]
      exact edge.2
    let dart : G.Dart := ⟨(vertex, other), hadj⟩
    exact (data.toRotationSystem.mem_incidentEdges_iff).2
      ⟨dart, Subtype.ext hedgeValue.symm, rfl⟩

/-- The scalar indicator of one quotient facial boundary. -/
def orbitFaceBoundaryIndicator (data : Data G)
    (face : OrbitFace data.toRotationSystem) : G.edgeSet → F2 :=
  fun edge => if edge ∈ orbitFaceBoundary data.toRotationSystem face
    then 1 else 0

/-- A two-sided quotient facial boundary is a genuine element of the graph's
`F2` cycle space. -/
theorem orbitFaceBoundaryIndicator_mem_f2CycleSpace
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (face : OrbitFace data.toRotationSystem) :
    orbitFaceBoundaryIndicator data face ∈ f2CycleSpace G := by
  rw [f2CycleSpace, LinearMap.mem_ker]
  funext vertex
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    f2IncidenceMatrix, orbitFaceBoundaryIndicator]
  change (∑ edge : G.edgeSet,
    (if vertex ∈ (edge.1 : Sym2 V) then 1 else 0) *
      (if edge ∈ orbitFaceBoundary data.toRotationSystem face
        then 1 else 0)) = 0
  let incidentBoundary :=
    data.toRotationSystem.incidentEdges vertex ∩
      orbitFaceBoundary data.toRotationSystem face
  have hfilter :
      (Finset.univ.filter fun edge : G.edgeSet =>
        vertex ∈ (edge.1 : Sym2 V) ∧
          edge ∈ orbitFaceBoundary data.toRotationSystem face) =
        incidentBoundary := by
    ext edge
    simp [incidentBoundary, mem_toRotationSystem_incidentEdges_iff data]
  calc
    (∑ edge : G.edgeSet,
      (if vertex ∈ (edge.1 : Sym2 V) then 1 else 0) *
        (if edge ∈ orbitFaceBoundary data.toRotationSystem face
          then 1 else 0)) =
        ∑ edge : G.edgeSet,
          if vertex ∈ (edge.1 : Sym2 V) ∧
            edge ∈ orbitFaceBoundary data.toRotationSystem face
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hvertex : vertex ∈ (edge.1 : Sym2 V) <;>
        by_cases hface : edge ∈
          orbitFaceBoundary data.toRotationSystem face <;>
        simp [hvertex, hface]
    _ = ((Finset.univ.filter fun edge : G.edgeSet =>
        vertex ∈ (edge.1 : Sym2 V) ∧
          edge ∈ orbitFaceBoundary data.toRotationSystem face).card : F2) := by
      exact Finset.sum_boole _ _
    _ = (incidentBoundary.card : F2) := by rw [hfilter]
    _ = 0 :=
      (incidentEdges_inter_orbitFaceBoundary_card_even
        data.toRotationSystem htwoSided face vertex).natCast_zmod_two

end

end GoertzelV24OrbitFaceCycleSpace

end Mettapedia.GraphTheory.FourColor
