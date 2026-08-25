import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInteriorFaceGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleTurn

/-!
# Face adjacency from local cubicity on the opened closed-web carrier

The opened annulus has ten degree-one boundary stubs, so it is not globally
cubic and its faces are not globally two-sided.  Neither global hypothesis is
needed to turn adjacency of two distinct primal edges into adjacency of two
named incident faces.  A named face containing an edge is the face of one of
the edge's two darts, and a vertex incident to two distinct edges cannot be a
degree-one stub.  The remaining corner calculation is therefore locally
cubic on the literal opened carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalFaceBoundaryAdjacency

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceCycleSpace
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Every named face containing an edge is the face of one of its two oriented
darts.  This is intrinsic to a rotation system and needs no global
two-sidedness premise. -/
theorem dartOrbitFace_eq_or_alpha_eq_of_mem_faceBoundary
    (RS : RotationSystem V E) (dart : RS.D) (face : OrbitFace RS)
    (hedge : RS.edgeOf dart ∈ orbitFaceBoundary RS face) :
    dartOrbitFace RS dart = face ∨
      dartOrbitFace RS (RS.alpha dart) = face := by
  rcases (mem_orbitFaceBoundary_iff RS face (RS.edgeOf dart)).1 hedge with
    ⟨witness, hwitnessFace, hwitnessEdge⟩
  have hdartOn : dart ∈ RS.dartsOn (RS.edgeOf dart) :=
    RS.mem_dartsOn.2 rfl
  have hwitnessOn : witness ∈ RS.dartsOn (RS.edgeOf dart) :=
    RS.mem_dartsOn.2 hwitnessEdge
  have hwitnessCases : witness = dart ∨ witness = RS.alpha dart := by
    have : witness ∈ ({dart, RS.alpha dart} : Finset RS.D) := by
      rw [← RS.dartsOn_eq_pair_of_mem hdartOn]
      exact hwitnessOn
    simpa using this
  have hwitnessOrbit : dartOrbitFace RS witness = face :=
    (mem_orbitFaceDarts_iff RS face witness).1 hwitnessFace
  rcases hwitnessCases with rfl | rfl
  · exact Or.inl hwitnessOrbit
  · exact Or.inr hwitnessOrbit

/-- Consecutive incident darts at one locally cubic vertex force adjacency of
any two distinct named faces containing their edges. -/
private theorem interiorDualGraph_adj_of_consecutive_incident_darts
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {first second : RS.D}
    (hcard : (RS.dartsAt (RS.vertOf first)).card = 3)
    (hforward : RS.rho first = second)
    {left right : OrbitFace RS}
    (hfaces : left ≠ right)
    (hleft : RS.edgeOf first ∈ orbitFaceBoundary RS left)
    (hright : RS.edgeOf second ∈ orbitFaceBoundary RS right) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩ := by
  rcases dartOrbitFace_eq_or_alpha_eq_of_mem_faceBoundary RS first left hleft
      with hleftOwn | hleftOpposite
  · rcases dartOrbitFace_eq_or_alpha_eq_of_mem_faceBoundary
        RS second right hright with hrightOwn | hrightOpposite
    · have hmiddle : dartOrbitFace RS (RS.alpha first) = right := by
        rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho RS first, hforward]
        exact hrightOwn
      have hedge := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
        RS (RS.alpha first)
      rw [RS.edge_alpha first, hmiddle] at hedge
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
          (orbitFace_incidence_le_two RS)
          (f := ⟨left, Finset.mem_univ _⟩)
          (g := ⟨right, Finset.mem_univ _⟩)
          (e := RS.edgeOf first) hfaces hleft hedge
    · have hphi : RS.phi (RS.alpha first) = second := by
        rw [RotationSystem.phi_apply, RS.alpha_involutive]
        exact hforward
      have hleftFace :
          dartOrbitFace RS (RS.alpha (RS.alpha first)) = left := by
        rw [RS.alpha_involutive]
        exact hleftOwn
      have hrightFace :
          dartOrbitFace RS (RS.alpha (RS.phi (RS.alpha first))) = right := by
        rw [hphi]
        exact hrightOpposite
      have hcornerNe :
          dartOrbitFace RS (RS.alpha (RS.alpha first)) ≠
            dartOrbitFace RS (RS.alpha (RS.phi (RS.alpha first))) := by
        intro heq
        exact hfaces (hleftFace.symm.trans (heq.trans hrightFace))
      have hcorner := oppositeFaces_adjacent_at_locally_cubic_corner
        RS hrotation (RS.alpha first) (by
          rw [RS.alpha_involutive]
          exact hcard) hcornerNe
      simpa only [hleftFace, hrightFace] using hcorner
  · have hleftMiddle : dartOrbitFace RS second = left := by
      rw [← hforward, ← dartOrbitFace_alpha_eq_dartOrbitFace_rho]
      exact hleftOpposite
    rcases dartOrbitFace_eq_or_alpha_eq_of_mem_faceBoundary
        RS second right hright with hrightOwn | hrightOpposite
    · exact (hfaces (hleftMiddle.symm.trans hrightOwn)).elim
    · have hleftSecond : RS.edgeOf second ∈ orbitFaceBoundary RS left := by
        rw [← hleftMiddle]
        exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS second
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
          (orbitFace_incidence_le_two RS)
          (f := ⟨left, Finset.mem_univ _⟩)
          (g := ⟨right, Finset.mem_univ _⟩)
          (e := RS.edgeOf second) hfaces hleftSecond hright

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- On the actual opened closed-web carrier, distinct named faces containing
adjacent primal edges are adjacent in the full facial dual.  The common vertex
is locally cubic because its two distinct incident edges exclude every
degree-one boundary stub. -/
theorem interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {leftEdge rightEdge : G.edgeSet}
    {left right : OrbitFace web.annular.RS}
    (hfaces : left ≠ right)
    (hleft : leftEdge ∈ orbitFaceBoundary web.annular.RS left)
    (hright : rightEdge ∈ orbitFaceBoundary web.annular.RS right)
    (hadj : web.annular.RS.edgeAdjacencyGraph.Adj leftEdge rightEdge) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩ := by
  let RS := web.annular.RS
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨hedgesNe, vertex, hleftVertex, hrightVertex⟩
  have hleftIncident : leftEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hleftVertex
  have hrightIncident : rightEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hrightVertex
  have hleftGraphIncident : leftEdge ∈ incidentEdgeFinset G vertex := by
    have hmem : vertex ∈ (leftEdge.1 : Sym2 V) :=
      (GoertzelV24OrbitFaceCycleSpace.mem_toRotationSystem_incidentEdges_iff
        web.annular.cellulation.rotation vertex leftEdge).1 hleftIncident
    simpa [incidentEdgeFinset] using hmem
  have hrightGraphIncident : rightEdge ∈ incidentEdgeFinset G vertex := by
    have hmem : vertex ∈ (rightEdge.1 : Sym2 V) :=
      (GoertzelV24OrbitFaceCycleSpace.mem_toRotationSystem_incidentEdges_iff
        web.annular.cellulation.rotation vertex rightEdge).1 hrightIncident
    simpa [incidentEdgeFinset] using hmem
  have hnotInner : ∀ inner, vertex ≠ data.innerStub inner := by
    intro inner heq
    subst vertex
    rw [data.innerStub_incidentEdgeFinset_eq_singleton
      web.boundary_wellFormed inner] at hleftGraphIncident hrightGraphIncident
    have hleftEq := Finset.mem_singleton.mp hleftGraphIncident
    have hrightEq := Finset.mem_singleton.mp hrightGraphIncident
    exact hedgesNe (hleftEq.trans hrightEq.symm)
  have hnotOuter : ∀ outer, vertex ≠ data.outerStub outer := by
    intro outer heq
    subst vertex
    rw [data.outerStub_incidentEdgeFinset_eq_singleton
      web.boundary_wellFormed outer] at hleftGraphIncident hrightGraphIncident
    have hleftEq := Finset.mem_singleton.mp hleftGraphIncident
    have hrightEq := Finset.mem_singleton.mp hrightGraphIncident
    exact hedgesNe (hleftEq.trans hrightEq.symm)
  have hcard : (RS.dartsAt vertex).card = 3 := by
    rw [← RS.incidentEdges_card_eq_dartsAt_card]
    have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
      hnotInner hnotOuter
    have hincidentEq :
        RS.incidentEdges vertex = incidentEdgeFinset G vertex := by
      ext edge
      rw [GoertzelV24OrbitFaceCycleSpace.mem_toRotationSystem_incidentEdges_iff]
      simp [incidentEdgeFinset]
    rw [hincidentEq]
    exact hcubic
  rcases (RS.mem_incidentEdges_iff).1 hleftIncident with
    ⟨first, hfirstEdge, hfirstVertex⟩
  rcases (RS.mem_incidentEdges_iff).1 hrightIncident with
    ⟨second, hsecondEdge, hsecondVertex⟩
  have hbase : RS.vertOf second = RS.vertOf first :=
    hsecondVertex.trans hfirstVertex.symm
  have hdartsNe : first ≠ second := by
    intro hdarts
    apply hedgesNe
    exact hfirstEdge.symm.trans ((congrArg RS.edgeOf hdarts).trans hsecondEdge)
  have hleftDart : RS.edgeOf first ∈ orbitFaceBoundary RS left := by
    simpa only [hfirstEdge] using hleft
  have hrightDart : RS.edgeOf second ∈ orbitFaceBoundary RS right := by
    simpa only [hsecondEdge] using hright
  have hfirstCard : (RS.dartsAt (RS.vertOf first)).card = 3 := by
    simpa only [hfirstVertex] using hcard
  rcases RotationSystem.rho_eq_or_rho_eq_of_card_dartsAt_eq_three
      RS (Instance.InteriorFace.vertexRotationCyclic web)
      hfirstCard hbase hdartsNe with hforward | hbackward
  · exact interiorDualGraph_adj_of_consecutive_incident_darts
      RS (Instance.InteriorFace.vertexRotationCyclic web)
        hfirstCard hforward hfaces hleftDart hrightDart
  · have hsecondCard : (RS.dartsAt (RS.vertOf second)).card = 3 := by
      simpa only [hbase] using hfirstCard
    exact (interiorDualGraph_adj_of_consecutive_incident_darts
      RS (Instance.InteriorFace.vertexRotationCyclic web)
        hsecondCard hbackward hfaces.symm hrightDart hleftDart).symm

end

end GoertzelV24ClosedWebLocalFaceBoundaryAdjacency

end Mettapedia.GraphTheory.FourColor
