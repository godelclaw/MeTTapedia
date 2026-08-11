import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Adjacent primal edges force adjacent incident faces in a cubic map

At a cubic cyclic vertex, two distinct incident edges are consecutive in one
of the two directions.  Hence any distinct quotient faces containing those
edges either already share one of them or share the third edge at the corner.

This is generic local rotation-system theory.  It is kept in the light
corridor import layer so open-tangle arguments do not depend on the
closed-cubic collar stack.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CubicFaceBoundaryAdjacency

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- In a cyclic cubic dart fiber, either of two distinct darts is the
immediate successor of the other. -/
theorem rho_eq_or_rho_eq_of_isCubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second : RS.D}
    (hbase : RS.vertOf second = RS.vertOf first)
    (hne : first ≠ second) :
    RS.rho first = second ∨ RS.rho second = first := by
  by_cases hforward : RS.rho first = second
  · exact Or.inl hforward
  · right
    let vertex := RS.vertOf first
    have hfirstMem : first ∈ RS.dartsAt vertex := by
      simp [RotationSystem.dartsAt, vertex]
    have hnontrivialFinset : (RS.dartsAt vertex).Nontrivial := by
      apply Finset.one_lt_card_iff_nontrivial.mp
      rw [hcubic vertex]
      omega
    have hnontrivial : (RS.dartsAt vertex : Set RS.D).Nontrivial := by
      simpa only [Finset.coe_sort_coe] using hnontrivialFinset
    have hfirstRho : first ≠ RS.rho first := by
      exact ((rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
        hnontrivial hfirstMem).symm
    have hrhoMem : RS.rho first ∈ RS.dartsAt vertex := by
      simp [RotationSystem.dartsAt, vertex, RS.vert_rho]
    have hsecondMem : second ∈ RS.dartsAt vertex := by
      simp [RotationSystem.dartsAt, vertex, hbase]
    have htripleSubset : ({first, RS.rho first, second} : Finset RS.D) ⊆
        RS.dartsAt vertex := by
      intro dart hdart
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
      rcases hdart with rfl | rfl | rfl
      · exact hfirstMem
      · exact hrhoMem
      · exact hsecondMem
    have htripleCard : ({first, RS.rho first, second} : Finset RS.D).card = 3 := by
      simp [hfirstRho, hne, hforward]
    have htripleEq : ({first, RS.rho first, second} : Finset RS.D) =
        RS.dartsAt vertex := by
      apply Finset.eq_of_subset_of_card_le htripleSubset
      rw [hcubic vertex, htripleCard]
    have hrhoSecondMem : RS.rho second ∈ RS.dartsAt vertex := by
      simp [RotationSystem.dartsAt, vertex, RS.vert_rho, hbase]
    rw [← htripleEq] at hrhoSecondMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrhoSecondMem
    rcases hrhoSecondMem with hback | hcollision | hfixed
    · exact hback
    · exact (hne (RS.rho.injective hcollision.symm)).elim
    · exact (((rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
        hnontrivial hsecondMem) hfixed).elim

/-- If the darts of two distinct incident edges occur consecutively around a
cubic vertex, then any distinct faces containing the two edges are adjacent
in the full facial dual. -/
private theorem interiorDualGraph_adj_of_consecutive_incident_darts
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {first second : RS.D}
    (hforward : RS.rho first = second)
    {left right : OrbitFace RS}
    (hfaces : left ≠ right)
    (hleft : RS.edgeOf first ∈ orbitFaceBoundary RS left)
    (hright : RS.edgeOf second ∈ orbitFaceBoundary RS right) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩ := by
  by_cases hleftOwn : dartOrbitFace RS first = left
  · by_cases hrightOwn : dartOrbitFace RS second = right
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
    · have hrightOpposite :
          dartOrbitFace RS (RS.alpha second) = right :=
        dartOrbitFace_alpha_eq_of_mem_other_face
          RS htwoSided second right hright hrightOwn
      have hphi : RS.phi (RS.alpha first) = second := by
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
      have hcorner := oppositeFaces_adjacent_at_cubic_corner
        RS hcubic hrotation (RS.alpha first) hcornerNe
      simpa only [hleftFace, hrightFace] using hcorner
  · have hleftOpposite : dartOrbitFace RS (RS.alpha first) = left :=
      dartOrbitFace_alpha_eq_of_mem_other_face
        RS htwoSided first left hleft hleftOwn
    have hleftMiddle : dartOrbitFace RS second = left := by
      rw [← hforward, ← dartOrbitFace_alpha_eq_dartOrbitFace_rho]
      exact hleftOpposite
    by_cases hrightOwn : dartOrbitFace RS second = right
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

/-- In a cubic cyclic two-sided rotation system, distinct quotient faces that
contain adjacent primal edges are adjacent in the full facial dual. -/
theorem interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {leftEdge rightEdge : E} {left right : OrbitFace RS}
    (hfaces : left ≠ right)
    (hleft : leftEdge ∈ orbitFaceBoundary RS left)
    (hright : rightEdge ∈ orbitFaceBoundary RS right)
    (hadj : RS.edgeAdjacencyGraph.Adj leftEdge rightEdge) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩ := by
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨hedgesNe, vertex, hleftVertex, hrightVertex⟩
  have hleftIncident : leftEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hleftVertex
  have hrightIncident : rightEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hrightVertex
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
  rcases rho_eq_or_rho_eq_of_isCubic RS hcubic hrotation hbase hdartsNe with
    hforward | hbackward
  · exact interiorDualGraph_adj_of_consecutive_incident_darts
      RS hcubic hrotation htwoSided hforward hfaces hleftDart hrightDart
  · exact (interiorDualGraph_adj_of_consecutive_incident_darts
      RS hcubic hrotation htwoSided hbackward hfaces.symm
        hrightDart hleftDart).symm

end

end GoertzelV24CubicFaceBoundaryAdjacency

end Mettapedia.GraphTheory.FourColor
