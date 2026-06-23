import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mettapedia.GraphTheory.FourColor.FaceIncidence
import Mettapedia.GraphTheory.FourColor.RotationDiskData

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

namespace RotationSystem

variable (RS : RotationSystem V E)

theorem totalIncidenceCount_internalFaces_eq_facesIncidence_card (e : E) :
    totalIncidenceCount (fun f : Finset E => f) RS.internalFaces e =
      (RS.facesIncidence e).card := by
  rfl

/-- The rotation-system face incidence theorem in the generic
`FaceIncidence.totalIncidenceCount` vocabulary used by Theorem49 modules. -/
theorem totalIncidenceCount_internalFaces_le_two (e : E) :
    totalIncidenceCount (fun f : Finset E => f) RS.internalFaces e ≤ 2 := by
  rw [RS.totalIncidenceCount_internalFaces_eq_facesIncidence_card e]
  exact RS.facesIncidence_card_le_two e

theorem mem_interiorEdgeSupport_internalFaces_iff {e : E} :
    e ∈ interiorEdgeSupport (fun f : Finset E => f) RS.internalFaces ↔
      e ∈ RS.internalFaces.biUnion (fun f : Finset E => f) ∧
        (RS.facesIncidence e).card = 2 := by
  rw [mem_interiorEdgeSupport_iff]
  simp [RS.totalIncidenceCount_internalFaces_eq_facesIncidence_card e]

theorem totalIncidenceCount_internalFaces_eq_two_of_interiorFacePlanarity
    (P : RS.InteriorFacePlanarity) {e : E}
    (heInterior : e ∉ RS.boundaryEdges) {d : RS.D} (hd : RS.edgeOf d = e) :
    totalIncidenceCount (fun f : Finset E => f) RS.internalFaces e = 2 := by
  rw [RS.totalIncidenceCount_internalFaces_eq_facesIncidence_card e]
  exact RS.facesIncidence_card_eq_two_of_interiorFacePlanarity P heInterior hd

theorem mem_interiorEdgeSupport_internalFaces_of_interiorFacePlanarity
    (P : RS.InteriorFacePlanarity) {e : E} (heInterior : e ∉ RS.boundaryEdges) :
    e ∈ interiorEdgeSupport (fun f : Finset E => f) RS.internalFaces := by
  rcases RS.dartsOn_nonempty e with ⟨d, hdmem⟩
  have hd : RS.edgeOf d = e := (RS.mem_dartsOn).1 hdmem
  refine (RS.mem_interiorEdgeSupport_internalFaces_iff).2 ?_
  constructor
  · rcases RS.interior_edge_covered heInterior with ⟨f, hf, hef⟩
    exact Finset.mem_biUnion.2 ⟨f, hf, hef⟩
  · exact RS.facesIncidence_card_eq_two_of_interiorFacePlanarity P heInterior hd

namespace PlanarGeometry

variable (PG : PlanarGeometry V E)

theorem totalIncidenceCount_internalFaces_eq_two_of_interior_edge {e : E}
    (heInterior : e ∉ PG.toRotationSystem.boundaryEdges) :
    totalIncidenceCount (fun f : Finset E => f) PG.toRotationSystem.internalFaces e = 2 := by
  rw [PG.toRotationSystem.totalIncidenceCount_internalFaces_eq_facesIncidence_card e]
  exact PG.facesIncidence_card_eq_two_of_interior_edge heInterior

theorem mem_interiorEdgeSupport_internalFaces_of_interior_edge {e : E}
    (heInterior : e ∉ PG.toRotationSystem.boundaryEdges) :
    e ∈ interiorEdgeSupport (fun f : Finset E => f) PG.toRotationSystem.internalFaces :=
  PG.toRotationSystem.mem_interiorEdgeSupport_internalFaces_of_interiorFacePlanarity
    PG.toInteriorFacePlanarity heInterior

/-- Generic `FaceIncidence` witness extracted from a non-boundary edge of a
planar rotation geometry.  This is the modern, explicit-hypothesis version of
the old `interior_edge_two_internal_faces` route. -/
noncomputable def interiorEdgeFacePairOfInteriorEdge {e : E}
    (heInterior : e ∉ PG.toRotationSystem.boundaryEdges) :
    InteriorEdgeFacePair (fun f : Finset E => f) PG.toRotationSystem.internalFaces e :=
  interiorEdgeFacePairOfMem (fun f : Finset E => f) PG.toRotationSystem.internalFaces
    (PG.mem_interiorEdgeSupport_internalFaces_of_interior_edge heInterior)

theorem interiorEdgeFacePairOfInteriorEdge_interiorDualGraph_adj {e : E}
    (heInterior : e ∉ PG.toRotationSystem.boundaryEdges) :
    (interiorDualGraph (fun f : Finset E => f) PG.toRotationSystem.internalFaces).Adj
      (PG.interiorEdgeFacePairOfInteriorEdge heInterior).left
      (PG.interiorEdgeFacePairOfInteriorEdge heInterior).right :=
  (PG.interiorEdgeFacePairOfInteriorEdge heInterior).interiorDualGraph_adj

end PlanarGeometry

/-- Under explicit modern planarity-style hypotheses, the darts where a face
orbit toggles membership at `v` are in bijection with the edges of that face
incident to `v`. This is the honest modern replacement for the old
`PlanarGeometry`-based `toggles_biject_edges_internal`. -/
theorem togglesOn_card_eq_incidentEdges_inter_faceEdges
    (hboundary :
      ∀ {e : E} {d : RS.D}, RS.edgeOf d = e → e ∈ RS.boundaryEdges →
        RS.faceEdges d = RS.boundaryEdges)
    (halpha :
      ∀ {d : RS.D}, RS.edgeOf d ∉ RS.boundaryEdges →
        RS.faceEdges (RS.alpha d) ≠ RS.faceEdges d)
    (d₀ : RS.D) (v : V)
    (hInternal : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    (RS.togglesOn v d₀).card =
      (RS.incidentEdges v ∩ RS.faceEdges d₀).card := by
  classical
  refine Finset.card_bij
    (fun d _hd => RS.edgeOf d)
    ?mem ?inj ?surj
  · intro d hd
    have hd' := (RS.mem_togglesOn_iff).1 hd
    have hdOrbit : d ∈ RS.faceOrbit d₀ := hd'.1
    have htoggle : decide (RS.vertOf d = v) ≠
        decide (RS.vertOf (RS.phi d) = v) := hd'.2
    have hface : RS.edgeOf d ∈ RS.faceEdges d₀ :=
      (RS.mem_faceEdges_iff).2 ⟨d, hdOrbit, rfl⟩
    have hVertex :
        (RS.vertOf d = v ∧ RS.vertOf (RS.phi d) ≠ v) ∨
          (RS.vertOf d ≠ v ∧ RS.vertOf (RS.phi d) = v) := by
      by_cases h₁ : RS.vertOf d = v
      · by_cases h₂raw : RS.vertOf (RS.rho (RS.alpha d)) = v
        · exfalso
          exact htoggle (by simp [RotationSystem.phi_apply, h₁, h₂raw])
        · have h₂ : RS.vertOf (RS.phi d) ≠ v := by
            intro h
            exact h₂raw (by simpa [RotationSystem.phi_apply] using h)
          exact Or.inl ⟨h₁, h₂⟩
      · by_cases h₂raw : RS.vertOf (RS.rho (RS.alpha d)) = v
        · have h₂ : RS.vertOf (RS.phi d) = v := by
            simpa [RotationSystem.phi_apply] using h₂raw
          exact Or.inr ⟨h₁, h₂⟩
        · exfalso
          exact htoggle (by simp [RotationSystem.phi_apply, h₁, h₂raw])
    have hIncident : RS.edgeOf d ∈ RS.incidentEdges v := by
      rcases hVertex with ⟨hv, _hvphi⟩ | ⟨_hvd, hvphi⟩
      · exact (RS.mem_incidentEdges_iff).2 ⟨d, rfl, hv⟩
      · have hvalpha : RS.vertOf (RS.alpha d) = v := by
          rw [← RS.vert_phi_eq_vert_alpha d]
          exact hvphi
        exact (RS.mem_incidentEdges_iff).2
          ⟨RS.alpha d, RS.edge_alpha d, hvalpha⟩
    exact Finset.mem_inter.2 ⟨hIncident, hface⟩
  · intro d₁ hd₁ d₂ hd₂ hEdge
    have hd₁' := (RS.mem_togglesOn_iff).1 hd₁
    have hd₂' := (RS.mem_togglesOn_iff).1 hd₂
    have hdOrbit₁ : d₁ ∈ RS.faceOrbit d₀ := hd₁'.1
    have hdOrbit₂ : d₂ ∈ RS.faceOrbit d₀ := hd₂'.1
    have hedgeFace : RS.edgeOf d₁ ∈ RS.faceEdges d₀ :=
      (RS.mem_faceEdges_iff).2 ⟨d₁, hdOrbit₁, rfl⟩
    have hInterior : RS.edgeOf d₁ ∉ RS.boundaryEdges :=
      RS.edge_of_internal_face_not_boundary hboundary hedgeFace hInternal
    have halphaNot :
        RS.alpha d₁ ∉ RS.faceOrbit d₀ :=
      RS.alpha_not_mem_faceOrbit_of_interior halpha hInterior hdOrbit₁
    have hcases := RS.edge_fiber_two_cases
      (e := RS.edgeOf d₁) (d := d₁) (y := d₂) rfl (by simp [hEdge])
    rcases hcases with h | h
    · exact h.symm
    · have : RS.alpha d₁ ∈ RS.faceOrbit d₀ := by
        rw [← h]
        exact hdOrbit₂
      exact (halphaNot this).elim
  · intro e he
    have hIncident : e ∈ RS.incidentEdges v := (Finset.mem_inter.1 he).1
    have hFace : e ∈ RS.faceEdges d₀ := (Finset.mem_inter.1 he).2
    rcases (RS.mem_faceEdges_iff).1 hFace with ⟨d, hdOrbit, hde⟩
    rcases (RS.mem_incidentEdges_iff).1 hIncident with ⟨d', hd'e, hv'⟩
    have hcases := RS.edge_fiber_two_cases
      (e := RS.edgeOf d) (d := d) (y := d') rfl (by rw [hde, ← hd'e])
    rcases hcases with hEq | hAlpha
    · have hvd : RS.vertOf d = v := by
        rw [← hEq]
        exact hv'
      have hnotPhi : RS.vertOf (RS.phi d) ≠ v := by
        intro hvphi
        have hvalpha : RS.vertOf (RS.alpha d) = v := by
          rw [← RS.vert_phi_eq_vert_alpha d]
          exact hvphi
        exact RS.no_self_loops d (hvd.trans hvalpha.symm)
      have hnotRhoAlpha : RS.vertOf (RS.rho (RS.alpha d)) ≠ v := by
        intro h
        exact hnotPhi (by simpa [RotationSystem.phi_apply] using h)
      refine ⟨d, ?_, hde⟩
      exact (RS.mem_togglesOn_iff).2
        ⟨hdOrbit, by simp [RotationSystem.phi_apply, hvd, hnotRhoAlpha]⟩
    · have hvalpha : RS.vertOf (RS.alpha d) = v := by
        rw [← hAlpha]
        exact hv'
      have hvphi : RS.vertOf (RS.phi d) = v := by
        rw [RS.vert_phi_eq_vert_alpha d]
        exact hvalpha
      have hvRhoAlpha : RS.vertOf (RS.rho (RS.alpha d)) = v := by
        simpa [RotationSystem.phi_apply] using hvphi
      have hnotD : RS.vertOf d ≠ v := by
        intro hvd
        exact RS.no_self_loops d (hvd.trans hvalpha.symm)
      refine ⟨d, ?_, hde⟩
      exact (RS.mem_togglesOn_iff).2
        ⟨hdOrbit, by simp [RotationSystem.phi_apply, hnotD, hvRhoAlpha]⟩

theorem incidentEdges_inter_faceEdges_card_even
    (hboundary :
      ∀ {e : E} {d : RS.D}, RS.edgeOf d = e → e ∈ RS.boundaryEdges →
        RS.faceEdges d = RS.boundaryEdges)
    (halpha :
      ∀ {d : RS.D}, RS.edgeOf d ∉ RS.boundaryEdges →
        RS.faceEdges (RS.alpha d) ≠ RS.faceEdges d)
    (d₀ : RS.D) (v : V)
    (hInternal : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    Even ((RS.incidentEdges v ∩ RS.faceEdges d₀).card) := by
  rw [← RS.togglesOn_card_eq_incidentEdges_inter_faceEdges
    hboundary halpha d₀ v hInternal]
  exact RS.togglesOn_card_even d₀ v

theorem togglesOn_card_eq_incidentEdges_inter_faceEdges_of_interiorFacePlanarity
    (P : RS.InteriorFacePlanarity) (d₀ : RS.D) (v : V)
    (hInternal : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    (RS.togglesOn v d₀).card =
      (RS.incidentEdges v ∩ RS.faceEdges d₀).card :=
  RS.togglesOn_card_eq_incidentEdges_inter_faceEdges
    P.boundary_edge_both_outer P.alpha_interior_distinct_faces d₀ v hInternal

theorem incidentEdges_inter_faceEdges_card_even_of_interiorFacePlanarity
    (P : RS.InteriorFacePlanarity) (d₀ : RS.D) (v : V)
    (hInternal : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    Even ((RS.incidentEdges v ∩ RS.faceEdges d₀).card) :=
  RS.incidentEdges_inter_faceEdges_card_even
    P.boundary_edge_both_outer P.alpha_interior_distinct_faces d₀ v hInternal

theorem incidentEdges_inter_internalFace_card_even
    (P : RS.InteriorFacePlanarity) {f : Finset E}
    (hf : f ∈ RS.internalFaces) (v : V) :
    Even ((RS.incidentEdges v ∩ f).card) := by
  rcases RS.face_witness_of_mem_internalFaces hf with ⟨d₀, hd₀⟩
  have hInternal : RS.faceEdges d₀ ≠ RS.boundaryEdges := by
    rw [hd₀]
    exact RS.ne_boundaryEdges_of_mem_internalFaces hf
  simpa [hd₀] using
    RS.incidentEdges_inter_faceEdges_card_even_of_interiorFacePlanarity
      P d₀ v hInternal

end RotationSystem

namespace RotationDiskData

variable (G : RotationDiskData V E)

theorem face_cycle_parity_of_interiorFacePlanarity
    (P : G.rotation.InteriorFacePlanarity)
    {f : Finset E} (hf : f ∈ G.rotation.internalFaces) (v : V) :
    Even ((G.asZeroBoundary.incident v ∩ f).card) := by
  rw [G.asZeroBoundary_incident_eq_rotation_incidentEdges v]
  exact G.rotation.incidentEdges_inter_internalFace_card_even P hf v

/-- Degree of a vertex inside a finite face boundary. -/
def faceDeg (face : Finset E) (v : V) : Nat :=
  (G.asZeroBoundary.incident v ∩ face).card

theorem faceDeg_eq_card_bipartiteAbove (face : Finset E) (v : V) :
    G.faceDeg face v =
      (face.bipartiteAbove (fun v e => e ∈ G.asZeroBoundary.incident v) v).card := by
  have hset :
      G.asZeroBoundary.incident v ∩ face =
        face.bipartiteAbove (fun v e => e ∈ G.asZeroBoundary.incident v) v := by
    ext e
    simp [Finset.mem_bipartiteAbove, Finset.mem_inter, and_comm]
  simp [faceDeg, hset]

theorem bipartiteBelow_incident_eq_edgeEndpoints (e : E) :
    (Finset.univ : Finset V).bipartiteBelow
        (fun v e => e ∈ G.asZeroBoundary.incident v) e =
      G.edgeEndpoints e := by
  ext v
  simp [Finset.mem_bipartiteBelow, G.mem_edgeEndpoints_iff]

theorem card_bipartiteBelow_incident_eq_two (e : E) :
    ((Finset.univ : Finset V).bipartiteBelow
        (fun v e => e ∈ G.asZeroBoundary.incident v) e).card = 2 := by
  rw [G.bipartiteBelow_incident_eq_edgeEndpoints e]
  exact G.edgeEndpoints_card_two e

/-- Handshake for a finite face boundary: summing the within-face incidence
degrees over all vertices counts each face edge twice. -/
theorem sum_faceDeg_eq_two_card (face : Finset E) :
    (∑ v : V, G.faceDeg face v) = 2 * face.card := by
  classical
  let r : V → E → Prop := fun v e => e ∈ G.asZeroBoundary.incident v
  calc
    (∑ v : V, G.faceDeg face v)
        = (Finset.univ : Finset V).sum
            (fun v => (face.bipartiteAbove r v).card) := by
            refine Finset.sum_congr rfl ?_
            intro v _hv
            exact G.faceDeg_eq_card_bipartiteAbove face v
    _ = face.sum
            (fun e => ((Finset.univ : Finset V).bipartiteBelow r e).card) := by
            simpa [r] using
              (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
                (r := r) (s := (Finset.univ : Finset V)) (t := face))
    _ = face.sum (fun _e => (2 : Nat)) := by
            refine Finset.sum_congr rfl ?_
            intro e _he
            exact G.card_bipartiteBelow_incident_eq_two e
    _ = 2 * face.card := by
            simp [Finset.sum_const, Nat.mul_comm]

end RotationDiskData

end Mettapedia.GraphTheory.FourColor
