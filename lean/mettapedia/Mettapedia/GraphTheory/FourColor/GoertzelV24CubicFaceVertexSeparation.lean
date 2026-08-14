import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport

/-!
# Cubic face separation survives a literal cap opening

In a cubic cyclic two-sided rotation system, two distinct facial cycles that
meet at a primal vertex are adjacent in the full facial dual.  Consequently a
face that is distinct and dual-nonadjacent to a deleted cap face contains no
cap vertex and is fully retained by the corresponding literal opening.

This is generic local geometry for the source's L1 formation step.  It does
not construct the pentagonal cap or the long separated crosscuts; it turns a
future boundary-cleanliness theorem into the exact `FaceFullyRetained` premise
used by the literal-open face and corner transport layer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CubicFaceVertexSeparation

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The primal vertices visited by a quotient facial cycle. -/
def orbitFaceVertices (RS : RotationSystem V E) (face : OrbitFace RS) :
    Finset V :=
  (orbitFaceDarts RS face).image RS.vertOf

theorem mem_orbitFaceVertices_iff
    (RS : RotationSystem V E) (face : OrbitFace RS) (vertex : V) :
    vertex ∈ orbitFaceVertices RS face ↔
      ∃ dart ∈ orbitFaceDarts RS face, RS.vertOf dart = vertex := by
  simp [orbitFaceVertices]

/-- Distinct quotient faces meeting at a primal vertex are adjacent in the
full facial dual of a cubic cyclic two-sided rotation system. -/
theorem interiorDualGraph_adj_of_distinct_faces_share_vertex
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {left right : OrbitFace RS}
    (hfaces : left ≠ right)
    {leftDart rightDart : RS.D}
    (hleft : leftDart ∈ orbitFaceDarts RS left)
    (hright : rightDart ∈ orbitFaceDarts RS right)
    (hvertex : RS.vertOf leftDart = RS.vertOf rightDart) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩ := by
  have hleftEdge : RS.edgeOf leftDart ∈ orbitFaceBoundary RS left := by
    rw [mem_orbitFaceBoundary_iff]
    exact ⟨leftDart, hleft, rfl⟩
  have hrightEdge : RS.edgeOf rightDart ∈ orbitFaceBoundary RS right := by
    rw [mem_orbitFaceBoundary_iff]
    exact ⟨rightDart, hright, rfl⟩
  by_cases hedges : RS.edgeOf leftDart = RS.edgeOf rightDart
  · have hrightEdge' : RS.edgeOf leftDart ∈ orbitFaceBoundary RS right := by
      rw [hedges]
      exact hrightEdge
    exact
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_incidence_le_two RS)
        (f := ⟨left, Finset.mem_univ _⟩)
        (g := ⟨right, Finset.mem_univ _⟩)
        (e := RS.edgeOf leftDart) hfaces hleftEdge hrightEdge'
  · have hadj : RS.edgeAdjacencyGraph.Adj
        (RS.edgeOf leftDart) (RS.edgeOf rightDart) := by
      apply (RS.edgeAdjacencyGraph_adj_iff).2
      refine ⟨hedges, RS.vertOf leftDart, ?_, ?_⟩
      · apply (RS.mem_endpoints_iff_mem_incidentEdges).2
        exact (RS.mem_incidentEdges_iff).2 ⟨leftDart, rfl, rfl⟩
      · apply (RS.mem_endpoints_iff_mem_incidentEdges).2
        exact (RS.mem_incidentEdges_iff).2
          ⟨rightDart, rfl, hvertex.symm⟩
    exact interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
      RS hcubic hrotation htwoSided hfaces hleftEdge hrightEdge hadj

/-- Two distinct dual-nonadjacent facial cycles have disjoint primal vertex
supports. -/
theorem orbitFaceVertices_disjoint_of_not_adj
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {left right : OrbitFace RS}
    (hfaces : left ≠ right)
    (hnotAdj : ¬ (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨left, Finset.mem_univ _⟩ ⟨right, Finset.mem_univ _⟩) :
    Disjoint (orbitFaceVertices RS left) (orbitFaceVertices RS right) := by
  rw [Finset.disjoint_left]
  intro vertex hleftVertex hrightVertex
  rcases (mem_orbitFaceVertices_iff RS left vertex).1 hleftVertex with
    ⟨leftDart, hleftDart, hleftVert⟩
  rcases (mem_orbitFaceVertices_iff RS right vertex).1 hrightVertex with
    ⟨rightDart, hrightDart, hrightVert⟩
  apply hnotAdj
  exact interiorDualGraph_adj_of_distinct_faces_share_vertex
    RS hcubic hrotation htwoSided hfaces hleftDart hrightDart
      (hleftVert.trans hrightVert.symm)

/-- Deleting precisely the vertices of one cap face fully retains every
distinct dual-nonadjacent face.  This is the cap-opening premise needed by
the literal-open L1 face-transport layer. -/
theorem faceFullyRetained_compl_orbitFaceVertices_of_not_adj
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (capRoot faceRoot : RS.D)
    (hfaces : dartOrbitFace RS faceRoot ≠ dartOrbitFace RS capRoot)
    (hnotAdj : ¬ (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨dartOrbitFace RS faceRoot, Finset.mem_univ _⟩
        ⟨dartOrbitFace RS capRoot, Finset.mem_univ _⟩) :
    FaceFullyRetained RS
      (fun vertex => vertex ∉ orbitFaceVertices RS (dartOrbitFace RS capRoot))
      faceRoot := by
  have hdisjoint := orbitFaceVertices_disjoint_of_not_adj
    RS hcubic hrotation htwoSided hfaces hnotAdj
  intro point hpoint
  have hpointFace : point ∈
      orbitFaceDarts RS (dartOrbitFace RS faceRoot) := by
    rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit, RS.mem_faceOrbit]
    exact hpoint
  have hpointVertex : RS.vertOf point ∈
      orbitFaceVertices RS (dartOrbitFace RS faceRoot) := by
    exact (mem_orbitFaceVertices_iff RS _ _).2 ⟨point, hpointFace, rfl⟩
  exact Finset.disjoint_left.mp hdisjoint hpointVertex

/-- Deleting two displayed facial vertex supports still fully retains a face
that is distinct and dual-nonadjacent to each of them.  This is the exact
two-boundary retention premise needed by a future literal two-cap formation:
it is only a local consequence of the two supplied separation facts, and does
not select cap faces or construct an annular opening. -/
theorem faceFullyRetained_compl_union_orbitFaceVertices_of_not_adj
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (firstCapRoot secondCapRoot faceRoot : RS.D)
    (hfirstFaces : dartOrbitFace RS faceRoot ≠ dartOrbitFace RS firstCapRoot)
    (hfirstNotAdj : ¬ (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨dartOrbitFace RS faceRoot, Finset.mem_univ _⟩
        ⟨dartOrbitFace RS firstCapRoot, Finset.mem_univ _⟩)
    (hsecondFaces : dartOrbitFace RS faceRoot ≠ dartOrbitFace RS secondCapRoot)
    (hsecondNotAdj : ¬ (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        ⟨dartOrbitFace RS faceRoot, Finset.mem_univ _⟩
        ⟨dartOrbitFace RS secondCapRoot, Finset.mem_univ _⟩) :
    FaceFullyRetained RS
      (fun vertex => vertex ∉ orbitFaceVertices RS (dartOrbitFace RS firstCapRoot) ∪
        orbitFaceVertices RS (dartOrbitFace RS secondCapRoot))
      faceRoot := by
  intro point hpoint
  have hfirst := faceFullyRetained_compl_orbitFaceVertices_of_not_adj
    RS hcubic hrotation htwoSided firstCapRoot faceRoot hfirstFaces hfirstNotAdj
  have hsecond := faceFullyRetained_compl_orbitFaceVertices_of_not_adj
    RS hcubic hrotation htwoSided secondCapRoot faceRoot hsecondFaces hsecondNotAdj
  simp only [Finset.mem_union, not_or]
  exact ⟨hfirst point hpoint, hsecond point hpoint⟩

end

end GoertzelV24CubicFaceVertexSeparation

end Mettapedia.GraphTheory.FourColor
