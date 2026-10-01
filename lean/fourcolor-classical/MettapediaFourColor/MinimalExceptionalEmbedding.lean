import MettapediaFourColor.ActualDualRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualTriangleClassification

/-!
# Collision elimination in the actual minimal facial dual

The established singleton-cut theorem puts the three crossed primal edges
of any dual triangle at one cubic vertex. The actual dual rotation therefore
makes that triangle facial. Applying this to the exceptional core's explicit
nonfacial collision alternative proves injectivity from the two retained
source occurrences. Inducedness, the outer ring and colouring repair are
separate obligations.
-/

namespace FourColor.MinimalExceptionalEmbedding

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections GoertzelV24TwoEdgeCutMinimality
open GoertzelV24MinimalDualTriangleClassification
open ExceptionalCoreOrientation ExceptionalOverlap ExceptionalCore

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

abbrev graph := ActualDualRotation.graph original.toRotationSystem minimal.facesTwoSided

abbrev rotation := ActualDualRotation.data original.toRotationSystem minimal.facesTwoSided
  (pairwiseUniqueSharedInteriorEdges original minimal)

local instance : (graph original minimal).LocallyFinite := fun _ => Fintype.ofFinite _

/-- The rotated dual has exactly the adjacency used by the coverage scaffold. -/
theorem graph_eq_coverage_dual : graph original minimal =
    GoertzelV24PrimalCycleFacialBond.orbitFaceDualGraph original := by
  ext a b
  exact ActualDualRotation.dual_adj_iff original.toRotationSystem minimal.facesTwoSided

theorem cyclic : (rotation original minimal).IsVertexwiseCyclic :=
  ActualDualRotation.cyclic _ _ _

theorem triangular : Triangular (rotation original minimal) :=
  ActualDualRotation.triangular _ _ _ minimal.spherical.cubic minimal.vertexRotationCyclic

/-- The existing three-edge separator is facial in the same actual rotation
used by the exceptional pattern, in one of its two orientations. -/
theorem triangle_facial {a b c : OrbitFace original.toRotationSystem}
    (ab : (graph original minimal).Adj a b)
    (bc : (graph original minimal).Adj b c)
    (ca : (graph original minimal).Adj c a) :
    Corner (rotation original minimal) a b c ∨
      Corner (rotation original minimal) a c b := by
  let RS := original.toRotationSystem
  let unique := pairwiseUniqueSharedInteriorEdges original minimal
  have hab := (ActualDualRotation.dual_adj_iff RS minimal.facesTwoSided).mp ab
  have hbc := (ActualDualRotation.dual_adj_iff RS minimal.facesTwoSided).mp bc
  have hca := (ActualDualRotation.dual_adj_iff RS minimal.facesTwoSided).mp ca
  let e := sharedInteriorEdgeOfAdjOfPairwiseUnique (orbitFaceBoundary RS)
    Finset.univ unique hab
  let f := sharedInteriorEdgeOfAdjOfPairwiseUnique (orbitFaceBoundary RS)
    Finset.univ unique hbc
  obtain ⟨v, he, hf, _⟩ :=
    exists_vertex_mem_three_shared_edges_of_dual_triangle original minimal hab hbc hca
  have ve : v ∈ RS.endpoints e :=
    (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      original e v).mpr he
  have vf : v ∈ RS.endpoints f :=
    (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      original f v).mpr hf
  obtain ⟨d, _, hd⟩ := RS.mem_endpoints_iff.mp ve
  have cubic := PhysicalForkCodeFaces.cubic3_of RS minimal.spherical.cubic
    minimal.vertexRotationCyclic
  have ha := ActualDualRotation.face_mem_vertex_triangle RS cubic d
    (hd.symm ▸ ve)
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
      (orbitFaceBoundary RS) Finset.univ unique hab)
  have hb := ActualDualRotation.face_mem_vertex_triangle RS cubic d
    (hd.symm ▸ ve)
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
      (orbitFaceBoundary RS) Finset.univ unique hab)
  have hc := ActualDualRotation.face_mem_vertex_triangle RS cubic d
    (hd.symm ▸ vf)
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
      (orbitFaceBoundary RS) Finset.univ unique hbc)
  apply ActualDualRotation.corner_of_three_members (rotation original minimal)
    (triangular original minimal)
    (ActualDualRotation.corner_at_vertex RS minimal.facesTwoSided unique
      minimal.spherical.cubic minimal.vertexRotationCyclic d)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      exact ha.imp_right Or.symm)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
      exact hb.imp_right Or.symm)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc ⊢
      exact hc.imp_right Or.symm)
    ab.ne bc.ne ca.ne

/-- The retained joint reading is injective in a graph-backed minimal Tait
counterexample. No global Four Colour theorem is used to eliminate collisions. -/
theorem joint_injective (r : JointReading (rotation original minimal)) :
    Function.Injective r.core.map := by
  classical
  apply ExceptionalCoreCollision.injective_of_local_triangles_facial r
    (triangular original minimal) (cyclic original minimal)
  intro a b c hab hbc hca
  exact triangle_facial original minimal hab hbc hca

/-- Two aligned actual occurrences construct the joint witness consumed by
the collision theorem; injectivity is not supplied as an extra field. -/
theorem source_core_injective
    (x y : ExceptionalPattern.Occurrence (rotation original minimal))
    (aligned : y.vertex 0 = x.vertex 14) :
    Function.Injective (coreHom x (triangular original minimal)) := by
  classical
  exact joint_injective original minimal
    (jointReading x (triangular original minimal) (cyclic original minimal) y aligned)

end
end FourColor.MinimalExceptionalEmbedding
