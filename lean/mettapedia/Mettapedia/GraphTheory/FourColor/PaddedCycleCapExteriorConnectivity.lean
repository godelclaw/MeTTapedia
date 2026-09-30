import Mettapedia.GraphTheory.FourColor.PaddedCycleCapRecognition
import Mettapedia.GraphTheory.FourColor.Compositional.ShortFaceBoundaryConnectivity

/-!
# The face-traced cap has connected exterior

Complete cap stars and short seam faces connect the outside port endpoints.
Ambient connectedness then gives connectedness of the whole exterior. The
actual strict reduction therefore needs no separate exterior hypothesis.
Vertex injectivity remains an explicit local geometric condition.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal

open Equiv Equiv.Perm PhysicalForkCodeFaces
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open SerialTangleSmallCutTransfer GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSideOpenTangle GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphFaceDualConnectedness
open OpenTangleClosedWitness

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (m : ℕ) [NeZero m] (hm : 2 ≤ m) (root : RS.D)
  (hC : Cubic3 RS) (hf : FaceLengths RS m root)
  (hv : Function.Injective (vertex RS m root))

include hC in
/-- Rotating a boundary port enters an actual internal cap edge. -/
theorem port_rotated_mate_mem (j : Fin (m*2)) :
    RS.vertOf (RS.alpha (RS.rho (port RS m root j))) ∈ deleted RS m root := by
  obtain ⟨⟨i,b⟩,rfl⟩ := (portIndex m).surjective j
  cases b
  · apply (mem_deleted_iff RS m root _).mpr
    refine ⟨(i,4), ?_⟩
    simp [vertex, base, port, boundary_dart_false RS m root, hC.cube,
      outerFirst, RS.alpha_involutive, RS.vert_rho]
  · apply (mem_deleted_iff RS m root _).mpr
    refine ⟨(i,6), ?_⟩
    simp [vertex, base, port, boundary_dart_true RS m root, hC.cube,
      outerLast, RS.alpha_involutive, RS.vert_rho]

include hm hC hf hv in
/-- Exhaustive retained-dart coordinates classify every actual outgoing
edge, without assuming an occurrence isomorphism or exterior connectivity. -/
theorem outgoing_is_port (d : RS.D)
    (hin : RS.vertOf d ∈ deleted RS m root)
    (hout : RS.vertOf (RS.alpha d) ∉ deleted RS m root) :
    ∃ j, port RS m root j = d := by
  have hkeep : deletedSideKeep (deleted RS m root) (RS.vertOf d) := by
    simpa [deletedSideKeep, deletedRegionKeep] using hin
  obtain ⟨p,hp⟩ := (darts RS m hm root hC hv).surjective ⟨d,hkeep⟩
  have he : ambient RS m root p = d := congrArg Subtype.val hp
  rcases p with i | (e | j)
  · exfalso
    apply hout
    have hh := (retained RS m hm root
      (.inl ((asOpen (indexedCap m hm)).interiorAlpha i))).2
    change deletedSideKeep (deleted RS m root) (RS.vertOf (ambient RS m root _)) at hh
    rw [ambient_alpha RS m hm root hC hf, he] at hh
    simpa [deletedSideKeep, deletedRegionKeep] using hh
  · exact nomatch e
  · exact ⟨j,he⟩

end

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G)

local instance capExteriorEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance capExteriorEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)
  (root : rotation.toRotationSystem.D) (hC : Cubic3 rotation.toRotationSystem)
  (hf : FaceLengths rotation.toRotationSystem m root)
  (hv : Function.Injective (vertex rotation.toRotationSystem m root))
  (hs : BoundaryShortFaces rotation.toRotationSystem m root)

include hm hC hf hv hs in
/-- The stated face trace and short seam faces derive connected exterior
at every width. No colouring or cyclic-connectivity hypothesis is used. -/
theorem face_traced_exterior_connected (hconnected : G.Connected) :
    (G.induce {v | deletedRegionKeep (deleted rotation.toRotationSystem m root) v}).Connected := by
  let RS := rotation.toRotationSystem
  exact Compositional.ShortFaceBoundaryConnectivity.exterior_connected rotation
    (fun v => v ∈ deleted RS m root) (port RS m root)
    (port_not_deleted RS m root hC hf hv hs)
    (fun d hin hout => outgoing_is_port RS m hm root hC hf hv d hin hout)
    (port_rotated_mate_mem RS m root hC)
    (port_arc RS m root hC hf) hs hconnected

/-- The literal smaller map retains the actual complementary shore and
uses the boundary matching derived from the face-traced representation. -/
def reducedSystem :=
  sewn (ofVertexSide rotation.toRotationSystem
    (deletedRegionKeep (deleted rotation.toRotationSystem m root))
    (outsideRoot rotation.toRotationSystem m root hC hf hv hs))
    (CycleCap.cap (m*2) (by omega))
    ((complementBoundaryAlphaEquiv rotation.toRotationSystem
      (deleted rotation.toRotationSystem m root)).trans
      (recognition rotation.toRotationSystem m hm root hC hf hv hs).symm.boundary)

include hv in
omit [NeZero m] in
/-- Count the whole map, including every replacement vertex. -/
theorem face_traced_vertex_count :
    Fintype.card V = Fintype.card ({v : V // deletedRegionKeep
      (deleted rotation.toRotationSystem m root) v} ⊕ Fin (m*2)) + 6*m := by
  have hk := Fintype.card_congr (vertices rotation.toRotationSystem m root hv)
  have hc := Fintype.card_congr
    (GoertzelV24VertexSideReassembly.complementaryVertexEquiv
      (deleted rotation.toRotationSystem m root))
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin] at hk
  simp only [Fintype.card_sum, Fintype.card_fin] at hc ⊢
  omega

include hC hf hv hs in
/-- The whole-map strict reduction and genuine colouring reconstruction
now consume derived exterior connectivity. Only vertex separation remains
as an additional local geometric condition on the face pattern. -/
theorem face_traced_strict_reduction
    (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem) :
    Fintype.card ({v : V // deletedRegionKeep
      (deleted rotation.toRotationSystem m root) v} ⊕ Fin (m*2)) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (reducedSystem rotation m hm root hC hf hv hs) ∧
      (RotationSystemTaitColorable (reducedSystem rotation m hm root hC hf hv hs) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  exact recognized_cap_strict_reduction m hm rotation
    (deleted rotation.toRotationSystem m root)
    (outsideRoot rotation.toRotationSystem m root hC hf hv hs)
    (insideRoot rotation.toRotationSystem m hm root)
    (recognition rotation.toRotationSystem m hm root hC hf hv hs).symm h htwo
    (face_traced_exterior_connected rotation m hm root hC hf hv hs hg)

include hm hf hv hs in
/-- The strengthened face-pattern consumer assumes no exterior
connectivity: the same actual seam geometry proves it. -/
theorem no_face_traced_cap_of_short_faces
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  let hC := cubic3_of rotation.toRotationSystem minimal.spherical.cubic
    minimal.vertexRotationCyclic
  obtain ⟨hcard,hsmall,hreconstruct⟩ := face_traced_strict_reduction rotation m hm root
    hC hf hv hs minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided
  exact minimal.notColorable (hreconstruct (minimal.smallerColorable _ hcard hsmall))

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal
