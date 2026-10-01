import Mettapedia.GraphTheory.FourColor.SourceAlternatingBoundaryRepair
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCyclicOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

/-!
# Adjacent source pairs with a derived boundary order

The two local rotations enumerate the deleted-side ports. Connected planar
shores reverse that order on the retained side. This adapter derives the
literal boundary order consumed by the alternating-pin repair, rather than
accepting it as an independent certificate. The result concerns a proper
partial source exterior and its dual-and-truncate target; it is not a
strict reduction or an occurrence theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentSourceBoundaryRepair

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary
open GoertzelV24DeletedRegionBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RotationCutDartDecomposition GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided GoertzelV24CyclicBoundaryClosure
open GoertzelV24OrderedCutFaceReturnProfile
open TwoCellSourceRepair SourceAlternatingBoundaryRepair

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Reverse the four-port orientation while retaining the two pairs of pins
at their respective omitted vertices. -/
def reflection : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

@[simp] theorem reflection_zero : reflection 0 = 1 := by decide
@[simp] theorem reflection_one : reflection 1 = 0 := by decide
@[simp] theorem reflection_two : reflection 2 = 3 := by decide
@[simp] theorem reflection_three : reflection 3 = 2 := by decide

theorem reflection_rotate : reflection.permCongr (finRotate 4) = (finRotate 4)⁻¹ := by
  decide

/-- The incidence frame in the positive retained-side orientation. -/
def frame (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    Frame graphData.toRotationSystem where
  left := data.firstVertex
  right := data.secondVertex
  distinct := G.ne_of_adj data.centralAdjacent
  pins i := data.rotationPortVertex graphData (reflection i)
  pins_outside i :=
    ⟨data.rotationPortVertex_ne_firstVertex graphData hcubic hrotation _,
      data.rotationPortVertex_ne_secondVertex graphData hcubic hrotation _⟩
  left_neighbours d hd := by
    let ordered := data.rotationOrderedData graphData hcubic hrotation
    have hm : d.snd ∈ G.neighborSet ordered.firstVertex := by
      change d.fst = data.firstVertex at hd
      change G.Adj data.firstVertex d.snd
      simpa only [ordered, AdjacentPairData.rotationOrderedData, hd] using d.adj
    rw [ordered.firstNeighbors] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    change d.snd = data.secondVertex ∨
      d.snd = data.rotationPortVertex graphData (reflection 0) ∨
      d.snd = data.rotationPortVertex graphData (reflection 1)
    simpa [ordered, AdjacentPairData.rotationOrderedData, or_left_comm,
      or_comm, or_assoc] using hm
  right_neighbours d hd := by
    let ordered := data.rotationOrderedData graphData hcubic hrotation
    have hm : d.snd ∈ G.neighborSet ordered.secondVertex := by
      change d.fst = data.secondVertex at hd
      change G.Adj data.secondVertex d.snd
      simpa only [ordered, AdjacentPairData.rotationOrderedData, hd] using d.adj
    rw [ordered.secondNeighbors] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    change d.snd = data.firstVertex ∨
      d.snd = data.rotationPortVertex graphData (reflection 2) ∨
      d.snd = data.rotationPortVertex graphData (reflection 3)
    simpa [ordered, AdjacentPairData.rotationOrderedData, or_left_comm,
      or_comm, or_assoc] using hm

theorem frame_outside_eq (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    (frame graphData data hcubic hrotation).outside = deletedRegionKeep data.deletedVertices := by
  funext v
  simp [Frame.outside, frame, deletedRegionKeep, AdjacentPairData.deletedVertices]

/-- The deleted pair is a connected shore, independently of any colouring. -/
theorem complement_connected (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    (SideGraph G (fun v => ¬(frame graphData data hcubic hrotation).outside v)).Connected := by
  classical
  let : Nonempty {v // ¬(frame graphData data hcubic hrotation).outside v} :=
    ⟨⟨data.firstVertex, by simp [Frame.outside, frame]⟩⟩
  constructor
  intro x y
  by_cases hxy : x = y
  · subst y
    exact Reachable.refl x
  · have hx : x.1 = data.firstVertex ∨ x.1 = data.secondVertex := by
      have h := x.2
      change ¬(x.1 ≠ data.firstVertex ∧ x.1 ≠ data.secondVertex) at h
      tauto
    have hy : y.1 = data.firstVertex ∨ y.1 = data.secondVertex := by
      have h := y.2
      change ¬(y.1 ≠ data.firstVertex ∧ y.1 ≠ data.secondVertex) at h
      tauto
    apply Adj.reachable
    change G.Adj x.1 y.1
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))
    · rw [hx, hy]; exact data.centralAdjacent
    · rw [hx, hy]; exact data.centralAdjacent.symm
    · exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))

/-- The canonical deleted-side enumeration uses actual darts. -/
def deletedDart (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) (i : Fin 4) :
    BoundaryDart graphData.toRotationSystem (deletedRegionKeep data.deletedVertices) :=
  deletedBoundaryHalfDartEquivBoundaryDart
    ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem graphData)
    (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
    (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation i)

theorem deletedDart_pin (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) (i : Fin 4) :
    (deletedDart graphData data hcubic hrotation i).1.1.fst =
      data.rotationPortVertex graphData i := rfl

theorem deletedDart_bijective (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    Function.Bijective (deletedDart graphData data hcubic hrotation) := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  constructor
  · intro i j hij
    apply data.rotationPortVertex_injective graphData hcubic hrotation
    exact congrArg (fun d => d.1.1.fst) hij
  · intro d
    have hm := boundaryDart_edge_mem_vertexSetCrossingEdges
      graphData.toRotationSystem data.deletedVertices d
    change graphData.toRotationSystem.edgeOf d.1.1 ∈
      GoertzelV24RotationVertexCutProfile.vertexSetCrossingEdges
        graphData.toRotationSystem ordered.deletedVertices at hm
    rw [← ordered.boundaryEdgeSet_eq_vertexSetCrossingEdges graphData] at hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    refine ⟨i, ?_⟩
    apply boundaryDart_eq_of_edgeOf_eq
    exact (data.rotationBoundaryDart_edgeOf graphData hcubic hrotation i).trans hi

/-- Every boundary dart occurs exactly once in the local rotation order. -/
def deletedOrder (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    Fin 4 ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep data.deletedVertices) :=
  Equiv.ofBijective _ (deletedDart_bijective graphData data hcubic hrotation)

theorem deletedOrder_successor (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    (deletedOrder graphData data hcubic hrotation).permCongr (finRotate 4) =
      deletedRegionBoundarySuccessor graphData.toRotationSystem data.deletedVertices := by
  apply Equiv.ext
  intro d
  obtain ⟨i, rfl⟩ := (deletedOrder graphData data hcubic hrotation).surjective d
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact (data.rotationBoundarySuccessor_apply_port graphData hcubic hrotation i).symm

/-- The actual planar complementary shores determine the retained order.
The four ports are reflected together; the two insertion choices stay coupled. -/
theorem exists_retained_order (graphData : Data G) (data : AdjacentPairData G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    ∃ order : Fin 4 ≃ BoundaryDart graphData.toRotationSystem
        (frame graphData data hsphere.cubic hrotation).outside,
      order.permCongr (finRotate 4) = retainedRegionBoundarySuccessor graphData.toRotationSystem
        (frame graphData data hsphere.cubic hrotation).outside ∧
      ∀ i, (order i).1.1.fst = (frame graphData data hsphere.cubic hrotation).pins i := by
  rw [frame_outside_eq]
  let localOrder := deletedOrder graphData data hsphere.cubic hrotation
  let order := reflection.trans localOrder
  refine ⟨order, ?_, ?_⟩
  · have hdeleted : (G.induce {v | ¬deletedRegionKeep data.deletedVertices v}).Connected := by
      rw [← frame_outside_eq graphData data hsphere.cubic hrotation]
      exact complement_connected graphData data hsphere.cubic hrotation
    have hinverse := retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
      graphData data.deletedVertices hsphere htwoSided hconnected hrotation hretained hdeleted
    rw [hinverse]
    calc
      order.permCongr (finRotate 4) = localOrder.permCongr (reflection.permCongr (finRotate 4)) := by
        ext d; rfl
      _ = localOrder.permCongr ((finRotate 4)⁻¹) := by rw [reflection_rotate]
      _ = (localOrder.permCongr (finRotate 4))⁻¹ := by
        ext d
        rfl
      _ = (deletedRegionBoundarySuccessor graphData.toRotationSystem data.deletedVertices)⁻¹ := by
        rw [deletedOrder_successor]
  · intro i
    exact deletedDart_pin graphData data hsphere.cubic hrotation (reflection i)

/-- Geometry for the existing repair consumer, with the full face dual,
deleted connectedness and boundary order all derived. -/
def geometry (graphData : Data G) (data : AdjacentPairData G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    Geometry graphData (frame graphData data hsphere.cubic hrotation) where
  twoSided := htwoSided
  dual := orbitFaceInteriorDual_connected graphData.toRotationSystem hsphere.cubic
    (by rw [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq];
        exact hconnected) hrotation
  connected := hconnected
  spherical := hsphere
  rotation := hrotation
  complement := complement_connected graphData data hsphere.cubic hrotation
  order := (exists_retained_order graphData data hsphere htwoSided hconnected hrotation hretained).choose
  successor := (exists_retained_order graphData data hsphere htwoSided hconnected hrotation
    hretained).choose_spec.1
  pins := (exists_retained_order graphData data hsphere htwoSided hconnected hrotation
    hretained).choose_spec.2

section Consumers

variable (graphData : Data G) (data : AdjacentPairData G)
  (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
  (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
  (hconnected : G.Connected)
  (hrotation : VertexRotationCyclic graphData.toRotationSystem)
  (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected)


variable (c : V → Color)
  (hc : SourcePatchKempe.ExteriorProper graphData.toRotationSystem (frame graphData data hsphere.cubic hrotation).outside c)
  (a b : Color) (hab : a ≠ b)
  (hvalues : c ((frame graphData data hsphere.cubic hrotation).pins 0) = a ∧ c ((frame graphData data hsphere.cubic hrotation).pins 1) = b ∧
    c ((frame graphData data hsphere.cubic hrotation).pins 2) = a ∧ c ((frame graphData data hsphere.cubic hrotation).pins 3) = b)

/-- A repair derived from an actual embedded adjacent pair. Neither its
cyclic order nor a successful component is supplied separately. -/
def repair : Repair graphData.toRotationSystem (frame graphData data hsphere.cubic hrotation) c := (geometry graphData data hsphere htwoSided hconnected hrotation hretained).repair c hc a b hab hvalues

/-- A whole source witness reconstructed from the partial exterior, using
the derived cyclic geometry and both joint insertion choices. -/
def sourceColouring : DualTruncateColoring.ThreeVertexColoring graphData.toRotationSystem :=
  (geometry graphData data hsphere htwoSided hconnected hrotation hretained).sourceColouring c hc a b hab hvalues

/-- The actual expanded target is properly Tait-coloured. -/
theorem target_tait : (DualTruncateColoring.rotation graphData.toRotationSystem).IsTaitEdgeColoring
    (DualTruncateColoring.colouring graphData.toRotationSystem
      (sourceColouring graphData data hsphere htwoSided hconnected hrotation hretained
        c hc a b hab hvalues)) := (geometry graphData data hsphere htwoSided hconnected hrotation hretained).target_tait c hc a b hab hvalues

/-- The derived source component acts on a saturated region of actual
target edges, excluding the omitted patch. -/
theorem physical_region :
    let r := repair graphData data hsphere htwoSided hconnected hrotation hretained c hc a b hab hvalues
    RotationPatchKempe.Region (DualTruncateColoring.rotation graphData.toRotationSystem)
      (fun d => ¬DualTruncateOpenPatch.vertexRegion graphData.toRotationSystem (frame graphData data hsphere.cubic hrotation).selected d)
      (DualTruncateColoring.edgeColour graphData.toRotationSystem c) r.pair
      (DualTruncateKempeTransport.edgeMask graphData.toRotationSystem (frame graphData data hsphere.cubic hrotation).selected c r.pair r.mask) :=
  (geometry graphData data hsphere htwoSided hconnected hrotation hretained).physical_region c hc a b hab hvalues

/-- Whole-witness reconstruction preserves the switched exterior on all
actual target stars and their cut observations. -/
theorem reconstructs :
    let r := repair graphData data hsphere htwoSided hconnected hrotation hretained c hc a b hab hvalues
    DualTruncateOpenPatch.Extends graphData.toRotationSystem
      (DualTruncateOpenPatch.vertexRegion graphData.toRotationSystem (frame graphData data hsphere.cubic hrotation).selected)
      (RotationPatchKempe.switched (DualTruncateColoring.edgeColour graphData.toRotationSystem c)
        r.pair (DualTruncateKempeTransport.edgeMask graphData.toRotationSystem (frame graphData data hsphere.cubic hrotation).selected c r.pair r.mask))
      (DualTruncateColoring.colouring graphData.toRotationSystem
        (sourceColouring graphData data hsphere htwoSided hconnected hrotation hretained
          c hc a b hab hvalues)) := (geometry graphData data hsphere htwoSided hconnected hrotation hretained).reconstructs c hc a b hab hvalues

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

include data hsphere htwoSided hconnected hrotation hretained c hc a b hab hvalues in
/-- The derived colouring supplies jointly compatible witnesses along every
complete faithful GSLT sweep of the expanded map. -/
theorem every_complete_sweep (order : List graphData.toRotationSystem.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic graphData.toRotationSystem)
        (DualTruncateConstructionGSLT.rotationCyclic graphData.toRotationSystem)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  (geometry graphData data hsphere htwoSided hconnected hrotation hretained).every_complete_sweep c hc a b hab hvalues order hn he hcover

end Consumers

end
end Mettapedia.GraphTheory.FourColor.AdjacentSourceBoundaryRepair
