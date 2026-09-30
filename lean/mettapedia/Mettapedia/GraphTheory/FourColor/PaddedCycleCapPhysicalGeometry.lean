import Mettapedia.GraphTheory.FourColor.PaddedCycleCapPhysicalRepair
import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly

/-!
# Physical cap repair on an exactly recognized spherical shore

The cap's computed first return and the opposite complementary-shore orders
derive the exterior's cyclic order. The actual spherical separator theorem
then supplies physical noncrossing. Cap connectivity follows from the local
representation; exterior connectivity is retained as an explicit hypothesis.
Compatible repaired witnesses reconstruct the original ambient graph.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24VertexSideOpenTangle
open GoertzelV24VertexSideReassembly GoertzelV24VertexSidePrimalKempeTrail
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24FaceDualConnectedness
open GoertzelV24SimpleGraphFaceDualConnectedness GoertzelV24CompositeSeamMultigraph
open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open OpenTanglePortReplacement OpenTangleClosedWitness SerialTangleSmallCutTransfer

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
  (outsideRoot : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
  (insideRoot : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))

local instance physicalCapGraphEdgeSetFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance physicalCapGraphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (e : OpenTangleIsomorphism.Iso
  (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) insideRoot)
  (asOpen (indexedCap m hm)))

include e in
/-- The local cap representation proves that its actual ambient shore is
connected. No hypothesis about a rich colouring support is used. -/
theorem recognized_cap_connected : (G.induce {v | deletedSideKeep deleted v}).Connected := by
  have hcap : (sideMultigraph (asOpen (indexedCap m hm))).Connected := by
    simpa only [indexedCap, TwoSidedBoundaryJoint.side_reindex] using
      (cap_connected_bridgeless m hm).1
  have hside := OpenTangleVertexSideReturn.induce_connected rotation.toRotationSystem
    (deletedSideKeep deleted) insideRoot (e.symm.connected hcap)
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using hside

variable (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
  (houtside : (G.induce {v | deletedRegionKeep deleted v}).Connected)

include h htwo houtside in
/-- The cap's preceding-port return and the actual planar bond force the
exterior order used by the repair. Both orientations are determined from
the same local representation and ambient edge matching. -/
theorem recognized_cap_exterior_order :
    (capCoordinates m ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans
      e.boundary)).permCongr (finRotate (m*2)) =
      retainedRegionBoundarySuccessor rotation.toRotationSystem (deletedRegionKeep deleted) := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS deleted
  let seam := matching.trans e.boundary
  let order := capCoordinates m seam
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hcode := e.returnCode
  rw [OpenTangleVertexSideReturn.returnCode_eq, indexed_returnCode] at hcode
  have hreturn (b) : e.boundary (retainedRegionBoundarySuccessor RS (deletedSideKeep deleted) b) =
      CycleCap.boundaryPerm (m*2) (e.boundary b) := by
    have he := congrArg (fun p => p (e.boundary b)) hcode
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using he
  have hstep (i) : retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) (order i) =
      order (i+1) := by
    apply seam.injective
    apply (CycleCap.boundaryPerm (m*2)).injective
    have hop := boundarySuccessors_opposite_of_planarBond rotation deleted h.spherical htwo hg
      h.vertexRotationCyclic houtside (recognized_cap_connected m hm rotation deleted insideRoot e)
      (order i)
    have he := congrArg e.boundary hop
    rw [hreturn] at he
    change CycleCap.boundaryPerm (m*2)
      (seam (retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) (order i))) =
        seam (order i) at he
    exact he.trans (by simp [order, capCoordinates, seam, CycleCap.boundaryPerm])
  apply Equiv.ext
  intro b
  obtain ⟨i,rfl⟩ := order.surjective b
  change order ((finRotate (m*2)) (order.symm (order i))) = _
  rw [Equiv.symm_apply_apply, finRotate_apply]
  exact (hstep i).symm

include h htwo houtside in
/-- Actual spherical geometry discharges the physical matching condition
for every exterior colouring of this recognized cap. -/
theorem physical_noncrossing_recognized_cap :
    PhysicalNoncrossing m
      (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) outsideRoot)
      ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans e.boundary) := by
  intro hcubic coloring hproper pair
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem h.spherical.cubic
    h.primalConnected h.vertexRotationCyclic
  exact physicalMateInCoordinates_isNoncrossing rotation htwo hdual hg h.spherical
    h.spherical.cubic h.vertexRotationCyclic (deletedRegionKeep deleted)
    (recognized_cap_connected m hm rotation deleted insideRoot e) (by omega)
    (capCoordinates m ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans
      e.boundary)) (recognized_cap_exterior_order m hm rotation deleted insideRoot e h htwo houtside)
    outsideRoot coloring hproper pair

include h htwo houtside in
/-- Colouring the smaller cycle in the actual exterior reconstructs the
original ambient graph at every width, including odd sector counts. -/
theorem recognized_cap_reconstruct :
    RotationSystemTaitColorable
      (sewn (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) outsideRoot)
        (CycleCap.cap (m*2) (by omega))
        ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans e.boundary)) →
      RotationSystemTaitColorable rotation.toRotationSystem := by
  rintro ⟨c,hc⟩
  have hp := physical_noncrossing_recognized_cap m hm rotation deleted outsideRoot insideRoot e
    h htwo houtside
  have hcolour := closed_reconstruct_of_physical_noncrossing m hm
    (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) outsideRoot)
    ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans e.boundary)
    (openIsCubic_ofVertexSide _ _ _ h.spherical.cubic) hp c hc
  have hcomposite := (e.sewn_colorable_iff
    (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) outsideRoot)
    (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted)).mpr hcolour
  exact (rotationSystemTaitColorable_complementaryComposite_iff rotation.toRotationSystem
    deleted outsideRoot insideRoot).mp hcomposite

include h htwo houtside in
/-- The actual recognized cap has a valid strict reduction at every sector
count. All vertices introduced by the cycle are included in this comparison. -/
theorem recognized_cap_strict_reduction :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin (m*2)) < Fintype.card V ∧
      BridgelessSphericalCubicMapData
        (sewn (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) outsideRoot)
          (CycleCap.cap (m*2) (by omega))
          ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans e.boundary)) ∧
      (RotationSystemTaitColorable
        (sewn (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) outsideRoot)
          (CycleCap.cap (m*2) (by omega))
          ((complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).trans e.boundary)) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS deleted
  let O := ofVertexSide RS (deletedRegionKeep deleted) outsideRoot
  let seam := matching.trans e.boundary
  let order := capCoordinates m seam
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hne : order 0 ≠ order 1 := by
    intro he
    have he' := congrArg Fin.val (order.injective he)
    have hm' := NeZero.pos m
    simp [Nat.mod_eq_of_lt (show 1 < m*2 by omega)] at he'
  have hcanonical := bridgelessSphericalCubicMapData_of_planarBond_canonical rotation deleted
    outsideRoot insideRoot h.spherical htwo hg h.vertexRotationCyclic houtside
    (recognized_cap_connected m hm rotation deleted insideRoot e)
    ((bridgeless_iff_edgeBridgeFree RS).mpr h.edgeBridgeFree) (order 0) (order 1) hne
  have hclass := e.sewn_class O matching hcanonical
  have hplanar := physical_noncrossing_recognized_cap m hm rotation deleted outsideRoot
    insideRoot e h htwo houtside
  obtain ⟨hcard,hsmall,_⟩ := strict_reduction_of_physical_noncrossing m hm O seam hplanar hclass
  let v : {v : V // deletedRegionKeep deleted v} ⊕ Vertex m ≃ V :=
    (Equiv.sumCongr (Equiv.refl _) e.vertex.symm).trans (complementaryVertexEquiv deleted)
  rw [Fintype.card_congr v] at hcard
  exact ⟨hcard,hsmall,recognized_cap_reconstruct m hm rotation deleted outsideRoot insideRoot
    e h htwo houtside⟩

include e outsideRoot in
/-- A vertex-minimal counterexample contains no exactly represented padded
cap with connected exterior. The geometric and colouring hypotheses are
derived from that occurrence and the ambient source class. -/
theorem no_recognized_cap
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (houtside : (G.induce {v | deletedRegionKeep deleted v}).Connected) : False := by
  obtain ⟨hcard,hsmall,hreconstruct⟩ := recognized_cap_strict_reduction m hm rotation deleted
    outsideRoot insideRoot e minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided houtside
  exact minimal.notColorable (hreconstruct (minimal.smallerColorable _ hcard hsmall))

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
