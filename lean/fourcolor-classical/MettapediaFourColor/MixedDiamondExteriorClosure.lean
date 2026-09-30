import Mettapedia.GraphTheory.FourColor.CrossingBoundaryEquiv
import MettapediaFourColor.MixedDiamondFaceRecognition
import MettapediaFourColor.MixedDiamondIntrinsic
import MettapediaFourColor.OpenTangleKempeClosure
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryReflection
import Mettapedia.GraphTheory.FourColor.SevenPortBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn
import Mettapedia.GraphTheory.FourColor.VertexSideExactReassembly
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

/-!
# Actual seven-port exterior closure for the mixed diamond

Normal-form geometry supplies connected shores and the exact reversed cyclic
boundary order. The physical component pairing is therefore noncrossing.
The width-independent matching codec then discharges reference Kempe closure
of the actual exterior. Its colouring witnesses reconstruct the source.

An initial proper exterior colouring is still required. Constructing a
smaller valid map that supplies that colouring is a separate reduction step.
-/

namespace FourColor.MixedDiamondPatch.Tangle.FaceRecognition

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24VertexSidePrimalKempeTrail
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24PortTangleCutParity
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24FaceDualConnectedness MatchingBoundaryConnectivity
open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance mixedExteriorEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance mixedExteriorEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : MixedDiamond.FaceLengths rotation root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

include hfaces h hminimum hinternal in
theorem inside_connected : (G.induce {v | Recognition.keep rotation root v}).Connected := by
  have hh := OpenTangleVertexSideReturn.induce_connected rotation.toRotationSystem
    (Recognition.keep rotation root) (Recognition.rootIn rotation root (cubic rotation h) hfaces)
    ((recognized rotation root hfaces h hminimum hinternal).connected piece_connected)
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using hh

include hfaces h hminimum hinternal in
theorem exterior_card :
    Fintype.card {v : V // deletedRegionKeep (Recognition.deleted rotation root) v} + 13 =
      Fintype.card V := by
  have he := Fintype.card_congr
    ((Equiv.sumCongr (Equiv.refl {v : V // deletedRegionKeep (Recognition.deleted rotation root) v})
      (recognized rotation root hfaces h hminimum hinternal).vertex).trans
        (complementaryVertexEquiv (Recognition.deleted rotation root)))
  simpa only [Fintype.card_sum, Fintype.card_fin] using he

include hfaces h hminimum hinternal in
theorem inside_hasCycle : HasCycleOnSide G (Recognition.keep rotation root) := by
  have hv := Fintype.card_congr (recognized rotation root hfaces h hminimum hinternal).vertex
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (Recognition.keep rotation root)).trans
      (recognized rotation root hfaces h hminimum hinternal).boundary.symm)
  simp only [Fintype.card_fin] at hv hb
  exact CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v))
    (Recognition.keep rotation root) (Fintype.card_pos_iff.mp (by omega)) (by omega)

include hfaces h hminimum hinternal in
/-- The seven external attachments may share vertices. Their actual
incidence and the ambient cut bound still force a connected exterior. -/
theorem exterior_connected :
    (G.induce {v | deletedRegionKeep (Recognition.deleted rotation root) v}).Connected := by
  have hs := exterior_card rotation root hfaces h hminimum hinternal
  have ht := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedRegionKeep (Recognition.deleted rotation root))).trans
      (ports rotation root hfaces h hminimum hinternal).symm)
  simp only [Fintype.card_fin] at hb
  apply SevenPortBoundaryConnectivity.connected_of_six_le_card_of_boundary_card_le_seven
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)) hinternal.1
    (deletedRegionKeep (Recognition.deleted rotation root))
  · exact inside_hasCycle rotation root hfaces h hminimum hinternal
  · omega
  · omega

variable (htwo : OrbitFacesTwoSided rotation.toRotationSystem)

include htwo in
/-- Recognition transports the interior cycle; the planar bond theorem
derives the exterior's opposite cyclic order. -/
theorem exterior_order :
    (ports rotation root hfaces h hminimum hinternal).permCongr (finRotate 7) =
      (retainedRegionBoundarySuccessor rotation.toRotationSystem
        (deletedRegionKeep (Recognition.deleted rotation root)))⁻¹ := by
  let R := recognized rotation root hfaces h hminimum hinternal
  let RS := rotation.toRotationSystem
  let deleted := Recognition.deleted rotation root
  let m := complementBoundaryAlphaEquiv RS deleted
  let si := retainedRegionBoundarySuccessor RS (Recognition.keep rotation root)
  let so := retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted)
  have hi : R.boundary.permCongr (finRotate 7) = si := by
    rw [← piece_returnCode, R.returnCode, OpenTangleVertexSideReturn.returnCode_eq]
  have hi' (i : Fin 7) : si (R.boundary i) = R.boundary (finRotate 7 i) := by
    have he := Equiv.congr_fun hi (R.boundary i)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using he.symm
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hop := boundarySuccessors_opposite_of_planarBond rotation deleted h.spherical htwo hg
    h.vertexRotationCyclic (exterior_connected rotation root hfaces h hminimum hinternal)
    (inside_connected rotation root hfaces h hminimum hinternal)
  let order := ports rotation root hfaces h hminimum hinternal
  apply Equiv.ext
  intro b
  apply so.injective
  change so (order (finRotate 7 (order.symm b))) = so (so.symm b)
  rw [Equiv.apply_symm_apply]
  apply m.injective
  apply si.injective
  calc
    si (m (so (order (finRotate 7 (order.symm b))))) = m (order (finRotate 7 (order.symm b))) :=
      hop _
    _ = R.boundary (finRotate 7 (order.symm b)) := by simp [order, ports, R, m, RS, deleted]
    _ = si (R.boundary (order.symm b)) := (hi' _).symm
    _ = si (m b) := by simp [order, ports, R, m, RS, deleted]

include htwo in
/-- Reference closure is derived from physical geometry and the uniform
matching reconstruction theorem, with no separate seven-port certificate. -/
theorem exterior_closed : KempeClosed (OpenTangleKempeRepair.Trace
    (outside rotation root hfaces h hminimum hinternal)
    (ports rotation root hfaces h hminimum hinternal)) := by
  let O := outside rotation root hfaces h hminimum hinternal
  let seam := ports rotation root hfaces h hminimum hinternal
  apply OpenTangleKempeRepair.closed_of_physical_noncrossing O seam
    (isCubic_vertexSidePortTangle rotation _ _ h.spherical.cubic)
  intro c hc
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem h.spherical.cubic
    h.primalConnected h.vertexRotationCyclic
  exact physicalMateInCoordinates_isNoncrossing_inverse rotation htwo hdual hg
    h.spherical h.spherical.cubic h.vertexRotationCyclic
    (deletedRegionKeep (Recognition.deleted rotation root))
    (inside_connected rotation root hfaces h hminimum hinternal) (by decide) seam
    (exterior_order rotation root hfaces h hminimum hinternal htwo) _ c hc .bluePurple

include htwo in
/-- The shared diamond repair reconstructs the original map from any
genuine starting exterior colouring, allowing compatible recolouring. -/
theorem colorable_of_exterior
    (r : _ → Mettapedia.GraphTheory.FourColor.Color)
    (hr : OpenTangleClosedWitness.IsColor (outside rotation root hfaces h hminimum hinternal) r) :
    RotationSystemTaitColorable rotation.toRotationSystem :=
  colorable_of_exterior_closure rotation root hfaces h hminimum hinternal
    (exterior_closed rotation root hfaces h hminimum hinternal htwo) r hr

end
end FourColor.MixedDiamondPatch.Tangle.FaceRecognition
