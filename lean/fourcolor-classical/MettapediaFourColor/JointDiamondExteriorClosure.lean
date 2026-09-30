import MettapediaFourColor.JointDiamondOccurrence
import MettapediaFourColor.OpenTangleKempeClosure
import Mettapedia.GraphTheory.FourColor.CrossingBoundaryEquiv
import Mettapedia.GraphTheory.FourColor.EightPortBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryReflection
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn
import Mettapedia.GraphTheory.FourColor.VertexSideExactReassembly
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

/-!
# Physical exterior closure at an actual joint-diamond occurrence

The occurrence supplies its internal hexagon and exact eight-port order.
The ambient internal-six cut law forces exterior connectivity, including
when several ports attach to the same exterior vertex. Spherical geometry
then supplies noncrossing physical component switches. The width-independent
matching reconstruction theorem proves Kempe closure of the exterior.

A genuine compatible coupled-wiring witness now suffices to colour the
original ambient graph. The occurrence is an explicit exact isomorphism;
recognition from face lengths and preservation of the smaller map class
remain separate obligations.
-/

namespace FourColor.JointDiamondPatch.Tangle.Occurrence

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24VertexSidePrimalKempeTrail
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24PortTangleCutParity
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24SimpleGraphFaceDualConnectedness GoertzelV24FaceDualConnectedness
open MatchingBoundaryConnectivity
open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance jointExteriorEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance jointExteriorEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (deleted : Finset V)
  (root : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (R : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) root))
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

def ports := R.boundary.trans
  (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).symm

abbrev outside := ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted)
  ((ports rotation deleted root R 0).1)

include R

theorem inside_connected : (G.induce {v | deletedSideKeep deleted v}).Connected := by
  have hh := OpenTangleVertexSideReturn.induce_connected rotation.toRotationSystem
    (deletedSideKeep deleted) root (R.connected piece_connected)
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using hh

theorem exterior_card :
    Fintype.card {v : V // deletedRegionKeep deleted v} + 14 = Fintype.card V := by
  have he := Fintype.card_congr
    ((Equiv.sumCongr (Equiv.refl {v : V // deletedRegionKeep deleted v}) R.vertex).trans
      (complementaryVertexEquiv deleted))
  simpa only [Fintype.card_sum, Fintype.card_fin] using he

include h in
theorem inside_hasCycle : HasCycleOnSide G (deletedSideKeep deleted) := by
  have hv := Fintype.card_congr R.vertex
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedSideKeep deleted)).trans R.boundary.symm)
  simp only [Fintype.card_fin] at hv hb
  exact CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v))
    (deletedSideKeep deleted) (Fintype.card_pos_iff.mp (by omega)) (by omega)

include h hminimum hinternal in
/-- The occurrence's hexagon supplies the needed size. No distinctness of
the eight exterior attachment vertices is required. -/
theorem exterior_connected :
    (G.induce {v | deletedRegionKeep deleted v}).Connected := by
  have hs := exterior_card rotation deleted root R
  have ht := twenty_lt_vertices rotation.toRotationSystem (deletedSideKeep deleted) root R
    h.spherical hminimum
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedRegionKeep deleted)).trans
      (ports rotation deleted root R).symm)
  have hi := Fintype.card_congr R.vertex
  simp only [Fintype.card_fin] at hb hi
  change 14 = Fintype.card {v // ¬ deletedRegionKeep deleted v} at hi
  apply EightPortBoundaryConnectivity.connected_of_seven_le_card_of_boundary_card_le_eight
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)) hinternal
    (deletedRegionKeep deleted)
  · exact inside_hasCycle rotation deleted root R h
  · omega
  · omega
  · omega

variable (htwo : OrbitFacesTwoSided rotation.toRotationSystem)

include h hminimum hinternal htwo in
theorem exterior_order :
    (ports rotation deleted root R).permCongr (finRotate 8) =
      (retainedRegionBoundarySuccessor rotation.toRotationSystem
        (deletedRegionKeep deleted))⁻¹ := by
  let RS := rotation.toRotationSystem
  let m := complementBoundaryAlphaEquiv RS deleted
  let si := retainedRegionBoundarySuccessor RS (deletedSideKeep deleted)
  let so := retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted)
  have hi : R.boundary.permCongr (finRotate 8) = si := by
    rw [← piece_returnCode, R.returnCode, OpenTangleVertexSideReturn.returnCode_eq]
  have hi' (i : Fin 8) : si (R.boundary i) = R.boundary (finRotate 8 i) := by
    have he := Equiv.congr_fun hi (R.boundary i)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using he.symm
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hop := boundarySuccessors_opposite_of_planarBond rotation deleted h.spherical htwo hg
    h.vertexRotationCyclic (exterior_connected rotation deleted root R h hminimum hinternal)
    (inside_connected rotation deleted root R)
  let order := ports rotation deleted root R
  apply Equiv.ext
  intro b
  apply so.injective
  change so (order (finRotate 8 (order.symm b))) = so (so.symm b)
  rw [Equiv.apply_symm_apply]
  apply m.injective
  apply si.injective
  calc
    si (m (so (order (finRotate 8 (order.symm b))))) = m (order (finRotate 8 (order.symm b))) :=
      hop _
    _ = R.boundary (finRotate 8 (order.symm b)) := by simp [order, ports, m, RS]
    _ = si (R.boundary (order.symm b)) := (hi' _).symm
    _ = si (m b) := by simp [order, ports, m, RS]

include h hminimum hinternal htwo in
/-- The actual exterior language is closed under the reference Kempe
queries, with genuine whole-colouring witnesses for every answer. -/
theorem exterior_closed : KempeClosed (OpenTangleKempeRepair.Trace
    (outside rotation deleted root R) (ports rotation deleted root R)) := by
  let O := outside rotation deleted root R
  let seam := ports rotation deleted root R
  apply OpenTangleKempeRepair.closed_of_physical_noncrossing O seam
    (isCubic_vertexSidePortTangle rotation _ _ h.spherical.cubic)
  intro c hc
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem h.spherical.cubic
    h.primalConnected h.vertexRotationCyclic
  exact physicalMateInCoordinates_isNoncrossing_inverse rotation htwo hdual hg
    h.spherical h.spherical.cubic h.vertexRotationCyclic
    (deletedRegionKeep deleted) (inside_connected rotation deleted root R) (by decide) seam
    (exterior_order rotation deleted root R h hminimum hinternal htwo) _ c hc .bluePurple

include h hminimum hinternal htwo in
/-- A single compatible joint contract witness starts the shared repair
and reconstructs the actual original map. Exterior closure is derived. -/
theorem colorable_of_joint_exterior (k : DiamondCoupledWiring.Coloring)
    (hk : OpenTangleKempeRepair.Trace (outside rotation deleted root R)
      (ports rotation deleted root R) (DiamondCoupledWiring.word k)) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  let O := outside rotation deleted root R
  let seam := ports rotation deleted root R
  obtain ⟨et, ht, l, hl, he⟩ := DiamondCoupledWiring.repair k _
    (exterior_closed rotation deleted root R h hminimum hinternal htwo) hk
  obtain ⟨c, rfl⟩ := (DiamondConfigurations.reducibilityTrace004 et).mp ht
  have hm (b) : l (.inr b) = colouring c (.inr (seam.symm b)) := by
    have hh := List.map_inj_left.mp (he.trans (boundary_colouring c).symm)
      (seam.symm b) (List.mem_finRange (seam.symm b))
    simpa only [seam, Equiv.apply_symm_apply] using hh
  obtain ⟨c', hc', _⟩ := OpenTangleClosedWitness.glueOpen O piece seam.symm
    l (colouring c) hl (colouring_valid c) hm
  have hs := (R.sewn_colorable_iff O seam.symm).mp ⟨c', hc'⟩
  have hm' : seam.symm.trans R.boundary =
      complementBoundaryAlphaEquiv rotation.toRotationSystem deleted := by
    apply Equiv.ext
    intro b
    simp [seam, ports]
  rw [hm'] at hs
  exact (rotationSystemTaitColorable_complementaryComposite_iff
    rotation.toRotationSystem deleted _ _).mp hs

end
end FourColor.JointDiamondPatch.Tangle.Occurrence
