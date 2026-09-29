import MettapediaFourColor.PentagonalLobeOpenRepair
import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn
import Mettapedia.GraphTheory.FourColor.VertexSideExactReassembly
import Mettapedia.GraphTheory.FourColor.SixPortBoundaryReflection

/-!
# Tree reduction of an actual recognized pentagonal lobe

Recognition is an exact isomorphism from the literal patch to an ambient
vertex shore, preserving all vertices, internal darts, ports and rotations.
In a spherical simple-graph source with connected exterior, its computed
return order supplies physical noncrossing on the opposite shore. The tree
replacement loses twelve total vertices and reconstructs the original map.

No boundary-support or recolouring premise is supplied by the caller.
Deriving the recognition data from alternating-lobe geometry, and proving
that such a patch occurs, remain separate obligations.
-/

namespace FourColor.PentagonalLobePatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph GoertzelV24BoundaryEssentialGluing.Multigraph
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideOpenTangle
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24VertexSideReassembly GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24PhysicalKempeNoncrossingClosure
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24HexagonPairingTargetAwareBoundary

/-- Every vertex of the literal patch reaches a lower numbered neighbour,
until it reaches zero. -/
theorem piece_connected : (sideMultigraph piece).Connected := by
  have down : ∀ v : Fin 16, v ≠ 0 → ∃ i : Fin 42,
      piece.interiorVert i = v ∧ piece.interiorVert (piece.interiorAlpha i) < v := by
    decide +kernel
  have root (v : Fin 16) : (sideMultigraph piece).Reach v 0 := by
    induction v using Fin.strong_induction_on with
    | h v ih =>
      by_cases hv : v = 0
      · subst v; exact .refl
      · obtain ⟨i, hi, hj⟩ := down v hv
        have hs : (sideMultigraph piece).Step v (piece.interiorVert (piece.interiorAlpha i)) := by
          refine ⟨sideEdgeOf piece i, not_false, ?_⟩
          simpa only [hi] using sideMultigraph_ends piece i
        exact (Relation.ReflTransGen.single hs).trans (ih _ hj)
  intro u v
  exact (root u).trans (reach_symm (root v))

namespace Embedded
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
  (rootOut : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
  (rootIn : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (recognition : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) rootIn))

abbrev outside := ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) rootOut

/-- Read each port's actual mate across the cut, in the literal patch coordinates. -/
def ports := recognition.boundary.trans (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).symm

abbrev smaller := (outside rotation deleted rootOut).composeRotationSystem Tree.piece
  (ports rotation deleted rootIn recognition).symm

include recognition in
theorem inside_connected : (G.induce {v | deletedSideKeep deleted v}).Connected := by
  have h := OpenTangleVertexSideReturn.induce_connected rotation.toRotationSystem
    (deletedSideKeep deleted) rootIn (recognition.connected piece_connected)
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using h

theorem reassembled_class (h : BridgelessSphericalCubicMapData rotation.toRotationSystem) :
    BridgelessSphericalCubicMapData ((outside rotation deleted rootOut).composeRotationSystem piece
      (ports rotation deleted rootIn recognition).symm) := by
  exact recognition.symm.sewn_class (outside rotation deleted rootOut)
    (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted)
    (VertexSideExactReassembly.mapClass rotation.toRotationSystem deleted rootOut rootIn h)

theorem reassembled_colorable_iff :
    RotationSystemTaitColorable ((outside rotation deleted rootOut).composeRotationSystem piece
      (ports rotation deleted rootIn recognition).symm) ↔
      RotationSystemTaitColorable rotation.toRotationSystem := by
  have h := recognition.sewn_colorable_iff (outside rotation deleted rootOut)
    (ports rotation deleted rootIn recognition).symm
  have hm : (ports rotation deleted rootIn recognition).symm.trans recognition.boundary =
      complementBoundaryAlphaEquiv rotation.toRotationSystem deleted := by
    apply Equiv.ext
    intro b
    simp [ports]
  rw [hm] at h
  exact h.trans (rotationSystemTaitColorable_complementaryComposite_iff
    rotation.toRotationSystem deleted rootOut rootIn)

variable (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
  (hout : (G.induce {v | deletedRegionKeep deleted v}).Connected)

include h htwo hout in
/-- The exterior order is derived from the recognized patch and the planar
bond theorem, with the opposite orientation accounted for explicitly. -/
theorem exterior_order :
    (ports rotation deleted rootIn recognition).permCongr (finRotate 6) =
      (retainedRegionBoundarySuccessor rotation.toRotationSystem (deletedRegionKeep deleted))⁻¹ := by
  let RS := rotation.toRotationSystem
  let m := complementBoundaryAlphaEquiv RS deleted
  let si := retainedRegionBoundarySuccessor RS (deletedSideKeep deleted)
  let so := retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted)
  have hc : portCycle = finRotate 6 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hi : recognition.boundary.permCongr (finRotate 6) = si := by
    rw [← hc, ← piece_returnCode, recognition.returnCode,
      OpenTangleVertexSideReturn.returnCode_eq]
  have hi' (i : Fin 6) : si (recognition.boundary i) = recognition.boundary (finRotate 6 i) := by
    have hi' := Equiv.congr_fun hi (recognition.boundary i)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using hi'.symm
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hop := boundarySuccessors_opposite_of_planarBond rotation deleted h.spherical htwo hg
    h.vertexRotationCyclic hout (inside_connected rotation deleted rootIn recognition)
  let order := ports rotation deleted rootIn recognition
  apply Equiv.ext
  intro b
  apply so.injective
  change so (order (finRotate 6 (order.symm b))) = so (so.symm b)
  rw [Equiv.apply_symm_apply]
  apply m.injective
  apply si.injective
  calc
    si (m (so (order (finRotate 6 (order.symm b))))) = m (order (finRotate 6 (order.symm b))) :=
      hop _
    _ = recognition.boundary (finRotate 6 (order.symm b)) := by simp [order, ports, m, RS]
    _ = si (recognition.boundary (order.symm b)) := (hi' _).symm
    _ = si (m b) := by simp [order, ports, m, RS]

include htwo hout in
theorem exterior_noncrossing
    (c : PortTangle.Coloring (openExteriorTangle (outside rotation deleted rootOut)))
    (hc : IsProper c) (pair : TaitColorPair) :
    IsNoncrossingMatching (orderedPhysicalMate (ports rotation deleted rootIn recognition)
      (openExteriorTangle (outside rotation deleted rootOut))
      (isCubic_vertexSidePortTangle rotation (deletedRegionKeep deleted) rootOut h.spherical.cubic)
      c hc pair) := by
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem h.spherical.cubic
    h.primalConnected h.vertexRotationCyclic
  exact SixPortBoundaryReflection.orderedPhysicalMate_isNoncrossing_inverse rotation htwo hdual hg
    h.spherical h.spherical.cubic h.vertexRotationCyclic (deletedRegionKeep deleted)
    (inside_connected rotation deleted rootIn recognition) (ports rotation deleted rootIn recognition)
    (exterior_order rotation deleted rootIn recognition h htwo hout) rootOut c hc pair

include recognition in
/-- Count all surviving vertices and all four introduced tree vertices. -/
theorem size_decrease : Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + 12 =
    Fintype.card V := by
  have he := Fintype.card_congr ((Equiv.sumCongr (Equiv.refl {v : V // deletedRegionKeep deleted v})
    recognition.vertex).trans (complementaryVertexEquiv deleted))
  simp only [Fintype.card_sum, Fintype.card_fin] at he ⊢
  omega

include h htwo hout in
/-- One exact occurrence yields a strict reduction in the original ambient
map. No arbitrary-support, Kempe-closure or noncrossing assumption remains. -/
theorem strict_reduction :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + 12 = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation deleted rootOut rootIn recognition) ∧
      (RotationSystemTaitColorable (smaller rotation deleted rootOut rootIn recognition) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hs := size_decrease rotation deleted rootIn recognition
  have hout' : (sideMultigraph (outside rotation deleted rootOut)).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using hout
  refine ⟨hs, by omega, tree_replacement_class (outside rotation deleted rootOut)
    (ports rotation deleted rootIn recognition).symm hout'
    (reassembled_class rotation deleted rootOut rootIn recognition h), ?_⟩
  intro hc
  apply (reassembled_colorable_iff rotation deleted rootOut rootIn recognition).mp
  exact open_reconstruct_from_tree (outside rotation deleted rootOut)
    (ports rotation deleted rootIn recognition)
    (isCubic_vertexSidePortTangle rotation (deletedRegionKeep deleted) rootOut h.spherical.cubic)
    (exterior_noncrossing rotation deleted rootOut rootIn recognition h htwo hout) hc

include rootOut recognition h htwo hout in
/-- Minimality supplies the actual smaller-map colouring. -/
theorem colorable_of_smallerColorable
    (hminimal : ∀ {V' E' : Type u} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
      (candidate : RotationSystem.{u,u,u} V' E'), Fintype.card V' < Fintype.card V →
        BridgelessSphericalCubicMapData candidate → RotationSystemTaitColorable candidate) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  obtain ⟨_, hlt, hs, hr⟩ := strict_reduction rotation deleted rootOut rootIn recognition h htwo hout
  exact hr (hminimal (smaller rotation deleted rootOut rootIn recognition) hlt hs)

include rootOut recognition hout in
/-- A vertex-minimal counterexample cannot contain a recognized occurrence
with connected exterior. The geometric occurrence has no colouring fields. -/
theorem not_in_minimal_counterexample
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  minimal.notColorable (colorable_of_smallerColorable rotation deleted rootOut rootIn recognition
    minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided hout minimal.smallerColorable)

end
end Embedded
end FourColor.PentagonalLobePatch.Tangle
