import MettapediaFourColor.PentagonalLobeMinimalExterior
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementClass

/-!
# A shared six-port reduction scheme

An actual open piece supplies its boundary repair, connectedness, face-return
order and Euler mass. One theorem then replaces any recognized occurrence by
the same four-vertex tree and reconstructs a genuine colouring in its context.
The source piece's size is explicit in the whole-map count.
-/

namespace FourColor.SixPortTreeReplacement

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
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open PentagonalLobePatch.Tangle

noncomputable section
universe u

/-- The independently proved obligations consumed by a six-port replacement. -/
structure Scheme (n m : ℕ) where
  piece : OpenTangleData (Fin n) (Fin m) (Fin 6)
  size : 4 < n
  connected : (sideMultigraph piece).Connected
  return_eq : returnCode piece = portCycle
  euler_eq : eulerMass piece = 4
  repair : KempeBoundarySplit.Repairs (OpenTrace piece (Equiv.refl _)) 6

variable {n m : ℕ} (S : Scheme n m)

section Context
variable {W J B : Type u}
  [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData W J B) (seam : Fin 6 ≃ B)

/-- The final two witnesses agree jointly on every port. -/
theorem open_colorable
    (hcubic : IsCubic (openExteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (openExteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair), IsNoncrossingMatching
        (orderedPhysicalMate seam (openExteriorTangle outside) hcubic c hc pair))
    (r : J ⊕ B → Mettapedia.GraphTheory.FourColor.Color)
    (hr : OpenTangleClosedWitness.IsColor outside r) :
    RotationSystemTaitColorable (outside.composeRotationSystem S.piece seam.symm) := by
  let c : PortTangle.Coloring (openExteriorTangle outside) := ⟨r, hr.1⟩
  have hc : IsProper c := ⟨hr.2.2, fun d e hv hn => hr.2.1 hv hn⟩
  let w := orderedProperBoundaryWord seam c hc
  have hw := orderedProperBoundaryWord_mem_orderedTaitSupport seam (openExteriorTangle outside) c hc
  have ht : PhysicalKempeBoundary.Trace
      (orderedTaitSupport seam (openExteriorTangle outside)) (PhysicalKempeBoundary.encode w) :=
    ⟨w, hw, rfl⟩
  obtain ⟨hlen, hzero, hsum⟩ := PhysicalKempeBoundary.trace_valid seam _ hcubic ht
  obtain ⟨et, ⟨l, hl, hel⟩, r', hr', her⟩ := S.repair _ hlen hzero hsum
    (OpenTrace outside seam) (open_exterior_closed outside seam hcubic hnoncrossing)
    ((openTrace_iff outside seam _).mp ht)
  have hm (i : Fin 6) : l (.inr i) = r' (.inr (seam i)) :=
    List.map_inj_left.mp (hel.trans her.symm) i (List.mem_finRange i)
  obtain ⟨result, hresult, _⟩ := OpenTangleClosedWitness.glueOpen outside S.piece seam.symm
    r' l hr' hl (fun b => by simpa only [Equiv.apply_symm_apply] using (hm (seam.symm b)).symm)
  exact ⟨result, hresult⟩

theorem open_reconstruct_from_tree
    (hcubic : IsCubic (openExteriorTangle outside))
    (hnoncrossing : ∀ (c : PortTangle.Coloring (openExteriorTangle outside)) (hc : IsProper c)
      (pair : TaitColorPair), IsNoncrossingMatching
        (orderedPhysicalMate seam (openExteriorTangle outside) hcubic c hc pair))
    (hc : RotationSystemTaitColorable (outside.composeRotationSystem Tree.piece seam.symm)) :
    RotationSystemTaitColorable (outside.composeRotationSystem S.piece seam.symm) := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨r, _, hr, _, _, _⟩ := OpenTangleClosedWitness.restrictOpen outside Tree.piece seam.symm c hc
  exact open_colorable S outside seam hcubic hnoncrossing r hr

end Context

section Geometry
variable {W J B : Type*}
  [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData W J B) (seam : B ≃ Fin 6)

theorem tree_replacement_euler :
    OpenTangleRewireFaces.compositeEuler outside S.piece seam =
      OpenTangleRewireFaces.compositeEuler outside Tree.piece seam := by
  apply (euler_eq_iff_mass S.piece Tree.piece
    (S.return_eq.trans tree_returnCode.symm) outside seam).mpr
  exact S.euler_eq.trans tree_eulerMass.symm

theorem tree_replacement_class
    (hout : (sideMultigraph outside).Connected)
    (h : BridgelessSphericalCubicMapData (outside.composeRotationSystem S.piece seam)) :
    BridgelessSphericalCubicMapData (outside.composeRotationSystem Tree.piece seam) := by
  exact OpenTangleReplacementClass.mapClass outside S.piece Tree.piece seam
    (S.return_eq.trans tree_returnCode.symm) (S.euler_eq.trans tree_eulerMass.symm)
    Tree.cubic Tree.cyclic hout Tree.connected
    (OpenTangleConnectedReplacement.essential_of_surjective (sideMultigraph Tree.piece)
      (Tree.piece.boundaryVert ∘ seam) (Tree.ports_surjective.comp seam.surjective))
    (p := seam.symm 0) (q := seam.symm 1)
    (by intro he; have := seam.symm.injective he; exact (by decide : (0 : Fin 6) ≠ 1) this) h
end Geometry

namespace Embedded
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable {n m : ℕ} (S : Scheme n m)

variable (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
  (rootOut : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
  (rootIn : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (recognition : OpenTangleIsomorphism.Iso S.piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) rootIn))

abbrev outside := ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) rootOut

/-- Read each port's actual mate across the cut, in the literal patch coordinates. -/
def ports := recognition.boundary.trans (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).symm

abbrev smaller := (outside rotation deleted rootOut).composeRotationSystem Tree.piece
  (ports S rotation deleted rootIn recognition).symm

include recognition in
theorem inside_connected : (G.induce {v | deletedSideKeep deleted v}).Connected := by
  have h := OpenTangleVertexSideReturn.induce_connected rotation.toRotationSystem
    (deletedSideKeep deleted) rootIn (recognition.connected S.connected)
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using h

theorem reassembled_class (h : BridgelessSphericalCubicMapData rotation.toRotationSystem) :
    BridgelessSphericalCubicMapData ((outside rotation deleted rootOut).composeRotationSystem S.piece
      (ports S rotation deleted rootIn recognition).symm) := by
  exact recognition.symm.sewn_class (outside rotation deleted rootOut)
    (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted)
    (VertexSideExactReassembly.mapClass rotation.toRotationSystem deleted rootOut rootIn h)

theorem reassembled_colorable_iff :
    RotationSystemTaitColorable ((outside rotation deleted rootOut).composeRotationSystem S.piece
      (ports S rotation deleted rootIn recognition).symm) ↔
      RotationSystemTaitColorable rotation.toRotationSystem := by
  have h := recognition.sewn_colorable_iff (outside rotation deleted rootOut)
    (ports S rotation deleted rootIn recognition).symm
  have hm : (ports S rotation deleted rootIn recognition).symm.trans recognition.boundary =
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
    (ports S rotation deleted rootIn recognition).permCongr (finRotate 6) =
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
    rw [← hc, ← S.return_eq, recognition.returnCode,
      OpenTangleVertexSideReturn.returnCode_eq]
  have hi' (i : Fin 6) : si (recognition.boundary i) = recognition.boundary (finRotate 6 i) := by
    have hi' := Equiv.congr_fun hi (recognition.boundary i)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using hi'.symm
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hop := boundarySuccessors_opposite_of_planarBond rotation deleted h.spherical htwo hg
    h.vertexRotationCyclic hout (inside_connected S rotation deleted rootIn recognition)
  let order := ports S rotation deleted rootIn recognition
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
    IsNoncrossingMatching (orderedPhysicalMate (ports S rotation deleted rootIn recognition)
      (openExteriorTangle (outside rotation deleted rootOut))
      (isCubic_vertexSidePortTangle rotation (deletedRegionKeep deleted) rootOut h.spherical.cubic)
      c hc pair) := by
  have hg : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using h.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem h.spherical.cubic
    h.primalConnected h.vertexRotationCyclic
  exact SixPortBoundaryReflection.orderedPhysicalMate_isNoncrossing_inverse rotation htwo hdual hg
    h.spherical h.spherical.cubic h.vertexRotationCyclic (deletedRegionKeep deleted)
    (inside_connected S rotation deleted rootIn recognition) (ports S rotation deleted rootIn recognition)
    (exterior_order S rotation deleted rootIn recognition h htwo hout) rootOut c hc pair

include recognition in
/-- Count all surviving vertices and all four introduced tree vertices. -/
theorem size_decrease : Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + (n - 4) =
    Fintype.card V := by
  have he := Fintype.card_congr ((Equiv.sumCongr (Equiv.refl {v : V // deletedRegionKeep deleted v})
    recognition.vertex).trans (complementaryVertexEquiv deleted))
  simp only [Fintype.card_sum, Fintype.card_fin] at he ⊢
  have := S.size
  omega

include h htwo hout in
/-- One exact occurrence yields a strict reduction in the original ambient
map. No arbitrary-support, Kempe-closure or noncrossing assumption remains. -/
theorem strict_reduction :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) + (n - 4) = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 4) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller S rotation deleted rootOut rootIn recognition) ∧
      (RotationSystemTaitColorable (smaller S rotation deleted rootOut rootIn recognition) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hs := size_decrease S rotation deleted rootIn recognition
  have hn := S.size
  have hout' : (sideMultigraph (outside rotation deleted rootOut)).Connected := by
    apply sideMultigraph_connected_of_induce_connected
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using hout
  refine ⟨hs, by omega, tree_replacement_class S (outside rotation deleted rootOut)
    (ports S rotation deleted rootIn recognition).symm hout'
    (reassembled_class S rotation deleted rootOut rootIn recognition h), ?_⟩
  intro hc
  apply (reassembled_colorable_iff S rotation deleted rootOut rootIn recognition).mp
  exact open_reconstruct_from_tree S (outside rotation deleted rootOut)
    (ports S rotation deleted rootIn recognition)
    (isCubic_vertexSidePortTangle rotation (deletedRegionKeep deleted) rootOut h.spherical.cubic)
    (exterior_noncrossing S rotation deleted rootOut rootIn recognition h htwo hout) hc

include rootOut recognition h htwo hout in
/-- Minimality supplies the actual smaller-map colouring. -/
theorem colorable_of_smallerColorable
    (hminimal : ∀ {V' E' : Type u} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
      (candidate : RotationSystem.{u,u,u} V' E'), Fintype.card V' < Fintype.card V →
        BridgelessSphericalCubicMapData candidate → RotationSystemTaitColorable candidate) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  obtain ⟨_, hlt, hs, hr⟩ := strict_reduction S rotation deleted rootOut rootIn recognition h htwo hout
  exact hr (hminimal (smaller S rotation deleted rootOut rootIn recognition) hlt hs)

include rootOut recognition hout in
/-- A vertex-minimal counterexample cannot contain a recognized occurrence
with connected exterior. The geometric occurrence has no colouring fields. -/
theorem not_in_minimal_counterexample
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False :=
  minimal.notColorable (colorable_of_smallerColorable S rotation deleted rootOut rootIn recognition
    minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided hout minimal.smallerColorable)

open GoertzelV24CubicSmallBoundaryCycle GoertzelV24ThreeEdgeCutMinimality
open MatchingBoundaryConnectivity

include recognition in
theorem inside_hasCycle (hcubic : rotation.toRotationSystem.IsCubic) :
    HasCycleOnSide G (deletedSideKeep deleted) := by
  classical
  have hs := Fintype.card_congr recognition.vertex
  simp only [Fintype.card_fin] at hs
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedSideKeep deleted)).trans recognition.boundary.symm)
  simp only [Fintype.card_fin] at hb
  have hn := S.size
  apply SixPortBoundaryConnectivity.hasCycle_of_boundary_card_lt_card_add_two
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hcubic) v))
    (deletedSideKeep deleted) (inside_connected S rotation deleted rootIn recognition)
  omega

include recognition in
/-- Three exterior vertices suffice; their attachment endpoints may coincide. -/
theorem exterior_connected
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hspace : n + 3 ≤ Fintype.card V) :
    (G.induce {v | deletedRegionKeep deleted v}).Connected := by
  classical
  have hsize := size_decrease S rotation deleted rootIn recognition
  simp only [Fintype.card_sum, Fintype.card_fin] at hsize
  have hn := S.size
  have hb := Fintype.card_congr
    ((crossingBoundaryEquiv rotation (deletedRegionKeep deleted)).trans
      (ports S rotation deleted rootIn recognition).symm)
  simp only [Fintype.card_fin] at hb
  apply SixPortBoundaryConnectivity.connected_of_two_lt_card_of_boundary_card_le_six
    (deletedRegionKeep deleted)
    (fun v => (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hcubic) v)) hcyclic
  · exact inside_hasCycle S rotation deleted rootIn recognition hcubic
  · omega
  · omega

include recognition in
theorem not_in_minimal_counterexample_of_recognition (hn : n ≤ 17)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem minimal.spherical
    (GoertzelV24MinimalFaceSize.orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample
      rotation minimal)
  exact not_in_minimal_counterexample S rotation deleted
    (ports S rotation deleted rootIn recognition 0).1 rootIn recognition
    (exterior_connected S rotation deleted rootIn recognition minimal.spherical.cubic
      (cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample rotation minimal)
      (by omega)) minimal

end Embedded

end
end FourColor.SixPortTreeReplacement
