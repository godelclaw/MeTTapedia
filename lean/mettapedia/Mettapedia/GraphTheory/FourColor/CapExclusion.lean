import Mettapedia.GraphTheory.FourColor.DerivableReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeStructuralData
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryShoreBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly
import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubClosure

/-!
# A certified cap excludes its configuration from a least counterexample

Cut a graph-backed vertex-minimal Tait counterexample along a vertex disk with connected
sides.  Sew the outside shore to a *cap*: any open tangle on the same ports which is a
connected, boundary-essential, cubic disc (its hub closure, under the rotation forced by
the shore's boundary order, is a sphere with distinct hub faces).  The stack's seam theorem
puts the sewn map in the minimality class; the derivable-replacement theorem transfers
non-colourability to it; if the cap has fewer vertices than the disk, minimality is
contradicted (`false_of_derivable_cap`).

The cap facts are collected in `CapDiscData` and stay visible: for a concrete cap they are
finite checks, discharged separately.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation
namespace CapExclusion

open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open Compositional.CyclicNoncrossing
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24CanonicalHubClosure
open GoertzelV24ClosedCountReplacement GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity
open GoertzelV24CompositeStructuralData
open GoertzelV24CyclicBondBoundary
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SeamExchange
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideOpenTangle
open GoertzelV24VertexSideReassembly
open SimpleGraph
open SimpleGraphDartRotation

universe u

section Rotation

variable {V : Type*} {E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The hub rotation of a cap glued to the shore of `keep`: the shore's canonical hub
rotation, transported through the port matching and inverted, so that the matching reverses
orientation. -/
noncomputable def capHubRotation (RS : RotationSystem V E) (keep : V → Prop) {R : Type*}
    (matching : BoundaryDart RS keep ≃ R) : Equiv.Perm R :=
  matching.symm.trans ((canonicalHubRotation RS keep).symm.trans matching)

theorem orientationReversing_capHubRotation (RS : RotationSystem V E) (keep : V → Prop)
    {R : Type*} (matching : BoundaryDart RS keep ≃ R) :
    OrientationReversing matching (canonicalHubRotation RS keep)
      (capHubRotation RS keep matching) := by
  intro b
  simp [capHubRotation]

/-- Everything the seam theorem asks of the cap: a connected, boundary-essential, cubic open
tangle with cyclic rotations, whose hub closure under the forced rotation is a sphere with
distinct hub faces. -/
structure CapDiscData (RS : RotationSystem V E) (keep : V → Prop)
    {Y J R : Type*} [Fintype Y] [DecidableEq Y] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R]
    (cap : OpenTangleData Y J R) (matching : BoundaryDart RS keep ≃ R) : Prop where
  cubic : OpenIsCubic cap
  rotation : OpenRotationCyclic cap
  connected : (sideMultigraph cap).Connected
  essential : BoundaryEssential (sideMultigraph cap)
    (fun port : BoundaryDart RS keep => cap.boundaryVert (matching port))
  facesDistinct : HubFacesDistinct cap (capHubRotation RS keep matching)
  spherical : ClosedSideSpherical cap (capHubRotation RS keep matching)

end Rotation

section Exclusion

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

omit [DecidableEq V] in
/-- The shore of a deleted disk has fewer vertices than the map by the disk's size. -/
theorem card_retainedVertex_add_card_deleted (deleted : Finset V) :
    Fintype.card ({ vertex : V // deletedRegionKeep deleted vertex }) + deleted.card =
      Fintype.card V := by
  have hcompl : Fintype.card ({ vertex : V // deletedRegionKeep deleted vertex }) =
      Fintype.card V - Fintype.card {v : V // v ∈ deleted} := by
    unfold deletedRegionKeep
    exact Fintype.card_subtype_compl _
  have hdel : Fintype.card {v : V // v ∈ deleted} = deleted.card :=
    Fintype.card_coe deleted
  have hle : deleted.card ≤ Fintype.card V := Finset.card_le_univ _
  omega

/-- **A certified cap excludes its configuration.**  If every seam word of the cap derives
into the deleted disk's support, the cap is a disc on the shore's ports, and the cap is
smaller than the disk, the map was not a least counterexample. -/
theorem false_of_derivable_cap
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (deleted : Finset V)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | ¬ deletedRegionKeep deleted vertex}).Connected)
    (outerRetained : RetainedDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    {n : Nat} (hn : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (hsuccessor : order.permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem (deletedRegionKeep deleted))
    {Y J R : Type u} [Fintype Y] [DecidableEq Y] [Fintype J] [DecidableEq J]
      [Fintype R] [DecidableEq R]
    (cap : OpenTangleData Y J R)
    (matching : BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted) ≃ R)
    (hdisc : CapDiscData graphData.toRotationSystem (deletedRegionKeep deleted) cap matching)
    (hsmall : Fintype.card Y < deleted.card)
    (hder : ∀ w ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle cap matching)),
      Derivable (wordsOf order (taitInnerSupport (rightClosedPortTangle
        (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
        (complementBoundaryAlphaEquiv graphData.toRotationSystem deleted)))) w) :
    False := by
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hcubic : graphData.toRotationSystem.IsCubic := minimal.spherical.cubic
  have hrotation : VertexRotationCyclic graphData.toRotationSystem :=
    minimal.vertexRotationCyclic
  have hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem hcubic
      minimal.primalConnected hrotation
  -- the original sewn instance is the map itself, hence not colourable
  have hzero : ¬ ∃ coloring : (complementaryCompositeRS graphData.toRotationSystem deleted
        outerRetained outerDeleted).EdgeColoring Color,
      (complementaryCompositeRS graphData.toRotationSystem deleted
        outerRetained outerDeleted).IsTaitEdgeColoring coloring := by
    intro h
    exact minimal.notColorable
      ((rotationSystemTaitColorable_complementaryComposite_iff graphData.toRotationSystem
        deleted outerRetained outerDeleted).1 h)
  -- the sewn instance with the cap is not colourable
  have hnot := not_composeRotationSystem_taitColorable_of_derivable graphData
    minimal.facesTwoSided hdual hconnected minimal.spherical hcubic hrotation
    (deletedRegionKeep deleted) hdeletedConnected hn order hsuccessor outerRetained
    (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
    (complementBoundaryAlphaEquiv graphData.toRotationSystem deleted)
    cap matching hder hzero
  -- it lies in the minimality class
  have hbridgeless : (toMultigraph graphData.toRotationSystem).Bridgeless :=
    (bridgeless_iff_edgeBridgeFree (RS := graphData.toRotationSystem)).2
      minimal.edgeBridgeFree
  have hretainedConnected' :
      ((rotationPrimalGraph graphData.toRotationSystem).induce
        {vertex | deletedRegionKeep deleted vertex}).Connected := by
    simpa [rotationPrimalGraph_toRotationSystem_eq] using hretainedConnected
  haveI : Nonempty ({ vertex : V // deletedRegionKeep deleted vertex }) :=
    ⟨⟨graphData.toRotationSystem.vertOf outerRetained.1, outerRetained.2⟩⟩
  have hne : order ⟨0, by omega⟩ ≠ order ⟨1, by omega⟩ := by
    intro h
    have := order.injective h
    simp [Fin.ext_iff] at this
  have hclass : BridgelessSphericalCubicMapData
      ((ofVertexSide graphData.toRotationSystem (deletedRegionKeep deleted)
        outerRetained).composeRotationSystem cap matching) :=
    bridgelessSphericalCubicMapData_composeRotationSystem
      (ofVertexSide graphData.toRotationSystem (deletedRegionKeep deleted) outerRetained)
      cap matching
      (canonicalHubRotation graphData.toRotationSystem (deletedRegionKeep deleted))
      (capHubRotation graphData.toRotationSystem (deletedRegionKeep deleted) matching)
      (sideMultigraph_connected_of_induce_connected graphData.toRotationSystem
        (deletedRegionKeep deleted) outerRetained hretainedConnected')
      hdisc.connected
      (boundaryEssential_ofVertexSide graphData.toRotationSystem
        (deletedRegionKeep deleted) outerRetained hbridgeless)
      hdisc.essential
      (order ⟨0, by omega⟩) (order ⟨1, by omega⟩) hne
      (openIsCubic_ofVertexSide graphData.toRotationSystem
        (deletedRegionKeep deleted) outerRetained hcubic)
      hdisc.cubic
      (openRotationCyclic_ofVertexSide graphData.toRotationSystem
        (deletedRegionKeep deleted) outerRetained hrotation)
      hdisc.rotation
      (hubFacesDistinct_canonical graphData.toRotationSystem
        (deletedRegionKeep deleted) outerRetained)
      hdisc.facesDistinct
      (orientationReversing_capHubRotation graphData.toRotationSystem
        (deletedRegionKeep deleted) matching)
      (closedSideSpherical_canonical_of_planarBond graphData deleted outerRetained
        minimal.spherical minimal.facesTwoSided hconnected hrotation
        hretainedConnected hdeletedConnected)
      hdisc.spherical
  -- and it is strictly smaller
  have hcard : Fintype.card ({ vertex : V // deletedRegionKeep deleted vertex } ⊕ Y) <
      Fintype.card V := by
    rw [Fintype.card_sum]
    have := card_retainedVertex_add_card_deleted (V := V) deleted
    omega
  exact hnot (minimal.smallerColorable _ hcard hclass)

end Exclusion

end CapExclusion
end KempeDerivation
end Mettapedia.GraphTheory.FourColor
