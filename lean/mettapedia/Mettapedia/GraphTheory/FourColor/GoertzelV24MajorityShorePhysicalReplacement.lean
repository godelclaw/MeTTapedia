import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreNormalizedState
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleBoundaryReindexColor

/-!
# Physical replacement at equal normalized majority-shore states

This is the consumer-facing M2 adapter.  It keeps three logically separate
facts visible: the exact Count receipt preserves non-colorability, a strict
majority-shore vertex makes the new carrier smaller, and the two disc sides
with the transported orientation produce the cap-stable structural class.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MajorityShorePhysicalReplacement

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24CanonicalHubClosure
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24NormalizedTaitSupport
open GoertzelV24OpenTangleBoundaryReindexColor
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24FaceDualConnectedness
open GoertzelV24SeamExchange
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideReassembly
open GoertzelV24VertexSideOpenTangle

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The old exterior piece: the literal complement of the old majority
vertex shore. -/
noncomputable abbrev outsideTangle
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore)) :=
  ofVertexSide rotation.toRotationSystem
    (majorityDeletedKeep G oldShore) outer

/-- The old ambient seam, displayed from the exterior toward the old inner
majority shore. -/
noncomputable abbrev oldExteriorMatching
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore : Finset G.edgeSet) :=
  (complementBoundaryAlphaEquiv rotation.toRotationSystem
    (majorityDeletedVertices G oldShore)).symm

/-- The matching to the replacement inner shore obtained by passing through
the common standard coordinates. -/
noncomputable def replacementMatching
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet) (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k) :
    BoundaryDart rotation.toRotationSystem
        (majorityDeletedKeep G oldShore) ≃
      BoundaryDart rotation.toRotationSystem
        (majorityRetainedKeep G newShore) :=
  (oldExteriorMatching rotation oldShore).trans
    ((boundaryCoordinate rotation oldShore k oldWidth).trans
      (boundaryCoordinate rotation newShore k newWidth).symm)

/-- Inverting an orientation-reversing matching and exchanging the two hub
rotations again gives an orientation-reversing matching. -/
theorem orientationReversing_symm
    {L R : Type u} (matching : L ≃ R)
    (ρL : Equiv.Perm L) (ρR : Equiv.Perm R)
    (hrev : OrientationReversing matching ρL ρR) :
    OrientationReversing matching.symm ρR ρL := by
  intro right
  apply matching.injective
  apply ρR.injective
  simpa using hrev (ρL (matching.symm right))

/-- **Semantic half of M2.**  Equal normalized states replace the old inner
majority shore by the new one while preserving non-Tait-colorability of the
literal physical composite.  Boundary reindexing is discharged by an exact
dart isomorphism, rather than treated as a semantic convention. -/
theorem not_taitColorable_replacement_of_normalizedState_eq
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (hstate : normalizedState rotation oldShore oldInnerOuter k oldWidth =
      normalizedState rotation newShore newInnerOuter k newWidth)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem) :
    ¬ RotationSystemTaitColorable
      ((outsideTangle rotation oldShore outsideOuter).composeRotationSystem
        (innerTangle rotation newShore newInnerOuter)
        (replacementMatching rotation oldShore newShore k
          oldWidth newWidth)) := by
  let outside := outsideTangle rotation oldShore outsideOuter
  let oldInner := innerTangle rotation oldShore oldInnerOuter
  let newInner := innerTangle rotation newShore newInnerOuter
  let oldCoordinate := boundaryCoordinate rotation oldShore k oldWidth
  let newCoordinate := boundaryCoordinate rotation newShore k newWidth
  let oldMatching := oldExteriorMatching rotation oldShore
  let outsideCoordinate := oldMatching.trans oldCoordinate
  let newMatching := replacementMatching rotation oldShore newShore k
    oldWidth newWidth
  have hsupport :
      normalizedTaitInnerSupport k oldInner oldCoordinate =
        normalizedTaitInnerSupport k newInner newCoordinate := by
    have := congrArg (fun state => state.support) hstate
    simpa [oldInner, newInner, oldCoordinate, newCoordinate] using this
  have hzeroOld :
      ¬ RotationSystemTaitColorable
        (outside.composeRotationSystem oldInner oldMatching) := by
    intro hcolorable
    apply hzero
    exact (rotationSystemTaitColorable_swappedComplementaryComposite_iff
      rotation.toRotationSystem (majorityDeletedVertices G oldShore)
      outsideOuter oldInnerOuter).1 hcolorable
  have hzeroReindexedOld :
      ¬ RotationSystemTaitColorable
        (reindexedLeftCompositeRS outside oldInner oldMatching
          outsideCoordinate) := by
    intro hcolorable
    exact hzeroOld
      ((rotationSystemTaitColorable_reindexedLeftComposite_iff
        outside oldInner oldMatching outsideCoordinate).1 hcolorable)
  have hmatchingOld :
      outsideCoordinate.symm.trans oldMatching = oldCoordinate.symm := by
    ext port
    simp [outsideCoordinate]
  have hzeroCoordinateOld :
      ¬ RotationSystemTaitColorable
        (OpenTangleData.composeRotationSystem
          (outside.reindexBoundary outsideCoordinate.symm)
          oldInner oldCoordinate.symm) := by
    intro hcolorable
    apply hzeroReindexedOld
    exact (rotationSystemTaitColorable_compose_iff_of_matching_eq
      (outside.reindexBoundary outsideCoordinate.symm) oldInner
      (outsideCoordinate.symm.trans oldMatching) oldCoordinate.symm
      hmatchingOld).2 hcolorable
  have hzeroCoordinateNew :
      ¬ RotationSystemTaitColorable
        (OpenTangleData.composeRotationSystem
          (outside.reindexBoundary outsideCoordinate.symm)
          newInner newCoordinate.symm) :=
    not_composeRotationSystem_taitColorable_of_normalized_eq
      k (outside.reindexBoundary outsideCoordinate.symm)
      oldInner oldCoordinate newInner newCoordinate hsupport hzeroCoordinateOld
  have hmatchingNew :
      outsideCoordinate.symm.trans newMatching = newCoordinate.symm := by
    ext port
    simp [outsideCoordinate, newMatching, replacementMatching,
      oldMatching, oldCoordinate, newCoordinate]
  have hzeroReindexedNew :
      ¬ RotationSystemTaitColorable
        (reindexedLeftCompositeRS outside newInner newMatching
          outsideCoordinate) := by
    intro hcolorable
    apply hzeroCoordinateNew
    exact (rotationSystemTaitColorable_compose_iff_of_matching_eq
      (outside.reindexBoundary outsideCoordinate.symm) newInner
      (outsideCoordinate.symm.trans newMatching) newCoordinate.symm
      hmatchingNew).1 hcolorable
  intro hcolorable
  exact hzeroReindexedNew
    ((rotationSystemTaitColorable_reindexedLeftComposite_iff
      outside newInner newMatching outsideCoordinate).2 hcolorable)

/-- A strict inclusion of the retained predicate, witnessed by a vertex in
the difference, makes the exterior-plus-new-interior vertex carrier strictly
smaller than the ambient carrier. -/
theorem card_complement_add_subtype_lt
    (inner outer : V → Prop)
    (hmono : ∀ {vertex}, inner vertex → outer vertex)
    (strictVertex : V)
    (houter : outer strictVertex) (hinner : ¬ inner strictVertex) :
    Fintype.card ({vertex : V // ¬ outer vertex} ⊕
      {vertex : V // inner vertex}) < Fintype.card V := by
  classical
  let inclusion : {vertex : V // inner vertex} → {vertex : V // outer vertex} :=
    fun vertex => ⟨vertex.1, hmono vertex.2⟩
  have hinclusion : Function.Injective inclusion := by
    intro left right heq
    apply Subtype.ext
    exact congrArg
      (fun vertex : {vertex : V // outer vertex} => vertex.1) heq
  have hnotRange :
      (⟨strictVertex, houter⟩ : {vertex : V // outer vertex}) ∉
        Set.range inclusion := by
    rintro ⟨vertex, hvertex⟩
    apply hinner
    have hvalue : vertex.1 = strictVertex := by
      exact congrArg Subtype.val hvertex
    simpa [hvalue] using vertex.2
  have hstrict :
      Fintype.card {vertex : V // inner vertex} <
        Fintype.card {vertex : V // outer vertex} :=
    Fintype.card_lt_of_injective_of_notMem inclusion hinclusion hnotRange
  rw [Fintype.card_sum, Fintype.card_subtype_compl]
  have houterCard :
      Fintype.card {vertex : V // outer vertex} ≤ Fintype.card V :=
    Fintype.card_subtype_le outer
  omega

/-- **Structural half of M2.**  The exterior of the old majority shore and
the interior of the new majority shore form a connected bridgeless spherical
cubic map.  Equality of normalized states supplies precisely the transported
orientation equation; the two side Euler equalities come independently from
the two ambient planar bonds. -/
def replacementStructuralData_of_normalizedState_eq
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (hOldConnected : EdgeShoreConnected G oldShore)
    (hOldComplementConnected :
      EdgeShoreConnected G (Finset.univ \ oldShore))
    (hOldMajorityNonempty :
      ∃ vertex, majorityVertexSide G oldShore vertex)
    (hOldComplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G oldShore vertex)
    (hNewConnected : EdgeShoreConnected G newShore)
    (hNewComplementConnected :
      EdgeShoreConnected G (Finset.univ \ newShore))
    (hNewMajorityNonempty :
      ∃ vertex, majorityVertexSide G newShore vertex)
    (hNewComplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G newShore vertex)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (hstate : normalizedState rotation oldShore oldInnerOuter k oldWidth =
      normalizedState rotation newShore newInnerOuter k newWidth)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hbridgeless :
      (toMultigraph rotation.toRotationSystem).Bridgeless)
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (hne : first ≠ second) :
    BridgelessSphericalCubicMapData
      ((outsideTangle rotation oldShore outsideOuter).composeRotationSystem
        (innerTangle rotation newShore newInnerOuter)
        (replacementMatching rotation oldShore newShore k
          oldWidth newWidth)) := by
  let RS := rotation.toRotationSystem
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation hsphere.cubic
  have hOldShores := connected_majority_shores_and_width
    hcubicEdges oldShore hOldConnected hOldComplementConnected
      hOldMajorityNonempty hOldComplementNonempty
  have hNewShores := connected_majority_shores_and_width
    hcubicEdges newShore hNewConnected hNewComplementConnected
      hNewMajorityNonempty hNewComplementNonempty
  have hOldRetainedConnected :
      (G.induce {vertex | majorityRetainedKeep G oldShore vertex}).Connected := by
    have hset :
        {vertex | majorityRetainedKeep G oldShore vertex} =
          {vertex | majorityVertexSide G oldShore vertex} := by
      ext vertex
      exact majorityRetainedKeep_iff oldShore vertex
    rw [hset]
    exact hOldShores.1
  have hOldDeletedConnected :
      (G.induce {vertex | majorityDeletedKeep G oldShore vertex}).Connected := by
    have hset :
        {vertex | majorityDeletedKeep G oldShore vertex} =
          {vertex | ¬ majorityVertexSide G oldShore vertex} := by
      ext vertex
      exact majorityDeletedKeep_iff oldShore vertex
    rw [hset]
    exact hOldShores.2.1
  have hNewRetainedConnected :
      (G.induce {vertex | majorityRetainedKeep G newShore vertex}).Connected := by
    have hset :
        {vertex | majorityRetainedKeep G newShore vertex} =
          {vertex | majorityVertexSide G newShore vertex} := by
      ext vertex
      exact majorityRetainedKeep_iff newShore vertex
    rw [hset]
    exact hNewShores.1
  have hNewDeletedConnected :
      (G.induce {vertex | majorityDeletedKeep G newShore vertex}).Connected := by
    have hset :
        {vertex | majorityDeletedKeep G newShore vertex} =
          {vertex | ¬ majorityVertexSide G newShore vertex} := by
      ext vertex
      exact majorityDeletedKeep_iff newShore vertex
    rw [hset]
    exact hNewShores.2.1
  have hOldDeletedConnectedRS :
      ((rotationPrimalGraph RS).induce
        {vertex | majorityDeletedKeep G oldShore vertex}).Connected := by
    simpa [RS,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hOldDeletedConnected
  have hNewRetainedConnectedRS :
      ((rotationPrimalGraph RS).induce
        {vertex | majorityRetainedKeep G newShore vertex}).Connected := by
    simpa [RS,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hNewRetainedConnected
  have hrevOldForward :=
    orientationReversing_canonicalHubRotation_of_planarBond
      rotation (majorityDeletedVertices G oldShore)
      hsphere htwoSided hconnected hrotation
      hOldRetainedConnected hOldDeletedConnected
  have hrevOld : OrientationReversing
      (oldExteriorMatching rotation oldShore)
      (canonicalHubRotation RS (majorityDeletedKeep G oldShore))
      (canonicalHubRotation RS (majorityRetainedKeep G oldShore)) :=
    orientationReversing_symm
      (complementBoundaryAlphaEquiv RS
        (majorityDeletedVertices G oldShore))
      (canonicalHubRotation RS (majorityRetainedKeep G oldShore))
      (canonicalHubRotation RS (majorityDeletedKeep G oldShore))
      hrevOldForward
  have hreceipt := replacement_receipt_of_normalizedState_eq
    rotation oldShore newShore oldInnerOuter newInnerOuter
    k oldWidth newWidth (oldExteriorMatching rotation oldShore)
    (canonicalHubRotation RS (majorityDeletedKeep G oldShore))
    hrevOld hstate
  exact bridgelessSphericalCubicMapData_ofVertexSides
      RS (majorityDeletedKeep G oldShore)
      (majorityRetainedKeep G newShore)
      outsideOuter newInnerOuter
      (replacementMatching rotation oldShore newShore k oldWidth newWidth)
      (canonicalHubRotation RS (majorityDeletedKeep G oldShore))
      (canonicalHubRotation RS (majorityRetainedKeep G newShore))
      hOldDeletedConnectedRS hNewRetainedConnectedRS hbridgeless
      first second hne hsphere.cubic hrotation
      (hubFacesDistinct_canonical RS
        (majorityDeletedKeep G oldShore) outsideOuter)
      (hubFacesDistinct_canonical RS
        (majorityRetainedKeep G newShore) newInnerOuter)
      hreceipt.1
      (closedSideSpherical_canonical_deletedSide_of_planarBond
        rotation (majorityDeletedVertices G oldShore) outsideOuter
        hsphere htwoSided hconnected hrotation
        hOldRetainedConnected hOldDeletedConnected)
      (closedSideSpherical_canonical_of_planarBond
        rotation (majorityDeletedVertices G newShore) newInnerOuter
        hsphere htwoSided hconnected hrotation
        hNewRetainedConnected hNewDeletedConnected)

/-- A vertex whose complete cubic star lies in the edge slab between two
nested shores witnesses strict material loss in the physical replacement. -/
theorem replacementVertexCount_lt_of_incident_sdiff
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (hsubset : newShore ⊆ oldShore)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore)
    (hcubic : rotation.toRotationSystem.IsCubic) :
    Fintype.card
        ({vertex : V // majorityDeletedKeep G oldShore vertex} ⊕
          {vertex : V // majorityRetainedKeep G newShore vertex}) <
      Fintype.card V := by
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation hcubic
  have hstrict := strict_majority_material_of_incident_sdiff
    hcubicEdges (A := newShore) (B := oldShore)
      (vertex := strictVertex) hall
  have hcard := card_complement_add_subtype_lt
    (inner := majorityVertexSide G newShore)
    (outer := majorityVertexSide G oldShore)
    (fun hvertex => majorityVertexSide_mono hsubset hvertex)
    strictVertex hstrict.1 hstrict.2
  simpa only [majorityDeletedKeep_iff, majorityRetainedKeep_iff] using hcard

/-- **Physical equal-state descent.**  Two connected nested edge shores with
equal canonical normalized states and one untouched cubic star in their slab
cannot occur in a graph-backed vertex-minimal Tait counterexample.  The proof
constructs the literal replacement rotation system, proves it lies in the
same cap-stable class, proves it is strictly smaller, and transports zero
Count/non-colorability to it before invoking minimality. -/
theorem no_nested_equal_normalizedState_of_strict_material
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (oldShore newShore : Finset G.edgeSet)
    (hsubset : newShore ⊆ oldShore)
    (hOldConnected : EdgeShoreConnected G oldShore)
    (hOldComplementConnected :
      EdgeShoreConnected G (Finset.univ \ oldShore))
    (hOldMajorityNonempty :
      ∃ vertex, majorityVertexSide G oldShore vertex)
    (hOldComplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G oldShore vertex)
    (hNewConnected : EdgeShoreConnected G newShore)
    (hNewComplementConnected :
      EdgeShoreConnected G (Finset.univ \ newShore))
    (hNewMajorityNonempty :
      ∃ vertex, majorityVertexSide G newShore vertex)
    (hNewComplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G newShore vertex)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (hstate : normalizedState rotation oldShore oldInnerOuter k oldWidth =
      normalizedState rotation newShore newInnerOuter k newWidth)
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (hne : first ≠ second)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore) : False := by
  let candidate :=
    (outsideTangle rotation oldShore outsideOuter).composeRotationSystem
      (innerTangle rotation newShore newInnerOuter)
      (replacementMatching rotation oldShore newShore k oldWidth newWidth)
  have hgraphConnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
    exact minimal.primalConnected
  have hbridgeless :
      (toMultigraph rotation.toRotationSystem).Bridgeless :=
    (bridgeless_iff_edgeBridgeFree
      (RS := rotation.toRotationSystem)).2 minimal.edgeBridgeFree
  have hcandidate : BridgelessSphericalCubicMapData candidate :=
    replacementStructuralData_of_normalizedState_eq
      rotation oldShore newShore
      hOldConnected hOldComplementConnected
      hOldMajorityNonempty hOldComplementNonempty
      hNewConnected hNewComplementConnected
      hNewMajorityNonempty hNewComplementNonempty
      outsideOuter oldInnerOuter newInnerOuter
      k oldWidth newWidth hstate
      minimal.spherical minimal.facesTwoSided hgraphConnected
      minimal.vertexRotationCyclic hbridgeless first second hne
  have hsmall :
      Fintype.card
          ({vertex : V // majorityDeletedKeep G oldShore vertex} ⊕
            {vertex : V // majorityRetainedKeep G newShore vertex}) <
        Fintype.card V :=
    replacementVertexCount_lt_of_incident_sdiff
      rotation oldShore newShore hsubset strictVertex hall
      minimal.spherical.cubic
  have hzero : ¬ RotationSystemTaitColorable candidate :=
    not_taitColorable_replacement_of_normalizedState_eq
      rotation oldShore newShore outsideOuter oldInnerOuter newInnerOuter
      k oldWidth newWidth hstate minimal.notColorable
  exact hzero (minimal.smallerColorable candidate hsmall hcandidate)

end

end GoertzelV24MajorityShorePhysicalReplacement

end Mettapedia.GraphTheory.FourColor
