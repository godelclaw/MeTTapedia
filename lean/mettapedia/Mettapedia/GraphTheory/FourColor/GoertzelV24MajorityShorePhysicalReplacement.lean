import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreNormalizedState
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleBoundaryReindexColor

/-!
# Physical replacement by inclusion of normalized colour supports

This is the consumer-facing M2 adapter.  It keeps three logically separate
facts visible: inclusion of colour supports preserves non-colorability, a strict
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

/-- **Semantic half of M2.**  Inclusion of normalized supports replaces the old inner
majority shore by the new one while preserving non-Tait-colorability of the
literal physical composite.  Boundary reindexing is discharged by an exact
dart isomorphism, rather than treated as a semantic convention. -/
theorem not_taitColorable_replacement_of_support_subset
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
    (hsupport : (normalizedState rotation newShore newInnerOuter k newWidth).support ⊆
      (normalizedState rotation oldShore oldInnerOuter k oldWidth).support)
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
  have hsupport' :
      normalizedTaitInnerSupport k newInner newCoordinate ⊆
        normalizedTaitInnerSupport k oldInner oldCoordinate := hsupport
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
    not_composeRotationSystem_taitColorable_of_normalized_subset
      k (outside.reindexBoundary outsideCoordinate.symm)
      oldInner oldCoordinate newInner newCoordinate hsupport' hzeroCoordinateOld
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

/-- Equal-state specialization of one-sided colour-support replacement. -/
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
  exact not_taitColorable_replacement_of_support_subset
    rotation oldShore newShore outsideOuter oldInnerOuter newInnerOuter
    k oldWidth newWidth (congrArg (fun state => state.support) hstate).ge hzero

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
cubic map.  Equality of normalized hub rotations supplies the transported
orientation equation; the two side Euler equalities come independently from
the two ambient planar bonds. -/
def replacementStructuralData_of_normalizedHubRotation_eq
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
    (hhub : (normalizedState rotation oldShore oldInnerOuter k oldWidth).hubRotation =
      (normalizedState rotation newShore newInnerOuter k newWidth).hubRotation)
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
  have hrevNew := GoertzelV24NormalizedSeamState.orientationReversing_replacement
    k (oldExteriorMatching rotation oldShore)
    (canonicalHubRotation RS (majorityDeletedKeep G oldShore))
    (canonicalHubRotation RS (majorityRetainedKeep G oldShore))
    (canonicalHubRotation RS (majorityRetainedKeep G newShore))
    (boundaryCoordinate rotation oldShore k oldWidth)
    (boundaryCoordinate rotation newShore k newWidth)
    hrevOld hhub
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
      hrevNew
      (closedSideSpherical_canonical_deletedSide_of_planarBond
        rotation (majorityDeletedVertices G oldShore) outsideOuter
        hsphere htwoSided hconnected hrotation
        hOldRetainedConnected hOldDeletedConnected)
      (closedSideSpherical_canonical_of_planarBond
        rotation (majorityDeletedVertices G newShore) newInnerOuter
        hsphere htwoSided hconnected hrotation
        hNewRetainedConnected hNewDeletedConnected)

/-- Equal-state specialization of the structural splice. -/
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
  exact replacementStructuralData_of_normalizedHubRotation_eq
    rotation oldShore newShore
    hOldConnected hOldComplementConnected hOldMajorityNonempty hOldComplementNonempty
    hNewConnected hNewComplementConnected hNewMajorityNonempty hNewComplementNonempty
    outsideOuter oldInnerOuter newInnerOuter k oldWidth newWidth
    (congrArg (fun state => state.hubRotation) hstate)
    hsphere htwoSided hconnected hrotation hbridgeless first second hne

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

/-- The literal rotation system obtained by retaining the exterior of the
old shore and the interior of the new shore.  Naming this object keeps the
consumer-facing replacement theorem below from hiding the physical map in a
local proof term. -/
noncomputable abbrev replacementCandidate
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k) :=
  (outsideTangle rotation oldShore outsideOuter).composeRotationSystem
    (innerTangle rotation newShore newInnerOuter)
    (replacementMatching rotation oldShore newShore k oldWidth newWidth)

/-- The complete output of physical support replacement before
minimality is invoked.  It records one literal smaller rotation system, its
full cap-stable structural class, and preservation of zero Count (equivalently
non-Tait-colorability). -/
structure StrictPhysicalReplacementData
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k) : Type u where
  structural : BridgelessSphericalCubicMapData
    (replacementCandidate rotation oldShore newShore outsideOuter
      newInnerOuter k oldWidth newWidth)
  vertexCount_lt :
    Fintype.card
        ({vertex : V // majorityDeletedKeep G oldShore vertex} ⊕
          {vertex : V // majorityRetainedKeep G newShore vertex}) <
      Fintype.card V
  notColorable : ¬ RotationSystemTaitColorable
    (replacementCandidate rotation oldShore newShore outsideOuter
      newInnerOuter k oldWidth newWidth)

/-- **Constructive form of M2.**  Equal hub rotations and inclusion of the new
colour support in the old one on two nested connected literal edge shores
construct a specific strictly smaller
zero-Count map in the same connected, bridgeless, spherical, cubic
rotation-system class.  The theorem returns the map certificate itself;
minimality is not used.

The connected edge-shore hypotheses are the combinatorial planar-bond data
supplied by an actual noose (or directly by a connected branch
decomposition).  All cap orders, orientation reversal, face counting and
physical gluing are derived inside the theorem. -/
noncomputable def strictPhysicalReplacement_of_support_subset
    (rotation : SimpleGraphDartRotation.Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (hfacesTwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
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
    (hhub : (normalizedState rotation oldShore oldInnerOuter k oldWidth).hubRotation =
      (normalizedState rotation newShore newInnerOuter k newWidth).hubRotation)
    (hsupport : (normalizedState rotation newShore newInnerOuter k newWidth).support ⊆
      (normalizedState rotation oldShore oldInnerOuter k oldWidth).support)
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (hne : first ≠ second)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore) :
    StrictPhysicalReplacementData rotation oldShore newShore outsideOuter
      newInnerOuter k oldWidth newWidth := by
  have hgraphConnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
    exact ambient.primalConnected
  have hbridgeless :
      (toMultigraph rotation.toRotationSystem).Bridgeless :=
    (bridgeless_iff_edgeBridgeFree
      (RS := rotation.toRotationSystem)).2 ambient.edgeBridgeFree
  refine
    { structural := ?_
      vertexCount_lt := ?_
      notColorable := ?_ }
  · exact replacementStructuralData_of_normalizedHubRotation_eq
      rotation oldShore newShore
      hOldConnected hOldComplementConnected
      hOldMajorityNonempty hOldComplementNonempty
      hNewConnected hNewComplementConnected
      hNewMajorityNonempty hNewComplementNonempty
      outsideOuter oldInnerOuter newInnerOuter
      k oldWidth newWidth hhub
      ambient.spherical hfacesTwoSided hgraphConnected
      ambient.vertexRotationCyclic hbridgeless first second hne
  · exact replacementVertexCount_lt_of_incident_sdiff
      rotation oldShore newShore hsubset strictVertex hall
      ambient.spherical.cubic
  · exact not_taitColorable_replacement_of_support_subset
      rotation oldShore newShore outsideOuter oldInnerOuter newInnerOuter
      k oldWidth newWidth hsupport hzero

/-- Equal-state specialization of strict physical support replacement. -/
noncomputable def strictPhysicalReplacement_of_normalizedState_eq
    (rotation : SimpleGraphDartRotation.Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (hfacesTwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
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
      edge ∈ oldShore \ newShore) :
    StrictPhysicalReplacementData rotation oldShore newShore outsideOuter
      newInnerOuter k oldWidth newWidth := by
  exact strictPhysicalReplacement_of_support_subset
    rotation ambient hfacesTwoSided hzero oldShore newShore hsubset
    hOldConnected hOldComplementConnected hOldMajorityNonempty hOldComplementNonempty
    hNewConnected hNewComplementConnected hNewMajorityNonempty hNewComplementNonempty
    outsideOuter oldInnerOuter newInnerOuter k oldWidth newWidth
    (congrArg (fun state => state.hubRotation) hstate)
    (congrArg (fun state => state.support) hstate).ge
    first second hne strictVertex hall

/-- **Physical support descent.**  Two connected nested edge shores with
equal normalized hub rotations, the inner support included in the outer
support, and one untouched cubic star in their slab
cannot occur in a graph-backed vertex-minimal Tait counterexample.  The proof
constructs the literal replacement rotation system, proves it lies in the
same cap-stable class, proves it is strictly smaller, and transports zero
Count/non-colorability to it before invoking minimality. -/
theorem no_nested_support_subset_of_strict_material
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
    (hhub : (normalizedState rotation oldShore oldInnerOuter k oldWidth).hubRotation =
      (normalizedState rotation newShore newInnerOuter k newWidth).hubRotation)
    (hsupport : (normalizedState rotation newShore newInnerOuter k newWidth).support ⊆
      (normalizedState rotation oldShore oldInnerOuter k oldWidth).support)
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (hne : first ≠ second)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore) : False := by
  let candidate := replacementCandidate rotation oldShore newShore
    outsideOuter newInnerOuter k oldWidth newWidth
  have replacement := strictPhysicalReplacement_of_support_subset
    rotation minimal.toBridgelessSphericalCubicMapData
    minimal.facesTwoSided minimal.notColorable
    oldShore newShore hsubset
    hOldConnected hOldComplementConnected
    hOldMajorityNonempty hOldComplementNonempty
    hNewConnected hNewComplementConnected
    hNewMajorityNonempty hNewComplementNonempty
    outsideOuter oldInnerOuter newInnerOuter
    k oldWidth newWidth hhub hsupport first second hne strictVertex hall
  exact replacement.notColorable
    (minimal.smallerColorable candidate replacement.vertexCount_lt
      replacement.structural)

/-- Equal-state descent follows from the more general support-inclusion descent. -/
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
  let candidate := replacementCandidate rotation oldShore newShore
    outsideOuter newInnerOuter k oldWidth newWidth
  have replacement := strictPhysicalReplacement_of_normalizedState_eq
    rotation minimal.toBridgelessSphericalCubicMapData
    minimal.facesTwoSided minimal.notColorable
    oldShore newShore hsubset
    hOldConnected hOldComplementConnected
    hOldMajorityNonempty hOldComplementNonempty
    hNewConnected hNewComplementConnected
    hNewMajorityNonempty hNewComplementNonempty
    outsideOuter oldInnerOuter newInnerOuter
    k oldWidth newWidth hstate first second hne strictVertex hall
  exact replacement.notColorable
    (minimal.smallerColorable candidate replacement.vertexCount_lt
      replacement.structural)

end

end GoertzelV24MajorityShorePhysicalReplacement

end Mettapedia.GraphTheory.FourColor
