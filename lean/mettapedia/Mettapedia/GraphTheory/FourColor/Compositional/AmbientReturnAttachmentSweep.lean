import Mettapedia.GraphTheory.CubicPathChordDiagram
import Mettapedia.GraphTheory.Embedding.CubicPathChord
import Mettapedia.GraphTheory.FourColor.Compositional.PathChordSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnChordSeparator

/-!
# Two-stack sweeps of attachments along ambient residual returns

The strict internal vertices of an ambient residual-return path have one
third edge each.  Internal returning edges form a partial matching by
cubicity.  The two local rotation turns split that matching into two planar
noncrossing families, so each family has a literal LIFO sweep.

Edges leaving the path and chords incident to either path endpoint are not
put into these stacks.  They remain explicit escape and boundary horns for
the geometric descent; the construction does not silently assume that a
partial attachment relation is total.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentSweep

open CubicPathAttachment
open CubicPathChordDiagram
open CubicPathRotation
open GoertzelV24FaceDualConnectedness
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.Embedding
open PathChordSweep
open ResidualReturnChordSeparator
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Crossing internal chords of one ambient return necessarily have opposite
local attachment turns.  This is the pointwise exact-face-cut theorem applied
to the finite coordinate diagram of the ambient path. -/
theorem attachmentTurn_ne_of_crosses_internalChords
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < returnChord.right.val - returnChord.left.val)
    (first second : OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hfirst : IsInternalChord first) (hsecond : IsInternalChord second)
    (hcrosses : first.Crosses second) :
    attachmentTurn rotation
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG)
        (leftPosition first hfirst) ≠
      attachmentTurn rotation
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG)
        (leftPosition second hsecond) := by
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site returnChord
  let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  let closure := ambientReturnPathCycleClosure
    hG sigma hSigma site returnChord hlong
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem
    minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  rcases hcrosses with hright | hleft
  · let selected := leftAttachment hpath hregular first hfirst
    let other := leftAttachment hpath hregular second hsecond
    rcases exists_exactFaceCut_of_ambientReturnChord
        rotation minimal.facesTwoSided hdual hconnected minimal.spherical
        hG sigma hSigma site returnChord (leftPosition first hfirst)
          selected with ⟨cut, _hlinear⟩
    have hexact : ∀ dart : rotation.toRotationSystem.D,
        cut.label (GoertzelV24FaceOrbitIncidence.dartOrbitFace
            rotation.toRotationSystem dart) ≠
            cut.label (GoertzelV24FaceOrbitIncidence.dartOrbitFace
              rotation.toRotationSystem
                (rotation.toRotationSystem.alpha dart)) ↔
          (rotation.toRotationSystem.edgeOf dart).1 ∈
            (selected.boundary hpath hregular
              (leftPosition first hfirst)).cycleWalk.edges := by
      intro dart
      exact (cut.separates dart).trans (by
        simpa [ambientReturnChordBoundary] using
          (SamePathChordBoundary.mem_wall_iff_mem_cycleWalk_edges
            (selected.boundary hpath hregular (leftPosition first hfirst))
            (rotation.toRotationSystem.edgeOf dart)))
    have hselectedCoordinates : selected.orderedCoordinates hpath hregular
        (leftPosition first hfirst) = first := by
      simpa only [selected] using
        leftAttachment_orderedCoordinates hpath hregular first hfirst
    have hotherCoordinates : other.orderedCoordinates hpath hregular
        (leftPosition second hsecond) = second := by
      simpa only [other] using
        leftAttachment_orderedCoordinates hpath hregular second hsecond
    exact attachmentTurn_ne_of_right_interleaving_exactFaceCut_of_pathCycleClosure
      rotation minimal.vertexRotationCyclic closure hpath hregular
        (leftPosition first hfirst) (leftPosition second hsecond)
        selected other
        (leftAttachment_isLeftEndpoint hpath hregular first hfirst)
        (leftAttachment_isLeftEndpoint hpath hregular second hsecond)
        cut.label hexact
        (by simpa only [hselectedCoordinates, hotherCoordinates] using hright.1)
        (by simpa only [hselectedCoordinates, hotherCoordinates] using hright.2.1)
        (by simpa only [hselectedCoordinates, hotherCoordinates] using hright.2.2)
  · let selected := leftAttachment hpath hregular second hsecond
    let other := leftAttachment hpath hregular first hfirst
    rcases exists_exactFaceCut_of_ambientReturnChord
        rotation minimal.facesTwoSided hdual hconnected minimal.spherical
        hG sigma hSigma site returnChord (leftPosition second hsecond)
          selected with ⟨cut, _hlinear⟩
    have hexact : ∀ dart : rotation.toRotationSystem.D,
        cut.label (GoertzelV24FaceOrbitIncidence.dartOrbitFace
            rotation.toRotationSystem dart) ≠
            cut.label (GoertzelV24FaceOrbitIncidence.dartOrbitFace
              rotation.toRotationSystem
                (rotation.toRotationSystem.alpha dart)) ↔
          (rotation.toRotationSystem.edgeOf dart).1 ∈
            (selected.boundary hpath hregular
              (leftPosition second hsecond)).cycleWalk.edges := by
      intro dart
      exact (cut.separates dart).trans (by
        simpa [ambientReturnChordBoundary] using
          (SamePathChordBoundary.mem_wall_iff_mem_cycleWalk_edges
            (selected.boundary hpath hregular (leftPosition second hsecond))
            (rotation.toRotationSystem.edgeOf dart)))
    have hselectedCoordinates : selected.orderedCoordinates hpath hregular
        (leftPosition second hsecond) = second := by
      simpa only [selected] using
        leftAttachment_orderedCoordinates hpath hregular second hsecond
    have hotherCoordinates : other.orderedCoordinates hpath hregular
        (leftPosition first hfirst) = first := by
      simpa only [other] using
        leftAttachment_orderedCoordinates hpath hregular first hfirst
    exact (attachmentTurn_ne_of_right_interleaving_exactFaceCut_of_pathCycleClosure
      rotation minimal.vertexRotationCyclic closure hpath hregular
        (leftPosition second hsecond) (leftPosition first hfirst)
        selected other
        (leftAttachment_isLeftEndpoint hpath hregular second hsecond)
        (leftAttachment_isLeftEndpoint hpath hregular first hfirst)
        cut.label hexact
        (by simpa only [hselectedCoordinates, hotherCoordinates] using hleft.1)
        (by simpa only [hselectedCoordinates, hotherCoordinates] using hleft.2.1)
        (by simpa only [hselectedCoordinates, hotherCoordinates] using hleft.2.2)).symm

/-- Total turn label used only to filter the finite chord carrier.  The
fallback value is irrelevant because the selected carrier already consists
of internal chords. -/
def internalChordTurn
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (chord : OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :
    AttachmentTurn :=
  if hchord : IsInternalChord chord then
    attachmentTurn rotation
      (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG)
      (leftPosition chord hchord)
  else
    .backwardToAttachment

@[simp] theorem internalChordTurn_of_isInternalChord
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (chord : OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hchord : IsInternalChord chord) :
    internalChordTurn rotation hG sigma hSigma site returnChord chord =
      attachmentTurn rotation
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG)
        (leftPosition chord hchord) := by
  unfold internalChordTurn
  rw [dif_pos hchord]

/-- The internal chords of one chosen local rotation turn. -/
def turnChords
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (turn : AttachmentTurn) :
    Finset (OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :=
  (internalChords
      (orderedChordAmbientPath hG sigma hSigma site returnChord)).filter
    fun chord =>
      internalChordTurn rotation hG sigma hSigma site returnChord chord = turn

@[simp] theorem mem_turnChords_iff
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (turn : AttachmentTurn)
    (chord : OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :
    chord ∈ turnChords rotation hG sigma hSigma site returnChord turn ↔
      IsInternalChord chord ∧
        internalChordTurn rotation hG sigma hSigma site returnChord chord = turn := by
  simp only [turnChords, Finset.mem_filter, mem_internalChords_iff]

/-- Each turn class is a noncrossing chord diagram. -/
theorem pairwiseNoncrossing_turnChords
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < returnChord.right.val - returnChord.left.val)
    (turn : AttachmentTurn) :
    PairwiseNoncrossing
      (turnChords rotation hG sigma hSigma site returnChord turn) := by
  intro first hfirstMem second hsecondMem _hne hcrosses
  have hfirst := (mem_turnChords_iff rotation hG sigma hSigma site
    returnChord turn first).mp hfirstMem
  have hsecond := (mem_turnChords_iff rotation hG sigma hSigma site
    returnChord turn second).mp hsecondMem
  have hturnNe := attachmentTurn_ne_of_crosses_internalChords rotation minimal
    hG sigma hSigma site returnChord hlong first second hfirst.1 hsecond.1
      hcrosses
  apply hturnNe
  rw [← internalChordTurn_of_isInternalChord rotation hG sigma hSigma site
      returnChord first hfirst.1,
    ← internalChordTurn_of_isInternalChord rotation hG sigma hSigma site
      returnChord second hsecond.1,
    hfirst.2, hsecond.2]

/-- Each turn class inherits the endpoint-disjoint partial-matching property
of all internal chords. -/
theorem pairwiseEndpointDisjoint_turnChords
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (turn : AttachmentTurn) :
    PairwiseEndpointDisjoint
      (turnChords rotation hG sigma hSigma site returnChord turn) := by
  intro first hfirst second hsecond hne
  apply pairwiseEndpointDisjoint_internalChords
    (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG)
      first (Finset.mem_filter.mp hfirst).1
      second (Finset.mem_filter.mp hsecond).1 hne

/-- One turn class, represented as the literal LIFO input used by the finite
sweep theorem. -/
def turnMatching
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < returnChord.right.val - returnChord.left.val)
    (turn : AttachmentTurn) :
    NoncrossingMatching Unit
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1) :=
  noncrossingMatchingOfChordDiagram
    (turnChords rotation hG sigma hSigma site returnChord turn)
    (pairwiseEndpointDisjoint_turnChords rotation hG sigma hSigma site
      returnChord turn)
    (pairwiseNoncrossing_turnChords rotation minimal hG sigma hSigma site
      returnChord hlong turn)
    (fun _ => ())

end

end Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentSweep
