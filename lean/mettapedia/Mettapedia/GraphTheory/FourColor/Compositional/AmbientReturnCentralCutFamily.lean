import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnSweepBoundedRepeat
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixCyclicCut
import Mettapedia.GraphTheory.FourColor.Compositional.RestrictedPositionMargins

/-!
# Many bounded cyclic cuts from a shallow ambient-return sweep

The physical sweep-width theorem applies at every shallow selected position.
After discarding a fixed margin at both path endpoints, cubic tree counting
promotes every remaining prefix boundary to a cyclic cut with connected
complementary shores.  This file deliberately stops before any pigeonhole:
later repetition must use the complete compositional profile of these actual
cuts, rather than the earlier raw two-stack sweep state.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnCentralCutFamily

open AmbientReturnAttachmentSweep
open AmbientReturnSweepBoundedRepeat
open AmbientReturnSweepInterface
open AmbientReturnSweepWidth
open CubicPathAttachment
open CubicPathChordDiagram
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixCyclicCut
open ResidualReturnPathAttachment
open RestrictedPositionMargins
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The uniform physical cut width supplied by two shallow turn stacks. -/
def physicalSweepBound (depth : Nat) : Nat := 7 + 2 * depth

/-- Central selected positions of one ambient-return sweep. -/
def centralSweepPositions
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (depth : Nat) :
    Finset (Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :=
  withMargins
    (orderedChordAmbientPath hG sigma hSigma site returnChord).length
    (physicalSweepBound depth)
    (eligibleAmbientReturnSweepPositions hG sigma hSigma site returnChord)

/-- A large central family on which both turn stacks are shallow. -/
structure ShallowCentralCutFamilyReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat) where
  many : target <
    (centralSweepPositions hG sigma hSigma site returnChord depth).card
  noExternal : ∀ position : InternalPosition
      (orderedChordAmbientPath hG sigma hSigma site returnChord),
    ¬IsExternalAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position
  stackBound : ∀ family cut,
    cut ∈ centralSweepPositions hG sigma hSigma site returnChord depth →
      (((ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma site
        returnChord closure).family family).stackAt cut).length ≤ depth

theorem ShallowCentralCutFamilyReceipt.mem_eligible
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target)
    {cut} (hcut : cut ∈ centralSweepPositions hG sigma hSigma site returnChord
      depth) :
    cut ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma site
      returnChord := by
  exact (Finset.mem_filter.mp hcut).1

theorem ShallowCentralCutFamilyReceipt.margins
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target)
    {cut} (hcut : cut ∈ centralSweepPositions hG sigma hSigma site returnChord
      depth) :
    physicalSweepBound depth ≤ cut.val ∧
      physicalSweepBound depth ≤
        (orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1 -
          cut.val := by
  exact (Finset.mem_filter.mp hcut).2

/-- Every selected shallow central position has the promised physical width. -/
theorem ShallowCentralCutFamilyReceipt.boundaryWidth
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target)
    {cut} (hcut : cut ∈ centralSweepPositions hG sigma hSigma site returnChord
      depth) :
    (crossingEdgeFinset G
      (pathPrefixSide
        (orderedChordAmbientPath hG sigma hSigma site returnChord) cut)).card ≤
      physicalSweepBound depth := by
  have hpositive := positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma
    hSigma site returnChord cut
      (ShallowCentralCutFamilyReceipt.mem_eligible rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hcut)
  have hphysical := card_ambientReturnPrefixBoundary_le_stack_lengths rotation
    minimal hG sigma hSigma site returnChord closure receipt.noExternal cut
      hpositive
  have hback :
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .backwardToAttachment).stackAt cut).length ≤ depth := by
    simpa [ambientReturnAttachmentSweepData, indexedAttachmentTurn] using
      receipt.stackBound (0 : Fin 2) cut hcut
  have hforward :
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .forwardToAttachment).stackAt cut).length ≤ depth := by
    simpa [ambientReturnAttachmentSweepData, indexedAttachmentTurn] using
      receipt.stackBound (1 : Fin 2) cut hcut
  simp only [physicalSweepBound]
  omega

/-- Every selected shallow central position is a genuine cyclic cut. -/
noncomputable def ShallowCentralCutFamilyReceipt.cyclicCut
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target)
    (cut) (hcut : cut ∈ centralSweepPositions hG sigma hSigma site returnChord
      depth) :
    CyclicEdgeCutRealization G
      (crossingEdgeFinset G
        (pathPrefixSide
          (orderedChordAmbientPath hG sigma hSigma site returnChord) cut)) := by
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  have hpositive := positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma
    hSigma site returnChord cut
      (ShallowCentralCutFamilyReceipt.mem_eligible rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hcut)
  have hmargins := ShallowCentralCutFamilyReceipt.margins rotation minimal hG
    sigma hSigma site returnChord closure depth target receipt hcut
  apply pathPrefixCyclicEdgeCutRealization
    (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) cut hpositive
    (physicalSweepBound depth)
      (ShallowCentralCutFamilyReceipt.boundaryWidth rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hcut)
  · omega
  · omega

/-- Width-preserving saturation gives connected complementary shores at every
selected position. -/
theorem ShallowCentralCutFamilyReceipt.exists_connectedCut
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target)
    (cut) (hcut : cut ∈ centralSweepPositions hG sigma hSigma site returnChord
      depth) :
    Nonempty (CyclicEdgeCutRealization.ConnectedAtWidth G
      (physicalSweepBound depth)) := by
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
    exact minimal.primalConnected
  have hpositive := positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma
    hSigma site returnChord cut
      (ShallowCentralCutFamilyReceipt.mem_eligible rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hcut)
  have hmargins := ShallowCentralCutFamilyReceipt.margins rotation minimal hG
    sigma hSigma site returnChord closure depth target receipt hcut
  exact exists_connectedAtWidth_pathPrefix hconnected
    (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) cut hpositive
    (physicalSweepBound depth)
      (ShallowCentralCutFamilyReceipt.boundaryWidth rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hcut)
      (by omega) (by omega)

/-- A path longer than the endpoint loss, the desired family size, and the
two physical margins yields an exit, a deep stack, or that many bounded
cyclic-cut positions. -/
theorem exists_external_or_deep_or_shallowCentralCutFamily
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (depth target : Nat)
    (hmany : 6 + (target + 2 * physicalSweepBound depth) <
      (orderedChordAmbientPath hG sigma hSigma site returnChord).support.toFinset.card) :
    (∃ position : InternalPosition
        (orderedChordAmbientPath hG sigma hSigma site returnChord),
      IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position) ∨
      ∃ closure : PathCycleClosure
          (orderedChordAmbientPath hG sigma hSigma site returnChord),
        (∃ family cut,
          cut ∈ centralSweepPositions hG sigma hSigma site returnChord depth ∧
          depth <
            (((ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
              site returnChord closure).family family).stackAt cut).length) ∨
        Nonempty (ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
          site returnChord closure depth target) := by
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site returnChord
  let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  by_cases hexternal : ∃ position : InternalPosition path,
      IsExternalAttachment hpath hregular position
  · exact Or.inl hexternal
  · right
    push Not at hexternal
    have hpathLong : 1 < path.length := by
      have hsupport : path.support.toFinset.card = path.length + 1 := by
        rw [List.toFinset_card_of_nodup hpath.support_nodup,
          path.length_support]
      have hlarge : 6 < path.support.toFinset.card := by
        have hmany' : 6 + (target + 2 * physicalSweepBound depth) <
            path.support.toFinset.card := by simpa only [path] using hmany
        omega
      rw [hsupport] at hlarge
      omega
    let closure := ambientReturnPathCycleClosureOfLongPath
      hG sigma hSigma site returnChord hpathLong
    refine ⟨closure, ?_⟩
    let eligible := eligibleAmbientReturnSweepPositions hG sigma hSigma site
      returnChord
    let positions := centralSweepPositions hG sigma hSigma site returnChord depth
    let data := ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
      site returnChord closure
    have heligibleMany : target + 2 * physicalSweepBound depth < eligible.card := by
      have hlower : path.support.toFinset.card - 6 ≤ eligible.card := by
        simpa only [path, eligible] using
          support_card_sub_six_le_eligibleAmbientReturnSweepPositions_card
            hG sigma hSigma site returnChord
      have hmany' : 6 + (target + 2 * physicalSweepBound depth) <
          path.support.toFinset.card := by simpa only [path] using hmany
      omega
    have hpositionsMany : target < positions.card := by
      apply target_lt_card_withMargins_of_add_two_mul_lt
        path.length (physicalSweepBound depth) target eligible
      simpa only [positions, centralSweepPositions, path, eligible] using
        heligibleMany
    by_cases hdeep : ∃ family cut, cut ∈ positions ∧
        depth < ((data.family family).stackAt cut).length
    · exact Or.inl (by simpa only [positions, data] using hdeep)
    · right
      have hbounded : ∀ family cut, cut ∈ positions →
          ((data.family family).stackAt cut).length ≤ depth := by
        intro family cut hcut
        exact Nat.le_of_not_gt (fun hlt => hdeep ⟨family, cut, hcut, hlt⟩)
      exact ⟨⟨by simpa only [positions] using hpositionsMany,
        by simpa only [path, hpath, hregular] using hexternal,
        by simpa only [positions, data] using hbounded⟩⟩

end

end AmbientReturnCentralCutFamily

end Mettapedia.GraphTheory.FourColor.Compositional
