import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentSweep
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixBoundary

/-!
# Width represented by the ambient-return attachment sweep

The two LIFO stacks along an ambient residual-return path are not merely a
finite code.  Together they enumerate exactly the internal path chords open
at the sweep cut.  This file records that representation theorem before any
vertex-side or colouring semantics are added.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

set_option maxHeartbeats 1000000

namespace AmbientReturnSweepWidth

open AmbientReturnAttachmentSweep
open CubicPathAttachment
open CubicPathChordDiagram
open CubicPathRotation
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathChordSweep
open PathPrefixBoundary
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two local rotation turns partition the open internal chords. -/
theorem openInternalChords_eq_turn_union
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (cut : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :
    openInternalChords
        (orderedChordAmbientPath hG sigma hSigma site returnChord) cut =
      ((turnChords rotation hG sigma hSigma site returnChord
          .backwardToAttachment).filter fun chord =>
        chord.left < cut ∧ cut ≤ chord.right) ∪
      ((turnChords rotation hG sigma hSigma site returnChord
          .forwardToAttachment).filter fun chord =>
        chord.left < cut ∧ cut ≤ chord.right) := by
  ext chord
  simp only [openInternalChords, Finset.mem_filter, mem_internalChords_iff,
    mem_turnChords_iff, Finset.mem_union]
  constructor
  · intro hchord
    cases hturn : internalChordTurn rotation hG sigma hSigma site returnChord chord
    · exact Or.inl ⟨⟨hchord.1, rfl⟩, hchord.2⟩
    · exact Or.inr ⟨⟨hchord.1, rfl⟩, hchord.2⟩
  · rintro (⟨⟨hchord, _hturn⟩, hopen⟩ | ⟨⟨hchord, _hturn⟩, hopen⟩)
    · exact ⟨hchord, hopen⟩
    · exact ⟨hchord, hopen⟩

/-- No chord can belong to both turn classes. -/
theorem disjoint_open_turnChords
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (cut : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :
    Disjoint
      ((turnChords rotation hG sigma hSigma site returnChord
          .backwardToAttachment).filter fun chord =>
        chord.left < cut ∧ cut ≤ chord.right)
      ((turnChords rotation hG sigma hSigma site returnChord
          .forwardToAttachment).filter fun chord =>
        chord.left < cut ∧ cut ≤ chord.right) := by
  rw [Finset.disjoint_left]
  intro chord hback hforward
  have hb := (mem_turnChords_iff rotation hG sigma hSigma site returnChord
    .backwardToAttachment chord).mp (Finset.mem_filter.mp hback).1
  have hf := (mem_turnChords_iff rotation hG sigma hSigma site returnChord
    .forwardToAttachment chord).mp (Finset.mem_filter.mp hforward).1
  rw [hb.2] at hf
  cases hf.2

/-- The two stack lengths are exactly the number of open internal chords. -/
theorem card_openInternalChords_eq_stack_lengths
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
    (cut : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :
    (openInternalChords
        (orderedChordAmbientPath hG sigma hSigma site returnChord) cut).card =
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .backwardToAttachment).stackAt cut).length +
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .forwardToAttachment).stackAt cut).length := by
  rw [openInternalChords_eq_turn_union rotation hG sigma hSigma site
      returnChord cut,
    Finset.card_union_of_disjoint
      (disjoint_open_turnChords rotation hG sigma hSigma site returnChord cut)]
  simp only [turnMatching]
  rw [stackAt_length_noncrossingMatchingOfChordDiagram,
    stackAt_length_noncrossingMatchingOfChordDiagram]

/-- In the no-external-attachment branch, the physical boundary of an
ambient-return prefix is bounded by seven endpoint/path edges plus the two
literal sweep-stack depths. -/
theorem card_ambientReturnPrefixBoundary_le_stack_lengths
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
    (hnoExternal : ∀ position : InternalPosition
        (orderedChordAmbientPath hG sigma hSigma site returnChord),
      ¬IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position)
    (cut : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hcut : 0 < cut.val) :
    (crossingEdgeFinset G
      (pathPrefixSide
        (orderedChordAmbientPath hG sigma hSigma site returnChord) cut)).card ≤
      7 +
        ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          .backwardToAttachment).stackAt cut).length +
        ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          .forwardToAttachment).stackAt cut).length := by
  have hbound := card_crossingEdgeFinset_pathPrefixSide_le
    (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) hnoExternal cut hcut
  rw [card_openInternalChords_eq_stack_lengths rotation minimal hG sigma hSigma
    site returnChord closure cut] at hbound
  omega

end

end AmbientReturnSweepWidth

end Mettapedia.GraphTheory.FourColor.Compositional
