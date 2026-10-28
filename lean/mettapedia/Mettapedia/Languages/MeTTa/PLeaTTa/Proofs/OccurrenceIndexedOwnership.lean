-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.OccurrenceIndexedOwnership
Purpose: Type-valued source-occurrence ownership, its exact erasure,
  uniqueness, and constructive producer laws
Trusted boundary: none

The indexed carrier retains its source coordinates explicitly. Its relation
to the existing existential projection is stated by the erasure and recovery
laws below.
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologAnswerSelectedHeadOffsetBridge
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologScheduledPayloadPathRegression
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologScheduledPayloadPostHeadBridge

namespace Mettapedia.Languages.MeTTa.PLeaTTa.OccurrenceIndexedOwnership

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologActivationMacro
open PrologAnswerSelectedHeadOffsetBridge
open PrologAnswerSourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologCallPayloadBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedCursorOwnershipBridge
open PrologRetainedPayloadSnapshotBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadPathBridge
open PrologSourceProductContextBridge
open PrologSupportedCallFrontierBridge
open PrologSupportedCursorAlternativeBridge

/-! ## A genuinely indexed ownership carrier -/

/-- A resource whose source occurrence is part of the carrier's type.

Unlike `HasIndexedOwnershipAt`, `callStart` and `position` are not hidden by
an existential proposition.  Construction therefore requires a producer
which already knows the exact occurrence, or an explicitly noncomputable
choice from erased proof data.  Erasure has no computational inverse. -/
structure OwnedSegmentAt
    (alpha : List (LogicVar × String))
    (callStart cursor : PreparedCursor) (position : Nat) : Type where
  resource : RetainedAlternativeSegment
  ownership : resource.Owns alpha callStart cursor position

namespace OwnedSegmentAt

/-- Forgetting coordinates is mechanical and preserves the exact ownership
proof.  The reverse direction is intentionally absent: the existential lives
in `Prop`, so it cannot computationally produce a Type-valued carrier. -/
theorem erase
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (owned : OwnedSegmentAt alpha callStart cursor position) :
    owned.resource.HasIndexedOwnershipAt alpha cursor :=
  ⟨callStart, position, owned.ownership⟩

/-- Classical choice can cross the `Prop`/`Type` boundary noncomputably.

This records why the experiment must not claim a hard expressibility wall:
the seal already admits `Classical.choice`.  The migration question is about
proof compression and structural clarity, not bare recoverability. -/
noncomputable def recover
    {alpha : List (LogicVar × String)} {cursor : PreparedCursor}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
    Σ callStart, Σ position, OwnedSegmentAt alpha callStart cursor position := by
  classical
  have candidates :
      Nonempty
        { coordinates : PreparedCursor × Nat //
          resource.Owns alpha coordinates.1 cursor coordinates.2 } := by
    rcases ownership with ⟨callStart, position, exactOwnership⟩
    exact ⟨⟨(callStart, position), exactOwnership⟩⟩
  let chosen := Classical.choice candidates
  exact
    ⟨chosen.1.1, chosen.1.2,
      { resource := resource
        ownership := chosen.2 }⟩

/-- Exposing occurrence coordinates removes one existential elimination, but
marker-freedom remains a semantic consequence of the retained scan rather
than a definitional equality. -/
theorem barrierCount_zero
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (owned : OwnedSegmentAt alpha callStart cursor position) :
    Mettapedia.Languages.MeTTa.PLeaTTa.barrierCount owned.resource.alts = 0 :=
  RetainedAlternativeSegment.barrierCount_zero owned.ownership

/-- For fixed call-start and current cursors, the proposed position index is
unique.  It carries real source information rather than an arbitrary label. -/
theorem position_unique
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {left right : Nat}
    (leftOwned : OwnedSegmentAt alpha callStart cursor left)
    (rightOwned : OwnedSegmentAt alpha callStart cursor right) :
    left = right :=
  CallScopedCursorPosition.position_unique
    leftOwned.ownership.positioned rightOwned.ownership.positioned

end OwnedSegmentAt

/-- The real local-clause activation already knows the exact call start and
absolute position needed by `OwnedSegmentAt`.  Threading those indices at
this producer is mechanical and requires no invented coordinate. -/
theorem SpinedRepresentativeProductActivation.producesOwnedSegmentAt
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    {copied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {segmentReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {segmentExecutableRest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {outer : List PrologControlSegmentSpineBridge.ControlSegment}
    {qterm : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (retainedPosition : Nat)
    (positioned :
      CallScopedCursorPosition opened.cursor
        (finish.advance branch branchTail) retainedPosition)
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (alignment :
      SourceControlResourceContextAgrees nextAlpha qterm callerBarrier outer
        resources callerScope context outerScope)
    (baseAlts : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources baseAlts) :
    ∃ owned : OwnedSegmentAt nextAlpha opened.cursor
        (finish.advance branch branchTail) retainedPosition,
      owned.resource.rest =
          segmentExecutableRest ++
            PrologControlSegmentSpineBridge.flattenExecutables outer ∧
        owned.resource.qterm = qterm ∧
        owned.resource.barrier = bodyBarrier ∧
        owned.resource.alts = altTail ∧
        owned.resource.finalCounter = pending.persistent.counter ∧
        (activatedExecutableSuccessor
          pending copied
            (segmentExecutableRest ++
              PrologControlSegmentSpineBridge.flattenExecutables outer)
            qterm installed).alts =
          flattenOwnedAlts (owned.resource :: resources) baseAlts := by
  obtain
    ⟨active, activeRest, activeQuery, activeBarrier, activeAlts,
      activeFinalCounter, activeOwnership, actualAlts, _markerCount,
      _controlAlignment⟩ :=
    activation.resources_throughAlignedContext retainedPosition positioned
      alignment baseAlts outerAlts
  exact
    ⟨⟨active, activeOwnership⟩, activeRest, activeQuery, activeBarrier,
      activeAlts, activeFinalCounter, actualAlts⟩

/-! ## The one producer seam which really erases a coordinate -/

/-- Counterfactual post-head carrier with the call start and absolute source
position exposed as indices.

This is the production `PulledHeadOffsetAgrees` relation with only its final
existential changed: the pre-head position and the post-head ownership are
named directly.  Every other semantic field is retained verbatim. -/
structure IndexedPulledHeadOffsetAgrees
    (alpha : List (LogicVar × String))
    (callStart cursor : PreparedCursor) (position : Nat)
    (branch : ClauseBranch) (clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt) : Prop where
  cursorRemaining : cursor.remaining = branch :: branchTail
  cursorWellFormed : cursor.WellFormed
  query :
    RepresentativeNormalizedCallAgrees alpha cursor resource.argsv
      (Mettapedia.Languages.MeTTa.PLeaTTa.subst resource.binding resource.res)
  substitutedArgs :
    resource.argsv = resource.args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst resource.binding)
  supported :
    SupportedPreparedCandidateAgrees cursor.callGeneration cursor.predicate
      cursor.arguments cursor.bindings branch clause
  arity : clause.params.length = resource.argsv.length
  retained :
    resolutionClauseRetained resource.argsv
      (Mettapedia.Languages.MeTTa.PLeaTTa.subst resource.binding resource.res) clause = true
  priorAlts :
    resource.alts =
      resolutionAlt resource.argsv resource.args resource.res resource.rest
        resource.binding resource.qterm resource.barrier resource.counter
        clause :: remainingAlts
  copiedExact :
    copied =
      Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause resource.argsv resource.args
        resource.res resource.rest resource.binding resource.qterm
        resource.counter resource.barrier clause
  positioned : CallScopedCursorPosition callStart cursor position
  tailOwnership :
    (afterPulledHead resource remainingAlts).Owns alpha callStart
      (cursor.advance branch branchTail) (position + 1)

namespace IndexedPulledHeadOffsetAgrees

/-- Erasing the explicit indices reconstructs the production relation. -/
theorem erase
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    {branch : ClauseBranch} {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (agreement :
      IndexedPulledHeadOffsetAgrees alpha callStart cursor position branch
        clause branchTail copied resource remainingAlts) :
    PulledHeadOffsetAgrees alpha cursor branch clause branchTail copied
      resource remainingAlts :=
  { cursorRemaining := agreement.cursorRemaining
    cursorWellFormed := agreement.cursorWellFormed
    query := agreement.query
    substitutedArgs := agreement.substitutedArgs
    supported := agreement.supported
    arity := agreement.arity
    retained := agreement.retained
    priorAlts := agreement.priorAlts
    copiedExact := agreement.copiedExact
    positionedTailOwnership :=
      ⟨callStart, position, agreement.positioned, agreement.tailOwnership⟩ }

/-- The post-head absolute position is now a direct projection; no existential
must be reopened and no coordinate is reconstructed. -/
theorem tailOwnershipExact
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    {branch : ClauseBranch} {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (agreement :
      IndexedPulledHeadOffsetAgrees alpha callStart cursor position branch
        clause branchTail copied resource remainingAlts) :
    (afterPulledHead resource remainingAlts).Owns alpha callStart
      (cursor.advance branch branchTail) (position + 1) :=
  agreement.tailOwnership

end IndexedPulledHeadOffsetAgrees

/-- The real selected-frontier producer supplies every proposed index without
choice or invention.  This is the positive result of the experiment: the
post-head offset is a mechanically indexable seam. -/
theorem SelectedReadyFrontier.pulledHeadOffsetIndexed
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    ∃ branch clause branchTail copied,
      IndexedPulledHeadOffsetAgrees alpha callStart finish
        (startPosition + frontier.rejectedCount) branch clause branchTail
        copied resource selectedTail := by
  obtain ⟨branch, clause, branchTail, copied, offset, tailOwnership⟩ :=
    PrologAnswerSelectedHeadOffsetBridge.SelectedReadyFrontier.pulledHeadOffsetExact
      frontier
  exact
    ⟨branch, clause, branchTail, copied,
      { cursorRemaining := offset.cursorRemaining
        cursorWellFormed := offset.cursorWellFormed
        query := offset.query
        substitutedArgs := offset.substitutedArgs
        supported := offset.supported
        arity := offset.arity
        retained := offset.retained
        priorAlts := offset.priorAlts
        copiedExact := offset.copiedExact
        positioned := frontier.positioned
        tailOwnership := tailOwnership }⟩

/-! ## The three proposed savings which do not follow from these indices -/

/-- A coordinate-indexed payload cell.  Erasure into the production cell is
mechanical, but selecting the same scheduled-history occurrence still needs
the existing route equality. -/
structure IndexedPayloadCell
    (alpha support : List (LogicVar × String))
    (callStart cursor : PreparedCursor) (position : Nat) : Type where
  currentBarrier : Nat
  currentScope : CutScopeId
  nextScope : CutScopeId
  outerScope : CutScopeId
  segment : PrologControlSegmentSpineBridge.ControlSegment
  outerSegments : List PrologControlSegmentSpineBridge.ControlSegment
  resource : RetainedAlternativeSegment
  ownership : resource.Owns alpha callStart cursor position
  snapshot :
    RetainedCallPayloadSnapshot alpha support resource cursor segment
      outerSegments

namespace IndexedPayloadCell

def historyCell
    {alpha support : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (cell : IndexedPayloadCell alpha support callStart cursor position) :
    ScheduledHistoryCell alpha :=
  { resource := cell.resource
    cursor := cursor
    ownership := ⟨callStart, position, cell.ownership⟩ }

/-- Even with occurrence coordinates in the carrier, resource selection is
still obtained from the route's exact history-cell equality.  The new indices
do not participate in the proof. -/
theorem selectedResourceExact
    {alpha support : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (cell : IndexedPayloadCell alpha support callStart cursor position)
    (selected : ScheduledHistoryCell alpha)
    (sameOccurrence : cell.historyCell = selected) :
    cell.resource = selected.resource :=
  congrArg ScheduledHistoryCell.resource sameOccurrence

/-- Cursor selection has the same unchanged dependency on route equality;
the ownership coordinate cannot replace it. -/
theorem selectedCursorExact
    {alpha support : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (cell : IndexedPayloadCell alpha support callStart cursor position)
    (selected : ScheduledHistoryCell alpha)
    (sameOccurrence : cell.historyCell = selected) :
    cursor = selected.cursor :=
  congrArg ScheduledHistoryCell.cursor sameOccurrence

end IndexedPayloadCell

/-- Duplicate-resource discrimination is already supplied by the dependent
payload path.  It does not require the call-start or absolute-position index
introduced by this experiment. -/
theorem duplicate_resource_guard_is_already_path_indexed
    {alpha support : List (LogicVar × String)} {qterm : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (left right : PayloadPath payload)
    (sameResource : left.cell.resource = right.cell.resource)
    (differentCursor : left.cell.cursor ≠ right.cell.cursor) :
    left.cell.resource = right.cell.resource ∧ left ≠ right :=
  PrologScheduledPayloadPathRegression.duplicate_resource_cannot_identify_payload_path
    left right sameResource differentCursor

end Mettapedia.Languages.MeTTa.PLeaTTa.OccurrenceIndexedOwnership
