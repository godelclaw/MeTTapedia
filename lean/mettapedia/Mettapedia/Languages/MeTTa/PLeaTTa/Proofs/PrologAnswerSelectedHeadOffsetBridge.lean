-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologAnswerSelectedHeadOffsetBridge
Purpose: Turn an exactly selected answer frontier into the post-head retained
  cursor/resource offset at its absolute call-start position.
Trusted boundary: none
Main exports:
  SelectedReadyFrontier.pulledHeadOffsetExact
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologAnswerSourceCatchupBridge
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologBodyFailureResourceTransitionBridge

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologAnswerSelectedHeadOffsetBridge

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationMacro
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologAnswerSourceCatchupBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologBodyFailureResourceTransitionBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologCallPayloadBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologPrefilterScanBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologProductResourceContextBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologRepresentativeCallFrontierBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologRepresentativeCallPrefilterBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologRecursiveCallPayloadBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologSupportedCallFrontierBridge
open Mettapedia.Languages.MeTTa.PLeaTTa.PrologSupportedCursorAlternativeBridge

/-!
# The source/executable head offset

The scheduled executable pull and the independent source cursor move on two
different axes.  The source first consumes `rejectedCount` definitely rejected
clause occurrences.  The executable has already selected the next retained
head.  Consuming that head therefore places the surviving resource at the
absolute call-start position

`startPosition + rejectedCount + 1`.

The theorem below reconstructs the complete indexed ownership certificate at
that position.  It uses the stored rejected-pull derivation, rather than the
count alone, so fresh-reservation and call-identity preservation are proved
from the actual path.
-/

namespace SelectedReadyFrontier

/-- A selected ready frontier advances through every stored source rejection
and then consumes exactly the selected retained head.

The second conjunct is intentionally redundant with the existential ownership
inside `PulledHeadOffsetAgrees`: it exposes the exact absolute coordinate for
the scheduled-payload zipper, so a later proof cannot silently replace
`start + rejected + 1` by `start + 1`. -/
theorem pulledHeadOffsetExact
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
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
          resource selectedTail ∧
        (afterPulledHead resource selectedTail).Owns alpha callStart
          (finish.advance branch branchTail)
          ((startPosition + frontier.rejectedCount) + 1) := by
  rcases frontier.ownership.scan with
    ⟨_originalCandidates, originalWellFormed, originalQuery,
      substitutedArgs, _originalSupported, _originalArities,
      _originalScan⟩
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail,
      cursorRemaining, candidatesExact, priorAlts, selectedExact,
      supported, arity, retained, tailSupported, tailScan⟩ :=
    frontier.head_exact
  have banksEqual :
      resolutionAlt resource.argsv resource.args resource.res resource.rest
            resource.binding resource.qterm resource.barrier resource.counter
            clause :: altTail =
        .br selectedGoals selectedBinding :: selectedTail :=
    priorAlts.symm.trans selectedExact
  have altTailExact : altTail = selectedTail :=
    (List.cons.inj banksEqual).2
  subst altTail
  let copied :=
    Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause resource.argsv resource.args resource.res
      resource.rest resource.binding resource.qterm resource.counter
      resource.barrier clause
  have finishWellFormed : finish.WellFormed :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      frontier.rejectedPulls originalWellFormed
  have queryAtFinish :
      RepresentativeNormalizedCallAgrees alpha finish resource.argsv
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst resource.binding resource.res) :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      frontier.context (.refl original) originalQuery
  have supportedAtFinish :
      SupportedPreparedCandidateAgrees finish.callGeneration finish.predicate
        finish.arguments finish.bindings branch clause :=
    frontier.context.supportedPreparedCandidate supported
  have advancedContext :
      CursorCallContext (finish.advance branch branchTail)
        original.callGeneration original.predicate original.arguments
        original.bindings :=
    frontier.context.advance branch branchTail
  have advancedWellFormed :
      (finish.advance branch branchTail).WellFormed :=
    finish.advance_wellFormed finishWellFormed cursorRemaining
  have queryAtAdvanced :
      RepresentativeNormalizedCallAgrees alpha
        (finish.advance branch branchTail) resource.argsv
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst resource.binding resource.res) :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      advancedContext frontier.context queryAtFinish
  have tailArities :
      ∀ candidate, candidate ∈ clauseTail →
        candidate.params.length = resource.argsv.length := by
    intro candidate member
    exact frontier.readyArities candidate (by
      rw [candidatesExact]
      simp [member])
  have tailSupportedAtAdvanced :
      List.Forall₂
        (SupportedPreparedCandidateAgrees
          (finish.advance branch branchTail).callGeneration
          (finish.advance branch branchTail).predicate
          (finish.advance branch branchTail).arguments
          (finish.advance branch branchTail).bindings)
        (finish.advance branch branchTail).remaining clauseTail := by
    have transported :
        List.Forall₂
          (SupportedPreparedCandidateAgrees
            (finish.advance branch branchTail).callGeneration
            (finish.advance branch branchTail).predicate
            (finish.advance branch branchTail).arguments
            (finish.advance branch branchTail).bindings)
          branchTail clauseTail :=
      tailSupported.imp
        (fun _branch _clause item =>
          advancedContext.supportedPreparedCandidate item)
    simpa [PreparedCursor.advance] using transported
  have advancedIdentity :
      PreparedCallIdentity.ofCursor (finish.advance branch branchTail) =
        PreparedCallIdentity.ofCursor original := by
    apply PreparedCallIdentity.ofCursor_eq_of_callContext advancedContext
    simpa [PreparedCursor.advance] using
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
        frontier.rejectedPulls)
  have tailOwnership :
      (afterPulledHead resource selectedTail).Owns alpha callStart
        (finish.advance branch branchTail)
        ((startPosition + frontier.rejectedCount) + 1) := by
    refine ⟨?_, ?_, frontier.positioned.advance cursorRemaining⟩
    · calc
        (afterPulledHead resource selectedTail).callIdentity =
            resource.callIdentity := rfl
        _ = PreparedCallIdentity.ofCursor original :=
          frontier.ownership.identity
        _ = PreparedCallIdentity.ofCursor
              (finish.advance branch branchTail) := advancedIdentity.symm
    · exact
        ⟨clauseTail, advancedWellFormed, queryAtAdvanced, substitutedArgs,
          tailSupportedAtAdvanced, tailArities, tailScan⟩
  have offset :
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
        resource selectedTail :=
    ⟨cursorRemaining, finishWellFormed, queryAtFinish, substitutedArgs,
      supportedAtFinish, arity, retained, priorAlts,
      rfl,
      ⟨callStart, startPosition + frontier.rejectedCount,
        frontier.positioned, tailOwnership⟩⟩
  exact ⟨branch, clause, branchTail, copied, offset, tailOwnership⟩

end SelectedReadyFrontier

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologAnswerSelectedHeadOffsetBridge
