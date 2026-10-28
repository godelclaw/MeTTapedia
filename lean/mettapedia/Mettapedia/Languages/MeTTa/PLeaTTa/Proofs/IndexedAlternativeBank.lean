-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.IndexedAlternativeBank
Purpose: Indexed views of retained alternative banks, their erasure laws,
  and the exact conversion obligations at the executable boundary.
Trusted boundary: none
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologNestedCallReadyRegression
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologRootClosedLocalLiveBridge

namespace Mettapedia.Languages.MeTTa.PLeaTTa.IndexedAlternativeBank

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologHeterogeneousPrefixBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologBodyFailureResourceTransitionBridge
open PrologActivationMacro
open PrologPersistentFreeScheduledPayloadBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRootClosedAnswerBridge
open PrologRootClosedLocalLiveBridge
open PrologScheduledPayloadResumeBridge

/-! ## An executable control whose alternative bank is an index -/

/-- Control data with no independently supplied alternative list.  The bank
is computed from the exact retained resource spine and older base named by the
type indices. -/
structure IndexedControl
    (resources : List RetainedAlternativeSegment)
    (base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt) where
  private mk ::
  cur : Option (List Mettapedia.Languages.MeTTa.PLeaTTa.Goal × Subst)
  qterm : Atom
  answers : List Atom
  answerKeys : List (Option Mettapedia.Languages.MeTTa.PLeaTTa.PersistentSubst.AtomExactKey)
  answerKeys_sound :
    answerKeys = answers.map Mettapedia.Languages.MeTTa.PLeaTTa.PersistentSubst.atomExactKey
  barriers : Option Nat

namespace IndexedControl

/-- Erasure into the executable control computes the alternative bank; it
cannot accept a differently shaped bank. -/
def toControl
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (control : IndexedControl resources base) : Control :=
  { cur := control.cur
    alts := flattenOwnedAlts resources base
    qterm := control.qterm
    answers := control.answers
    answerKeys := control.answerKeys
    answerKeys_sound := control.answerKeys_sound
    barriers := control.barriers }

@[simp] theorem toControl_alts
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (control : IndexedControl resources base) :
    control.toControl.alts = flattenOwnedAlts resources base := rfl

/-- Forget an ordinary control's alternative list while retaining every other
field.  Recovering the original control is deliberately a separate theorem:
that theorem exposes the exact conversion obligation at the machine seam. -/
def ofControl
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (control : Control)
    (_altsExact : control.alts = flattenOwnedAlts resources base) :
    IndexedControl resources base :=
  { cur := control.cur
    qterm := control.qterm
    answers := control.answers
    answerKeys := control.answerKeys
    answerKeys_sound := control.answerKeys_sound
    barriers := control.barriers }

/-- Conversion back to the original executable control is possible exactly
when its freely stored alternative field already has the indexed shape. -/
theorem toControl_ofControl
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (control : Control)
    (altsExact : control.alts = flattenOwnedAlts resources base) :
    (ofControl (resources := resources) (base := base) control
      altsExact).toControl =
      control := by
  cases control with
  | mk cur alts qterm answers answerKeys answerKeys_sound barriers =>
      simp only [ofControl, toControl] at altsExact ⊢
      subst alts
      rfl

end IndexedControl

/-- Fine executable state whose active alternative bank is computed from its
resource indices.  Persistent state, frames, and typed scope chronology remain
ordinary data and are neither restored nor inferred. -/
structure IndexedOpenConf
    (resources : List RetainedAlternativeSegment)
    (base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt) where
  persistent : Persistent
  control : IndexedControl resources base
  frames : List Frame
  scopes : ScopeHighWaters

namespace IndexedOpenConf

def toOpenConf
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : IndexedOpenConf resources base) : OpenConf :=
  { persistent := state.persistent
    control := state.control.toControl
    frames := state.frames
    scopes := state.scopes }

@[simp] theorem toOpenConf_alts
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : IndexedOpenConf resources base) :
    state.toOpenConf.control.alts = flattenOwnedAlts resources base := rfl

def ofOpenConf
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : OpenConf)
    (altsExact : state.control.alts = flattenOwnedAlts resources base) :
    IndexedOpenConf resources base :=
  { persistent := state.persistent
    control := IndexedControl.ofControl state.control altsExact
    frames := state.frames
    scopes := state.scopes }

/-- The indexed state recovers the actual executable state only by consuming
the same bank-shape fact carried by the present correspondence relation. -/
theorem toOpenConf_ofOpenConf
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : OpenConf)
    (altsExact : state.control.alts = flattenOwnedAlts resources base) :
    (ofOpenConf (resources := resources) (base := base) state
      altsExact).toOpenConf =
      state := by
  cases state with
  | mk persistent control frames scopes =>
      simp only [ofOpenConf, toOpenConf]
      rw [IndexedControl.toControl_ofControl control altsExact]

/-- Pulling the indexed state consults the computed bank, with no equality
transport at the call site. -/
def pullAux
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : IndexedOpenConf resources base) :=
  Mettapedia.Languages.MeTTa.PLeaTTa.pullAux state.toOpenConf.control.alts

@[simp] theorem pullAux_exact
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : IndexedOpenConf resources base) :
    state.pullAux = Mettapedia.Languages.MeTTa.PLeaTTa.pullAux (flattenOwnedAlts resources base) := rfl

/-- Cached pulling is likewise definitionally tied to the indexed bank. -/
def pullAuxTracked
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : IndexedOpenConf resources base) :=
  Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked state.toOpenConf.control.barriers
    state.toOpenConf.control.alts

@[simp] theorem pullAuxTracked_exact
    {resources : List RetainedAlternativeSegment}
    {base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
    (state : IndexedOpenConf resources base) :
    state.pullAuxTracked =
      Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked state.toOpenConf.control.barriers
        (flattenOwnedAlts resources base) := rfl

end IndexedOpenConf

/-! ## Non-vacuous closure of the flattened bank shape -/

/-- Every region owned by a local resolver contains ordinary branches only.
This is the precise structural premise needed to scan by retained segment
rather than by the erased flat list. -/
def BranchOnlyResources
    (resources : List RetainedAlternativeSegment) : Prop :=
  ∀ resource ∈ resources, ∀ alternative ∈ resource.alts,
    ∃ goals binding, alternative = Mettapedia.Languages.MeTTa.PLeaTTa.Alt.br goals binding

/-- The existing Type-valued source/resource payload zipper supplies the
branch-only premise for every one of its exact retained regions. -/
theorem BranchOnlyResources.ofPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    BranchOnlyResources resources := by
  induction payload with
  | nil => simp [BranchOnlyResources]
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerPayload
      inductionHypothesis =>
      intro candidate member alternative alternativeMember
      simp only [List.mem_cons] at member
      rcases member with head | tail
      · subst candidate
        exact
          RetainedAlternativeSegment.HasIndexedOwnershipAt.alts_all_branches
            resourceOwnership alternative alternativeMember
      · exact inductionHypothesis candidate tail alternative alternativeMember

/-- A source clause occurrence and an executable alternative are not a
one-to-one structural unit.  This concrete wrong-arity candidate remains a
real source occurrence while the certified conservative scan emits no
alternative.  Any useful index must therefore describe a whole retained
region, including zero-width regions, rather than index each `Alt` by one
source clause. -/
private def wrongArityClause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause :=
  { params := []
    result := .sym "result"
    body := [] }

theorem one_source_occurrence_can_emit_zero_alternatives :
    (scanResolution [.sym "input"] [.sym "input"] (.sym "result") [] []
      (.sym "query") 0 [wrongArityClause] 0).1 = [] ∧
      [wrongArityClause] ≠ [] := by
  exact ⟨rfl, by simp⟩

/-- Pulling a flattened branch-only bank either:

* crosses a uniquely described prefix of empty retained regions and selects
  the literal head of the next region, leaving that same source region with
  its executable head consumed; or
* proves every retained region empty and falls through to the exact older
  base.

The residual cannot be laundered into a freely chosen `base`: the local arm
retains the selected segment and every later segment explicitly.  This is the
shape-level closure prerequisite for an indexed executable transition. -/
theorem pullAux_flattenOwnedAlts_shape
    (resources : List RetainedAlternativeSegment)
    (base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt)
    (branchOnly : BranchOnlyResources resources) :
    (∃ earlier selected later goals binding localTail,
        resources = earlier ++ selected :: later ∧
          (∀ resource ∈ earlier, resource.alts = []) ∧
          selected.alts = Mettapedia.Languages.MeTTa.PLeaTTa.Alt.br goals binding :: localTail ∧
          Mettapedia.Languages.MeTTa.PLeaTTa.pullAux (flattenOwnedAlts resources base) =
            some
              (.branch goals binding,
                flattenOwnedAlts
                  (afterPulledHead selected localTail :: later) base)) ∨
      ((∀ resource ∈ resources, resource.alts = []) ∧
        Mettapedia.Languages.MeTTa.PLeaTTa.pullAux (flattenOwnedAlts resources base) =
          Mettapedia.Languages.MeTTa.PLeaTTa.pullAux base) := by
  induction resources with
  | nil =>
      exact .inr ⟨by simp, rfl⟩
  | cons head tail inductionHypothesis =>
      have headBranches :
          ∀ alternative ∈ head.alts,
            ∃ goals binding, alternative = Mettapedia.Languages.MeTTa.PLeaTTa.Alt.br goals binding := by
        intro alternative member
        exact branchOnly head (by simp) alternative member
      have tailBranches : BranchOnlyResources tail := by
        intro resource member alternative alternativeMember
        exact branchOnly resource (by simp [member]) alternative alternativeMember
      cases headAlts : head.alts with
      | nil =>
          rcases inductionHypothesis tailBranches with landed | exhausted
          · left
            rcases landed with
              ⟨earlier, selected, later, goals, binding, localTail,
                resourcesExact, earlierEmpty, selectedHead, pullExact⟩
            refine
              ⟨head :: earlier, selected, later, goals, binding, localTail,
                ?_, ?_, selectedHead, ?_⟩
            · simp [resourcesExact]
            · intro resource member
              simp only [List.mem_cons] at member
              rcases member with headExact | member
              · simpa [headExact] using headAlts
              · exact earlierEmpty resource member
            · simpa [flattenOwnedAlts, headAlts, Mettapedia.Languages.MeTTa.PLeaTTa.pullAux] using pullExact
          · right
            refine ⟨?_, ?_⟩
            · intro resource member
              simp only [List.mem_cons] at member
              rcases member with headExact | member
              · simpa [headExact] using headAlts
              · exact exhausted.1 resource member
            · simpa [flattenOwnedAlts, headAlts, Mettapedia.Languages.MeTTa.PLeaTTa.pullAux] using
                exhausted.2
      | cons alternative localTail =>
          rcases headBranches alternative (by simp [headAlts]) with
            ⟨goals, binding, alternativeExact⟩
          subst alternative
          left
          refine
            ⟨[], head, tail, goals, binding, localTail, rfl, by simp, headAlts,
              ?_⟩
          simp [flattenOwnedAlts, headAlts, Mettapedia.Languages.MeTTa.PLeaTTa.pullAux, afterPulledHead]

/-- Pop exactly one cached predicate marker per crossed retained region.  The
definition mirrors the cached runtime scan but deliberately does not reset to
zero until the actual older bank is exhausted. -/
def popBarrierCacheN : Option Nat → Nat → Option Nat
  | cache, 0 => cache
  | none, _count + 1 => none
  | some depth, count + 1 => popBarrierCacheN (some (depth - 1)) count

@[simp] theorem popBarrierCacheN_none (count : Nat) :
    popBarrierCacheN none count = none := by
  cases count <;> rfl

/-- Cached pulling through a structurally empty retained prefix reaches the
same older base with exactly one cache pop per crossed region. -/
theorem pullAuxTracked_flattenOwnedAlts_all_empty
    (resources : List RetainedAlternativeSegment)
    (base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt)
    (allEmpty : ∀ resource ∈ resources, resource.alts = [])
    (cache : Option Nat) :
    Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked cache (flattenOwnedAlts resources base) =
      Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked (popBarrierCacheN cache resources.length) base := by
  induction resources generalizing cache with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headEmpty : head.alts = [] := allEmpty head (by simp)
      have tailEmpty : ∀ resource ∈ tail, resource.alts = [] := by
        intro resource member
        exact allEmpty resource (by simp [member])
      cases cache with
      | none =>
          have first :=
            congrArg Prod.fst (inductionHypothesis tailEmpty none)
          simpa [flattenOwnedAlts, headEmpty, Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked,
            Mettapedia.Languages.MeTTa.PLeaTTa.pullAux, popBarrierCacheN] using first
      | some depth =>
          simpa [flattenOwnedAlts, headEmpty, Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked,
            Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxCached, popBarrierCacheN] using
              inductionHypothesis tailEmpty (some (depth - 1))

/-- Cached local selection is closed at the same non-vacuous segment split as
the uncached theorem.  The selected region remains represented explicitly and
the returned cache is determined by the number of earlier empty regions. -/
theorem pullAuxTracked_flattenOwnedAlts_local
    (earlier : List RetainedAlternativeSegment)
    (selected : RetainedAlternativeSegment)
    (later : List RetainedAlternativeSegment)
    (base : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt)
    (goals : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal) (binding : Subst)
    (localTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt)
    (earlierEmpty : ∀ resource ∈ earlier, resource.alts = [])
    (selectedHead :
      selected.alts = Mettapedia.Languages.MeTTa.PLeaTTa.Alt.br goals binding :: localTail)
    (cache : Option Nat) :
    Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked cache
        (flattenOwnedAlts (earlier ++ selected :: later) base) =
      (some
          (.branch goals binding,
            flattenOwnedAlts
              (afterPulledHead selected localTail :: later) base),
        popBarrierCacheN cache earlier.length) := by
  induction earlier generalizing cache with
  | nil =>
      cases cache <;>
        simp [flattenOwnedAlts, selectedHead, Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked,
          Mettapedia.Languages.MeTTa.PLeaTTa.pullAux, Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxCached, afterPulledHead,
          popBarrierCacheN]
  | cons head tail inductionHypothesis =>
      have headEmpty : head.alts = [] := earlierEmpty head (by simp)
      have tailEmpty : ∀ resource ∈ tail, resource.alts = [] := by
        intro resource member
        exact earlierEmpty resource (by simp [member])
      cases cache with
      | none =>
          have first :=
            congrArg Prod.fst (inductionHypothesis tailEmpty none)
          simpa [flattenOwnedAlts, headEmpty, Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked,
            Mettapedia.Languages.MeTTa.PLeaTTa.pullAux, popBarrierCacheN] using first
      | some depth =>
          simpa [flattenOwnedAlts, headEmpty, Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxTracked,
            Mettapedia.Languages.MeTTa.PLeaTTa.pullAuxCached, popBarrierCacheN] using
              inductionHypothesis tailEmpty (some (depth - 1))

/-! The theorem above closes only executable list shape.  Advancing the source
cursor is stronger: the post-pull resource must own the exact advanced cursor
and absolute occurrence.  That fact is carried by `PulledHeadOffsetAgrees`,
not by `RetainedAlternativeSegment` or `IndexedOpenConf`; producer integration
must therefore account for that phase rather than treating list closure as
source/executable closure. -/

/-- The phase obstruction is observable, not just a missing convenience
lemma: after the executable pulls a retained head, the source cursor frontier
is still distinct from the active clause-body source at every outer depth.
Thus replacing the indexed region by its post-head resource does not by itself
yield a closed source/executable state. -/
theorem bank_shape_closure_is_not_phase_closure
    (context : PrologSourceProductContextBridge.ActiveProductContext)
    (callerScope : CutScopeId)
    (opened : PeTTaSpec.PrologCore.GoalSemantics.OpenedCall)
    (cursor finish : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (branch : PeTTaSpec.PrologCore.Resolver.ClauseBranch)
    (branchTail : List PeTTaSpec.PrologCore.Resolver.ClauseBranch)
    (current : PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (body referenceRest : List PeTTaSpec.PrologCore.Goal) :
    PrologSourceProductContextBridge.ActiveProductContext.plug context
        (PrologRepresentativeProductActivationBridge.sourceProductFrontier
          callerScope opened cursor referenceRest) ≠
      PrologSourceProductContextBridge.ActiveProductContext.plug context
        (PrologActivatedProductStepBridge.activeSourceProduct callerScope opened
          finish branch branchTail current body referenceRest) :=
  post_failure_frontier_is_not_active context callerScope opened cursor finish
    branch branchTail current body referenceRest

/-! ## Root-closed pull through the indexed executable state -/

/-- Root-closed answer readiness with the executable bank represented by
construction.  `stateExact` is intentionally retained: it is the measured
conversion seam from the current unindexed machine. -/
structure IndexedRootClosedAnswerReady
    (before : RepresentativePersistentFreeScheduledPayloadState) : Type where
  ready : RootClosedAnswerReady before
  indexedState : IndexedOpenConf ready.result.history.resources []
  stateExact :
    indexedState.toOpenConf = before.carrier.index.openConf

namespace IndexedRootClosedAnswerReady

/-- Every existing ready state embeds, but the embedding consumes precisely
its old `bankExact` proof. -/
def ofReady
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    IndexedRootClosedAnswerReady before :=
  { ready := ready
    indexedState :=
      IndexedOpenConf.ofOpenConf before.carrier.index.openConf ready.bankExact
    stateExact :=
      IndexedOpenConf.toOpenConf_ofOpenConf
        before.carrier.index.openConf ready.bankExact }

/-- The exact executable bank now follows from the indexed state by
definitional reduction; the only transport is the explicit machine seam. -/
theorem actualBankExact
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (indexed : IndexedRootClosedAnswerReady before) :
    before.carrier.index.openConf.control.alts =
      flattenOwnedAlts indexed.ready.result.history.resources [] := by
  rw [← indexed.stateExact]
  rfl

/-- Re-run the closed source classifier and couple it to the literal machine
bank through the indexed state. -/
theorem classifyPull
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (indexed : IndexedRootClosedAnswerReady before) :
    ∃ events,
      ClosedScheduledPullOutcome indexed.ready.result.history events ∧
        ((∃ goals binding rest,
            events = [] ∧
              PrologFindallAnswerResourceBridge.PullOutcomeAgrees
                before.carrier.index.openConf.control.alts
                (some (goals, binding)) rest) ∨
          (events = [.completed] ∧
            PrologFindallAnswerResourceBridge.PullOutcomeAgrees
              before.carrier.index.openConf.control.alts none [])) := by
  obtain ⟨events, outcome⟩ :=
    indexed.ready.result.history.classifyClosedPull
  refine ⟨events, outcome, ?_⟩
  rcases outcome.toPullOutcomeAgrees with selected | exhausted
  · left
    rcases selected with ⟨goals, binding, rest, eventsExact, pull⟩
    exact ⟨goals, binding, rest, eventsExact, by
      simpa only [indexed.actualBankExact] using pull⟩
  · right
    rcases exhausted with ⟨eventsExact, pull⟩
    exact ⟨eventsExact, by
      simpa only [indexed.actualBankExact] using pull⟩

end IndexedRootClosedAnswerReady

/-! ## The real depth-two regression -/

private theorem groundRootClosedScheduledCarrier
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ before : RepresentativePersistentFreeScheduledPayloadState,
      before.carrier.index.callerReferences = [] ∧
        before.carrier.index.baseAlts = [] ∧
        before.carrier.index.outer.length = 2 ∧
        (∀ segment ∈ before.carrier.index.outer,
          segment.references = []) := by
  obtain
    ⟨_root, _qHead, _middle, _qReady, _qPredicate, _qPayload,
      _rootReferences, _rootExecutables, _rootSourceSteps, _rootFineSteps,
      _qCertificate, _rHead, after, _rReady, _rPredicate, _rPayload,
      _rCertificate, bodyReferencesEmpty, bodyExecutablesEmpty,
      callerReferencesEmpty, baseAltsEmpty, _afterActiveAlts,
      _afterResources, _middleActiveAlts, _rootActiveAlts, outerLength,
      outerAllEmpty⟩ :=
    PrologNestedCallReadyRegression.ground_p_q_r_two_nested_pushes
      (prog := prog) (gt := gt)
  obtain ⟨representative, carrierExact⟩ := after.existsRepresentative
  subst after
  let before :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt representative
      bodyReferencesEmpty bodyExecutablesEmpty
  exact
    ⟨before, by simpa [before] using callerReferencesEmpty,
      by simpa only [before,
        RepresentativeActivePayloadState.afterBodyAnswer_baseAlts] using
          baseAltsEmpty,
      by simpa [before] using outerLength,
      by simpa [before] using outerAllEmpty⟩

/-- The literal `p -> q -> r` carrier reaches the indexed classifier through
the real source/executable construction.  The result deliberately exports the
conversion seam so the experiment cannot hide where the unindexed machine
still needs an equality proof. -/
theorem ground_two_frame_root_closed_indexed_pull_is_inhabited
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ before : RepresentativePersistentFreeScheduledPayloadState,
      ∃ indexed : IndexedRootClosedAnswerReady before,
        before.carrier.index.outer.length = 2 ∧
          indexed.indexedState.toOpenConf = before.carrier.index.openConf ∧
          ∃ events,
            ClosedScheduledPullOutcome indexed.ready.result.history events ∧
              ((∃ goals binding rest,
                  events = [] ∧
                    PrologFindallAnswerResourceBridge.PullOutcomeAgrees
                      before.carrier.index.openConf.control.alts
                      (some (goals, binding)) rest) ∨
                (events = [.completed] ∧
                  PrologFindallAnswerResourceBridge.PullOutcomeAgrees
                    before.carrier.index.openConf.control.alts none [])) := by
  obtain ⟨before, callerEmpty, baseEmpty, outerLength, outerEmpty⟩ :=
    groundRootClosedScheduledCarrier (prog := prog) (gt := gt)
  let ready :=
    PrologRootClosedAnswerBridge.RepresentativePersistentFreeScheduledPayloadState.rootClosedAnswerReady
      before callerEmpty outerEmpty baseEmpty
  let indexed := IndexedRootClosedAnswerReady.ofReady ready
  obtain ⟨events, outcome, classified⟩ := indexed.classifyPull
  exact
    ⟨before, indexed, outerLength, indexed.stateExact, events, outcome,
      classified⟩

end Mettapedia.Languages.MeTTa.PLeaTTa.IndexedAlternativeBank
