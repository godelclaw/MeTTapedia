import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.WorkSpan
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls
import Mettapedia.Machines.Cursor.Fold

/-!
# Work and span for ordered interaction histories

The interaction computation fibre retains exact chronological events.
Its canonical work/span readout is therefore serial: each event contributes
one unit of work and one unit of span.  Genuine parallel span requires more
information than an endpoint path contains, so this module separately
internalizes Cost-rho's proof-relevant `ParallelCostSchedule`, whose wave
boundaries are retained in `Type`.

Both objects are types and terms of the staged scoped-reflective family model.  The
schedule erases to the established proposition-valued `ParallelCostTrace`;
its executable work/span value is computed from the schedule, never from a
proof in `Prop`.  This keeps logical reachability, scheduling, and accounting
at their proper abstraction boundaries.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionCost

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Work/span as a native semantic value -/

/-- Work/span pairs are ordinary closed candidate semantic values. -/
def workSpanTy : familiesCwF.Ty CandidateContext :=
  fun _ => WorkSpan

def internalWorkSpan (value : WorkSpan) :
    familiesCwF.Tm CandidateContext workSpanTy :=
  fun _ => value

/-! ## Chronological interaction paths -/

/-- The serial work/span readout of an authenticated event path.  A plain
path contains order but no concurrency-wave partition, so its span equals its
work. -/
def pathWorkSpan {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm CandidateContext
      (interactionComputationTy presentation source target)) :
    familiesCwF.Tm CandidateContext workSpanTy :=
  fun context =>
    let eventCount := EventPath.pathLength presentation (path context)
    WorkSpan.mk eventCount eventCount

@[simp] theorem pathWorkSpan_work {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm CandidateContext
      (interactionComputationTy presentation source target))
    (context : CandidateContext) :
    (pathWorkSpan path context).work =
      EventPath.pathLength presentation (path context) :=
  rfl

@[simp] theorem pathWorkSpan_span {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm CandidateContext
      (interactionComputationTy presentation source target))
    (context : CandidateContext) :
    (pathWorkSpan path context).span =
      EventPath.pathLength presentation (path context) :=
  rfl

/-- Chronological path composition is exactly sequential work/span
composition. -/
theorem pathWorkSpan_compose {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source middle target : theory.Term}
    (firstPath : familiesCwF.Tm CandidateContext
      (interactionComputationTy presentation source middle))
    (secondPath : familiesCwF.Tm CandidateContext
      (interactionComputationTy presentation middle target)) :
    pathWorkSpan (composePath firstPath secondPath) =
      fun context => WorkSpan.sequential
        (pathWorkSpan firstPath context) (pathWorkSpan secondPath context) := by
  funext context
  apply WorkSpan.ext <;>
    simp [pathWorkSpan, composePath, WorkSpan.sequential]
  all_goals exact EventPath.pathLength_append presentation (firstPath context) (secondPath context)

/-! ## Proof-relevant concurrent schedules -/

/-- Cost-rho schedules are native candidate semantic types indexed by endpoints,
the complete occurrence receipt, exact work, and exact wave count. -/
def parallelScheduleTy {Ground : Type}
    (source : CostConfig Ground)
    (receipt : Multiset (SpendEvent Ground (CostName Ground)))
    (target : CostConfig Ground) (count waves : Nat) :
    familiesCwF.Ty CandidateContext :=
  fun _ => ParallelCostSchedule source receipt target count waves

/-- The logical trace to which a proof-relevant schedule erases. -/
def parallelTraceTy {Ground : Type}
    (source : CostConfig Ground)
    (receipt : Multiset (SpendEvent Ground (CostName Ground)))
    (target : CostConfig Ground) (count : Nat) :
    familiesCwF.Ty CandidateContext :=
  fun _ => PLift (ParallelCostTrace source receipt target count)

def internalSchedule {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    familiesCwF.Tm CandidateContext
      (parallelScheduleTy source receipt target count waves) :=
  fun _ => schedule

/-- Logical erasure is internalized as a map between candidate semantic types. -/
def eraseSchedule {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm CandidateContext
      (parallelScheduleTy source receipt target count waves)) :
    familiesCwF.Tm CandidateContext
      (parallelTraceTy source receipt target count) :=
  fun context => ⟨(schedule context).toTrace⟩

/-- Executable accounting reads the proof-relevant schedule. -/
def scheduleWorkSpan {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm CandidateContext
      (parallelScheduleTy source receipt target count waves)) :
    familiesCwF.Tm CandidateContext workSpanTy :=
  fun context => (schedule context).workSpan

@[simp] theorem scheduleWorkSpan_work {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm CandidateContext
      (parallelScheduleTy source receipt target count waves))
    (context : CandidateContext) :
    (scheduleWorkSpan schedule context).work = count :=
  (schedule context).workSpan_work_eq_count

@[simp] theorem scheduleWorkSpan_span {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm CandidateContext
      (parallelScheduleTy source receipt target count waves))
    (context : CandidateContext) :
    (scheduleWorkSpan schedule context).span = waves :=
  (schedule context).workSpan_span_eq_waves

/-- Internal scheduling never exceeds the serial span for the same exact
event count. -/
theorem scheduleWorkSpan_le_serial {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm CandidateContext
      (parallelScheduleTy source receipt target count waves))
    (context : CandidateContext) :
    (show WorkSpan from scheduleWorkSpan schedule context) ≤
      ParallelCostSchedule.serialBaseline count :=
  by
    change (schedule context).workSpan ≤
      ParallelCostSchedule.serialBaseline count
    exact (schedule context).workSpan_le_serialBaseline

/-! ## Positive and negative controls -/

/-- Positive: a one-event rho computation has unit work and unit span. -/
theorem internalComm_workSpan :
    pathWorkSpan internalComm PUnit.unit = ⟨1, 1⟩ :=
  rfl

/-- Negative: two independent unit events have the same work but smaller span
than the chronological two-event path. -/
theorem parallel_two_events_ne_sequential :
    WorkSpan.parallel ⟨1, 1⟩ ⟨1, 1⟩ ≠
      WorkSpan.sequential ⟨1, 1⟩ ⟨1, 1⟩ := by
  intro equal
  have spanEqual := congrArg WorkSpan.span equal
  norm_num [WorkSpan.parallel, WorkSpan.sequential] at spanEqual

#print axioms pathWorkSpan_compose
#print axioms scheduleWorkSpan_work
#print axioms scheduleWorkSpan_span
#print axioms scheduleWorkSpan_le_serial
#print axioms parallel_two_events_ne_sequential


/-! ## Occurrence-sensitive canonical COMM selection

The source recognizer and completeness theorem belong to the independent rho
kernel. This optional candidate adapter consumes its actual firing stream,
uses the existing retained minimum fold, and internalizes selected events.
The key and traversal are declared policy. Native C channel-group traversal,
key encoding and occurrence decoding are separate correspondence obligations;
persistent receivers and evaluated MeTTa payloads are outside this closed
strict-core source instance. Enumeration and callbacks have separate costs.
-/

namespace CanonicalSelection

set_option backward.isDefEq.respectTransparency false

open Mettapedia.Machines.Cursor
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Exact firing witnesses refine the existing public saturated step. This
interpretation does not replace the independent source judgments. -/
def presentation : InteractionPresentation rhoLanguageDefGSLT where
  Site := Unit
  Event _ source target := {firing : Firing (fromProcess source) // firing.target = fromProcess target}
  sound := fun event => (publicStep_iff_firing _ _).mpr ⟨event.val, event.property⟩

theorem presentation_complete : presentation.Complete := by
  intro source target step
  obtain ⟨firing, targetReadout⟩ := (publicStep_iff_firing source target).mp step
  exact ⟨⟨(), ⟨firing, targetReadout⟩⟩⟩

def enabled (source : RhoProcess) (firing : Firing (fromProcess source)) : presentation.Enabled source :=
  ⟨(), toProcess firing.target, ⟨firing, by rw [fromProcess_toProcess]⟩⟩

def candidates (source : RhoProcess) : List (Firing (fromProcess source)) :=
  Enumeration.firings (fromProcess source)

def candidateTy (source : RhoProcess) : familiesCwF.Ty CandidateContext :=
  fun _ => List (Firing (fromProcess source))

def internalCandidates (source : RhoProcess) : familiesCwF.Tm CandidateContext (candidateTy source) :=
  fun _ => candidates source

def internalFiring (source : RhoProcess) (firing : Firing (fromProcess source)) :
    familiesCwF.Tm CandidateContext
      (interactionComputationTy presentation source (toProcess firing.target)) :=
  internalEvent (presentation := presentation) (enabled source firing).evidence

theorem internalFiring_semantic_workSpan (source : RhoProcess) (firing : Firing (fromProcess source)) :
    pathWorkSpan (internalFiring source firing) PUnit.unit = ⟨1, 1⟩ := rfl

variable {Key : Type} [LinearOrder Key]
variable (source : RhoProcess) (key : Firing (fromProcess source) → Key)

abbrev provider := Sequence.tails (Firing (fromProcess source))
abbrev Saved := Fold.StableMinimum.Saved key (provider source)

def scan (fuel : Nat) : Saved source key :=
  Fold.StableMinimum.run key (provider source) fuel (candidates source)

def resume (fuel : Nat) (saved : Saved source key) : Saved source key :=
  Fold.StableMinimum.resume key (provider source) fuel saved

def published (saved : Saved source key) : Option (Option (Firing (fromProcess source) × Nat)) :=
  Fold.StableMinimum.published key saved

/-- The outer option keeps suspension distinct from a completed empty stream;
the inner option carries the actual selected event and its traversal ordinal. -/
def selectedEvent (saved : Saved source key) : Option (Option (presentation.Enabled source × Nat)) :=
  (published source key saved).map fun result => result.map fun chosen => (enabled source chosen.1, chosen.2)

def scanTy : familiesCwF.Ty CandidateContext := fun _ => Saved source key

def internalScan (fuel : Nat) : familiesCwF.Tm CandidateContext (scanTy source key) :=
  fun _ => scan source key fuel

theorem completed_selection_iff (selected : Option (Firing (fromProcess source) × Nat)) :
    published source key (scan source key ((candidates source).length + 2)) = some selected ↔
      Fold.StableMinimum.Specification key (candidates source) selected :=
  Fold.StableMinimum.completed_selection_iff_specification key (candidates source) selected

/-- The same chosen firing retains its whole rule, unmatched residue and
public endpoint. Selection does not reconstruct a firing from a coarse target. -/
theorem selected_whole_firing (firing : Firing (fromProcess source)) (ordinal : Nat)
    (chosen : published source key (scan source key ((candidates source).length + 2)) = some (some (firing, ordinal))) :
    fromProcess source = append firing.rule.redex firing.residue ∧
      firing.target = append firing.rule.reactum firing.residue ∧
      rhoLanguageDefGSLT.Step source (toProcess firing.target) ∧
      Fold.StableMinimum.IsFirstMinimum key (candidates source) (firing, ordinal) := by
  exact ⟨firing.source_readout, rfl, (enabled source firing).step,
    (completed_selection_iff source key _).mp chosen⟩

theorem prefix_retains_firings_and_residual (fuel : Nat) (within : fuel ≤ (candidates source).length) :
    scan source key fuel =
      (fuel, .paused (Fold.start _ (Fold.StableMinimum.consume key) ((candidates source).drop fuel)
        ⟨fuel, (((candidates source).take fuel).zipIdx).foldl (Fold.StableMinimum.choose key) none⟩)) :=
  Fold.StableMinimum.prefix_keeps_exact_occurrences key (candidates source) fuel within

theorem incomplete_scan_has_no_selected_event (fuel : Nat) (within : fuel ≤ (candidates source).length) :
    selectedEvent source key (scan source key fuel) = none := by
  have unfinished := Fold.StableMinimum.incomplete_prefix_has_no_final_selection key (candidates source) fuel within
  exact congrArg (fun value => value.map fun result =>
    result.map fun chosen => (enabled source chosen.1, chosen.2)) unfinished

theorem split_resume_preserves_whole_firing_and_account (first second : Nat) :
    resume source key second (scan source key first) = scan source key (first + second) :=
  Fold.StableMinimum.split_resume_full_account key (provider source) (candidates source) first second

/-- Pull work includes checking exhaustion. It is neither a COMM count nor a
price for building the candidate list, channel equality, substitution or export. -/
theorem candidate_pull_account (fuel : Nat) :
    (scan source key fuel).1 = min fuel ((candidates source).length + 1) :=
  Fold.StableMinimum.pull_account_exact key (candidates source) fuel

/-- The independently implemented array window retains the entire source
firing through the existing provider map. No native C decoder is asserted. -/
def window : Sequence.Slice (Firing (fromProcess source)) :=
  ⟨(candidates source).toArray, 0, (candidates source).length⟩

theorem window_transport_account (fuel : Nat) :
    ((Fold.StableMinimum.run key (Sequence.slices _) fuel (window source)).1,
      (Sequence.sliceHom _).outcome (Fold.StableMinimum.reader key)
        (Fold.StableMinimum.run key (Sequence.slices _) fuel (window source)).2) = scan source key fuel := by
  have transported := Fold.StableMinimum.transport_account key (Sequence.sliceHom _) (window source) fuel
  simpa only [scan, window, Sequence.sliceHom, List.toList_toArray, List.drop_zero, List.take_length] using transported

theorem completed_empty_iff_no_public_step :
    published source key (scan source key ((candidates source).length + 2)) = some none ↔
      ¬ ∃ target : RhoProcess, rhoLanguageDefGSLT.Step source target := by
  rw [completed_selection_iff]
  change candidates source = [] ↔ _
  constructor
  · intro empty ⟨target, step⟩
    obtain ⟨firing, member, _⟩ := (Enumeration.publicStep_iff_enumerated source target).mp step
    change firing ∈ candidates source at member
    rw [empty] at member
    exact List.not_mem_nil member
  · intro quiescent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro firing _member
    exact quiescent ⟨toProcess firing.target, (enabled source firing).step⟩

theorem window_resume_transport (saved : Fold.StableMinimum.Saved key (Sequence.slices _)) (fuel : Nat) :
    ((Fold.StableMinimum.resume key (Sequence.slices _) fuel saved).1,
      (Sequence.sliceHom _).outcome (Fold.StableMinimum.reader key)
        (Fold.StableMinimum.resume key (Sequence.slices _) fuel saved).2) =
      resume source key fuel (saved.1, (Sequence.sliceHom _).outcome (Fold.StableMinimum.reader key) saved.2) :=
  Fold.StableMinimum.transport_resume_account key (Sequence.sliceHom _) saved fuel

theorem window_completion_iff (selected : Option (Firing (fromProcess source) × Nat)) :
    Fold.StableMinimum.published key
      (Fold.StableMinimum.run key (Sequence.slices _) ((candidates source).length + 2) (window source)) =
        some selected ↔ Fold.StableMinimum.Specification key (candidates source) selected := by
  have transported := Fold.StableMinimum.transported_completion_iff_specification key
    (Sequence.sliceHom _) (window source) selected
  simpa only [window, Sequence.sliceHom, List.toList_toArray, List.drop_zero, List.take_length] using transported

namespace Controls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The existing closed COMM control is reused as source data. The executable
stream never uses its noncomputable reference firing selectors. -/
def duplicateSource : RhoProcess := toProcess CanonicalReactionControls.duplicates

def duplicateStream : List (Firing (fromProcess duplicateSource)) := candidates duplicateSource

theorem enumerates_distinct_occurrences_with_same_endpoint :
    ∃ first second : Firing (fromProcess duplicateSource),
      first ∈ duplicateStream ∧ second ∈ duplicateStream ∧ first ≠ second ∧
      first.target = second.target ∧
      first.tail = [output CanonicalReactionControls.channel CanonicalReactionControls.payload] ∧
      second.tail = [output CanonicalReactionControls.channel CanonicalReactionControls.payload] ∧
      first.target.1 = ([CanonicalReactionControls.payload,
        output CanonicalReactionControls.channel CanonicalReactionControls.payload] : List Pattern) := by
  have references : ∃ first second : Firing CanonicalReactionControls.duplicates,
      first ∈ Enumeration.firings CanonicalReactionControls.duplicates ∧
      second ∈ Enumeration.firings CanonicalReactionControls.duplicates ∧ first ≠ second ∧
      first.target = second.target ∧
      first.tail = [output CanonicalReactionControls.channel CanonicalReactionControls.payload] ∧
      second.tail = [output CanonicalReactionControls.channel CanonicalReactionControls.payload] ∧
      first.target.1 = ([CanonicalReactionControls.payload,
        output CanonicalReactionControls.channel CanonicalReactionControls.payload] : List Pattern) :=
    ⟨CanonicalReactionControls.first, CanonicalReactionControls.second,
      Enumeration.mem_firings _ _, Enumeration.mem_firings _ _,
      CanonicalReactionControls.different_occurrences, CanonicalReactionControls.same_endpoint,
      CanonicalReactionControls.first_tail, CanonicalReactionControls.second_tail,
      CanonicalReactionControls.complete_endpoint_inventory⟩
  unfold duplicateStream candidates duplicateSource
  rw [fromProcess_toProcess]
  exact references

theorem duplicate_stream_has_two_occurrences : 2 ≤ duplicateStream.length := by
  obtain ⟨first, second, firstMember, secondMember, different, _⟩ :=
    enumerates_distinct_occurrences_with_same_endpoint
  cases shape : duplicateStream with
  | nil => simp only [shape, List.not_mem_nil] at firstMember
  | cons head rest =>
      cases rest with
      | nil =>
          simp only [shape, List.mem_singleton] at firstMember secondMember
          exact (different (firstMember.trans secondMember.symm)).elim
      | cons next tail => simp only [List.length_cons]; omega

theorem duplicate_stream_nonempty : duplicateStream ≠ [] := by
  intro empty
  have bound := duplicate_stream_has_two_occurrences
  simp only [empty, List.length_nil] at bound
  omega

/-- This selector is an actual read of the enumerated list, not a choice of a
reference firing. Its proof argument supplies no runtime data. -/
def firstEnumerated : Firing (fromProcess duplicateSource) := duplicateStream.head duplicate_stream_nonempty

theorem duplicate_stream_head_tail : duplicateStream = firstEnumerated :: duplicateStream.tail :=
  (List.cons_head_tail duplicate_stream_nonempty).symm

def equalKey (_ : Firing (fromProcess duplicateSource)) : Nat := 7

theorem equal_keys_select_first_occurrence :
    published duplicateSource equalKey (scan duplicateSource equalKey (duplicateStream.length + 2)) =
      some (some (firstEnumerated, 0)) := by
  apply (completed_selection_iff duplicateSource equalKey _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change (firstEnumerated, 0) ∈ duplicateStream.zipIdx
    rw [duplicate_stream_head_tail]
    exact List.mem_cons_self
  · intro other _
    exact Nat.le_refl _
  · intro other _ _
    exact Nat.zero_le _

theorem equal_keys_cannot_select_a_later_ordinal
    (firing : Firing (fromProcess duplicateSource)) (ordinal : Nat) (later : 0 < ordinal) :
    published duplicateSource equalKey (scan duplicateSource equalKey (duplicateStream.length + 2)) ≠
      some (some (firing, ordinal)) := by
  rw [equal_keys_select_first_occurrence]
  intro same
  have equalOrdinals := congrArg Prod.snd (Option.some.inj (Option.some.inj same))
  change 0 = ordinal at equalOrdinals
  omega

theorem one_pull_retains_provisional_first_and_full_suffix :
    scan duplicateSource equalKey 1 =
      (1, .paused (Fold.start _ (Fold.StableMinimum.consume equalKey) duplicateStream.tail
        ⟨1, some (firstEnumerated, 0)⟩)) := by
  have within : 1 ≤ (candidates duplicateSource).length := by
    have two := duplicate_stream_has_two_occurrences
    change 2 ≤ (candidates duplicateSource).length at two
    omega
  have retainedPrefix := prefix_retains_firings_and_residual duplicateSource equalKey 1 within
  change scan duplicateSource equalKey 1 =
    (1, .paused (Fold.start _ (Fold.StableMinimum.consume equalKey) (duplicateStream.drop 1)
      ⟨1, (duplicateStream.take 1).zipIdx.foldl (Fold.StableMinimum.choose equalKey) none⟩)) at retainedPrefix
  have takeFirst : duplicateStream.take 1 = [firstEnumerated] := by
    rw [duplicate_stream_head_tail]
    rfl
  rw [takeFirst] at retainedPrefix
  simpa only [List.drop_one, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons,
    List.foldl_nil, Fold.StableMinimum.choose] using retainedPrefix

theorem provisional_winner_is_not_final :
    selectedEvent duplicateSource equalKey (scan duplicateSource equalKey 1) = none :=
  incomplete_scan_has_no_selected_event duplicateSource equalKey 1
    (Nat.le_trans (by decide) duplicate_stream_has_two_occurrences)

/-- The completed receipt retains the actual firing fold and charges each
candidate plus the exhaustion pull, even when resumed after a provisional win. -/
theorem resumed_duplicate_scan_has_full_receipt :
    resume duplicateSource equalKey (duplicateStream.length + 1) (scan duplicateSource equalKey 1) =
      (duplicateStream.length + 1,
        .done ⟨(), duplicateStream.foldl (Fold.StableMinimum.consume equalKey) Fold.StableMinimum.initial, []⟩) := by
  rw [split_resume_preserves_whole_firing_and_account]
  have total : 1 + (duplicateStream.length + 1) = duplicateStream.length + 2 := by omega
  rw [total]
  exact Fold.StableMinimum.completion_is_exact equalKey duplicateStream

def cheaperLaterKey (firing : Firing (fromProcess duplicateSource)) : Nat :=
  if firing = firstEnumerated then 1 else 0

private theorem another_enumerated_occurrence :
    ∃ firing ∈ duplicateStream, firing ≠ firstEnumerated := by
  obtain ⟨first, second, firstMember, secondMember, different, _⟩ :=
    enumerates_distinct_occurrences_with_same_endpoint
  by_cases same : first = firstEnumerated
  · exact ⟨second, secondMember, fun other => different (same.trans other.symm)⟩
  · exact ⟨first, firstMember, same⟩

/-- The later cheap occurrence really wins on the actual enumerated source;
the first provisional candidate is not published merely because it arrived. -/
theorem cheaper_later_occurrence_wins :
    ∃ firing ordinal,
      published duplicateSource cheaperLaterKey
        (scan duplicateSource cheaperLaterKey (duplicateStream.length + 2)) = some (some (firing, ordinal)) ∧
      cheaperLaterKey firing = 0 ∧ 0 < ordinal ∧ firing ≠ firstEnumerated := by
  obtain ⟨other, member, different⟩ := another_enumerated_occurrence
  obtain ⟨otherOrdinal, atOther⟩ := List.mem_iff_getElem?.mp member
  have otherIncluded : (other, otherOrdinal) ∈ duplicateStream.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr atOther
  cases chosen : (duplicateStream.foldl (Fold.StableMinimum.consume cheaperLaterKey)
      Fold.StableMinimum.initial).best with
  | none =>
      have empty := (Fold.StableMinimum.scan_specification cheaperLaterKey duplicateStream none).mp chosen
      exact (duplicate_stream_nonempty empty).elim
  | some selected =>
      obtain ⟨firing, ordinal⟩ := selected
      have spec := (Fold.StableMinimum.scan_specification cheaperLaterKey duplicateStream _).mp chosen
      have noWorse := spec.2.1 (other, otherOrdinal) otherIncluded
      have cheapest : cheaperLaterKey firing = 0 := by
        simpa only [cheaperLaterKey, if_neg different, Nat.le_zero] using noWorse
      have notFirst : firing ≠ firstEnumerated := by
        intro same
        simp only [cheaperLaterKey, same] at cheapest
        contradiction
      have later : 0 < ordinal := by
        have atSelected := List.mk_mem_zipIdx_iff_getElem?.mp spec.1
        cases ordinal with
        | zero =>
            rw [duplicate_stream_head_tail] at atSelected
            simp only [List.getElem?_cons_zero, Option.some.injEq] at atSelected
            exact (notFirst atSelected.symm).elim
        | succ ordinal => omega
      exact ⟨firing, ordinal, (completed_selection_iff duplicateSource cheaperLaterKey _).mpr spec,
        cheapest, later, notFirst⟩

theorem selected_residue_has_one_unmatched_occurrence (firing : Firing (fromProcess duplicateSource)) :
    firing.tail.length = 1 := by
  have sourceLength : (ordered (fromProcess duplicateSource).1).length = 3 := by
    unfold duplicateSource
    rw [fromProcess_toProcess]
    change (Multiset.sort _ _).length = 3
    rw [Multiset.length_sort]
    rfl
  have first := List.length_eraseIdx_add_one firing.inputIndex.isLt
  have second := List.length_eraseIdx_add_one firing.outputIndex.isLt
  unfold Firing.tail
  omega

theorem no_endpoint_decoder_for_enumerated_occurrences :
    ¬ ∃ decode : Bag → Firing (fromProcess duplicateSource),
      ∀ firing ∈ duplicateStream, decode firing.target = firing := by
  rintro ⟨decode, decodes⟩
  obtain ⟨first, second, firstMember, secondMember, different, sameEndpoint, _⟩ :=
    enumerates_distinct_occurrences_with_same_endpoint
  apply different
  exact (decodes first firstMember).symm.trans
    ((congrArg decode sameEndpoint).trans (decodes second secondMember))

/-- A nonempty source can have no legal input/output address at all. -/
def onlyOutputs : Bag := append CanonicalReactionControls.oneOutput CanonicalReactionControls.oneOutput

theorem onlyOutputs_readout : ordered onlyOutputs.1 =
    [output CanonicalReactionControls.channel CanonicalReactionControls.payload,
      output CanonicalReactionControls.channel CanonicalReactionControls.payload] := by
  apply (List.perm_replicate (n := 2)).mp
  apply Multiset.coe_eq_coe.mp
  rw [ordered_multiset]
  rfl

theorem output_only_source_has_no_firing : Enumeration.firings onlyOutputs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro firing _member
  have selectedInput := List.getElem_mem firing.inputIndex.isLt
  rw [firing.inputAt, onlyOutputs_readout] at selectedInput
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at selectedInput
  simp only [input, output, Pattern.apply.injEq, String.reduceEq, false_and] at selectedInput

/-- Both physical positions exist, but the proposed receiver is an output. -/
def outputAsInputAddress : Enumeration.Address onlyOutputs :=
  ⟨⟨0, by rw [onlyOutputs_readout]; decide⟩,
    ⟨0, by
      change 0 < ((ordered onlyOutputs.1).eraseIdx 0).length
      rw [onlyOutputs_readout]
      decide⟩⟩

theorem output_as_input_address_is_rejected :
    Enumeration.recognize onlyOutputs outputAsInputAddress = none := by
  cases checked : Enumeration.recognize onlyOutputs outputAsInputAddress with
  | none => rfl
  | some firing =>
      have member := Enumeration.mem_firings onlyOutputs firing
      rw [output_only_source_has_no_firing] at member
      exact (List.not_mem_nil member).elim

def outputOnlySource : RhoProcess := toProcess onlyOutputs

theorem output_only_candidates_empty : candidates outputOnlySource = [] := by
  unfold candidates outputOnlySource
  rw [fromProcess_toProcess]
  exact output_only_source_has_no_firing

theorem output_only_completion_is_empty_but_zero_work_is_unfinished :
    published outputOnlySource (fun _ => (0 : Nat)) (scan outputOnlySource (fun _ => (0 : Nat)) 2) = some none ∧
      selectedEvent outputOnlySource (fun _ => (0 : Nat)) (scan outputOnlySource (fun _ => (0 : Nat)) 0) = none ∧
      ¬ ∃ target : RhoProcess, rhoLanguageDefGSLT.Step outputOnlySource target := by
  have completed : published outputOnlySource (fun _ => (0 : Nat))
      (scan outputOnlySource (fun _ => (0 : Nat)) ((candidates outputOnlySource).length + 2)) = some none := by
    apply (completed_selection_iff _ _ _).mpr
    exact output_only_candidates_empty
  refine ⟨?_, incomplete_scan_has_no_selected_event _ _ 0 (Nat.zero_le _), ?_⟩
  · simpa only [output_only_candidates_empty, List.length_nil, Nat.zero_add] using completed
  · exact (completed_empty_iff_no_public_step _ _).mp completed

end Controls

end CanonicalSelection

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionCost
