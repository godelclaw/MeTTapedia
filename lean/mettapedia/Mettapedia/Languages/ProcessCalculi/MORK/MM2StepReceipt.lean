import Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch
import Mettapedia.Languages.ProcessCalculi.MORK.ProofRelevantGSLT

/-!
# Checking a supplied reflective MM2 firing receipt

The checker below uses the existing supported, leave-inert reflective profile.
It recomputes that profile's scheduler selection, closes the existing structural
input cursor on its captured snapshot, compares every supplied physical match
row, and checks the existing staged sink finalization. The independent source
meaning is the already defined reflective work-queue step, whose input matcher
is the recursive finite join rather than this cursor.

The receipt retains source positions, row order and multiplicity even when the
sink's set-valued output identifies equal payloads. Matching reads the selected
exec in the captured snapshot; writes start from the workspace after consuming
that exec. No write is used to suppress another match in the same firing.

A fuel field bounds this submitted checking run, not MM2 answer cardinality or
native CPU work. Insufficient fuel does not establish quiescence or falsity.
The checker has no fixed global fuel cap and does not compute its proof bound.

Completeness here is closure of one finite captured input query, not a claim
that one successful match represents all matches. Candidate insertion can
invalidate a receipt while preserving all of its positive witnesses. Native
byte order, compact-variable unification, output-local binders, foreign effects
and unmodeled source/sink factories need their own source correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2StepReceipt

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef
open HostCalls (collect)
open MM2MatchingCursor
open ReflectiveComputable WQComputable

structure Receipt where
  directive : Atom
  fuel : Nat
  rows : List Row
  deriving DecidableEq, Repr

/-- Check the supplied physical rows only after the actual cursor has closed.
Sink finalization runs on its complete collected input, once. -/
def check (source target : List Atom) (receipt : Receipt) : Bool :=
  match selectNextScheduled (cSupportedSourceExecFacts source) with
  | none => false
  | some directive =>
      if receipt.directive = directive.atom then
        match collect (StructuralQuanta.pull (entries (MM2MatchingBatch.snapshot source directive)))
            receipt.fuel (MM2MatchingBatch.initial source directive) with
        | none => false
        | some actual =>
            decide (receipt.rows = actual ∧ MM2MatchingBatch.finalize source directive actual = target)
      else false

/-- Exact admission includes scheduler identity, complete cursor closure,
ordered physical match rows and the original sink result. -/
theorem check_exact (source target : List Atom) (receipt : Receipt) :
    check source target receipt = true ↔
      ∃ directive,
        selectNextScheduled (cSupportedSourceExecFacts source) = some directive ∧
        receipt.directive = directive.atom ∧
        collect (StructuralQuanta.pull (entries (MM2MatchingBatch.snapshot source directive)))
          receipt.fuel (MM2MatchingBatch.initial source directive) = some receipt.rows ∧
        MM2MatchingBatch.finalize source directive receipt.rows = target := by
  unfold check
  cases selected : selectNextScheduled (cSupportedSourceExecFacts source) with
  | none => simp
  | some directive =>
      by_cases identity : receipt.directive = directive.atom
      · simp only [if_pos identity]
        cases closed : collect
            (StructuralQuanta.pull (entries (MM2MatchingBatch.snapshot source directive)))
            receipt.fuel (MM2MatchingBatch.initial source directive) with
        | none => simp [identity, closed]
        | some actual =>
            simp only [decide_eq_true_eq]
            constructor
            · rintro ⟨same, written⟩
              exact ⟨directive, rfl, identity, same ▸ closed, same ▸ written⟩
            · rintro ⟨chosen, same, _identity, completed, written⟩
              cases Option.some.inj same
              have equal : actual = receipt.rows := Option.some.inj (closed.symm.trans completed)
              exact ⟨equal.symm, equal.symm ▸ written⟩
      · simp [identity]

/-- Closed receipts contain the whole independent physical-row denotation,
including repeated payloads at distinct source positions. -/
theorem accepted_rows_complete (source target : List Atom) (receipt : Receipt)
    (accepted : check source target receipt = true) :
    ∃ directive,
      selectNextScheduled (cSupportedSourceExecFacts source) = some directive ∧
      receipt.directive = directive.atom ∧
      receipt.rows = StructuralQuanta.residualRows
        (entries (MM2MatchingBatch.snapshot source directive)) (MM2MatchingBatch.initial source directive) := by
  obtain ⟨directive, selected, identity, closed, _written⟩ := (check_exact source target receipt).mp accepted
  exact ⟨directive, selected, identity, StructuralQuanta.collect_sound _ _ _ _ closed⟩

/-- Erasing physical positions recovers the existing recursive input matcher,
with exact row order and multiplicity rather than just set membership. -/
theorem accepted_input_exact (source target : List Atom) (receipt : Receipt)
    (accepted : check source target receipt = true) :
    ∃ directive,
      selectNextScheduled (cSupportedSourceExecFacts source) = some directive ∧
      receipt.directive = directive.atom ∧
      receipt.rows.map eraseRow = Conformance.Computable.cmatchInputSpec []
        (MM2MatchingBatch.snapshot source directive) directive.rule.input := by
  obtain ⟨directive, selected, identity, closed, _written⟩ := (check_exact source target receipt).mp accepted
  exact ⟨directive, selected, identity,
    StructuralQuanta.completed_rows_erase _ _ _ _ _ closed⟩

/-- Every claimed witness position reads its actual atom from the captured
snapshot. This positive-read law alone is weaker than complete enumeration. -/
theorem accepted_witness_positions (source target : List Atom) (receipt : Receipt)
    (accepted : check source target receipt = true) :
    ∃ directive,
      selectNextScheduled (cSupportedSourceExecFacts source) = some directive ∧
      receipt.directive = directive.atom ∧
      ∀ row ∈ receipt.rows, ∀ item ∈ row.2,
        (MM2MatchingBatch.snapshot source directive)[item.2]? = some item.1 := by
  obtain ⟨directive, selected, identity, closed, _written⟩ := (check_exact source target receipt).mp accepted
  refine ⟨directive, selected, identity, ?_⟩
  intro row generated item used
  have complete := StructuralQuanta.completed_rows
    (MM2MatchingBatch.snapshot source directive) directive.rule.input [] receipt.fuel receipt.rows closed
  rw [complete] at generated
  simp only [MM2MatchingCursor.residualRows, MM2MatchingCursor.start,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, workRows] at generated
  have present := rows_witnesses _ _ _ _ _ generated item used
  exact entry_at_position _ item (present.resolve_right (by simp))

/-- The actual completed cursor and staged write batch reflect to the already
defined recursive firing, not to a new receipt-defined transition system. -/
theorem check_sound (source target : List Atom) (receipt : Receipt)
    (accepted : check source target receipt = true) :
    cReflectiveSourceWorkQueueStep .leaveInert source = some target := by
  obtain ⟨directive, selected, _identity, closed, written⟩ := (check_exact source target receipt).mp accepted
  have complete := StructuralQuanta.collect_sound _ _ _ _ closed
  have fired : cFireReflectiveSourceExecFact source directive = target := by
    rw [complete, MM2MatchingBatch.finalize_reference] at written
    exact written
  simp [cReflectiveSourceWorkQueueStep, selected, fired]

/-- Every source step has a sufficiently closed physical-row receipt. The
existence proof uses the proven cursor work measure; checking never evaluates it. -/
theorem check_complete (source target : List Atom)
    (step : cReflectiveSourceWorkQueueStep .leaveInert source = some target) :
    ∃ receipt, check source target receipt = true := by
  unfold cReflectiveSourceWorkQueueStep at step
  cases selected : selectNextScheduled (cSupportedSourceExecFacts source) with
  | none => simp [selected] at step
  | some directive =>
      have fired : cFireReflectiveSourceExecFact source directive = target := by simpa [selected] using step
      let state := MM2MatchingBatch.initial source directive
      let snapshot := entries (MM2MatchingBatch.snapshot source directive)
      let rows := StructuralQuanta.residualRows snapshot state
      let fuel := StructuralQuanta.remainingCost snapshot state + 1
      refine ⟨⟨directive.atom, fuel, rows⟩, (check_exact _ _ _).mpr
        ⟨directive, selected, rfl, ?_, ?_⟩⟩
      · exact StructuralQuanta.collect_complete snapshot fuel state (Nat.lt_succ_self _)
      · exact (MM2MatchingBatch.finalize_reference source directive).trans fired

/-- Preservation and reflection hold for the concrete list observation, before
the separate quotient to a set-valued MM2 space. -/
theorem receipt_exists_iff_step (source target : List Atom) :
    (∃ receipt, check source target receipt = true) ↔
      (reflectiveNativeListExecGSLT .leaveInert).Step source target :=
  ⟨fun ⟨receipt, accepted⟩ => check_sound source target receipt accepted,
    check_complete source target⟩

/-- Finite executable recognition of the existing scheduler-key invariant.
This specification uses pairwise comparisons and claims no optimal lookup cost. -/
def uniqueKeysB {α : Type} [SchedulerKey α] [DecidableEq α] (facts : List α) : Bool :=
  facts.all (fun left => facts.all (fun right =>
    decide (SchedulerKey.key left = SchedulerKey.key right → left = right)))

theorem uniqueKeysB_exact {α : Type} [SchedulerKey α] [DecidableEq α] (facts : List α) :
    uniqueKeysB facts = true ↔ KeyInjective facts := by
  constructor
  · intro accepted left right leftPresent rightPresent equal
    have compared := List.all_eq_true.mp
      (List.all_eq_true.mp accepted left leftPresent) right rightPresent
    exact (of_decide_eq_true compared) equal
  · intro injective
    exact List.all_eq_true.mpr (fun left leftPresent => List.all_eq_true.mpr
      (fun right rightPresent => decide_eq_true (injective left right leftPresent rightPresent)))

/-- An executable source admission for the add/remove support fragment. None
of its clauses assumes that this firing has the requested semantic result. -/
def supportAdmissionB (source : List Atom) : Bool :=
  decide source.Nodup &&
    uniqueKeysB (cSupportedSourceExecFacts source) && uniqueKeysB (cRawExecFacts source) &&
    (cSupportedSourceExecFacts source).all
      (fun directive => directive.rule.tmpl.sinks.all reflectiveSupportSetSinkB) &&
    (cRawExecFacts source).all (fun raw => match decodeSupportedSourceExec raw with
      | none => true
      | some directive => directive.rule.tmpl.sinks.all reflectiveSupportSetSinkB)

/-- The complete physical realization invariant is derived from concrete
finite admission and the previously proved matcher/sink alignment laws. -/
theorem supportAdmissionB_invariant (source : List Atom)
    (accepted : supportAdmissionB source = true) : ReflectiveWorkQueueInvariant source := by
  have conditions : source.Nodup ∧
      uniqueKeysB (cSupportedSourceExecFacts source) = true ∧
      uniqueKeysB (cRawExecFacts source) = true ∧
      (cSupportedSourceExecFacts source).all
        (fun directive => directive.rule.tmpl.sinks.all reflectiveSupportSetSinkB) = true ∧
      (cRawExecFacts source).all (fun raw => match decodeSupportedSourceExec raw with
        | none => true
        | some directive => directive.rule.tmpl.sinks.all reflectiveSupportSetSinkB) = true := by
    simpa only [supportAdmissionB, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using accepted
  obtain ⟨nodup, supportedKeys, rawKeys, supportedTemplates, rawTemplates⟩ := conditions
  apply reflectiveWorkQueueInvariant_of_supportSet source nodup
    ((uniqueKeysB_exact _).mp supportedKeys) ((uniqueKeysB_exact _).mp rawKeys)
  · intro directive selected
    exact (all_reflectiveSupportSetSinkB_eq_true_iff directive.rule.tmpl).mp
      (List.all_eq_true.mp supportedTemplates directive (selectNextScheduled_mem selected))
  · intro raw directive selected decoded
    have supported := List.all_eq_true.mp rawTemplates raw (selectNextScheduled_mem selected)
    rw [decoded] at supported
    exact (all_reflectiveSupportSetSinkB_eq_true_iff directive.rule.tmpl).mp supported

/-- The existing physical representation invariant is required to transport
both directions to the support-valued source GSLT. It is not replaced by a
single selected match or a claimed equality of final answer sets. -/
theorem support_step_iff_receipt (source : List Atom) (target : Space)
    (invariant : ReflectiveWorkQueueInvariant source) :
    (reflectiveSourceExecGSLT .leaveInert).Step source.toFinset target ↔
      ∃ concrete receipt, check source concrete receipt = true ∧ concrete.toFinset = target := by
  rw [reflectiveSourceExecGSLT_step_iff]
  rw [MM2MatchingBatch.completed_support_step_iff .leaveInert source target invariant]
  constructor
  · rintro ⟨concrete, completed, same⟩
    have moved := (MM2MatchingBatch.completed_step_iff .leaveInert source concrete).mp completed
    obtain ⟨receipt, accepted⟩ := check_complete source concrete moved
    exact ⟨concrete, receipt, accepted, same⟩
  · rintro ⟨concrete, receipt, accepted, same⟩
    exact ⟨concrete, (MM2MatchingBatch.completed_step_iff .leaveInert source concrete).mpr
      (check_sound source concrete receipt accepted), same⟩

/-- Both directions for the concretely admitted support fragment need no
caller-supplied firing-agreement premise or guessed matcher completeness. -/
theorem admitted_support_step_iff_receipt (source : List Atom) (target : Space)
    (admitted : supportAdmissionB source = true) :
    (reflectiveSourceExecGSLT .leaveInert).Step source.toFinset target ↔
      ∃ concrete receipt, check source concrete receipt = true ∧ concrete.toFinset = target :=
  support_step_iff_receipt source target (supportAdmissionB_invariant source admitted)

/-- The original proof-relevant event retains the receipt's selected directive,
not merely a source and target connected by some supported firing. -/
theorem accepted_same_directive_event (source target : List Atom) (receipt : Receipt)
    (invariant : ReflectiveWorkQueueInvariant source)
    (accepted : check source target receipt = true) :
    ∃ event : ReflectiveScheduledEvent source.toFinset target.toFinset,
      event.directive.atom = receipt.directive := by
  obtain ⟨directive, selected, identity, closed, written⟩ :=
    (check_exact source target receipt).mp accepted
  have complete := StructuralQuanta.collect_sound _ _ _ _ closed
  have fired : cFireReflectiveSourceExecFact source directive = target := by
    rw [complete, MM2MatchingBatch.finalize_reference] at written
    exact written
  have selectedSupport :
      selectNextScheduled (supportedSourceExecFactsOfSpace source.toFinset) = some directive := by
    rw [← cSourceWorkQueueStep_selectSupported_eq source invariant.nodup invariant.supportedKeyInj]
    exact selected
  have firedSupport : fireReflectiveSourceExecFact source.toFinset directive = target.toFinset :=
    (invariant.supportedAgreement directive selected).symm.trans (congrArg List.toFinset fired)
  exact ⟨⟨directive, selectedSupport, firedSupport⟩, identity.symm⟩

/-- The accepted support step has the original proof-relevant scheduled event.
Receipt rows remain available separately; quotienting does not recreate them. -/
theorem accepted_scheduled_event (source target : List Atom) (receipt : Receipt)
    (invariant : ReflectiveWorkQueueInvariant source)
    (accepted : check source target receipt = true) :
    Nonempty (ReflectiveScheduledEvent source.toFinset target.toFinset) := by
  obtain ⟨event, _identity⟩ := accepted_same_directive_event source target receipt invariant accepted
  exact ⟨event⟩

theorem changed_directive_refused (source target : List Atom) (receipt : Receipt)
    (directive : SourceExecFact)
    (selected : selectNextScheduled (cSupportedSourceExecFacts source) = some directive)
    (different : receipt.directive ≠ directive.atom) : check source target receipt = false := by
  simp [check, selected, different]

theorem zero_fuel_refused (source target : List Atom) (receipt : Receipt)
    (zero : receipt.fuel = 0) : check source target receipt = false := by
  cases selected : selectNextScheduled (cSupportedSourceExecFacts source) with
  | none => simp [check, selected]
  | some directive => simp [check, selected, zero, collect]

#print axioms check_exact
#print axioms accepted_rows_complete
#print axioms accepted_input_exact
#print axioms accepted_witness_positions
#print axioms check_sound
#print axioms check_complete
#print axioms receipt_exists_iff_step
#print axioms uniqueKeysB_exact
#print axioms supportAdmissionB_invariant
#print axioms support_step_iff_receipt
#print axioms admitted_support_step_iff_receipt
#print axioms accepted_same_directive_event
#print axioms accepted_scheduled_event

end Mettapedia.Languages.ProcessCalculi.MORK.MM2StepReceipt
