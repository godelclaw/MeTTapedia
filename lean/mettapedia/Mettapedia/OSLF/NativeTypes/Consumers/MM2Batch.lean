import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorResumable
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Generated native observations for captured MM2 batch publication

The underlying transitions are the existing retained structural matcher and
atomic publication events. The native type is the generated OSLF diamond of
the committed-store observation. Its independent meaning is a selected source
firing against the captured store, with no publication from a stale snapshot.

Both publication profiles use one-way matching. One finalizes all rows of
each sink before the next sink; the other applies each row's sinks before the
next row. Neither is identified with MORK kernel unification, and this does not
verify the Python MM2-to-MeTTa translator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Machines.Cursor
open WQComputable


abbrev Configuration := List Atom × ProgrammableSpaceMM2Resumable.Residual

/-- The two existing public effect orders are different languages. -/
inductive Profile where
  | sinkMajor | rowMajor
  deriving DecidableEq, Repr

def Advance (profile : Profile) := match profile with
  | .sinkMajor => ProgrammableSpaceMM2Resumable.Advance
  | .rowMajor => ProgrammableSpaceMM2RowMajorResumable.Advance

def finalize (profile : Profile) := match profile with
  | .sinkMajor => ProgrammableSpaceMM2Matching.finalize
  | .rowMajor => ProgrammableSpaceMM2RowMajor.finalize

def sourceFire (profile : Profile) := match profile with
  | .sinkMajor => cFireRuleScopedSourceExecFact
  | .rowMajor => ProgrammableSpaceMM2RowMajor.fire

def after (profile : Profile) (receipt : ProgrammableSpaceMM2.Receipt) : List Atom :=
  finalize profile receipt.before receipt.request receipt.rows

def Transition (profile : Profile) (scope : ProgrammableSpaceMM2.Scope)
    (before after : Configuration) : Prop :=
  ∃ receipt, Advance profile scope before.1 before.2 receipt after.1 after.2

abbrev theory (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) :=
  equalityGSLT Configuration (Transition profile scope)

theorem completed_finalize (profile : Profile) (space : List Atom)
    (request : ProgrammableSpaceMM2.Request) (fuel : Nat) (rows : List MM2MatchingCursor.Row)
    (completed : HostCalls.collect
      (MM2MatchingCursor.StructuralQuanta.pull
        (MM2MatchingCursor.entries (ProgrammableSpaceMM2Matching.snapshot space request)))
      fuel (ProgrammableSpaceMM2Matching.initial space request) = some rows) :
    finalize profile space request rows = sourceFire profile space request.directive := by
  cases profile with
  | sinkMajor => exact ProgrammableSpaceMM2Matching.completed_finalize _ _ fuel _ completed
  | rowMajor => exact ProgrammableSpaceMM2RowMajor.completed_finalize _ _ fuel _ completed

/-- This observation selects actual committed residuals, not private rows. -/
def committedStore (target : List Atom) (configuration : Configuration) : Prop :=
  configuration.1 = target ∧ ∃ receipt, configuration.2 = .committed receipt

/-- A genuine type in the OSLF generated from the existing source machine. -/
def publicationType (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (target : List Atom) : GSLTNativeType (theory profile scope) where
  sort := ()
  pred := semanticDiamond (theory profile scope) (saturatePredicate (theory profile scope) (committedStore target))

def Inhabits (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (target : List Atom) (configuration : Configuration) : Prop :=
  (gsltOSLF (theory profile scope)).satisfies (S := ()) configuration (publicationType profile scope target).pred

theorem inhabits_iff_publication (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (target : List Atom)
    (configuration : Configuration) :
    Inhabits profile scope target configuration ↔
      ∃ receipt publication, Advance profile scope configuration.1 configuration.2
        receipt target (.committed publication) := by
  change gsltDiamond (theory profile scope) (saturatePredicate (theory profile scope) (committedStore target)).1
    configuration ↔ _
  rw [gsltDiamond_spec]
  constructor
  · rintro ⟨next, ⟨receipt, step⟩, representative, equivalent, sameStore, publication, sameResidual⟩
    have same : next = representative := equivalent
    cases same
    cases next with
    | mk store residual =>
      simp only at sameStore sameResidual step
      subst store
      subst residual
      exact ⟨receipt, publication, step⟩
  · rintro ⟨receipt, publication, step⟩
    exact ⟨(target, .committed publication), ⟨receipt, step⟩,
      (target, .committed publication), rfl, rfl, publication, rfl⟩

/-- A source firing is an independent whole-batch operation. The generated
modal observation additionally enforces the captured store boundary. -/
theorem inhabits_iff_source (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) :
    Inhabits profile scope target (current, .matching checkpoint) ↔
      current = checkpoint.before ∧
        MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive ∧
        target = sourceFire profile checkpoint.before checkpoint.request.directive := by
  rw [inhabits_iff_publication]
  cases profile with
  | sinkMajor =>
    constructor
    · rintro ⟨receipt, publication, step⟩
      cases step with
      | commit checkpoint grant spent result selected completed =>
        obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result completed
        exact ⟨rfl, selected, completed_finalize .sinkMajor _ _ fuel _ collected⟩
    · rintro ⟨rfl, selected, targetExact⟩
      obtain ⟨receipt, actualTarget, publication, step, _, exactTarget⟩ :=
        ProgrammableSpaceMM2Resumable.selected_checkpoint_has_publication scope checkpoint selected
      refine ⟨receipt, publication, ?_⟩
      simpa only [Advance, sourceFire, targetExact, exactTarget] using step
  | rowMajor =>
    constructor
    · rintro ⟨receipt, publication, step⟩
      cases step with
      | commit checkpoint grant spent result selected completed =>
        obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result completed
        exact ⟨rfl, selected, completed_finalize .rowMajor _ _ fuel _ collected⟩
    · rintro ⟨rfl, selected, targetExact⟩
      obtain ⟨receipt, actualTarget, publication, step, _, exactTarget⟩ :=
        ProgrammableSpaceMM2RowMajorResumable.selected_checkpoint_has_publication scope checkpoint selected
      refine ⟨receipt, publication, ?_⟩
      simpa only [Advance, sourceFire, targetExact, exactTarget] using step

theorem stale_snapshot_not_inhabits (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (stale : current ≠ checkpoint.before) :
    ¬ Inhabits profile scope target (current, .matching checkpoint) := by
  rw [inhabits_iff_source]
  exact fun valid => stale valid.1

/-- The scheduler computation retains the distinction between refusing an
unsupported directive and selecting the requested supported directive. -/
def selectedDirective (scope : ProgrammableSpaceMM2.Scope) (store : List Atom) : Option SourceExecFact :=
  match scope with
  | .leaveInert => selectNextScheduled (cSupportedSourceExecFacts store)
  | .consume => (selectNextScheduled (cRawExecFacts store)).bind decodeSupportedSourceExec

theorem selectedDirective_exact (scope : ProgrammableSpaceMM2.Scope) (store : List Atom)
    (directive : SourceExecFact) :
    selectedDirective scope store = some directive ↔
      MM2MatchingBatch.SelectedFor scope store directive := by
  cases scope with
  | leaveInert => rfl
  | consume =>
    simp only [selectedDirective, MM2MatchingBatch.SelectedFor, Option.bind_eq_some_iff]

inductive Verdict where
  | proved | refuted | unknown
  deriving DecidableEq, Repr

inductive CheckResult where
  | proved (receipt : ProgrammableSpaceMM2.Receipt) (spent : Nat)
  | refuted
  | unknown (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint)

def CheckResult.verdict : CheckResult → Verdict
  | .proved _ _ => .proved
  | .refuted => .refuted
  | .unknown _ => .unknown

/-- Only a completed retained matcher can produce evidence. A paused
matcher remains unknown even after accumulating every eventual answer. -/
def check (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (grant : Nat) : CheckResult :=
  if current = checkpoint.before then
    if selectedDirective scope checkpoint.before = some checkpoint.request.directive then
      match computed : checkpoint.resume grant with
      | (spent, .paused packet) => .unknown (checkpoint.afterPause grant spent packet computed)
      | (spent, .done result) =>
        let receipt : ProgrammableSpaceMM2.Receipt := ⟨checkpoint.request, checkpoint.before, result.2.1⟩
        if after profile receipt = target then .proved receipt spent else .refuted
    else .refuted
  else .refuted

theorem completed_after (profile : Profile) (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (grant spent : Nat)
    (result : ProgrammableSpaceMM2Resumable.FinishedFor checkpoint.before checkpoint.request)
    (completed : checkpoint.resume grant = (spent, .done result)) :
    after profile (⟨checkpoint.request, checkpoint.before, result.2.1⟩ : ProgrammableSpaceMM2.Receipt) =
      sourceFire profile checkpoint.before checkpoint.request.directive := by
  obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result completed
  exact completed_finalize profile _ _ fuel _ collected

theorem check_completed (profile : Profile) (scope : ProgrammableSpaceMM2.Scope)
    (current target : List Atom) (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint)
    (grant spent : Nat) (result : ProgrammableSpaceMM2Resumable.FinishedFor checkpoint.before checkpoint.request)
    (same : current = checkpoint.before)
    (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive)
    (completed : checkpoint.resume grant = (spent, .done result)) :
    check profile scope current target checkpoint grant =
      if after profile ⟨checkpoint.request, checkpoint.before, result.2.1⟩ = target then
        .proved ⟨checkpoint.request, checkpoint.before, result.2.1⟩ spent else .refuted := by
  unfold check
  rw [if_pos same, if_pos ((selectedDirective_exact _ _ _).mpr selected)]
  split
  next actualSpent packet paused => cases (Prod.mk.inj (paused.symm.trans completed)).2
  next actualSpent actualResult done =>
    have parts := Prod.mk.inj (done.symm.trans completed)
    have sameSpent := parts.1
    have sameResult := Outcome.done.inj parts.2
    subst actualSpent
    subst actualResult
    rfl

theorem check_paused (profile : Profile) (scope : ProgrammableSpaceMM2.Scope)
    (current target : List Atom) (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint)
    (grant spent : Nat) (packet : ProgrammableSpaceMM2Resumable.PacketFor checkpoint.before checkpoint.request)
    (same : current = checkpoint.before)
    (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive)
    (paused : checkpoint.resume grant = (spent, .paused packet)) :
    check profile scope current target checkpoint grant =
      .unknown (checkpoint.afterPause grant spent packet paused) := by
  unfold check
  rw [if_pos same, if_pos ((selectedDirective_exact _ _ _).mpr selected)]
  split
  next actualSpent actualPacket actual =>
    have parts := Prod.mk.inj (actual.symm.trans paused)
    have sameSpent := parts.1
    have samePacket := Outcome.paused.inj parts.2
    subst actualSpent
    subst actualPacket
    rfl
  next actualSpent actualResult done => cases (Prod.mk.inj (done.symm.trans paused)).2

/-- Accepted evidence is the actual complete receipt, retaining all physical
witness rows; source agreement is derived from the independent source matcher. -/
theorem check_proved (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (grant spent : Nat) (receipt : ProgrammableSpaceMM2.Receipt)
    (accepted : check profile scope current target checkpoint grant = .proved receipt spent) :
    Inhabits profile scope target (current, .matching checkpoint) ∧
      receipt.request = checkpoint.request ∧ receipt.before = current ∧ after profile receipt = target ∧
      receipt.rows.map (ProgrammableSpaceMM2Grammar.sourceRow receipt.request.directive.rule.input) =
        cMatchInputSpecMork [] (ProgrammableSpaceMM2Matching.snapshot receipt.before receipt.request)
          receipt.request.directive.rule.input := by
  unfold check at accepted
  split at accepted
  next same =>
    split at accepted
    next selected =>
      split at accepted
      next actualSpent packet computed => cases accepted
      next actualSpent result computed =>
        dsimp only at accepted
        split at accepted
        next targetExact =>
          cases accepted
          obtain ⟨fuel, collected⟩ := checkpoint.completed_rows grant spent result computed
          refine ⟨(inhabits_iff_source profile scope current target checkpoint).mpr
            ⟨same, (selectedDirective_exact _ _ _).mp selected,
              targetExact.symm.trans (completed_after profile checkpoint grant spent result computed)⟩,
            rfl, same.symm, targetExact, ?_⟩
          exact ProgrammableSpaceMM2Matching.completed_rows _ _ fuel _ collected
        next => cases accepted
    next => cases accepted
  next => cases accepted

theorem check_refuted (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (grant : Nat)
    (rejected : check profile scope current target checkpoint grant = .refuted) :
    ¬ Inhabits profile scope target (current, .matching checkpoint) := by
  rw [inhabits_iff_source]
  intro valid
  unfold check at rejected
  rw [if_pos valid.1, if_pos ((selectedDirective_exact _ _ _).mpr valid.2.1)] at rejected
  split at rejected
  next spent packet computed => cases rejected
  next spent result computed =>
    have targetExact : after profile
        (⟨checkpoint.request, checkpoint.before, result.2.1⟩ : ProgrammableSpaceMM2.Receipt) =
        target := (completed_after profile checkpoint grant spent result computed).trans valid.2.2.symm
    rw [if_pos targetExact] at rejected
    cases rejected

theorem check_unknown_retains_pause (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (grant : Nat)
    (next : ProgrammableSpaceMM2Resumable.Checkpoint)
    (unknown : check profile scope current target checkpoint grant = .unknown next) :
    ∃ packet, checkpoint.resume grant = (next.spent, .paused packet) ∧
      next.before = checkpoint.before ∧ next.request = checkpoint.request ∧
      next.granted = checkpoint.granted + grant := by
  unfold check at unknown
  split at unknown
  next =>
    split at unknown
    next =>
      split at unknown
      next actualSpent packet computed =>
        cases unknown
        exact ⟨packet, computed, rfl, rfl, rfl⟩
      next actualSpent result computed =>
        dsimp only at unknown
        split at unknown <;> cases unknown
    next => cases unknown
  next => cases unknown

/-- True generated membership eventually yields executable evidence from
every reachable retained checkpoint. The witness bounds matcher polls only. -/
theorem check_complete (profile : Profile) (scope : ProgrammableSpaceMM2.Scope)
    (current target : List Atom) (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint)
    (holds : Inhabits profile scope target (current, .matching checkpoint)) :
    ∃ grant spent receipt, check profile scope current target checkpoint grant = .proved receipt spent := by
  obtain ⟨same, selected, sourceExact⟩ := (inhabits_iff_source _ _ _ _ _).mp holds
  obtain ⟨grant, spent, result, completed⟩ := checkpoint.finite_completion
  refine ⟨grant, spent, ⟨checkpoint.request, checkpoint.before, result.2.1⟩, ?_⟩
  unfold check
  rw [if_pos same, if_pos ((selectedDirective_exact _ _ _).mpr selected)]
  split
  next actualSpent packet paused =>
    have impossible := (Prod.mk.inj (paused.symm.trans completed)).2
    cases impossible
  next actualSpent actualResult done =>
    have same := Prod.mk.inj (done.symm.trans completed)
    have sameSpent := same.1
    have sameResult := Outcome.done.inj same.2
    subst actualSpent
    subst actualResult
    rw [if_pos ((completed_after profile checkpoint grant spent result completed).trans sourceExact.symm)]

theorem inhabits_iff_check_proves (profile : Profile) (scope : ProgrammableSpaceMM2.Scope)
    (current target : List Atom) (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) :
    Inhabits profile scope target (current, .matching checkpoint) ↔
      ∃ grant spent receipt, check profile scope current target checkpoint grant = .proved receipt spent := by
  constructor
  · exact check_complete profile scope current target checkpoint
  · rintro ⟨grant, spent, receipt, accepted⟩
    exact (check_proved profile scope current target checkpoint grant spent receipt accepted).1

end Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
