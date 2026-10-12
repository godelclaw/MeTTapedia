import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderSearch

/-!
# Equation-enabled firing and exact retained occurrence controls

These calculations use the actual authored conditional interpreter. A first
representative visit can yield no primitive actions while retaining a pending
equation-enabled representative. Resumption exposes both authored declarations
without identifying their equal targets or counting conversions as reactions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderRunControls

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Engine
open EquationFrontierBinderProfile EquationFrontierBinderSearch
open Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

def tucked {ambient : Nat} (index : Fin (ambient + 1)) : State ambient :=
  ⟨.tucked, index, .permit⟩

def exposed {ambient : Nat} (index : Fin (ambient + 1)) : State ambient :=
  ⟨.exposed, index, .permit⟩

def finished {ambient : Nat} (index : Fin (ambient + 1)) : State ambient :=
  ⟨.finished, index, .permit⟩

def forwardOrigin {ambient : Nat} (index : Fin (ambient + 1)) :
    ConditionalEquationExecution.EquationReceipt :=
  ⟨expectedReceipt ambient index .permit .exposed 0, 0, .forward⟩

def reverseOrigin {ambient : Nat} (index : Fin (ambient + 1)) :
    ConditionalEquationExecution.EquationReceipt :=
  ⟨expectedReceipt ambient index .permit .tucked 0, 0, .reverse⟩

def firstEntry {ambient : Nat} (index : Fin (ambient + 1)) :
    Entry Pattern ConditionalEquationExecution.EquationReceipt :=
  ⟨(tucked index).pattern, []⟩

def secondEntry {ambient : Nat} (index : Fin (ambient + 1)) :
    Entry Pattern ConditionalEquationExecution.EquationReceipt :=
  ⟨(exposed index).pattern, [(forwardOrigin index, (exposed index).pattern)]⟩

def primitiveOrigin {ambient : Nat} (index : Fin (ambient + 1)) (declaration : Nat) :
    AuthoredEquationOccurrenceSearch.RuleOrigin :=
  ⟨expectedReceipt ambient index .permit .finished 0, declaration⟩

def firedReceipt {ambient : Nat} (index : Fin (ambient + 1)) (declaration : Nat) :
    EquationOccurrenceNativeReceipts.RuntimeReceipt :=
  ⟨secondEntry index, declaration, primitiveOrigin index declaration, (finished index).pattern⟩

theorem exposed_ne_tucked {ambient : Nat} (index : Fin (ambient + 1)) :
    (exposed index).pattern ≠ (tucked index).pattern := by
  intro equal
  have states := state_pattern_injective equal
  have phases := congrArg State.phase states
  cases phases

theorem equation_batches {ambient : Nat} (index : Fin (ambient + 1)) :
    (model ambient [.permit]).equations (tucked index).pattern =
      ⟨[(forwardOrigin index, (exposed index).pattern)], []⟩ ∧
    (model ambient [.permit]).equations (exposed index).pattern =
      ⟨[(reverseOrigin index, (tucked index).pattern)], []⟩ := by
  change AuthoredEquationOccurrenceSearch.equationBatch _ _ _ _ _ _ = _ ∧
    AuthoredEquationOccurrenceSearch.equationBatch _ _ _ _ _ _ = _
  simp [equationBatch_family, expectedEquationReceipts, expectedReceipts,
    equationSourcePhase, equationTargetPhase, tucked, exposed, forwardOrigin, reverseOrigin,
    expectedReceipt]

theorem firing_batches {ambient : Nat} (index : Fin (ambient + 1)) :
    (model ambient [.permit]).firings (tucked index).pattern = ⟨[], []⟩ ∧
    (model ambient [.permit]).firings (exposed index).pattern =
      ⟨[(primitiveOrigin index 0, (finished index).pattern),
        (primitiveOrigin index 1, (finished index).pattern)], []⟩ := by
  change AuthoredEquationOccurrenceSearch.firingBatch _ _ _ _ _ _ = _ ∧
    AuthoredEquationOccurrenceSearch.firingBatch _ _ _ _ _ _ = _
  simp [firingBatch_family, expectedRuleReceipts, expectedReceipts, tucked,
    exposed, finished, primitiveOrigin, expectedReceipt]

def paused {ambient : Nat} (index : Fin (ambient + 1)) :
    Snapshot Pattern ConditionalEquationExecution.EquationReceipt
      AuthoredEquationOccurrenceSearch.RuleOrigin AuthoredEquationOccurrenceSearch.Obligation where
  pending := [secondEntry index]
  visited := [firstEntry index]
  conversions := [secondEntry index]
  receipts := []
  parked := []
  work := 1

def completed {ambient : Nat} (index : Fin (ambient + 1)) :
    Snapshot Pattern ConditionalEquationExecution.EquationReceipt
      AuthoredEquationOccurrenceSearch.RuleOrigin AuthoredEquationOccurrenceSearch.Obligation where
  pending := []
  visited := [firstEntry index, secondEntry index]
  conversions := [secondEntry index,
    (secondEntry index).extend (reverseOrigin index, (tucked index).pattern)]
  receipts := [firedReceipt index 0, firedReceipt index 1]
  parked := []
  work := 2

theorem run_one {ambient : Nat} (index : Fin (ambient + 1)) :
    execute [.permit] 1 (tucked index) = paused index := by
  have equations := (equation_batches index).1
  have firings := (firing_batches index).1
  simp [execute, run, tick, initial, equations, firings, discoveries, Entry.extend,
    readouts, obligations, paused, firstEntry, secondEntry, exposed_ne_tucked]

theorem resume_one {ambient : Nat} (index : Fin (ambient + 1)) :
    run (model ambient [.permit]) 1 (paused index) = completed index := by
  have equations := (equation_batches index).2
  have firings := (firing_batches index).2
  simp [run, tick, paused, firstEntry, secondEntry, equations, firings,
    exposed_ne_tucked, discoveries, Entry.extend, readouts, obligations, completed, firedReceipt]

theorem run_two {ambient : Nat} (index : Fin (ambient + 1)) :
    execute [.permit] 2 (tucked index) = completed index := by
  rw [show (2 : Nat) = 1 + 1 from rfl, exact_resume, run_one, resume_one]

theorem partial_empty_retains_work {ambient : Nat} (index : Fin (ambient + 1)) :
    (execute [.permit] 1 (tucked index)).receipts = [] ∧
      status [.permit] 1 (tucked index) = .searching 1 := by
  rw [run_one]
  simp [status, run_one, paused]

theorem resumed_firings_keep_origins {ambient : Nat} (index : Fin (ambient + 1)) :
    (execute [.permit] 2 (tucked index)).receipts =
      [firedReceipt index 0, firedReceipt index 1] ∧
      (firedReceipt index 0).target = (firedReceipt index 1).target ∧
      (firedReceipt index 0).origin ≠ (firedReceipt index 1).origin := by
  rw [run_two]
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have declarations := congrArg AuthoredEquationOccurrenceSearch.RuleOrigin.ruleIndex equal
  cases declarations

theorem completed_certificate_checked {ambient : Nat} (index : Fin (ambient + 1)) :
    status [.permit] 2 (tucked index) = .certificateChecked := by
  apply (checked_status_iff_quiescent [.permit] (tucked index) 2).mpr
  simp [run_two, quiescent, completed]

theorem one_conversion_one_premise {ambient : Nat} (index : Fin (ambient + 1))
    (declaration : Fin 2) :
    (firedReceipt index declaration.val).representative.conversions.length = 1 ∧
      (firedReceipt index declaration.val).origin.history.length = 1 := by
  exact ⟨rfl, rfl⟩

theorem fired_member {ambient : Nat} (index : Fin (ambient + 1))
    (declaration : Fin 2) :
    firedReceipt index declaration.val ∈ (execute [.permit] 2 (tucked index)).receipts := by
  rw [run_two]
  have alternatives : declaration.val = 0 ∨ declaration.val = 1 := by omega
  rcases alternatives with first | second
  · simp [completed, first]
  · simp [completed, second]

def actualNativeReceipt {ambient : Nat} (index : Fin (ambient + 1))
    (declaration : Fin 2) :=
  sortedNativeReceipt [.permit] (tucked index) 2
    (firedReceipt index declaration.val) (fired_member index declaration)

theorem actual_event_accounts {ambient : Nat} (index : Fin (ambient + 1))
    (declaration : Fin 2) :
    EquationOccurrenceNativeReceipts.administration (provider [.permit]) language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
        (ambientContext ambient) .proc (actualNativeReceipt index declaration).1 = 1 ∧
      (EquationOccurrenceNativeReceipts.history (provider [.permit]) language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
        (ambientContext ambient) .proc (actualNativeReceipt index declaration).1).length = 1 ∧
      (actualNativeReceipt index declaration).1.val.origin.history.length = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem actual_native_readouts {ambient : Nat} (index : Fin (ambient + 1))
    (declaration : Fin 2) :
    (actualNativeReceipt index declaration).1.val.target = (finished index).pattern ∧
      (actualNativeReceipt index declaration).1.val.origin.ruleIndex = declaration.val ∧
      (actualNativeReceipt index declaration).1.val.representative.conversions =
        [(forwardOrigin index, (exposed index).pattern)] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Empty partial output coexists with an actual independently admitted step. -/
theorem partial_empty_does_not_establish_absence {ambient : Nat}
    (index : Fin (ambient + 1)) :
    (execute [.permit] 1 (tucked index)).receipts = [] ∧
      (AuthoredEquationOccurrenceSemantics.gslt (provider [.permit]) language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
        (ambientContext ambient) .proc).Step (tucked index).pattern (finished index).pattern := by
  refine ⟨(partial_empty_retains_work index).1, ?_⟩
  exact EquationOccurrenceNativeReceipts.semantic_step (provider [.permit]) language
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
    (ambientContext ambient) .proc
    (nativeReceipt [.permit] (tucked index) 2 (firedReceipt index 0) (fired_member index 0))

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderRunControls
