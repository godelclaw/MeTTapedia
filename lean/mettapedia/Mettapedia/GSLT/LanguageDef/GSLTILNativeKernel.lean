import Mettapedia.GSLT.LanguageDef.GSLTILFreePath
import Mettapedia.GSLT.LanguageDef.SemanticService
import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution
import Mettapedia.OSLF.MeTTaIL.PatternTokens

/-!
# Source-native GSLT-ML command evidence

The native command core has the existing `at` and `via` forms and exactly
three reductions. A journal supplies one local certificate and an explicit
next state for each reduction. The dispatcher checks the command frame; the
selected fibre and transport checkers check their own independently stated
local evidence. No proof search or normalization occurs in the dispatcher.

The general theorem is relative to these local evidence contracts. The finite
catalog instance below earns them by actual indexed row lookup. It is not a
claim that every abstract GSLT fibre is effective, or that every authored
`.module` is a finite catalog. Pattern data and its structural codec are not
a textual source parser.

The concrete literal replay discipline uses command framing, indexed catalog
lookup, structural syntax equality and finite journal sequencing. It performs
no substitution, conversion search or implicit normalization. The generic
local-checker interface alone does not imply that discipline or a resource
class for an arbitrary installed fibre.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A reversible view of the two existing command frames. -/
inductive Command where
  | at (stage state : Pattern)
  | via (kind route sourceStage targetStage state : Pattern)
  deriving DecidableEq, Repr

def Command.toPattern : Command → Pattern
  | .at stage state => atPattern stage state
  | .via kind route sourceStage targetStage state =>
      viaPattern kind route sourceStage targetStage state

def Command.ofPattern? : Pattern → Option Command
  | .apply "at" [stage, state] => some (.at stage state)
  | .apply "via" [kind, route, sourceStage, targetStage, state] =>
      some (.via kind route sourceStage targetStage state)
  | _ => none

def Command.state : Command → Pattern
  | .at _ state | .via _ _ _ _ state => state

@[simp] theorem Command.ofPattern?_toPattern (command : Command) :
    Command.ofPattern? command.toPattern = some command := by
  cases command <;> rfl

theorem Command.toPattern_injective : Function.Injective Command.toPattern := by
  intro first second same
  have decoded := congrArg Command.ofPattern? same
  simpa only [Command.ofPattern?_toPattern, Option.some.injEq] using decoded

theorem Command.toPattern_wellFormed (command : Command) :
    WellFormedCommand command.toPattern := by
  cases command with
  | «at» stage state => exact .returned stage state
  | via kind route sourceStage targetStage state =>
      exact .pending kind route sourceStage targetStage state

theorem Command.exists_iff_wellFormed (pattern : Pattern) :
    (∃ command : Command, command.toPattern = pattern) ↔ WellFormedCommand pattern := by
  constructor
  · rintro ⟨command, rfl⟩
    exact command.toPattern_wellFormed
  · intro formed
    cases formed with
    | returned stage state => exact ⟨.at stage state, rfl⟩
    | pending kind route sourceStage targetStage state =>
        exact ⟨.via kind route sourceStage targetStage state, rfl⟩

/-- Local source relations are specified before choosing certificates. -/
structure Source where
  fibre : Pattern → Pattern → Pattern → Prop
  transport : Pattern → Pattern → Pattern → Pattern → Pattern → Pattern → Prop

/-- The three original command rules over the stated local source relations. -/
inductive Step (source : Source) : Command → Command → Prop where
  | fibre {stage first last : Pattern} : source.fibre stage first last →
      Step source (.at stage first) (.at stage last)
  | underneath {kind route sourceStage targetStage first last : Pattern} :
      source.fibre sourceStage first last →
      Step source (.via kind route sourceStage targetStage first)
        (.via kind route sourceStage targetStage last)
  | transport {kind route sourceStage targetStage first last : Pattern} :
      source.transport kind route sourceStage targetStage first last →
      Step source (.via kind route sourceStage targetStage first) (.at targetStage last)

/-- Finite source executions, independent of submitted journals. -/
inductive Runs (source : Source) : Command → Command → Prop where
  | refl (command : Command) : Runs source command command
  | tail {first middle last : Command} :
      Step source first middle → Runs source middle last → Runs source first last

/-- Certificate meanings belong to the selected local fibre/route service. -/
structure LocalEvidence where
  FibreProof : Type
  TransportProof : Type
  fibre : FibreProof → Pattern → Pattern → Pattern → Prop
  transport : TransportProof → Pattern → Pattern → Pattern → Pattern → Pattern → Pattern → Prop

/-- Only local certificate checking is supplied to the command dispatcher. -/
structure LocalChecking (evidence : LocalEvidence) where
  fibre : evidence.FibreProof → Pattern → Pattern → Pattern → Bool
  transport : evidence.TransportProof → Pattern → Pattern → Pattern → Pattern → Pattern → Pattern → Bool
  fibre_exact : ∀ proof stage first last,
    fibre proof stage first last = true ↔ evidence.fibre proof stage first last
  transport_exact : ∀ proof kind route sourceStage targetStage first last,
    transport proof kind route sourceStage targetStage first last = true ↔
      evidence.transport proof kind route sourceStage targetStage first last

/-- Source coverage is a separate local theorem, not a dispatcher callback. -/
structure LocalCoverage (source : Source) (evidence : LocalEvidence) : Prop where
  fibre : ∀ stage first last,
    source.fibre stage first last ↔ ∃ proof, evidence.fibre proof stage first last
  transport : ∀ kind route sourceStage targetStage first last,
    source.transport kind route sourceStage targetStage first last ↔
      ∃ proof, evidence.transport proof kind route sourceStage targetStage first last

/-- Every intermediate next state is materialized; its frame is retained by
the dispatcher, not selected by the certificate. -/
inductive Entry (FibreProof TransportProof : Type) where
  | fibre (next : Pattern) (proof : FibreProof)
  | underneath (next : Pattern) (proof : FibreProof)
  | transport (next : Pattern) (proof : TransportProof)
  deriving Repr

def Entry.next {F T : Type} : Entry F T → Pattern
  | .fibre next _ | .underneath next _ | .transport next _ => next

abbrev Journal (evidence : LocalEvidence) :=
  List (Entry evidence.FibreProof evidence.TransportProof)

/-- Logical evidence replay does not mention the executable checker. -/
def EntryJudges (evidence : LocalEvidence)
    (entry : Entry evidence.FibreProof evidence.TransportProof)
    (first last : Command) : Prop :=
  match first, entry with
  | .at stage state, .fibre next proof =>
      last = .at stage next ∧ evidence.fibre proof stage state next
  | .via kind route sourceStage targetStage state, .underneath next proof =>
      last = .via kind route sourceStage targetStage next ∧
        evidence.fibre proof sourceStage state next
  | .via kind route sourceStage targetStage state, .transport next proof =>
      last = .at targetStage next ∧
        evidence.transport proof kind route sourceStage targetStage state next
  | _, _ => False

def executeEntry {evidence : LocalEvidence} (checking : LocalChecking evidence)
    (first : Command) (entry : Entry evidence.FibreProof evidence.TransportProof) :
    Option Command :=
  match first, entry with
  | .at stage state, .fibre next proof =>
      if checking.fibre proof stage state next then some (.at stage next) else none
  | .via kind route sourceStage targetStage state, .underneath next proof =>
      if checking.fibre proof sourceStage state next then
        some (.via kind route sourceStage targetStage next) else none
  | .via kind route sourceStage targetStage state, .transport next proof =>
      if checking.transport proof kind route sourceStage targetStage state next then
        some (.at targetStage next) else none
  | _, _ => none

theorem executeEntry_exact {evidence : LocalEvidence}
    (checking : LocalChecking evidence) (first last : Command)
    (entry : Entry evidence.FibreProof evidence.TransportProof) :
    executeEntry checking first entry = some last ↔ EntryJudges evidence entry first last := by
  cases first <;> cases entry <;>
    simp [executeEntry, EntryJudges, checking.fibre_exact,
      checking.transport_exact, and_comm, eq_comm]

inductive JournalJudges (evidence : LocalEvidence) :
    Journal evidence → Command → Command → Prop where
  | nil (command : Command) : JournalJudges evidence [] command command
  | cons {entry : Entry evidence.FibreProof evidence.TransportProof}
      {rest : Journal evidence} {first middle last : Command} :
      EntryJudges evidence entry first middle → JournalJudges evidence rest middle last →
      JournalJudges evidence (entry :: rest) first last

def replay {evidence : LocalEvidence} (checking : LocalChecking evidence) :
    Command → Journal evidence → Option Command
  | first, [] => some first
  | first, entry :: rest =>
      (executeEntry checking first entry).bind (fun middle => replay checking middle rest)

theorem replay_exact {evidence : LocalEvidence} (checking : LocalChecking evidence)
    (journal : Journal evidence) (first last : Command) :
    replay checking first journal = some last ↔ JournalJudges evidence journal first last := by
  induction journal generalizing first with
  | nil =>
      constructor
      · intro same
        have equal : first = last := Option.some.inj same
        subst last
        exact .nil first
      · intro judged
        cases judged
        rfl
  | cons entry rest ih =>
      constructor
      · intro accepted
        obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp accepted
        exact .cons ((executeEntry_exact checking _ _ _).mp head) ((ih middle).mp tail)
      · intro judged
        cases judged with
        | cons head tail =>
            exact Option.bind_eq_some_iff.mpr
              ⟨_, (executeEntry_exact checking _ _ _).mpr head, (ih _).mpr tail⟩

def check {evidence : LocalEvidence} (checking : LocalChecking evidence)
    (first last : Command) (journal : Journal evidence) : Bool :=
  decide (replay checking first journal = some last)

theorem check_exact {evidence : LocalEvidence} (checking : LocalChecking evidence)
    (first last : Command) (journal : Journal evidence) :
    check checking first last journal = true ↔ JournalJudges evidence journal first last := by
  simp only [check, decide_eq_true_eq, replay_exact]

theorem EntryJudges.sourceStep {source : Source} {evidence : LocalEvidence}
    (coverage : LocalCoverage source evidence)
    {entry : Entry evidence.FibreProof evidence.TransportProof} {first last : Command}
    (judged : EntryJudges evidence entry first last) : Step source first last := by
  cases first <;> cases entry <;> simp only [EntryJudges] at judged
  all_goals rcases judged with ⟨rfl, leaf⟩
  · exact .fibre ((coverage.fibre _ _ _).mpr ⟨_, leaf⟩)
  · exact .underneath ((coverage.fibre _ _ _).mpr ⟨_, leaf⟩)
  · exact .transport ((coverage.transport _ _ _ _ _ _).mpr ⟨_, leaf⟩)

theorem Step.evidence {source : Source} {evidence : LocalEvidence}
    (coverage : LocalCoverage source evidence) {first last : Command}
    (step : Step source first last) :
    ∃ entry, EntryJudges evidence entry first last := by
  cases step with
  | fibre leaf =>
      obtain ⟨proof, judged⟩ := (coverage.fibre _ _ _).mp leaf
      exact ⟨.fibre _ proof, rfl, judged⟩
  | underneath leaf =>
      obtain ⟨proof, judged⟩ := (coverage.fibre _ _ _).mp leaf
      exact ⟨.underneath _ proof, rfl, judged⟩
  | transport leaf =>
      obtain ⟨proof, judged⟩ := (coverage.transport _ _ _ _ _ _).mp leaf
      exact ⟨.transport _ proof, rfl, judged⟩

theorem JournalJudges.sourceRuns {source : Source} {evidence : LocalEvidence}
    (coverage : LocalCoverage source evidence) {journal : Journal evidence}
    {first last : Command} (judged : JournalJudges evidence journal first last) :
    Runs source first last := by
  induction judged with
  | nil command => exact .refl command
  | cons head _ ih => exact .tail (head.sourceStep coverage) ih

theorem Runs.evidence {source : Source} {evidence : LocalEvidence}
    (coverage : LocalCoverage source evidence) {first last : Command}
    (run : Runs source first last) : ∃ journal, JournalJudges evidence journal first last := by
  induction run with
  | refl command => exact ⟨[], .nil command⟩
  | tail step _ ih =>
      obtain ⟨entry, head⟩ := step.evidence coverage
      obtain ⟨journal, tail⟩ := ih
      exact ⟨entry :: journal, .cons head tail⟩

theorem accepted_iff_runs {source : Source} {evidence : LocalEvidence}
    (coverage : LocalCoverage source evidence) (checking : LocalChecking evidence)
    (first last : Command) :
    (∃ journal, check checking first last journal = true) ↔ Runs source first last := by
  constructor
  · rintro ⟨journal, accepted⟩
    exact ((check_exact checking _ _ _).mp accepted).sourceRuns coverage
  · intro run
    obtain ⟨journal, judged⟩ := run.evidence coverage
    exact ⟨journal, (check_exact checking _ _ _).mpr judged⟩

theorem replay_append {evidence : LocalEvidence} (checking : LocalChecking evidence)
    (first : Command) (earlier later : Journal evidence) :
    replay checking first (earlier ++ later) =
      (replay checking first earlier).bind (fun middle => replay checking middle later) := by
  induction earlier generalizing first with
  | nil => rfl
  | cons entry rest ih => simp only [List.cons_append, replay, ih, Option.bind_assoc]

theorem EntryJudges.state_eq {evidence : LocalEvidence}
    {entry : Entry evidence.FibreProof evidence.TransportProof} {first last : Command}
    (judged : EntryJudges evidence entry first last) : last.state = entry.next := by
  cases first <;> cases entry <;> simp only [EntryJudges] at judged
  all_goals rcases judged with ⟨rfl, _⟩; rfl

/-- Replay does not manufacture an unrecorded intermediate state. Every
state is either the initial state or an explicit next-state payload. -/
theorem JournalJudges.last_state_mem {evidence : LocalEvidence}
    {journal : Journal evidence} {first last : Command}
    (judged : JournalJudges evidence journal first last) :
    last.state ∈ first.state :: journal.map Entry.next := by
  induction judged with
  | nil command => simp
  | cons head _ ih =>
      simp only [List.map_cons, List.mem_cons] at ih ⊢
      exact ih.elim (fun same => Or.inr (Or.inl (same.trans head.state_eq)))
        (fun member => Or.inr (Or.inr member))

private theorem weight_le_sum {α : Type} (weight : α → Nat) {value : α} {values : List α}
    (member : value ∈ values) : weight value ≤ (values.map weight).sum := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [List.map_cons, List.sum_cons]
      rcases member with rfl | tailMember
      · omega
      · have bound := ih tailMember
        omega

/-- The bound charges binary numeric fields and UTF-8 names through the
existing structural Pattern weight. It is a payload bound, not a clock. -/
theorem JournalJudges.state_weight_bound {evidence : LocalEvidence}
    {journal : Journal evidence} {first last : Command}
    (judged : JournalJudges evidence journal first last) :
    Mettapedia.OSLF.MeTTaIL.PatternTokens.weight last.state ≤
      Mettapedia.OSLF.MeTTaIL.PatternTokens.weight first.state +
        (journal.map (fun entry => Mettapedia.OSLF.MeTTaIL.PatternTokens.weight entry.next)).sum := by
  simpa only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def] using
    weight_le_sum Mettapedia.OSLF.MeTTaIL.PatternTokens.weight judged.last_state_mem

theorem replay_prefix_state_bound {evidence : LocalEvidence}
    (checking : LocalChecking evidence) (first middle : Command)
    (earlier later : Journal evidence)
    (accepted : replay checking first earlier = some middle) :
    Mettapedia.OSLF.MeTTaIL.PatternTokens.weight middle.state ≤
      Mettapedia.OSLF.MeTTaIL.PatternTokens.weight first.state +
        ((earlier ++ later).map
          (fun entry => Mettapedia.OSLF.MeTTaIL.PatternTokens.weight entry.next)).sum := by
  have bound := ((replay_exact checking earlier first middle).mp accepted).state_weight_bound
  rw [List.map_append, List.sum_append]
  omega

/-! ## Reference primitive accounting

These counts concern the actual reference replay's local-checker invocations
and indexed list traversal. A generic local checker may compute more; its
resource discipline is not inferred from its Boolean interface. No statement
below identifies these counts with a physical processor or Turing clock.
-/

def entryCallsLeaf {F T : Type} : Command → Entry F T → Bool
  | .at .., .fibre .. => true
  | .via .., .underneath .. => true
  | .via .., .transport .. => true
  | _, _ => false

/-- Replay with the count of local checker invocations actually requested
before acceptance or refusal. Unsupported command/entry pairs invoke none. -/
def replayWithRequests {evidence : LocalEvidence} (checking : LocalChecking evidence) :
    Command → Journal evidence → Option Command × Nat
  | first, [] => (some first, 0)
  | first, entry :: rest =>
      match executeEntry checking first entry with
      | none => (none, if entryCallsLeaf first entry then 1 else 0)
      | some middle =>
          let tail := replayWithRequests checking middle rest
          (tail.1, tail.2 + 1)

theorem replayWithRequests_projection {evidence : LocalEvidence}
    (checking : LocalChecking evidence) (first : Command) (journal : Journal evidence) :
    (replayWithRequests checking first journal).1 = replay checking first journal := by
  induction journal generalizing first with
  | nil => rfl
  | cons entry rest ih =>
      cases outcome : executeEntry checking first entry with
      | none => simp [replayWithRequests, replay, outcome]
      | some middle => simp [replayWithRequests, replay, outcome, ih]

theorem replayWithRequests_bound {evidence : LocalEvidence}
    (checking : LocalChecking evidence) (first : Command) (journal : Journal evidence) :
    (replayWithRequests checking first journal).2 ≤ journal.length := by
  induction journal generalizing first with
  | nil => simp [replayWithRequests]
  | cons entry rest ih =>
      cases outcome : executeEntry checking first entry with
      | none =>
          simp only [replayWithRequests, outcome, List.length_cons]
          split <;> omega
      | some middle =>
          simpa only [replayWithRequests, outcome, List.length_cons, Prod.snd] using
            Nat.add_le_add_right (ih middle) 1

/-- On a successful replay, no supplied inference is skipped or replayed. -/
theorem replayWithRequests_accepted {evidence : LocalEvidence}
    (checking : LocalChecking evidence) (first last : Command) (journal : Journal evidence)
    (accepted : replay checking first journal = some last) :
    (replayWithRequests checking first journal).2 = journal.length := by
  induction journal generalizing first with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp accepted
      simpa only [replayWithRequests, head, List.length_cons, Prod.snd] using
        congrArg (fun n => n + 1) (ih middle tail)

/-- Actual list lookup paired with the number of visited list cells. -/
def lookupWithVisits {α : Type} : List α → Nat → Option α × Nat
  | [], _ => (none, 0)
  | value :: _, 0 => (some value, 1)
  | _ :: rest, n + 1 =>
      let found := lookupWithVisits rest n
      (found.1, found.2 + 1)

theorem lookupWithVisits_projection {α : Type} (values : List α) (index : Nat) :
    (lookupWithVisits values index).1 = values[index]? := by
  induction values generalizing index with
  | nil => simp [lookupWithVisits]
  | cons value values ih =>
      cases index <;> simp [lookupWithVisits, ih]

theorem lookupWithVisits_count {α : Type} (values : List α) (index : Nat) :
    (lookupWithVisits values index).2 = min (index + 1) values.length := by
  induction values generalizing index with
  | nil => simp [lookupWithVisits]
  | cons value values ih =>
      cases index with
      | zero => simp [lookupWithVisits]
      | succ n => simp [lookupWithVisits, ih, Nat.succ_min_succ, Nat.add_assoc]

theorem lookupWithVisits_bound {α : Type} (values : List α) (index : Nat) :
    (lookupWithVisits values index).2 ≤ values.length := by
  rw [lookupWithVisits_count]
  exact Nat.min_le_right _ _

/-! ## The actual finite catalog instance -/

def catalogSource (catalog : Catalog) : Source where
  fibre stage first last := ∃ row ∈ catalog.fibreRows,
    row.stage = stage ∧ row.source = first ∧ row.target = last
  transport kind route sourceStage targetStage first last :=
    ∃ row ∈ catalog.transportRows,
      row.kind = kind ∧ row.route = route ∧ row.sourceStage = sourceStage ∧
        row.targetStage = targetStage ∧ row.source = first ∧ row.target = last

/-- Ordinals select occurrences, including equal rows at different positions. -/
abbrev catalogEvidence (catalog : Catalog) : LocalEvidence where
  FibreProof := Nat
  TransportProof := Nat
  fibre index stage first last := ∃ row,
    catalog.fibreRows[index]? = some row ∧
      row.stage = stage ∧ row.source = first ∧ row.target = last
  transport index kind route sourceStage targetStage first last := ∃ row,
    catalog.transportRows[index]? = some row ∧
      row.kind = kind ∧ row.route = route ∧ row.sourceStage = sourceStage ∧
        row.targetStage = targetStage ∧ row.source = first ∧ row.target = last

def catalogChecking (catalog : Catalog) : LocalChecking (catalogEvidence catalog) where
  fibre index stage first last := match (lookupWithVisits catalog.fibreRows index).1 with
    | none => false
    | some row => decide (row.stage = stage ∧ row.source = first ∧ row.target = last)
  transport index kind route sourceStage targetStage first last :=
    match (lookupWithVisits catalog.transportRows index).1 with
    | none => false
    | some row => decide (row.kind = kind ∧ row.route = route ∧
        row.sourceStage = sourceStage ∧ row.targetStage = targetStage ∧
        row.source = first ∧ row.target = last)
  fibre_exact := by
    intro index stage first last
    simp only [lookupWithVisits_projection]
    cases catalog.fibreRows[index]? <;> simp
  transport_exact := by
    intro index kind route sourceStage targetStage first last
    simp only [lookupWithVisits_projection]
    cases catalog.transportRows[index]? <;> simp

theorem catalogCoverage (catalog : Catalog) :
    LocalCoverage (catalogSource catalog) (catalogEvidence catalog) where
  fibre := by
    intro stage first last
    constructor
    · rintro ⟨row, member, stageEq, firstEq, lastEq⟩
      obtain ⟨index, known⟩ := List.mem_iff_getElem?.mp member
      exact ⟨index, row, known, stageEq, firstEq, lastEq⟩
    · rintro ⟨index, row, known, stageEq, firstEq, lastEq⟩
      exact ⟨row, List.mem_of_getElem? known, stageEq, firstEq, lastEq⟩
  transport := by
    intro kind route sourceStage targetStage first last
    constructor
    · rintro ⟨row, member, kinds, routes, sources, targets, firstEq, lastEq⟩
      obtain ⟨index, known⟩ := List.mem_iff_getElem?.mp member
      exact ⟨index, row, known, kinds, routes, sources, targets, firstEq, lastEq⟩
    · rintro ⟨index, row, known, kinds, routes, sources, targets, firstEq, lastEq⟩
      exact ⟨row, List.mem_of_getElem? known, kinds, routes, sources, targets, firstEq, lastEq⟩

theorem catalogStep_wire (catalog : Catalog) {first last : Command}
    (step : Step (catalogSource catalog) first last) :
    WireStep catalog first.toPattern last.toPattern := by
  cases step with
  | fibre leaf =>
      rcases leaf with ⟨row, member, rfl, rfl, rfl⟩
      exact .fibreAt member
  | underneath leaf =>
      rcases leaf with ⟨row, member, rfl, rfl, rfl⟩
      exact .fibreUnderVia member _ _ _
  | transport leaf =>
      rcases leaf with ⟨row, member, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact .applyVia member

theorem wireStep_commands (catalog : Catalog) {first last : Pattern}
    (step : WireStep catalog first last) :
    ∃ initial final : Command, initial.toPattern = first ∧ final.toPattern = last ∧
      Step (catalogSource catalog) initial final := by
  cases step with
  | @fibreAt row member =>
      exact ⟨.at row.stage row.source, .at row.stage row.target, rfl, rfl,
        .fibre ⟨row, member, rfl, rfl, rfl⟩⟩
  | @fibreUnderVia row member kind route targetStage =>
      exact ⟨.via kind route row.stage targetStage row.source,
        .via kind route row.stage targetStage row.target, rfl, rfl,
        .underneath ⟨row, member, rfl, rfl, rfl⟩⟩
  | @applyVia row member =>
      exact ⟨.via row.kind row.route row.sourceStage row.targetStage row.source,
        .at row.targetStage row.target, rfl, rfl,
        .transport ⟨row, member, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem catalogStep_iff_wireStep (catalog : Catalog) (first last : Command) :
    Step (catalogSource catalog) first last ↔
      WireStep catalog first.toPattern last.toPattern := by
  constructor
  · exact catalogStep_wire catalog
  · intro step
    obtain ⟨initial, final, initialEq, finalEq, native⟩ := wireStep_commands catalog step
    have firstEq := Command.toPattern_injective initialEq
    have lastEq := Command.toPattern_injective finalEq
    simpa only [firstEq, lastEq] using native

/-- Native one-entry checking covers exactly the existing authored wire rule;
there is no assumed agreement with a second command semantics. -/
theorem catalog_entry_exists_iff_wireStep (catalog : Catalog) (first last : Command) :
    (∃ entry, executeEntry (catalogChecking catalog) first entry = some last) ↔
      WireStep catalog first.toPattern last.toPattern := by
  rw [← catalogStep_iff_wireStep]
  constructor
  · rintro ⟨entry, accepted⟩
    exact ((executeEntry_exact _ _ _ _).mp accepted).sourceStep (catalogCoverage catalog)
  · intro step
    obtain ⟨entry, judged⟩ := step.evidence (catalogCoverage catalog)
    exact ⟨entry, (executeEntry_exact _ _ _ _).mpr judged⟩

theorem catalogRuns_wire (catalog : Catalog) {first last : Command}
    (run : Runs (catalogSource catalog) first last) :
    (wireGSLT catalog).MultiStep first.toPattern last.toPattern := by
  induction run with
  | refl command => exact .refl (S := wireGSLT catalog) command.toPattern
  | tail step _ ih => exact .step (S := wireGSLT catalog) (catalogStep_wire catalog step) ih

theorem catalogWire_runs (catalog : Catalog) {initial final : Pattern}
    (path : (wireGSLT catalog).MultiStep initial final)
    (first : Command) (initialEq : first.toPattern = initial) :
    ∃ last : Command, last.toPattern = final ∧ Runs (catalogSource catalog) first last := by
  refine Mettapedia.GSLT.GSLT.MultiStep.rec (S := wireGSLT catalog)
    (motive := fun initial final _ => ∀ first : Command, first.toPattern = initial →
      ∃ last : Command, last.toPattern = final ∧ Runs (catalogSource catalog) first last)
    (fun _ first equal => ⟨first, equal, .refl first⟩) ?_ path first initialEq
  intro initial middle final head tail ih first initialEq
  obtain ⟨left, right, leftEq, rightEq, native⟩ := wireStep_commands catalog head
  have same := Command.toPattern_injective (leftEq.trans initialEq.symm)
  subst left
  obtain ⟨last, finalEq, nativeTail⟩ := ih right rightEq
  exact ⟨last, finalEq, .tail native nativeTail⟩

theorem catalog_runs_iff_wire_paths (catalog : Catalog) (first last : Command) :
    Runs (catalogSource catalog) first last ↔
      (wireGSLT catalog).MultiStep first.toPattern last.toPattern := by
  constructor
  · exact catalogRuns_wire catalog
  · intro path
    obtain ⟨final, finalEq, run⟩ := catalogWire_runs catalog path first rfl
    simpa only [Command.toPattern_injective finalEq] using run

/-- Every finite native source path has a journal, and every accepted journal
is an original wire path, even when the path's intermediate states were not
restricted to the native view in advance. -/
theorem catalog_accepted_iff_wire_paths (catalog : Catalog) (first last : Command) :
    (∃ journal, check (catalogChecking catalog) first last journal = true) ↔
      (wireGSLT catalog).MultiStep first.toPattern last.toPattern :=
  (accepted_iff_runs (catalogCoverage catalog) (catalogChecking catalog) first last).trans
    (catalog_runs_iff_wire_paths catalog first last)

/-- Every original finite surface step has a checked native lowering. This
is a one-step result: route-name ambiguity does not license an unstated
globally coherent choice for an entire surface path. -/
theorem syntax_step_native (program : Syntax.Program) {source target : Pattern}
    (step : Syntax.Step program source target) :
    ∃ first last : Command, ∃ entry,
      Syntax.Elaborates program source first.toPattern ∧
      Syntax.Elaborates program target last.toPattern ∧
      executeEntry (catalogChecking program.toCatalog) first entry = some last := by
  obtain ⟨sourceIR, targetIR, sourceElaboration, targetElaboration, wire⟩ :=
    Syntax.step_preserved program step
  obtain ⟨first, last, firstEq, lastEq, native⟩ := wireStep_commands program.toCatalog wire
  obtain ⟨entry, judged⟩ := native.evidence (catalogCoverage program.toCatalog)
  exact ⟨first, last, entry, firstEq ▸ sourceElaboration, lastEq ▸ targetElaboration,
    (executeEntry_exact _ _ _ _).mpr judged⟩

theorem syntax_native_reflected (program : Syntax.Program) {source : Pattern}
    {first last : Command} {entry : Entry Nat Nat}
    (sourceElaboration : Syntax.Elaborates program source first.toPattern)
    (accepted : executeEntry (catalogChecking program.toCatalog) first entry = some last) :
    ∃ target, Syntax.Step program source target ∧
      Syntax.Elaborates program target last.toPattern := by
  exact Syntax.step_reflected program sourceElaboration
    ((catalog_entry_exists_iff_wireStep program.toCatalog first last).mp ⟨entry, accepted⟩)

/-! ## A genuine unbounded native fibre -/

namespace Tick

def stage : Pattern := .apply "native-tick" []
def forward : Pattern := .apply "forward" []
def identityRoute : Pattern := .apply "tick-identity" []
def tick (state : Pattern) : Pattern := .apply "Tick" [state]

/-- Source states are arbitrary patterns; a transition adds one Tick node. -/
def theory : Mettapedia.GSLT.GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites first last := last = tick first
  rewrites_resp_left := by
    intro first other last same step
    subst other
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last other step same
    exact same ▸ step

def source : Source where
  fibre selected first last := selected = stage ∧ last = tick first
  transport kind route sourceStage targetStage first last :=
    kind = forward ∧ route = identityRoute ∧ sourceStage = stage ∧
      targetStage = stage ∧ last = first

/-- Each primitive rule has no additional witness beyond its supplied
endpoints; the native checker still checks every source condition. -/
abbrev evidence : LocalEvidence where
  FibreProof := Unit
  TransportProof := Unit
  fibre _ selected first last := selected = stage ∧ last = tick first
  transport _ kind route sourceStage targetStage first last :=
    kind = forward ∧ route = identityRoute ∧ sourceStage = stage ∧
      targetStage = stage ∧ last = first

def checking : LocalChecking evidence where
  fibre _ selected first last := decide (selected = stage ∧ last = tick first)
  transport _ kind route sourceStage targetStage first last :=
    decide (kind = forward ∧ route = identityRoute ∧ sourceStage = stage ∧
      targetStage = stage ∧ last = first)
  fibre_exact _ _ _ _ := by simp
  transport_exact _ _ _ _ _ _ _ := by simp

theorem coverage : LocalCoverage source evidence where
  fibre _ _ _ := ⟨fun relation => ⟨(), relation⟩, fun ⟨_, relation⟩ => relation⟩
  transport _ _ _ _ _ _ := ⟨fun relation => ⟨(), relation⟩, fun ⟨_, relation⟩ => relation⟩

theorem fibre_step_exact (first last : Pattern) :
    source.fibre stage first last ↔ theory.Step first last := by
  simp [source, theory, Mettapedia.GSLT.GSLT.Step]

/-- This same unbounded source is realized by the existing authored GSLT-ML
fibre executor; it is not represented by enumerating its concrete edges. -/
theorem authored_cover :
    Mettapedia.GSLT.Ultrainfinite.StepCover theory
      (FibreExecution.theory stage (fun state => [tick state])) (atPattern stage) := by
  apply FibreExecution.stepCover theory stage id (fun state => [tick state])
  intro state answer
  simp [theory, Mettapedia.GSLT.GSLT.Step, id]

def states : Nat → Pattern
  | 0 => .apply "Start" []
  | n + 1 => tick (states n)

def depth : Pattern → Nat
  | .apply "Tick" [body] => depth body + 1
  | _ => 0

@[simp] theorem depth_states (n : Nat) : depth (states n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [states, tick, depth, ih]

theorem states_injective : Function.Injective states := by
  intro first last same
  have measured := congrArg depth same
  simpa only [depth_states] using measured

theorem no_finite_catalog_cover (catalog : Catalog) :
    ¬ Nonempty (Mettapedia.GSLT.Ultrainfinite.StepCover theory (totalTheory catalog)
      (atPattern stage)) := by
  exact FibreExecution.finite_catalog_not_cover theory stage id catalog states
    states_injective (fun n => ⟨tick (states n), rfl⟩)

def underneathThenTransport (state : Pattern) : Journal evidence :=
  [.underneath (tick state) (), .transport (tick state) ()]

def transportThenFibre (state : Pattern) : Journal evidence :=
  [.transport state (), .fibre (tick state) ()]

/-- The two naturality-square paths are both actually replayed. -/
theorem naturality_replay (state : Pattern) :
    replay checking (.via forward identityRoute stage stage state)
        (underneathThenTransport state) = some (.at stage (tick state)) ∧
      replay checking (.via forward identityRoute stage stage state)
        (transportThenFibre state) = some (.at stage (tick state)) := by
  simp [replay, executeEntry, checking, underneathThenTransport, transportThenFibre]

/-- A larger target relation can preserve every source step while inventing
one additional behaviour. Forward preservation is therefore insufficient. -/
def extraSource : Source where
  fibre selected first last := source.fibre selected first last ∨
    (selected = stage ∧ last = first)
  transport := source.transport

theorem extra_preserves {first last : Command} (step : Step source first last) :
    Step extraSource first last := by
  cases step with
  | fibre leaf => exact .fibre (Or.inl leaf)
  | underneath leaf => exact .underneath (Or.inl leaf)
  | transport leaf => exact .transport leaf

theorem extra_not_reflected :
    ∃ first last, Step extraSource first last ∧ ¬ Step source first last := by
  refine ⟨.at stage (states 0), .at stage (states 0), .fibre (Or.inr ⟨rfl, rfl⟩), ?_⟩
  intro step
  cases step with
  | fibre leaf => simp [source, states, tick] at leaf

end Tick

#print axioms accepted_iff_runs
#print axioms catalog_entry_exists_iff_wireStep
#print axioms catalog_accepted_iff_wire_paths
#print axioms Tick.no_finite_catalog_cover
#print axioms syntax_step_native
#print axioms syntax_native_reflected
#print axioms Tick.extra_not_reflected
#print axioms replayWithRequests_accepted
#print axioms lookupWithVisits_count
#print axioms replay_prefix_state_bound

end Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel


/-! ## Scoped finite-catalog source command services

These services act on the existing finite literal-catalog GSLT-ML command semantics. They
construct all immediate native answers and check native instruction sequences;
they do not identify the command carrier with cumulative dependent terms or
claim an unproved artifact/runtime realization.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.NativeCommand

open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService

/-- A command workspace after executable scope admission. Full source sorting
remains separate. Optional interpretations consume this source admission
without defining it. -/
structure Workspace where
  scope : Nat
  program : Program
  formed : Reindex.WellScoped scope program

/-- Untrusted authored rows enter the native service through the actual
scope checker, rather than a caller-supplied scope callback. -/
def admit? (scope : Nat) (program : Program) : Option Workspace :=
  if accepted : Reindex.checkScope scope program = true then
    some ⟨scope, program, (Reindex.checkScope_iff scope program).mp accepted⟩
  else none

theorem admit?_exists_iff (scope : Nat) (program : Program) :
    (∃ workspace, admit? scope program = some workspace) ↔
      Reindex.WellScoped scope program := by
  simp only [admit?]
  split
  · next accepted =>
      exact ⟨fun _ => (Reindex.checkScope_iff scope program).mp accepted,
        fun _ => ⟨_, rfl⟩⟩
  · next refused =>
      constructor
      · rintro ⟨workspace, impossible⟩
        cases impossible
      · intro formed
        exact (refused ((Reindex.checkScope_iff scope program).mpr formed)).elim

structure Claim where
  source : Pattern
  target : Pattern
  deriving DecidableEq

/-- Meaning is independently defined finite command reachability with formed
endpoints; it does not mention the checker or executable readout. -/
def target (workspace : Workspace) : AdmissionObject where
  Carrier := Claim
  Meaning claim :=
    claim.source.isWellScopedAt workspace.scope = true ∧
      claim.target.isWellScopedAt workspace.scope = true ∧
      Runs workspace.program claim.source claim.target

def proofSystem (workspace : Workspace) : NativeProofSystem Claim where
  ProofObject := List Instruction
  Judges script claim :=
    claim.source.isWellScopedAt workspace.scope = true ∧
      claim.target.isWellScopedAt workspace.scope = true ∧
      ScriptJudges workspace.program script claim.source claim.target

/-- The actual native kernel recomputes the selected command operations. -/
def kernel (workspace : Workspace) : NativeProofKernel (proofSystem workspace) where
  decide claim script :=
    claim.source.isWellScopedAt workspace.scope &&
      claim.target.isWellScopedAt workspace.scope &&
      decide (executeScript workspace.program script claim.source = some claim.target)
  correct claim script := by
    change List Instruction at script
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    change (_ ∧ _) ∧ executeScript workspace.program script claim.source =
      some claim.target ↔ _ ∧ _ ∧ ScriptJudges workspace.program script
        claim.source claim.target
    rw [executeScript_iff_judges]
    aesop

theorem meaning_exact (workspace : Workspace) (claim : Claim) :
    (target workspace).Meaning claim ↔
      Nonempty ((proofSystem workspace).ProofFibre claim) := by
  constructor
  · rintro ⟨sourceFormed, targetFormed, run⟩
    obtain ⟨script, judged⟩ := (script_exists_iff_runs workspace.program _ _).mpr run
    exact ⟨⟨script, sourceFormed, targetFormed, judged⟩⟩
  · rintro ⟨⟨script, sourceFormed, targetFormed, judged⟩⟩
    exact ⟨sourceFormed, targetFormed,
      (script_exists_iff_runs workspace.program _ _).mp ⟨script, judged⟩⟩

def proofService (workspace : Workspace) : Service (target workspace) :=
  .nativeProof (proofSystem workspace) (kernel workspace) (meaning_exact workspace)

theorem proofService_exact (workspace : Workspace) (claim : Claim) :
    (target workspace).Meaning claim ↔
      ∃ script, (kernel workspace).decide claim script = true :=
  Service.nativeProof_accepts_iff_meaning
    (target := target workspace)
    (proofSystem workspace) (kernel workspace) (meaning_exact workspace) claim

/-- The input to immediate native computation is an ordinary scoped command.
It contains no externally supplied proof journal. -/
def operationSource (workspace : Workspace) : AdmissionObject where
  Carrier := Pattern
  Meaning source := source.isWellScopedAt workspace.scope = true

/-- The native result retains the request and every indexed answer. Its
meaning requires complete instruction-level coverage and formed outputs. -/
def operationTarget (workspace : Workspace) : AdmissionObject where
  Carrier := Pattern × List (Instruction × Pattern)
  Meaning result :=
    result.1.isWellScopedAt workspace.scope = true ∧
      ∀ instruction output,
        (instruction, output) ∈ result.2 ↔
          Instruction.Judges workspace.program instruction result.1 output ∧
            output.isWellScopedAt workspace.scope = true

/-- Execute the authored primitive operations directly, retaining their row
positions. The semantic coverage theorem is earned from those operations. -/
def operation (workspace : Workspace) :
    operationSource workspace ⟶ operationTarget workspace where
  run source := (source, successors workspace.program source)
  preserves source formed := by
    change Pattern at source
    change source.isWellScopedAt workspace.scope = true at formed
    refine ⟨formed, ?_⟩
    intro instruction output
    change (instruction, output) ∈ successors workspace.program source ↔ _
    rw [mem_successors_iff]
    exact ⟨fun judged =>
      ⟨judged, judged.target_wellScoped workspace.formed⟩, And.left⟩

def operationService (workspace : Workspace) : Service (operationTarget workspace) :=
  .nativeOperation (operationSource workspace) (operation workspace)

/-- All outcomes of the implemented service reflect to the original source
command judgment, and every source step occurs among its answers. -/
theorem operation_outcomes_exact (workspace : Workspace)
    (source output : Pattern) :
    (∃ instruction,
      (instruction, output) ∈ ((operation workspace).run source).2) ↔
      Step workspace.program source output :=
  successors_exact workspace.program source output

/-- Reindexing an admitted workspace uses the original capture-avoiding
action and its proved scope law. -/
def reindex (workspace : Workspace) (destination : Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (images : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.WellScopedAssignment
      workspace.scope destination assignment) : Workspace where
  scope := destination
  program := Reindex.program assignment workspace.program
  formed := Reindex.wellScoped images workspace.formed

def Claim.reindex
    (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (claim : Claim) : Claim where
  source := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment claim.source
  target := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment claim.target

/-- Scope-correct simultaneous substitution transports the actual native
proof acceptance, using the same instruction sequence. -/
theorem kernel_reindex_preserves (workspace : Workspace) (destination : Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (images : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.WellScopedAssignment
      workspace.scope destination assignment)
    (claim : Claim) (script : List Instruction)
    (accepted : (kernel workspace).decide claim script = true) :
    (kernel (reindex workspace destination assignment images)).decide
      (claim.reindex assignment) script = true := by
  rcases (kernel workspace).correct claim script |>.mp accepted with
    ⟨sourceFormed, targetFormed, judged⟩
  apply (kernel (reindex workspace destination assignment images)).correct _ _ |>.mpr
  exact ⟨Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_wellScoped images sourceFormed,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_wellScoped images targetFormed,
    judged.reindex assignment⟩

/-- Split reindexing commutes with native computation at every output and
retains the request. This is the operational law for the current first-class
service; it does not identify its carrier with cumulative native terms. -/
theorem operation_reindex (workspace : Workspace) (destination : Nat)
    (forward backward : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (images : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.WellScopedAssignment
      workspace.scope destination forward)
    (retraction : ∀ index,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute backward
        (forward index) = Pattern.bvar index)
    (source : Pattern) :
    ((operation (reindex workspace destination forward images)).run
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute forward source)).2 =
      (((operation workspace).run source).2).map (fun answer =>
        (answer.1, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute forward answer.2)) :=
  successors_reindex forward backward retraction workspace.program source

namespace Canary

private def atom (name : String) : Pattern := .apply name []

private def space : Pattern := atom "native-command-space"
private def input : Pattern := atom "native-command-input"
private def middle : Pattern := atom "native-command-middle"
private def output : Pattern := atom "native-command-output"

private def localRule : SpaceRule where
  occurrence := atom "native-command-local"
  space := space
  source := input
  target := middle

private def duplicateLocalRule : SpaceRule :=
  { localRule with occurrence := atom "native-command-local-duplicate" }

private def declaredRoute : RouteDecl where
  occurrence := atom "native-command-route"
  name := "native-command-route"
  sourceSpace := space
  targetSpace := space

private def directRule : RouteRule where
  occurrence := atom "native-command-direct"
  name := declaredRoute.name
  source := input
  target := output

private def afterLocalRule : RouteRule :=
  { directRule with occurrence := atom "native-command-after-local", source := middle }

def authored : Program where
  spaceRules := [localRule, duplicateLocalRule]
  routes := [declaredRoute]
  routeRules := [directRule, afterLocalRule]

def workspace : Workspace where
  scope := 0
  program := authored
  formed := (Reindex.checkScope_iff 0 authored).mp (by decide +kernel)

def request : Pattern := routeCall declaredRoute.name input
def result : Pattern := inSpace space output

/-- Fusion changes the number of native instructions while retaining the
declared endpoint observation. Both paths use original authored operations. -/
theorem direct_and_expanded_execute :
    executeScript authored [.transport 0 0] request = some result ∧
      executeScript authored [.beneath 0 0, .transport 0 1] request = some result := by
  decide +kernel

theorem direct_and_expanded_are_source_runs :
    Runs authored request result ∧
      ScriptJudges authored [.beneath 0 0, .transport 0 1] request result := by
  exact ⟨(script_exists_iff_runs authored request result).mp
    ⟨[.transport 0 0], (executeScript_iff_judges authored _ _ _).mp
      direct_and_expanded_execute.1⟩,
    (executeScript_iff_judges authored _ _ _).mp direct_and_expanded_execute.2⟩

/-- Equal visible local answers retain two different authored positions. -/
theorem duplicate_answers_retained :
    successors authored request =
      [(.beneath 0 0, routeCall declaredRoute.name middle),
       (.beneath 0 1, routeCall declaredRoute.name middle),
       (.transport 0 0, result)] := by
  decide +kernel

theorem malformed_instruction_refused :
    executeScript authored [.transport 1 0] request = none := by
  decide +kernel

theorem wrong_endpoint_refused :
    (kernel workspace).decide ⟨request, inSpace space input⟩
      [.transport 0 0] = false := by
  decide +kernel

private def forged : Pattern := atom "native-command-forged"

private def extended : Program :=
  { authored with routeRules :=
    authored.routeRules ++ [{ directRule with target := forged }] }

/-- Adding a target row preserves old operations but exposes genuinely new
behavior. The original native kernel rejects the added instruction. -/
theorem added_behavior_separated :
    Instruction.execute extended (.transport 0 2) request =
        some (inSpace space forged) ∧
      Instruction.execute authored (.transport 0 2) request = none ∧
      ¬ Step authored request (inSpace space forged) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro edge
  have present := (successors_exact authored request (inSpace space forged)).mpr edge
  have absent : ¬ ∃ instruction,
      (instruction, inSpace space forged) ∈ successors authored request := by
    rw [duplicate_answers_retained]
    simp [result, forged, space, output, inSpace, routeCall, atom]
  exact absent present

private def malformedProgram : Program :=
  { authored with spaceRules := [{ localRule with target := .bvar 0 }] }

theorem dangling_program_refused : (admit? 0 malformedProgram).isNone = true := by
  decide +kernel

private def openProgram : Program where
  spaceRules :=
    [{ localRule with
       source := .bvar 0
       target := .lambda (some "inner") (.bvar 1) }]
  routes := []
  routeRules := []

private def closing : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment :=
  fun _ => atom "native-command-closed"

/-- Substitution reaches beneath a binder with the shared lifted action. -/
theorem closing_under_binder :
    executeScript (Reindex.program closing openProgram) [.fibre 0]
        (inSpace space (atom "native-command-closed")) =
      some (inSpace space
        (.lambda (some "inner") (atom "native-command-closed"))) := by
  decide +kernel

theorem captured_result_refused :
    executeScript (Reindex.program closing openProgram) [.fibre 0]
        (inSpace space (atom "native-command-closed")) ≠
      some (inSpace space (.lambda (some "inner") (.bvar 0))) := by
  decide +kernel

private def separatedSpaces : Program where
  spaceRules := [{ localRule with space := .bvar 0 }]
  routes := [{ declaredRoute with sourceSpace := .bvar 1 }]
  routeRules := []

/-- An unrestricted substitution can enable a previously forbidden command
by identifying different source-space keys. Preservation alone is correct;
reflection requires a separately justified context action. -/
theorem collapsing_substitution_adds_behavior :
    Instruction.execute separatedSpaces (.beneath 0 0) request = none ∧
      Instruction.execute (Reindex.program closing separatedSpaces)
          (.beneath 0 0) request = some (routeCall declaredRoute.name middle) := by
  decide +kernel

end Canary

end Mettapedia.GSLT.LanguageDef.GSLTIL.NativeCommand
