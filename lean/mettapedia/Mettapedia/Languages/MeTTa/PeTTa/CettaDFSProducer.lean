import Mettapedia.Languages.MeTTa.PeTTa.CettaEagerDFS
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog

/-!
# Depth-first program execution feeding independent consumers

This adapter selects one actual `CettaEagerDFS` execution. A source transition
that appends a root answer emits that occurrence together with the complete
post-transition configuration. Answers collected inside a `collapse` scope
remain private until its caller produces a root answer. Performed effects stay
in the saved world; the adapter never repeats them as effect requests.

Source transitions and composition microsteps have separate counts. Capture,
admission, backpressure and consumer cancellation use the existing owned log.
The source model retains its answer history, so a bound on buffered rows is
not a bound on the whole execution's storage. Capture and compatibility remain
qualified services; these laws do not establish native root discovery, lawful
sharing of two computations, operation admission or compiled-code refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSProducer

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Mettapedia.Machines.Cursor

/-- A fault or malformed stopped residual requires a separate host decision.
Neither is certified as ordinary exhaustion. -/
inductive Barrier where
  | fault (reason : Effects.Fault)
  | stopped

private def branchEmission (branch : CettaEagerDFS.Branch) : List Atom :=
  match branch.control, branch.frames with
  | .returned value, [] => [value]
  | _, _ => []

/-- Only a root return with no caller frame is a public answer occurrence. -/
def emission (configuration : CettaEagerDFS.Configuration) : List Atom :=
  match configuration.scopes with
  | [{ frontier := branch :: _, caller := none, .. }] => branchEmission branch
  | _ => []

/-- One source step, or inspection of a retained terminal/barrier residual. -/
def step (program : Program) (configuration : CettaEagerDFS.Configuration) :
    ProducerOccurrenceLog.ProducerOutcome CettaEagerDFS.Configuration Atom Empty Barrier :=
  match CettaEagerDFS.step program configuration with
  | some next =>
      match emission configuration with
      | value :: _ => .returned value next
      | [] => .progress next
  | none =>
      if CettaEagerDFS.completed configuration then .completed configuration
      else match CettaEagerDFS.fault configuration with
        | some reason => .handoff (.fault reason) configuration
        | none => .handoff .stopped configuration

private def movementEmission : CettaEagerDFS.Movement → List Atom
  | .answer value => [value]
  | _ => []

private theorem local_emission {program : Program} {world after : CettaEagerDFS.World}
    {branch : CettaEagerDFS.Branch} {movement : CettaEagerDFS.Movement}
    (transition : CettaEagerDFS.LocalTransition program world branch after movement) :
    movementEmission movement = branchEmission branch := by
  cases transition <;> simp [movementEmission, branchEmission]

private theorem nested_answers (world : CettaEagerDFS.World) (scope : CettaEagerDFS.Scope)
    (parents : List CettaEagerDFS.Scope) (nonempty : parents ≠ []) :
    CettaEagerDFS.answers ⟨world, scope :: parents⟩ = CettaEagerDFS.answers ⟨world, parents⟩ := by
  simp only [CettaEagerDFS.answers, List.getLast?_cons_of_ne_nil nonempty]

/-- This is a property of the independently authored source rules, including
the delimiter transition, rather than a definition of a desired trace. -/
theorem transition_answers {program : Program} {source target : CettaEagerDFS.Configuration}
    (transition : CettaEagerDFS.Transition program source target)
    (valid : CettaEagerDFS.ScopesValid source.scopes) :
    CettaEagerDFS.answers target = CettaEagerDFS.answers source ++ emission source := by
  cases transition with
  | @branch world after scope parents branch pending movement frontier derivation =>
      have emitted := local_emission derivation
      cases valid with
      | root work rows =>
          change work = branch :: pending at frontier
          subst work
          cases movement <;>
            simp_all [CettaEagerDFS.install, CettaEagerDFS.answers, emission, movementEmission]
      | nested work rows frames parentValid =>
          have nonempty := parentValid.nonempty
          cases parents with
          | nil => contradiction
          | cons parent rest =>
              cases movement <;> simp [CettaEagerDFS.install, CettaEagerDFS.answers, emission]
  | collapse_return =>
      cases valid with
      | nested work rows frames parentValid =>
          cases parentValid with
          | root => simp [CettaEagerDFS.finishScope, CettaEagerDFS.answers, emission]
          | nested work rows frames tailValid =>
              simp [CettaEagerDFS.finishScope, CettaEagerDFS.answers, emission,
                List.getLast?_cons_of_ne_nil tailValid.nonempty]

theorem emission_length (configuration : CettaEagerDFS.Configuration) :
    (emission configuration).length ≤ 1 := by
  unfold emission
  split
  · unfold branchEmission
    split <;> simp
  · simp

/-- Every adapter step is zero or one actual source-rule applications. It
retains valid scopes and emits exactly the newly appended root occurrence. -/
theorem step_source {program : Program} (configuration : CettaEagerDFS.Configuration)
    (valid : CettaEagerDFS.ScopesValid configuration.scopes) :
    ∃ count ≤ 1, CettaEagerDFS.SourceRun program count configuration (step program configuration).next ∧
      CettaEagerDFS.ScopesValid (step program configuration).next.scopes ∧
      CettaEagerDFS.answers (step program configuration).next =
        CettaEagerDFS.answers configuration ++ (step program configuration).returns := by
  cases advanced : CettaEagerDFS.step program configuration with
  | none =>
      simp only [step, advanced]
      split
      · exact ⟨0, by omega, .refl _, valid, by simp [ProducerOccurrenceLog.ProducerOutcome.next, ProducerOccurrenceLog.ProducerOutcome.returns]⟩
      · cases CettaEagerDFS.fault configuration <;>
          exact ⟨0, by omega, .refl _, valid, by simp [ProducerOccurrenceLog.ProducerOutcome.next, ProducerOccurrenceLog.ProducerOutcome.returns]⟩
  | some target =>
      have actual := CettaEagerDFS.step_transition advanced
      have retained := CettaEagerDFS.transition_scopes_valid actual valid
      have appended := transition_answers actual valid
      have bound := emission_length configuration
      cases emitted : emission configuration with
      | nil =>
          refine ⟨1, Nat.le_refl _, ?_, ?_, ?_⟩
          · simpa [step, advanced, emitted, ProducerOccurrenceLog.ProducerOutcome.next] using
              CettaEagerDFS.SourceRun.next actual (CettaEagerDFS.SourceRun.refl target)
          · simpa [step, advanced, emitted, ProducerOccurrenceLog.ProducerOutcome.next] using retained
          · simpa [step, advanced, emitted, ProducerOccurrenceLog.ProducerOutcome.next,
              ProducerOccurrenceLog.ProducerOutcome.returns] using appended

      | cons value rest =>
          have empty : rest = [] := by simpa [emitted] using bound
          subst rest
          refine ⟨1, Nat.le_refl _, ?_, ?_, ?_⟩
          · simpa [step, advanced, emitted, ProducerOccurrenceLog.ProducerOutcome.next] using
              CettaEagerDFS.SourceRun.next actual (CettaEagerDFS.SourceRun.refl target)
          · simpa [step, advanced, emitted, ProducerOccurrenceLog.ProducerOutcome.next] using retained
          · simpa [step, advanced, emitted, ProducerOccurrenceLog.ProducerOutcome.next,
              ProducerOccurrenceLog.ProducerOutcome.returns] using appended


theorem source_run_append {program : Program} {first second : Nat}
    {source middle target : CettaEagerDFS.Configuration}
    (earlier : CettaEagerDFS.SourceRun program first source middle)
    (later : CettaEagerDFS.SourceRun program second middle target) :
    CettaEagerDFS.SourceRun program (first + second) source target := by
  induction earlier with
  | refl => simpa using later
  | next transition tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        CettaEagerDFS.SourceRun.next transition (ih later)

/-- An arbitrary producer path is an actual source execution. Equal answer
values remain distinct occurrences, in the evaluator's original order. -/
theorem producer_path_source {program : Program} {source target : CettaEagerDFS.Configuration}
    {occurrences : List Atom} (path : ProducerOccurrenceLog.ProducerPath (step program) source occurrences target)
    (valid : CettaEagerDFS.ScopesValid source.scopes) :
    ∃ count, CettaEagerDFS.SourceRun program count source target ∧ CettaEagerDFS.ScopesValid target.scopes ∧
      CettaEagerDFS.answers target = CettaEagerDFS.answers source ++ occurrences := by
  induction path with
  | refl => exact ⟨0, .refl _, valid, by simp⟩
  | @next source outcome rest target transition tail ih =>
      obtain ⟨paid, _, first, retained, appended⟩ := step_source source valid
      rw [transition] at first retained appended
      obtain ⟨remaining, later, finalValid, finalAnswers⟩ := ih retained
      exact ⟨paid + remaining, source_run_append first later, finalValid,
        by rw [finalAnswers, appended, List.append_assoc]⟩

variable {Stored Context Output : Type} {clients : Nat}

abbrev Packet (Stored Context Output : Type) (clients : Nat) :=
  ProducerOccurrenceLog.Configuration CettaEagerDFS.Configuration Atom Stored Context Output Empty Barrier clients

/-- Backpressure and capture retries execute no extra source reductions. The
complete world, scope stack and branch frames remain the path's endpoint. -/
theorem run_source {program : Program} (capture : Atom → Option Stored)
    (capacity : Stored → Bool) (compatible : Context → Bool) (ticks : Nat)
    (state : Packet Stored Context Output clients)
    (execution : ProducerOccurrenceLog.Execution CettaEagerDFS.Configuration Atom Empty Barrier)
    (attached : state.execution = some execution)
    (valid : CettaEagerDFS.ScopesValid execution.producer.scopes) :
    ∃ next count, (ProducerOccurrenceLog.run (step program) capture capacity compatible ticks state).2.execution = some next ∧
      CettaEagerDFS.SourceRun program count execution.producer next.producer ∧
      CettaEagerDFS.ScopesValid next.producer.scopes ∧
      CettaEagerDFS.answers next.producer = CettaEagerDFS.answers execution.producer ++
        (ProducerOccurrenceLog.run (step program) capture capacity compatible ticks state).1.flatMap ProducerOccurrenceLog.returned := by
  obtain ⟨next, retained, path⟩ := ProducerOccurrenceLog.run_producer_path (step program)
    capture capacity compatible ticks state execution attached
  obtain ⟨count, source, finalValid, finalAnswers⟩ := producer_path_source path valid
  exact ⟨next, count, retained, source, finalValid, finalAnswers⟩

/-- Captured rows and the one pending return conserve exactly the newly
produced ordered answers. The capture law concerns observations; native
resource retention and service correctness remain separate obligations. -/
theorem initial_run_conservation {program : Program} (capture : Atom → Option Stored)
    (decode : Stored → Atom) (capacity : Stored → Bool) (compatible : Context → Bool)
    (captureSound : ∀ value stored, capture value = some stored → decode stored = value)
    (ticks : Nat) (configuration : CettaEagerDFS.Configuration)
    (valid : CettaEagerDFS.ScopesValid configuration.scopes) (context : Context) (limit : Nat) :
    let initial : Packet Stored Context Output clients :=
      ProducerOccurrenceLog.initial configuration context limit
    let result := ProducerOccurrenceLog.run (step program) capture capacity compatible ticks initial
    ∃ next count, result.2.execution = some next ∧
      CettaEagerDFS.SourceRun program count configuration next.producer ∧
      CettaEagerDFS.answers next.producer = CettaEagerDFS.answers configuration ++
        ((result.1.flatMap ProducerOccurrenceLog.admitted).map decode ++ next.pending.toList) := by
  dsimp only
  let initial : Packet Stored Context Output clients :=
    ProducerOccurrenceLog.initial configuration context limit
  let result := ProducerOccurrenceLog.run (step program) capture capacity compatible ticks initial
  obtain ⟨next, count, attached, actual, _, answers⟩ := run_source capture capacity compatible
    ticks initial ⟨configuration, none, 0, .active⟩ rfl valid
  have conserved := ProducerOccurrenceLog.run_conservation id decode (step program)
    capture capacity compatible captureSound ticks initial
  have noPending : ProducerOccurrenceLog.pending initial = none := rfl
  have finalPending : ProducerOccurrenceLog.pending result.2 = next.pending := by
    unfold ProducerOccurrenceLog.pending
    rw [attached]
    rfl
  have ordered : result.1.flatMap ProducerOccurrenceLog.returned =
      (result.1.flatMap ProducerOccurrenceLog.admitted).map decode ++ next.pending.toList := by
    rw [noPending, finalPending] at conserved
    simpa using conserved
  exact ⟨next, count, attached, actual, by rw [answers, ordered]⟩

/-- Genuine completion is recognized only after the evaluator's root scope
exhausts. Faults and malformed stopped scope stacks remain explicit barriers. -/
theorem step_completed_iff (program : Program) (configuration : CettaEagerDFS.Configuration) :
    step program configuration = .completed configuration ↔
      CettaEagerDFS.completed configuration = true := by
  constructor
  · intro complete
    cases advanced : CettaEagerDFS.step program configuration with
    | some target =>
        cases emitted : emission configuration <;> simp [step, advanced, emitted] at complete
    | none =>
        by_cases finished : CettaEagerDFS.completed configuration = true
        · exact finished
        · cases fault : CettaEagerDFS.fault configuration <;>
            simp [step, advanced, finished, fault] at complete
  · intro complete
    simp [step, complete, CettaEagerDFS.stopped_of_completed program configuration complete]

theorem fault_retains_the_entire_residual (program : Program)
    (configuration : CettaEagerDFS.Configuration) (reason : Effects.Fault)
    (fault : CettaEagerDFS.fault configuration = some reason)
    (incomplete : CettaEagerDFS.completed configuration = false) :
    step program configuration = .handoff (.fault reason) configuration := by
  simp [step, CettaEagerDFS.stopped_of_fault program configuration reason fault, incomplete, fault]

namespace Controls

def program : Program := { equations := [], declarations := [] }
def a : Atom := .symbol "a"
def b : Atom := .symbol "b"

/-- Mathematical immutable payloads, with their captured source token. This
fixture does not stand for a native capability or binding-graph capturer. -/
structure CapturedAnswer where
  value : Atom
  sourceToken : Nat
  deriving DecidableEq

def capture (value : Atom) : Option CapturedAnswer := some ⟨value, 7⟩
def compatible (token : Nat) : Bool := token == 7

theorem capture_observation (value : Atom) (stored : CapturedAnswer)
    (captured : capture value = some stored) : stored.value = value := by
  simp only [capture, Option.some.injEq] at captured
  subst stored
  rfl

def ready : CettaEagerDFS.Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [⟨.returned a, []⟩, ⟨.returned a, []⟩, ⟨.returned b, []⟩] }]⟩

theorem ready_valid : CettaEagerDFS.ScopesValid ready.scopes := .root _ _

abbrev Cohort := Packet CapturedAnswer Nat Nat 2

def initial (limit : Nat) : Cohort := ProducerOccurrenceLog.initial ready 7 limit
def feed (ticks limit : Nat) :=
  ProducerOccurrenceLog.run (step program) capture (fun _ => true) compatible ticks (initial limit)

theorem actual_root_returns_keep_order_and_duplicates :
    (feed 10 4).1.flatMap ProducerOccurrenceLog.returned = [a, a, b] := rfl

theorem captured_rows_keep_the_source_and_occurrences :
    (feed 10 4).2.delivery.log.rows = [⟨a, 7⟩, ⟨a, 7⟩, ⟨b, 7⟩] := rfl

theorem complete_retains_the_actual_answer_history :
    (feed 10 4).2.execution.map (fun execution => CettaEagerDFS.answers execution.producer) =
      some [a, a, b] ∧ (feed 10 4).2.delivery.log.completed = true := ⟨rfl, rfl⟩

def staged : Cohort := (feed 1 4).2

theorem return_stages_its_entire_post_transition_residual :
    staged.execution = some
      ⟨⟨ready.world, [{ frontier := [⟨.returned a, []⟩, ⟨.returned b, []⟩], collected := [a] }]⟩,
        some a, 0, .active⟩ := rfl

theorem refused_capture_keeps_the_saved_alternatives :
    ProducerOccurrenceLog.pump (step program) (fun _ => none) (fun _ => true) compatible staged =
      (.captureRefused, staged) := rfl

theorem refused_admission_retries_without_replaying_a_return :
    (ProducerOccurrenceLog.run (step program) capture (fun _ => false) compatible 5 staged).2 =
      staged := rfl

theorem full_buffer_preserves_the_next_unexecuted_answer :
    (feed 10 1).2.execution = staged.execution.map (fun execution =>
      {execution with pending := none, accepted := 1}) ∧
      (feed 10 1).2.delivery.log.completed = false := ⟨rfl, rfl⟩

def afterA : Cohort :=
  (ProducerOccurrenceLog.deliver compatible (feed 10 4).2 0 20).2

theorem independent_consumers_receive_the_same_occurrence_positions :
    (ProducerOccurrenceLog.deliver compatible (feed 10 4).2 0 20).1 =
      .observed (.answer 0 ⟨a, 7⟩) ∧
    (ProducerOccurrenceLog.deliver compatible afterA 0 20).1 = .observed (.answer 1 ⟨a, 7⟩) ∧
    (ProducerOccurrenceLog.deliver compatible afterA 1 21).1 = .observed (.answer 0 ⟨a, 7⟩) :=
  ⟨rfl, rfl, rfl⟩

def cancelledA : Cohort :=
  {afterA with delivery := SharedOccurrenceOwnership.cancelConsumer afterA.delivery 0}

theorem cancellation_retains_the_other_consumers_occurrence :
    (ProducerOccurrenceLog.deliver compatible cancelledA 1 21).1 = .observed (.answer 0 ⟨a, 7⟩) ∧
      cancelledA.delivery.published = afterA.delivery.published := ⟨rfl, rfl⟩

theorem stale_source_token_refuses_without_losing_the_buffer :
    ProducerOccurrenceLog.deliver (fun token => token == 8) (feed 10 4).2 0 20 =
      (.contextRefused, (feed 10 4).2) := rfl

def droppedPending : Cohort :=
  {staged with execution := staged.execution.map (fun execution => {execution with pending := none})}

theorem deleting_the_pending_return_loses_an_occurrence :
    ProducerOccurrenceLog.admitted
        (ProducerOccurrenceLog.pump (step program) capture (fun _ => true) compatible droppedPending).1 = [] ∧
      ProducerOccurrenceLog.admitted
        (ProducerOccurrenceLog.pump (step program) capture (fun _ => true) compatible staged).1 = [⟨a, 7⟩] :=
  ⟨rfl, rfl⟩

def insideCollapse : CettaEagerDFS.Configuration :=
  ⟨ready.world, { frontier := [⟨.returned a, []⟩], caller := some [] } :: ready.scopes⟩

theorem child_answer_stays_private :
    (step program insideCollapse).returns = [] ∧
      CettaEagerDFS.answers (step program insideCollapse).next = [] := ⟨rfl, rfl⟩

theorem treating_a_child_return_as_public_changes_the_observation :
    branchEmission ⟨.returned a, []⟩ ≠ emission insideCollapse := by decide

def printReady : CettaEagerDFS.Configuration :=
  ⟨ready.world, [{ frontier := [⟨.arguments [] (.function "println!") [] [a] 1, []⟩] }]⟩

def afterPrint : CettaEagerDFS.Configuration := (step program printReady).next
def printStaged : Cohort :=
  (ProducerOccurrenceLog.run (step program) capture (fun _ => true) compatible 2
    (ProducerOccurrenceLog.initial printReady 7 2)).2

theorem performed_effect_is_saved_before_capture_pause :
    afterPrint.world.output = [a] ∧
      printStaged.execution.map (fun execution => execution.producer.world.output) = some [a] :=
  ⟨rfl, rfl⟩

theorem capture_pause_does_not_repeat_the_performed_effect :
    ProducerOccurrenceLog.pump (step program) (fun _ => none) (fun _ => true) compatible printStaged =
      (.captureRefused, printStaged) := rfl

theorem arbitrary_split_retains_the_world_and_all_scopes (first second : Nat) :
    feed (first + second) 4 =
      (let earlier := feed first 4
       let later := ProducerOccurrenceLog.run (step program) capture (fun _ => true) compatible second earlier.2
       (earlier.1 ++ later.1, later.2)) :=
  ProducerOccurrenceLog.run_split _ _ _ _ first second (initial 4)

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSProducer
