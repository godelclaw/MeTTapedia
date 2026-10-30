import Mettapedia.Languages.HOLLight.MeTTa.RuleData

/-!
# Programmable HOL command lists with retained inference history

The values are the existing `HOL:Step` and `HOL:Cons` data. Their reader
preserves requests and duplicate premise addresses, but grants no authority.
An admitted plan earns its final cache and ordered receipts by executing the
ten existing primitive rules. List composition then executes the same source
replay loop, with the complete intermediate state retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.RulePrograms

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open InferenceSchedule SourceReplay CacheAuthorization Eval
open Effects (State)

def readCommand : Atom → Option Command
  | .expression [.symbol "HOL:Step", key, request] => some ⟨key, request⟩
  | _ => none

def readCommands : Atom → Option (List Command)
  | .symbol "HOL:Nil" => some []
  | .expression [.symbol "HOL:Cons", command, rest] => do
      return (← readCommand command) :: (← readCommands rest)
  | _ => none
termination_by input => sizeOf input

@[simp] theorem readCommand_atom (command : Command) :
    readCommand command.atom = some command := by cases command; rfl

@[simp] theorem readCommands_commandsAtom (commands : List Command) :
    readCommands (commandsAtom commands) = some commands := by
  induction commands with
  | nil => simp [commandsAtom, Premises.keys, readCommands]
  | cons command rest ih =>
      change readCommands (.expression [.symbol "HOL:Cons", command.atom, commandsAtom rest]) = _
      simp only [readCommands, readCommand_atom, ih]
      rfl

theorem commandsAtom_injective : Function.Injective commandsAtom := by
  intro first second same
  have decoded := congrArg readCommands same
  simpa only [readCommands_commandsAtom, Option.some.injEq] using decoded

theorem command_atom_read {input : Atom} {command : Command}
    (read : readCommand input = some command) : command.atom = input := by
  unfold readCommand at read
  split at read
  · cases read; rfl
  · cases read

theorem commandsAtom_read {input : Atom} {commands : List Command}
    (read : readCommands input = some commands) : commandsAtom commands = input := by
  unfold readCommands at read
  split at read
  · cases read; rfl
  · rename_i command rest
    cases hc : readCommand command <;> cases hr : readCommands rest <;>
      simp only [hc, hr, Bind.bind, Option.bind, pure,
        Option.some.injEq, reduceCtorEq] at read
    subst commands
    change Atom.expression [.symbol "HOL:Cons", Command.atom _, commandsAtom _] = _
    rw [command_atom_read hc, commandsAtom_read hr]
  · cases read
termination_by sizeOf input

/-- Concatenation preserves the entire command data; admission remains
the selected checker's job. -/
def appendPrograms (first second : Atom) : Option Atom := do
  return commandsAtom ((← readCommands first) ++ (← readCommands second))

theorem appendPrograms_exact (first second : List Command) :
    appendPrograms (commandsAtom first) (commandsAtom second) = some (commandsAtom (first ++ second)) := by
  simp [appendPrograms]

theorem appendPrograms_assoc (first second third : List Command) :
    appendPrograms (commandsAtom (first ++ second)) (commandsAtom third) =
      appendPrograms (commandsAtom first) (commandsAtom (second ++ third)) := by
  simp [appendPrograms_exact, List.append_assoc]

def receiptCommand (receipt : ReceiptKeys.Entry) : Command := ⟨receipt.key, receipt.request⟩

/-- The plan extends, rather than replaces, the original cache and receipt
lists. Newly recorded requests are exactly the executed commands in reverse
publication order; every premise occurrence is the one read from that request. -/
theorem plan_trace_history (frame : InferenceSchedule.Frame)
    {cache : Cache} {receipts : List ReceiptKeys.Entry} {length : Nat}
    (plan : Plan frame cache receipts length) (valid : Valid frame.policy frame.world cache)
    (state : State) :
    ∃ (added : Cache) (recorded : List ReceiptKeys.Entry) (commands : List Command),
      added.length = length ∧ recorded.length = length ∧ commands.length = length ∧
      recorded.reverse.map receiptCommand = commands ∧
      (∀ receipt ∈ recorded, RuleData.readPremises receipt.request = some receipt.premises) ∧
      Valid frame.policy frame.world (added ++ cache) ∧
      Trace state (frame.source cache receipts) commands
        (frame.source (added ++ cache) (recorded ++ receipts)) := by
  induction plan with
  | stop cache receipts =>
      exact ⟨[], [], [], rfl, rfl, rfl, rfl, by simp, valid, .nil _⟩
  | @event cache receipts length key invocation receiptFresh cacheFresh next ih =>
      obtain ⟨record, _, authorized, logical, returned⟩ :=
        executes frame cache valid receipts key invocation receiptFresh cacheFresh state
      obtain ⟨added, recorded, commands, addedCount, receiptCount, commandCount,
        ordered, premises, finalValid, trace⟩ := ih record logical authorized
      refine ⟨added ++ [(key, record)], recorded ++ [invocation.receipt key],
        invocation.command key :: commands, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addedCount]
      · simp [receiptCount]
      · simp [commandCount]
      · simp [List.reverse_append, ordered, receiptCommand, Invocation.receipt, Invocation.command]
      · intro receipt member
        rcases List.mem_append.mp member with old | new
        · exact premises receipt old
        · obtain rfl := List.mem_singleton.mp new
          exact RuleData.readPremises_invocation invocation
      · simpa only [List.append_assoc, List.singleton_append] using finalValid
      · apply Trace.cons returned
        simpa only [List.append_assoc, List.singleton_append] using trace

/-- Commands obtained by the retained-history theorem execute as ordinary
data through the maintained replay loop, and read back without information loss. -/
theorem plan_program_returns (frame : InferenceSchedule.Frame)
    {cache : Cache} {receipts : List ReceiptKeys.Entry} {length : Nat}
    (plan : Plan frame cache receipts length) (valid : Valid frame.policy frame.world cache)
    (state : State) :
    ∃ (added : Cache) (recorded : List ReceiptKeys.Entry) (commands : List Command),
      added.length = length ∧ recorded.length = length ∧ commands.length = length ∧
      readCommands (commandsAtom commands) = some commands ∧
      recorded.reverse.map receiptCommand = commands ∧
      Valid frame.policy frame.world (added ++ cache) ∧
      PureReturns program (environment (frame.source cache receipts) commands) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", frame.source (added ++ cache) (recorded ++ receipts)]) := by
  obtain ⟨added, recorded, commands, hc, hr, hn, ordered, _, authorized, trace⟩ :=
    plan_trace_history frame plan valid state
  exact ⟨added, recorded, commands, hc, hr, hn, readCommands_commandsAtom commands,
    ordered, authorized, authored_run_from trace _ "state" "commands" rfl rfl⟩

/-- Joining programs uses the actual intermediate source state. It cannot
resume a suffix against a different cache or theory merely by joining lists. -/
theorem composition_returns {state : State} {before middle after : Atom}
    {first second : List Command}
    (left : Trace state before first middle) (right : Trace state middle second after) :
    appendPrograms (commandsAtom first) (commandsAtom second) =
        some (commandsAtom (first ++ second)) ∧
      PureReturns program (environment before (first ++ second)) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", after]) :=
  ⟨appendPrograms_exact first second, authored_run_from (left.append right) _ "state" "commands" rfl rfl⟩

theorem malformed_command_refused (key request extra : Atom) :
    readCommand (.expression [.symbol "HOL:Step", key, request, extra]) = none := rfl

/-- Unknown requests remain data at this layer. The inference dispatcher,
not this list reader, decides which requests its selected theory admits. -/
theorem reading_does_not_admit (key : Atom) :
    readCommand (.expression [.symbol "HOL:Step", key, .symbol "unlicensed-rule"]) =
      some ⟨key, .symbol "unlicensed-rule"⟩ ∧
    RuleData.readRequest (.symbol "unlicensed-rule") = none := ⟨rfl, rfl⟩

#print axioms commandsAtom_read
#print axioms plan_trace_history
#print axioms plan_program_returns
#print axioms composition_returns

end Mettapedia.Languages.HOLLight.MeTTa.RulePrograms
