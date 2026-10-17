import Mettapedia.Machines.RunContracts.FilesystemObservation
import Mettapedia.Data.String.Utf8

/-!
# Chunk-independent Unicode line observation

The input here consists of decoded Unicode scalars. Strict byte decoding has
its separate Utf8 contract; native strict/ignore decoding is qualified against
an independent codec, not asserted adequate by these scalar-level theorems.

One scalar transition preserves a reverse pending line and remembers CR, so a
following LF contributes no second boundary. Empty input publishes no extra
line. Explicit finish publishes a nonempty pending suffix only. A finish request
is not evidence of OS completion; the filesystem provider must establish end.

An executable scanner is related to independently presented transitions. Its
append law states exact ordered output/state agreement across chunk boundaries.
These results do not assert correspondence with native C or the MeTTa adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.TextLineObservation

def isBoundary (scalar : Char) : Bool :=
  scalar == '\n' || scalar == '\r' || scalar == Char.ofNat 11 ||
  scalar == Char.ofNat 12 || scalar == Char.ofNat 28 || scalar == Char.ofNat 29 ||
  scalar == Char.ofNat 30 || scalar == Char.ofNat 0x85 ||
  scalar == Char.ofNat 0x2028 || scalar == Char.ofNat 0x2029

structure State where
  reversePending : List Char
  nextLine : Nat
  afterCR : Bool
  deriving DecidableEq, Repr

def State.initial : State := ⟨[], 1, false⟩

abbrev Row := Nat × List Char

def skipsLF (state : State) (scalar : Char) : Bool := state.afterCR && scalar == '\n'

def step (state : State) (scalar : Char) : List Row × State :=
  if skipsLF state scalar then
    ([], {state with afterCR := false})
  else if isBoundary scalar then
    ([(state.nextLine, state.reversePending.reverse)],
      ⟨[], state.nextLine + 1, scalar == '\r'⟩)
  else
    ([], {state with reversePending := scalar :: state.reversePending, afterCR := false})

def feed (input : List Char) (state : State) : List Row × State :=
  match input with
  | [] => ([], state)
  | scalar :: rest =>
      let first := step state scalar
      let later := feed rest first.2
      (first.1 ++ later.1, later.2)

/-- Declarative scalar transitions, without calling the scanner. -/
inductive Advances (state : State) (scalar : Char) : List Row → State → Prop where
  | crlf (skip : skipsLF state scalar = true) :
      Advances state scalar [] {state with afterCR := false}
  | boundary (noSkip : skipsLF state scalar = false) (boundary : isBoundary scalar = true) :
      Advances state scalar [(state.nextLine, state.reversePending.reverse)]
        ⟨[], state.nextLine + 1, scalar == '\r'⟩
  | ordinary (noSkip : skipsLF state scalar = false) (ordinary : isBoundary scalar = false) :
      Advances state scalar []
        {state with reversePending := scalar :: state.reversePending, afterCR := false}

theorem Advances.sound {state : State} {scalar : Char} {rows : List Row} {next : State}
    (advance : Advances state scalar rows next) : step state scalar = (rows, next) := by
  cases advance <;> simp_all [step]

theorem Advances.complete (state : State) (scalar : Char) :
    Advances state scalar (step state scalar).1 (step state scalar).2 := by
  cases skip : skipsLF state scalar with
  | true => simpa [step, skip] using Advances.crlf skip
  | false =>
      cases boundary : isBoundary scalar with
      | true => simpa [step, skip, boundary] using Advances.boundary skip boundary
      | false => simpa [step, skip, boundary] using Advances.ordinary skip boundary

inductive Observes : State → List Char → List Row → State → Prop where
  | nil (state : State) : Observes state [] [] state
  | cons {state next finish : State} {scalar : Char} {rest : List Char}
      {before after : List Row} (first : Advances state scalar before next)
      (later : Observes next rest after finish) :
      Observes state (scalar :: rest) (before ++ after) finish

theorem Observes.sound {state finish : State} {input : List Char} {rows : List Row}
    (observed : Observes state input rows finish) : feed input state = (rows, finish) := by
  induction observed with
  | nil => rfl
  | cons first later ih => simp [feed, first.sound, ih]

theorem Observes.complete (state : State) (input : List Char) :
    Observes state input (feed input state).1 (feed input state).2 := by
  induction input generalizing state with
  | nil => exact .nil state
  | cons scalar rest ih =>
      exact .cons (Advances.complete state scalar) (ih (step state scalar).2)

theorem feed_iff (state : State) (input : List Char) (rows : List Row) (finish : State) :
    feed input state = (rows, finish) ↔ Observes state input rows finish := by
  constructor
  · intro same
    simpa [same] using Observes.complete state input
  · exact Observes.sound

/-- Two chunks give exactly the same occurrences and residual as their
concatenation, including an empty chunk between CR and LF. -/
theorem feed_append (first second : List Char) (state : State) :
    feed (first ++ second) state =
      let earlier := feed first state
      let later := feed second earlier.2
      (earlier.1 ++ later.1, later.2) := by
  induction first generalizing state with
  | nil => simp [feed]
  | cons scalar rest ih => simp [feed, ih, List.append_assoc]

theorem step_counter (state : State) (scalar : Char) :
    (step state scalar).2.nextLine = state.nextLine + (step state scalar).1.length := by
  unfold step
  split
  · simp
  · split <;> simp

theorem feed_counter (input : List Char) (state : State) :
    (feed input state).2.nextLine = state.nextLine + (feed input state).1.length := by
  induction input generalizing state with
  | nil => simp [feed]
  | cons scalar rest ih =>
      simp only [feed]
      rw [ih, step_counter]
      simp [Nat.add_assoc]

/-- State-only execution does not construct a completed row. -/
def advanceScalar (state : State) (scalar : Char) : State :=
  if skipsLF state scalar then
    {state with afterCR := false}
  else if isBoundary scalar then
    ⟨[], state.nextLine + 1, scalar == '\r'⟩
  else
    {state with reversePending := scalar :: state.reversePending, afterCR := false}

def advance (input : List Char) (state : State) : State :=
  match input with
  | [] => state
  | scalar :: rest => advance rest (advanceScalar state scalar)

theorem advanceScalar_agrees (state : State) (scalar : Char) :
    advanceScalar state scalar = (step state scalar).2 := by
  unfold advanceScalar step
  split <;> simp_all
  split <;> rfl

theorem advance_agrees (input : List Char) (state : State) :
    advance input state = (feed input state).2 := by
  induction input generalizing state with
  | nil => rfl
  | cons scalar rest ih =>
      simp only [advance, feed, ih, advanceScalar_agrees]

theorem observations_after_advance (first second : List Char) (state : State) :
    (feed (first ++ second) state).1 =
      (feed first state).1 ++ (feed second (advance first state)).1 := by
  rw [advance_agrees, feed_append]

theorem advance_counter (input : List Char) (state : State) :
    (advance input state).nextLine = state.nextLine + (feed input state).1.length := by
  rw [advance_agrees, feed_counter]

def finish (state : State) : List Row × State :=
  match state.reversePending with
  | [] => ([], state)
  | _ :: _ =>
      ([(state.nextLine, state.reversePending.reverse)],
        {state with reversePending := [], nextLine := state.nextLine + 1})

theorem finish_empty_no_line (number : Nat) (afterCR : Bool) :
    finish ⟨[], number, afterCR⟩ = ([], ⟨[], number, afterCR⟩) := rfl

theorem finish_idempotent (state : State) :
    finish (finish state).2 = ([], (finish state).2) := by
  cases state with
  | mk pending number cr => cases pending <;> rfl

theorem finish_counter (state : State) :
    (finish state).2.nextLine = state.nextLine + (finish state).1.length := by
  cases state with
  | mk pending number cr => cases pending <;> simp [finish]

universe u v
variable {Fault : Type u} {Reason : Type v}

inductive Input (Fault : Type u) (Reason : Type v) where
  | chunk (scalars : List Char)
  | ended
  | fault (value : Fault)
  | interrupted (reason : Reason)

def observe (state : State) : Input Fault Reason → List Row × State × FilesystemObservation.Stop Fault Reason
  | .chunk scalars => ((feed scalars state).1, (feed scalars state).2, .paused)
  | .ended => ((finish state).1, (finish state).2, .ended)
  | .fault value => ([], state, .fault value)
  | .interrupted reason => ([], state, .interrupted reason)

theorem empty_chunk_not_end (state : State) :
    observe (Fault := Fault) (Reason := Reason) state (.chunk []) = ([], state, .paused) := rfl

theorem only_end_finishes (state : State) (input : Input Fault Reason) :
    (observe state input).2.2 = .ended ↔ input = .ended := by
  cases input <;> simp [observe]

theorem fault_keeps_pending (state : State) (fault : Fault) :
    observe (Reason := Reason) state (.fault fault) = ([], state, .fault fault) := rfl

theorem interruption_keeps_pending (state : State) (reason : Reason) :
    observe (Fault := Fault) state (.interrupted reason) = ([], state, .interrupted reason) := rfl

example : (feed ['\n', '\n'] State.initial).1 = [(1, []), (2, [])] := by decide
example : (feed ['a', '\r', '\n', 'b'] State.initial).1 = [(1, ['a'])] := by decide
example : (finish (feed ['a', '\r', '\n', 'b'] State.initial).2).1 = [(2, ['b'])] := by decide
example : (feed ['\r', '\n'] State.initial).1 = [(1, [])] := by decide
example : (feed [Char.ofNat 0x85, Char.ofNat 0x2028, Char.ofNat 0x2029] State.initial).1 =
    [(1, []), (2, []), (3, [])] := by decide

end Mettapedia.Machines.RunContracts.TextLineObservation
