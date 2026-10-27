import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.RegisterCode
import Mettapedia.Machines.OwnedPullDriverCost

/-!
# Contextual return sequencing through owned child frames

The independent reference concatenates each admitted body's ordered return
trace. The lowering instead installs the body as a child of the existing
explicit-frame driver. Its continuation retains the producer packet until
body retirement and producer acceptance. Raised control bypasses body
admission; an admission refusal retains the actual packet and remaining
producer occurrences, whereas an admitted empty body contributes zero answers.

This is the finite component-trace fragment of `CettaOwnedBind`. Interpreting
events can have non-idempotent effects. Live producer transitions, native pointer
ownership, cancellation, external invalidation and C correspondence need their
own adapters; administrative driver steps are not source-level fuel charges.

`NativeReader` joins the indexed native-return cursor to these child frames.
Its independent list specification preserves the exact terminal reason and a
handoff's pending occurrence. Producer-row allowances and physical driver
allowances remain distinct from source fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OwnedBind

open NativeCallReturn (Packet Returned)
open OwnedPullDriver

variable {Value Fault Delay Context : Type}

inductive Exit (Item : Type) where
  | complete
  | handoff (held : Item) (remaining : List Item)
  deriving DecidableEq, Repr

inductive Event (Item : Type) where
  | pull (item : Item)
  | admit (item : Item)
  | publish (item : Item)
  | retireBody (item : Item)
  | accept (item : Item)
  deriving DecidableEq, Repr

local notation "Entry" => Returned Value Fault Delay Context
local notation "Code" => Program (Exit Entry) (Event Entry)

def raised (item : Entry) : Bool :=
  match item.2 with
  | .raised _ => true
  | _ => false

/-- An ordinary recursive observer, independent of explicit child frames. -/
def reference (body : Entry → Option (List Entry)) :
    List Entry → List (Event Entry) × Exit Entry
  | [] => ([], .complete)
  | item :: rest =>
      if raised item then
        let suffix := reference body rest
        (.pull item :: .publish item :: .accept item :: suffix.1, suffix.2)
      else match body item with
        | none => ([.pull item, .admit item], .handoff item rest)
        | some rows =>
            let suffix := reference body rest
            (.pull item :: .admit item ::
              (rows.map Event.publish ++ .retireBody item :: .accept item :: suffix.1),
              suffix.2)

def publishAll : List Entry → Code
  | [] => .done .complete
  | item :: rest => .emit (.publish item) (publishAll rest)

/-- Body execution and the pending producer packet have distinct lifetimes. -/
def lower (body : Entry → Option (List Entry)) : List Entry → Code
  | [] => .done .complete
  | item :: rest =>
      .emit (.pull item)
        (if raised item then
          .emit (.publish item) (.emit (.accept item) (lower body rest))
        else
          .emit (.admit item) (match body item with
            | none => .done (.handoff item rest)
            | some rows => .child (publishAll rows) (fun _ =>
                .emit (.retireBody item) (.emit (.accept item) (lower body rest)))))

theorem publish_runs (rows : List Entry) :
    Runs (publishAll rows) (rows.map Event.publish) (.complete : Exit Entry) := by
  induction rows with
  | nil => exact .done
  | cons first rest ih => exact .emit ih

theorem lower_runs (body : Entry → Option (List Entry)) (items : List Entry) :
    Runs (lower body items) (reference body items).1 (reference body items).2 := by
  induction items with
  | nil => exact .done
  | cons item rest ih =>
      cases role : raised item with
      | true =>
          simpa [lower, reference, role] using Runs.emit (Runs.emit (Runs.emit ih))
      | false =>
          cases admission : body item with
          | none => simp only [lower, reference, role, Bool.false_eq_true, ↓reduceIte,
                               admission]; exact .emit (.emit .done)
          | some rows =>
              simpa [lower, reference, role, admission] using
                Runs.emit (Runs.emit (Runs.child (publish_runs rows)
                  (Runs.emit (Runs.emit ih))))

/-- The existing explicit driver realizes the independently specified ordered
trace, including factory admission, duplicates and release order. -/
theorem explicit_driver_refines (body : Entry → Option (List Entry)) (items : List Entry) :
    ∃ fuel, advance fuel ⟨lower body items, []⟩ =
      ((reference body items).1, ⟨.done (reference body items).2, []⟩) :=
  advance_refines_runs (lower_runs body items)

/-- Count only entered bodies, stopping at a refused continuation. Raised
control bypasses ordinary sequencing even when the supplied factory admits it. -/
def admittedBodies (body : Entry → Option (List Entry)) : List Entry → Nat
  | [] => 0
  | item :: rest =>
      if raised item then admittedBodies body rest
      else match body item with
        | none => 0
        | some _ => admittedBodies body rest + 1

theorem publish_costed (rows : List Entry) :
    CostedRuns (publishAll rows) (rows.map Event.publish)
      (.complete : Exit Entry) 0 0 := by
  induction rows with
  | nil => exact .done
  | cons _ _ ih => exact .emit ih

/-- Each admitted body contributes one child frame, which retires before the
next source occurrence. The finite trace fragment needs at most one such frame,
independently of producer length and result multiplicity. -/
theorem lower_costed (body : Entry → Option (List Entry)) (items : List Entry) :
    ∃ depth, depth ≤ 1 ∧ CostedRuns (lower body items)
      (reference body items).1 (reference body items).2
      (admittedBodies body items) depth := by
  induction items with
  | nil => exact ⟨0, by omega, .done⟩
  | cons item rest ih =>
      obtain ⟨depth, bounded, tail⟩ := ih
      cases role : raised item with
      | true =>
          exact ⟨depth, bounded, by
            simpa [lower, reference, admittedBodies, role] using
              CostedRuns.emit (CostedRuns.emit (CostedRuns.emit tail))⟩
      | false =>
          cases admission : body item with
          | none =>
              refine ⟨0, by omega, ?_⟩
              simp only [lower, reference, admittedBodies, role,
                Bool.false_eq_true, ↓reduceIte, admission]
              exact .emit (.emit .done)
          | some rows =>
              refine ⟨1, by omega, ?_⟩
              have maximum : max (0 + 1) depth = 1 := by omega
              simpa [lower, reference, admittedBodies, role, admission,
                maximum] using CostedRuns.emit (CostedRuns.emit
                  (CostedRuns.child
                    (resume := fun _ => .emit (.retireBody item)
                      (.emit (.accept item) (lower body rest)))
                    (publish_costed rows)
                    (CostedRuns.emit (CostedRuns.emit tail))))

/-- The explicit driver has an exact transition count: one per event and two
administrative transitions per entered body. No result-size factor multiplies
the number of retained child frames. Component-internal work is outside this
finite trace model. -/
theorem bounded_driver (body : Entry → Option (List Entry)) (items : List Entry) :
    PathWithin 1 ⟨lower body items, []⟩ (reference body items).1
      ((reference body items).1.length + 2 * admittedBodies body items)
      ⟨.done (reference body items).2, []⟩ := by
  obtain ⟨depth, bounded, run⟩ := lower_costed body items
  simpa using (run.driver []).weaken (by simpa using bounded)

theorem split_resumption (body : Entry → Option (List Entry)) (items : List Entry)
    (first extra : Nat) :
    advance (first + extra) ⟨lower body items, []⟩ =
      let earlier := advance first ⟨lower body items, []⟩
      let later := advance extra earlier.2
      (earlier.1 ++ later.1, later.2) :=
  advance_add first extra _

/-- After body entry the explicit continuation still captures the exact
producer packet, including its context, provenance and pending check. -/
theorem body_entry_retains_packet (body : Entry → Option (List Entry))
    (item : Entry) (rest rows : List Entry)
    (value : raised item = false) (admitted : body item = some rows) :
    advance 3 ⟨lower body (item :: rest), []⟩ =
      ([.pull item, .admit item],
        ⟨publishAll rows,
          [fun _ => .emit (.retireBody item) (.emit (.accept item) (lower body rest))]⟩) := by
  simp [advance, transition, lower, value, admitted]

def resumeCode (body : Entry → Option (List Entry))
    (held : Entry) (remaining rows : List Entry) : Code :=
  .child (publishAll rows) (fun _ =>
    .emit (.retireBody held) (.emit (.accept held) (lower body remaining)))

/-- A replacement worker starts with the retained packet. There is no new
pull or attempt to reenter its declined continuation. Later equal occurrences
remain independent source work. -/
theorem handoff_resume_runs (body : Entry → Option (List Entry))
    (held : Entry) (remaining rows : List Entry) :
    Runs (resumeCode body held remaining rows)
      (rows.map Event.publish ++ .retireBody held :: .accept held ::
        (reference body remaining).1)
      (reference body remaining).2 := by
  exact .child (publish_runs rows) (.emit (.emit (lower_runs body remaining)))

theorem resumed_driver_refines (body : Entry → Option (List Entry))
    (held : Entry) (remaining rows : List Entry) :
    ∃ fuel, advance fuel ⟨resumeCode body held remaining rows, []⟩ =
      (rows.map Event.publish ++ .retireBody held :: .accept held ::
        (reference body remaining).1, ⟨.done (reference body remaining).2, []⟩) :=
  advance_refines_runs (handoff_resume_runs body held remaining rows)

theorem world_and_history_resume {World : Type} (action : Event Entry → World → World)
    (body : Entry → Option (List Entry)) (items : List Entry) (world : World)
    (first extra : Nat) :
    Session.resume action (first + extra) (Session.begin (lower body items) world) =
      Session.resume action extra
        (Session.resume action first (Session.begin (lower body items) world)) :=
  Session.resume_add action first extra _

namespace NativeReader

local notation "Cursor" => NativeCallReturn.Cursor Value Fault Delay Context

/-- Target handoff retains an indexed producer, rather than materializing its
remaining answers. Logical completion, interruption and a physical row pause
have different constructors. -/
inductive Boundary (Value Fault Delay Context : Type) where
  | stopped (reason : NativeCallReturn.Stop)
  | handoff (held : Returned Value Fault Delay Context)
      (remaining : NativeCallReturn.Cursor Value Fault Delay Context)
  | paused (remaining : NativeCallReturn.Cursor Value Fault Delay Context)

inductive Observation (Item : Type) where
  | stopped (reason : NativeCallReturn.Stop)
  | handoff (held : Item) (remaining : List Item)
  | paused (remaining : List Item)
  deriving DecidableEq, Repr

def observe : Boundary Value Fault Delay Context → Observation Entry
  | .stopped reason => .stopped reason
  | .handoff held remaining => .handoff held (NativeCallReturn.residual remaining).1
  | .paused remaining => .paused (NativeCallReturn.residual remaining).1

/-- Independent bounded list semantics. The row allowance limits producer
loans, independently of the explicit driver's transition allowance. Neither
allowance asserts correspondence to a dialect's source fuel. -/
def reference (body : Entry → Option (List Entry)) :
    Nat → List Entry → NativeCallReturn.Stop → List (Event Entry) × Observation Entry
  | 0, rows, _ => ([], .paused rows)
  | _ + 1, [], reason => ([], .stopped reason)
  | allowance + 1, item :: rest, reason =>
      if raised item then
        let suffix := reference body allowance rest reason
        (.pull item :: .publish item :: .accept item :: suffix.1, suffix.2)
      else match body item with
        | none => ([.pull item, .admit item], .handoff item rest)
        | some rows =>
            let suffix := reference body allowance rest reason
            (.pull item :: .admit item ::
              (rows.map Event.publish ++ .retireBody item :: .accept item :: suffix.1),
              suffix.2)

private def emitRows (rows : List Entry) (exit : Boundary Value Fault Delay Context) :
    Program (Boundary Value Fault Delay Context) (Event Entry) :=
  match rows with
  | [] => .done exit
  | item :: rest => .emit (.publish item) (emitRows rest exit)

/-- The target uses the native reader's original array and offset. Only the
loaned occurrence enters a child frame. Refusal keeps the actual next cursor. -/
def lower (body : Entry → Option (List Entry)) : Nat → Cursor →
    Program (Boundary Value Fault Delay Context) (Event Entry)
  | 0, cursor => .done (.paused cursor)
  | allowance + 1, cursor =>
      match NativeCallReturn.read cursor with
      | .stopped reason => .done (.stopped reason)
      | .returned item next =>
          .emit (.pull item) (if raised item then
            .emit (.publish item) (.emit (.accept item) (lower body allowance next))
          else .emit (.admit item) (match body item with
            | none => .done (.handoff item next)
            | some rows => .child (emitRows rows (.stopped .complete)) (fun _ =>
                .emit (.retireBody item) (.emit (.accept item) (lower body allowance next)))))

private theorem emitRows_runs (rows : List Entry) (exit : Boundary Value Fault Delay Context) :
    Runs (emitRows rows exit) (rows.map Event.publish) exit := by
  induction rows with
  | nil => exact .done
  | cons _ _ ih => exact .emit ih

/-- Array-backed native delivery and the independent list specification agree
on every ordered event and on the retained handoff or terminal reason. -/
theorem lower_runs (body : Entry → Option (List Entry)) (allowance : Nat) (cursor : Cursor) :
    ∃ exit, Runs (lower body allowance cursor)
      (reference body allowance (NativeCallReturn.residual cursor).1
        (NativeCallReturn.residual cursor).2).1 exit ∧
      observe exit = (reference body allowance (NativeCallReturn.residual cursor).1
        (NativeCallReturn.residual cursor).2).2 := by
  induction allowance generalizing cursor with
  | zero => exact ⟨.paused cursor, .done, rfl⟩
  | succ allowance ih =>
      cases found : NativeCallReturn.read cursor with
      | stopped reason =>
          have residual := NativeCallReturn.read_stopped_residual found
          exact ⟨.stopped reason, by simp only [lower, found, residual, reference]; exact .done,
            by simp [observe, residual, reference]⟩
      | returned item next =>
          have residual := NativeCallReturn.read_returned_residual found
          obtain ⟨exit, tail, observed⟩ := ih next
          cases role : raised item with
          | true =>
              refine ⟨exit, ?_, ?_⟩
              · simpa [lower, found, role, residual, reference] using
                  Runs.emit (Runs.emit (Runs.emit tail))
              · simpa [residual, reference, role] using observed
          | false =>
              cases admitted : body item with
              | none =>
                  refine ⟨.handoff item next, ?_, ?_⟩
                  · simp only [lower, found, role, Bool.false_eq_true, ↓reduceIte,
                      admitted, residual, reference]; exact .emit (.emit .done)
                  · simp [observe, residual, reference, role, admitted]
              | some rows =>
                  refine ⟨exit, ?_, ?_⟩
                  · simpa [lower, found, role, admitted, residual, reference] using
                      Runs.emit (Runs.emit (Runs.child
                        (resume := fun _ => .emit (.retireBody item)
                          (.emit (.accept item) (lower body allowance next)))
                        (emitRows_runs rows (.stopped .complete))
                        (Runs.emit (Runs.emit tail))))
                  · simpa [residual, reference, role, admitted] using observed

theorem driver_refines (body : Entry → Option (List Entry)) (allowance : Nat) (cursor : Cursor) :
    ∃ fuel exit, advance fuel ⟨lower body allowance cursor, []⟩ =
      ((reference body allowance (NativeCallReturn.residual cursor).1
        (NativeCallReturn.residual cursor).2).1, ⟨.done exit, []⟩) ∧
      observe exit = (reference body allowance (NativeCallReturn.residual cursor).1
        (NativeCallReturn.residual cursor).2).2 := by
  obtain ⟨exit, run, observed⟩ := lower_runs body allowance cursor
  obtain ⟨fuel, executed⟩ := advance_refines_runs run
  exact ⟨fuel, exit, executed, observed⟩

theorem split_history {World : Type} (action : Event Entry → World → World)
    (body : Entry → Option (List Entry)) (allowance : Nat) (cursor : Cursor)
    (world : World) (first extra : Nat) :
    Session.resume action (first + extra) (Session.begin (lower body allowance cursor) world) =
      Session.resume action extra
        (Session.resume action first (Session.begin (lower body allowance cursor) world)) :=
  Session.resume_add action first extra _

def completeObservation (reason : NativeCallReturn.Stop) : Exit Entry → Observation Entry
  | .complete => .stopped reason
  | .handoff held remaining => .handoff held remaining

/-- Enough producer loans join the bounded native specification to the
existing unbounded owned-bind reference, preserving the source's stop reason. -/
theorem full_reference (body : Entry → Option (List Entry)) (rows : List Entry)
    (reason : NativeCallReturn.Stop) (allowance : Nat) (enough : rows.length < allowance) :
    reference body allowance rows reason =
      ((OwnedBind.reference body rows).1,
        completeObservation reason (OwnedBind.reference body rows).2) := by
  induction rows generalizing allowance with
  | nil =>
      cases allowance with
      | zero => simp at enough
      | succ allowance => rfl
  | cons item rest ih =>
      cases allowance with
      | zero => simp at enough
      | succ allowance =>
          have smaller : rest.length < allowance := by simpa using enough
          cases role : raised item with
          | true => simp [reference, OwnedBind.reference, role, ih allowance smaller]
          | false =>
              cases admitted : body item with
              | none => simp [reference, OwnedBind.reference, role, admitted, completeObservation]
              | some rows => simp [reference, OwnedBind.reference, role, admitted, ih allowance smaller]

/-- The indexed producer, the shared child-frame machine, and the independent
owned-bind list semantics form one refinement. Native interruption is kept
separate from logical zero; an admission handoff keeps its exact loan. -/
theorem full_driver_refines (body : Entry → Option (List Entry)) (cursor : Cursor) :
    ∃ fuel exit, advance fuel
      ⟨lower body ((NativeCallReturn.residual cursor).1.length + 1) cursor, []⟩ =
      ((OwnedBind.reference body (NativeCallReturn.residual cursor).1).1,
        ⟨.done exit, []⟩) ∧ observe exit = completeObservation
          (NativeCallReturn.residual cursor).2
          (OwnedBind.reference body (NativeCallReturn.residual cursor).1).2 := by
  obtain ⟨fuel, exit, executed, observed⟩ := driver_refines body
    ((NativeCallReturn.residual cursor).1.length + 1) cursor
  have full := full_reference body (NativeCallReturn.residual cursor).1
    (NativeCallReturn.residual cursor).2
    ((NativeCallReturn.residual cursor).1.length + 1) (by omega)
  exact ⟨fuel, exit, by simpa [full] using executed, by simpa [full] using observed⟩

end NativeReader

namespace NativeRegister

open RegisterCode

variable {V L O P H : Type}

def snapshot (live : Finset Nat) (registers : Regs V) : Regs V :=
  fun slot => if slot ∈ live then registers slot else none

private theorem answer_agrees {out : Finset Nat} {first second : Option (Outcome V)}
    (related : Option.Rel (Outcome.Agree out) first second) :
    answer first = answer second := by
  cases related with
  | none => rfl
  | @some first second related =>
      cases first <;> cases second <;> simp_all [Outcome.Agree, answer]

/-- A native result fills the same logical slot after readback. Only the
continuation's other live slots need a saved value; uninitialized and dead
registers are never inspected. This proves equality of complete outcomes,
including refusal, rather than equality only for successful examples. -/
theorem resume_live (sem : Sem V L O P H) (calls : H → List V → Option V)
    (rest : List (Instr L O P H)) (registers : Regs V) (destination : Nat) (value : V) :
    answer (exec sem calls rest (Function.update
      (snapshot ((liveIn sem.toPatterns rest ∅).erase destination) registers)
      destination (some value))) =
    answer (exec sem calls rest (Function.update registers destination (some value))) := by
  apply answer_agrees
  apply exec_live sem calls rest ∅
  intro slot live
  by_cases same : slot = destination
  · subst slot
    simp
  · simp [Function.update_of_ne same, snapshot, Finset.mem_erase.mpr ⟨same, live⟩]

/-- Join liveness-preserving native readback to the independent node
semantics through the existing compiler theorem. This is a concrete local
continuation law; flat-PC encoding and native pointer relocation remain
separate correspondence obligations. -/
theorem resume_matches_node (sem : Sem V L O P H) (calls : H → List V → Option V)
    (fuses : O → Nat → Bool) (body : Node L O P H) (locals : Nat) (scope : Finset Nat)
    (scopeValid : Scoped sem.toPatterns locals scope body)
    (bounds : ∀ slot ∈ scope, slot < locals)
    (registers : Regs V) (destination : Nat) (value : V) :
    let code := (compile fuses body true 0 locals).1
    answer (exec sem calls code (Function.update
      (snapshot ((liveIn sem.toPatterns code ∅).erase destination) registers)
      destination (some value))) =
      (eval sem calls (Function.update registers destination (some value)) body).map Prod.fst := by
  dsimp
  rw [resume_live]
  exact (lower_answers sem calls fuses scopeValid bounds (fun _ _ => rfl) (Nat.le_refl locals)).answer_eq

/-- Each native occurrence resumes independently. Mapping the proved local
law preserves the entire ordered occurrence list, including duplicates. -/
theorem ordered_resumption (sem : Sem V L O P H) (calls : H → List V → Option V)
    (fuses : O → Nat → Bool) (body : Node L O P H) (locals : Nat) (scope : Finset Nat)
    (scopeValid : Scoped sem.toPatterns locals scope body)
    (bounds : ∀ slot ∈ scope, slot < locals)
    (registers : Regs V) (destination : Nat) (rows : List V) :
    let code := (compile fuses body true 0 locals).1
    rows.map (fun value => answer (exec sem calls code (Function.update
      (snapshot ((liveIn sem.toPatterns code ∅).erase destination) registers)
      destination (some value)))) =
    rows.map (fun value =>
      (eval sem calls (Function.update registers destination (some value)) body).map Prod.fst) := by
  dsimp
  apply List.map_congr_left
  intro value _
  exact resume_matches_node sem calls fuses body locals scope scopeValid bounds registers destination value

/-- A waiting caller owns its lexical register file and receives the callee's
answer in one destination. Frames are ordered from the nearest caller outward. -/
structure SavedFrame (V L O P H : Type) (patterns : Patterns P) where
  body : Node L O P H
  locals : Nat
  scope : Finset Nat
  wellScoped : Scoped patterns locals scope body
  bounds : ∀ slot ∈ scope, slot < locals
  registers : Regs V
  destination : Nat

/-- Source continuations evaluate their bodies directly, with no readback or
register lowering. A refused inner caller never enters an outer caller. -/
def sourceFrames (sem : Sem V L O P H) (calls : H → List V → Option V) :
    List (SavedFrame V L O P H sem.toPatterns) → V → Option V
  | [], value => some value
  | frame :: rest, value =>
      ((eval sem calls (Function.update frame.registers frame.destination (some value))
        frame.body).map Prod.fst).bind (sourceFrames sem calls rest)

/-- The target restores only live slots of each waiting caller, installs the
actual callee answer, and executes its independently lowered register code. -/
def resumeFrames (sem : Sem V L O P H) (calls : H → List V → Option V)
    (fuses : O → Nat → Bool) :
    List (SavedFrame V L O P H sem.toPatterns) → V → Option V
  | [], value => some value
  | frame :: rest, value =>
      let code := (compile fuses frame.body true 0 frame.locals).1
      (answer (exec sem calls code (Function.update
        (snapshot ((liveIn sem.toPatterns code ∅).erase frame.destination) frame.registers)
        frame.destination (some value)))).bind (resumeFrames sem calls fuses rest)

/-- Readback preserves the whole waiting caller spine, including an inner
refusal and every caller's separate lexical registers. This joins the local
liveness and lowering laws; it does not identify flat C PCs or pointer owners. -/
theorem resume_frames_refines (sem : Sem V L O P H) (calls : H → List V → Option V)
    (fuses : O → Nat → Bool) (frames : List (SavedFrame V L O P H sem.toPatterns))
    (value : V) : resumeFrames sem calls fuses frames value = sourceFrames sem calls frames value := by
  induction frames generalizing value with
  | nil => rfl
  | cons frame rest ih =>
      simp only [resumeFrames, sourceFrames]
      rw [resume_matches_node sem calls fuses frame.body frame.locals frame.scope
        frame.wellScoped frame.bounds frame.registers frame.destination value]
      cases eval sem calls (Function.update frame.registers frame.destination (some value))
        frame.body with
      | none => rfl
      | some result => exact ih result.1

theorem ordered_frames_refines (sem : Sem V L O P H) (calls : H → List V → Option V)
    (fuses : O → Nat → Bool) (frames : List (SavedFrame V L O P H sem.toPatterns))
    (rows : List V) :
    rows.map (resumeFrames sem calls fuses frames) = rows.map (sourceFrames sem calls frames) := by
  apply List.map_congr_left
  intro value _
  exact resume_frames_refines sem calls fuses frames value

/-- Only a completed value enters a value continuation. An unavailable
continuation retains the producer loan; it is not an admitted empty body.
Expression and conditional packets still require their dialect completion. -/
def packetBody (run : V → Option V) (item : Returned V Fault Delay Context) :
    Option (List (Returned V Fault Delay Context)) :=
  match item.2 with
  | .value .completed value =>
      (run value).map fun answer => [(item.1, .value .completed answer)]
  | _ => none

/-- The indexed native reader, explicit owned child frames, live-register
readback and register lowering jointly realize the independent list/node
observer. The statement retains exact pauses, refused loans and stop causes,
not only final successful values. Native C layout and source fuel are outside
this composition of the maintained models. -/
theorem native_frames_driver_refines (sem : Sem V L O P H)
    (calls : H → List V → Option V) (fuses : O → Nat → Bool)
    (frames : List (SavedFrame V L O P H sem.toPatterns)) (allowance : Nat)
    (cursor : NativeCallReturn.Cursor V Fault Delay Context) :
    let source := packetBody (sourceFrames sem calls frames)
    let target := packetBody (resumeFrames sem calls fuses frames)
    ∃ fuel exit, advance fuel ⟨NativeReader.lower target allowance cursor, []⟩ =
      ((NativeReader.reference source allowance (NativeCallReturn.residual cursor).1
        (NativeCallReturn.residual cursor).2).1, ⟨.done exit, []⟩) ∧
      NativeReader.observe exit =
        (NativeReader.reference source allowance (NativeCallReturn.residual cursor).1
          (NativeCallReturn.residual cursor).2).2 := by
  have same : resumeFrames sem calls fuses frames = sourceFrames sem calls frames :=
    funext (resume_frames_refines sem calls fuses frames)
  dsimp only
  rw [same]
  exact NativeReader.driver_refines _ allowance cursor

namespace Controls

open RegisterCode.Example

def code : List (Instr Nat Op Nat Head) := [.opRet .add [.reg 0, .reg 1]]
def registers : Regs Nat := fun slot => if slot = 0 then some 40 else none

theorem live_value_and_duplicate_rows :
    [2, 2].map (fun value => answer (exec sem (fun _ _ => none) code
      (Function.update (snapshot {0} registers) 1 (some value)))) = [some 42, some 42] := by
  decide

theorem dropping_live_value_is_detected :
    answer (exec sem (fun _ _ => none) code
      (Function.update (snapshot ∅ registers) 1 (some 2))) = none ∧
    answer (exec sem (fun _ _ => none) code
      (Function.update (snapshot {0} registers) 1 (some 2))) = some 42 := by
  decide

def caller (operation : Op) (saved : Nat) : SavedFrame Nat Nat Op Nat Head sem.toPatterns where
  body := .op operation [.slot 0, .slot 1]
  locals := 2
  scope := {0, 1}
  wellScoped := by simp [Scoped, ScopedArgs]
  bounds := by simp
  registers := fun slot => if slot = 0 then some saved else none
  destination := 1

theorem waiting_callers_keep_order_and_duplicates :
    [2, 2].map (resumeFrames sem (fun _ _ => none) fuses [caller .add 40, caller .sub 100]) =
      [some 58, some 58] := by decide

theorem reversing_waiting_callers_is_detected :
    resumeFrames sem (fun _ _ => none) fuses [caller .add 40, caller .sub 100] 2 = some 58 ∧
    resumeFrames sem (fun _ _ => none) fuses [caller .sub 100, caller .add 40] 2 = some 138 := by
  decide

theorem completed_packet_preserves_context :
    packetBody (resumeFrames sem (fun _ _ => none) fuses
      [caller .add 40, caller .sub 100]) (7, .value .completed 2) =
      some [(7, (.value .completed 58 : Packet Nat Nat Nat))] := by decide

theorem expression_packet_requires_completion :
    packetBody (resumeFrames sem (fun _ _ => none) fuses [caller .add 40])
      ((7, .value .expression 2) : Returned Nat Nat Nat Nat) = none := by decide

end Controls
end NativeRegister

namespace NativeCompletion

variable {Effect Result Reason : Type}

structure Component (Effect Result Reason : Type) where
  effects : List Effect
  outcome : Except Reason (List Result)

inductive Event (Effect Result : Type) where
  | effect (event : Effect)
  | publish (value : Result)
  deriving DecidableEq, Repr

private def prepend (held : List Result) : Except Reason (List Result) →
    Except Reason (List Result)
  | .ok rows => .ok (held ++ rows)
  | .error reason => .error reason

/-- Independent recursive producer semantics, before its caller can consume
any result. Earlier effects survive a later fault; unpublished values do not. -/
def reference : List (Component Effect Result Reason) →
    List (Event Effect Result) × Except Reason (List Result)
  | [] => ([], .ok [])
  | first :: rest => match first.outcome with
      | .error reason => (first.effects.map Event.effect, .error reason)
      | .ok rows =>
          let suffix := reference rest
          (first.effects.map Event.effect ++ suffix.1, prepend rows suffix.2)

private def emitAll (events : List (Event Effect Result))
    (next : Program (Except Reason Unit) (Event Effect Result)) :=
  events.foldr Program.emit next

private def publication (held : List Result) : Except Reason (List Result) →
    List (Event Effect Result)
  | .ok rows => (held ++ rows).map Event.publish
  | .error _ => []

private def publicationWith (finish : List Result → List Result) (held : List Result) :
    Except Reason (List Result) → List (Event Effect Result)
  | .ok rows => (finish (held ++ rows)).map Event.publish
  | .error _ => []

private def status : Except Reason (List Result) → Except Reason Unit
  | .ok _ => .ok ()
  | .error reason => .error reason

/-- The worker stores values while effects execute. Only an exhausted producer
switches to publication; an entered fault retires the unpublished buffer. -/
def lowerWith (finish : List Result → List Result) (held : List Result) :
    List (Component Effect Result Reason) →
    Program (Except Reason Unit) (Event Effect Result)
  | [] => emitAll ((finish held).map Event.publish) (.done (.ok ()))
  | first :: rest => emitAll (first.effects.map Event.effect)
      (match first.outcome with
       | .error reason => .done (.error reason)
       | .ok rows => lowerWith finish (held ++ rows) rest)

/-- Ordinary completed frontiers publish every retained occurrence. A
collection specializes the same driver with one aggregate result. -/
def lower (held : List Result) (components : List (Component Effect Result Reason)) :=
  lowerWith id held components

private theorem emitAll_runs {next : Program (Except Reason Unit) (Event Effect Result)}
    {events : List (Event Effect Result)} {result : Except Reason Unit}
    (earlier : List (Event Effect Result)) (tail : Runs next events result) :
    Runs (emitAll earlier next) (earlier ++ events) result := by
  induction earlier with
  | nil => exact tail
  | cons _ _ ih => exact .emit ih

theorem lowerWith_runs (finish : List Result → List Result)
    (components : List (Component Effect Result Reason)) (held : List Result) :
    Runs (lowerWith finish held components)
      ((reference components).1 ++ publicationWith finish held (reference components).2)
      (status (reference components).2) := by
  induction components generalizing held with
  | nil =>
      simpa [lowerWith, reference, publicationWith, status] using
        emitAll_runs (Reason := Reason) ((finish held).map Event.publish) Runs.done
  | cons first rest ih =>
      rcases first with ⟨effects, outcome⟩
      cases outcome with
      | error reason =>
          simpa [lowerWith, reference, publicationWith, status] using
            emitAll_runs (Result := Result) (effects.map Event.effect)
              (Runs.done (value := Except.error reason))
      | ok rows =>
          cases result : (reference rest).2 <;>
            simpa [lowerWith, reference, prepend, publicationWith, status, result,
              List.append_assoc] using
              emitAll_runs (effects.map Event.effect) (ih (held ++ rows))

theorem lower_runs (components : List (Component Effect Result Reason)) (held : List Result) :
    Runs (lower held components)
      ((reference components).1 ++ publication held (reference components).2)
      (status (reference components).2) := by
  have exactRun := lowerWith_runs (Effect := Effect) id components held
  cases outcome : (reference components).2 <;>
    simpa [lower, publicationWith, publication, outcome] using exactRun

/-- Joins the independent batch specification to the same explicit driver as
owned sequencing. Effects precede all caller publications, including duplicates. -/
theorem driver_refines (components : List (Component Effect Result Reason)) :
    ∃ allowance, advance allowance ⟨lower [] components, []⟩ =
      ((reference components).1 ++ publication [] (reference components).2,
        ⟨.done (status (reference components).2), []⟩) :=
  advance_refines_runs (lower_runs components [])

/-- Result shaping happens only after the complete producer succeeds.
The same owned driver can publish a frontier or one reified collection. -/
theorem driverWith_refines (finish : List Result → List Result)
    (components : List (Component Effect Result Reason)) :
    ∃ allowance, advance allowance ⟨lowerWith finish [] components, []⟩ =
      ((reference components).1 ++
        (match (reference components).2 with
         | .ok rows => (finish rows).map Event.publish
         | .error _ => []),
        ⟨.done ((reference components).2.map (fun _ => ())), []⟩) := by
  have exactRun := advance_refines_runs (lowerWith_runs finish components [])
  cases outcome : (reference components).2 <;>
    simpa [publicationWith, status, outcome, Except.map] using exactRun

theorem effects_before_duplicate_publications :
    ∃ allowance, advance allowance
      ⟨lower [] ([⟨[1], .ok [7]⟩, ⟨[2], .ok [7]⟩] :
        List (Component Nat Nat String)), []⟩ =
      ([.effect 1, .effect 2, .publish 7, .publish 7], ⟨.done (.ok ()), []⟩) := by
  simpa [reference, prepend, publication, status] using
    driver_refines ([⟨[1], .ok [7]⟩, ⟨[2], .ok [7]⟩] :
      List (Component Nat Nat String))

theorem later_fault_discards_unpublished_prefix :
    ∃ allowance, advance allowance
      ⟨lower [] ([⟨[1], .ok [7]⟩, ⟨[2], .error "fault"⟩] :
        List (Component Nat Nat String)), []⟩ =
      ([.effect 1, .effect 2], ⟨.done (.error "fault"), []⟩) := by
  simpa [reference, prepend, publication, status] using
    driver_refines ([⟨[1], .ok [7]⟩, ⟨[2], .error "fault"⟩] :
      List (Component Nat Nat String))

theorem interleaving_is_observable :
    ([Event.effect 1, .effect 2, .publish 7, .publish 7] : List (Event Nat Nat)) ≠
      [.effect 1, .publish 7, .effect 2, .publish 7] := by decide

end NativeCompletion

namespace Controls

abbrev Row := Returned String Nat Nat Nat

def input : Row := (7, .conditional "held" 42)
def duplicate (row : Row) : Option (List Row) := some [row, row]

theorem duplicates_keep_context_and_check :
    (reference duplicate [input, input]).1.filterMap
      (fun event => match event with | .publish row => some row | _ => none) =
      [input, input, input, input] := by decide

theorem empty_body_is_completion :
    (reference (fun _ : Row => some []) [input]).2 = .complete := by decide

theorem refusal_is_retained_handoff :
    reference (fun _ : Row => none) [input] =
      ([.pull input, .admit input], .handoff input []) := by decide

theorem raised_control_bypasses_body :
    reference (fun _ : Row => none) [(7, .raised 3)] =
      ([.pull (7, .raised 3), .publish (7, .raised 3), .accept (7, .raised 3)],
        .complete) := by decide

theorem error_spelling_is_data :
    (reference duplicate [(7, .value .completed "Error")]).1.filterMap
      (fun event => match event with | .publish row => some row | _ => none) =
      [(7, .value .completed "Error"), (7, .value .completed "Error")] := by decide

def countPull : Event Row → Nat → Nat
  | .pull _, world => world + 1
  | _, world => world

theorem restarting_handoff_repeats_source_work :
    let old := (reference (fun _ : Row => none) [input]).1
    interpret countPull (old ++ [.publish input, .retireBody input, .accept input]) 0 = 1 ∧
    interpret countPull (old ++ old) 0 = 2 := by decide

def nativeRows : NativeCallReturn.Cursor String Nat Nat Nat :=
  ⟨.frontier .completed #["held", "held"], 7, 0⟩

theorem native_frontier_keeps_duplicate_contexts :
    (NativeReader.reference duplicate 3 (NativeCallReturn.residual nativeRows).1
      (NativeCallReturn.residual nativeRows).2).1.filterMap
      (fun event => match event with | .publish row => some row | _ => none) =
      [(7, .value .completed "held"), (7, .value .completed "held"),
       (7, .value .completed "held"), (7, .value .completed "held")] := by decide

theorem native_handoff_keeps_offset :
    let after := advance 2 ⟨NativeReader.lower (fun _ : Row => none) 2 nativeRows, []⟩
    match after.2.work with
    | .done (.handoff held next) =>
        next.position = 1 ∧ held = (7, .value .completed "held")
    | _ => False := by
  simp [advance, transition, NativeReader.lower, nativeRows, NativeCallReturn.read, raised]

private def nativeStop (source : NativeCallReturn.Source String Nat Nat) :
    Option NativeCallReturn.Stop :=
  match (advance 1 ⟨NativeReader.lower duplicate 1 ⟨source, 7, 0⟩, []⟩).2.work with
  | .done (.stopped reason) => some reason
  | _ => none

theorem native_interruption_is_not_zero_or_empty_data :
    nativeStop .interrupted = some .cancelled ∧
    nativeStop .failure = some .complete ∧
    nativeStop (.one (.value .completed "Empty")) = none := by decide

end Controls
end Mettapedia.Machines.OwnedBind

#print axioms Mettapedia.Machines.OwnedBind.lower_runs
#print axioms Mettapedia.Machines.OwnedBind.explicit_driver_refines
#print axioms Mettapedia.Machines.OwnedBind.split_resumption
#print axioms Mettapedia.Machines.OwnedBind.body_entry_retains_packet
#print axioms Mettapedia.Machines.OwnedBind.handoff_resume_runs
#print axioms Mettapedia.Machines.OwnedBind.resumed_driver_refines
#print axioms Mettapedia.Machines.OwnedBind.world_and_history_resume
#print axioms Mettapedia.Machines.OwnedBind.Controls.duplicates_keep_context_and_check
#print axioms Mettapedia.Machines.OwnedBind.Controls.empty_body_is_completion
#print axioms Mettapedia.Machines.OwnedBind.Controls.refusal_is_retained_handoff
#print axioms Mettapedia.Machines.OwnedBind.Controls.raised_control_bypasses_body
#print axioms Mettapedia.Machines.OwnedBind.Controls.error_spelling_is_data
#print axioms Mettapedia.Machines.OwnedBind.Controls.restarting_handoff_repeats_source_work

#print axioms Mettapedia.Machines.OwnedBind.lower_costed
#print axioms Mettapedia.Machines.OwnedBind.bounded_driver

#print axioms Mettapedia.Machines.OwnedBind.NativeReader.lower_runs
#print axioms Mettapedia.Machines.OwnedBind.NativeReader.driver_refines
#print axioms Mettapedia.Machines.OwnedBind.NativeReader.split_history

#print axioms Mettapedia.Machines.OwnedBind.NativeReader.full_reference
#print axioms Mettapedia.Machines.OwnedBind.NativeReader.full_driver_refines
#print axioms Mettapedia.Machines.OwnedBind.Controls.native_frontier_keeps_duplicate_contexts
#print axioms Mettapedia.Machines.OwnedBind.Controls.native_handoff_keeps_offset
#print axioms Mettapedia.Machines.OwnedBind.Controls.native_interruption_is_not_zero_or_empty_data

#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.resume_live
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.resume_matches_node
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.ordered_resumption
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.Controls.live_value_and_duplicate_rows
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.Controls.dropping_live_value_is_detected
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.resume_frames_refines
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.ordered_frames_refines
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.Controls.waiting_callers_keep_order_and_duplicates
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.Controls.reversing_waiting_callers_is_detected
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.native_frames_driver_refines
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.Controls.completed_packet_preserves_context
#print axioms Mettapedia.Machines.OwnedBind.NativeRegister.Controls.expression_packet_requires_completion
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.lower_runs
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.driver_refines
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.effects_before_duplicate_publications
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.later_fault_discards_unpublished_prefix
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.interleaving_is_observable
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.lowerWith_runs
#print axioms Mettapedia.Machines.OwnedBind.NativeCompletion.driverWith_refines
