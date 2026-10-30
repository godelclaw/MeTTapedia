import Mettapedia.Machines.OwnedBind

/-!
# Splicing an entered native caller into its parent

The existing owned-child lowering keeps a producer packet until its caller
body retires. The target emits that body's events directly in the parent,
retaining the same publication, retirement and acknowledgment order. Raised
control bypasses ordinary body admission; refusal retains the pending packet.

The independent reference and target preserve the complete contextual packet
trace. The target removes the administrative child frame, not producer work or
semantic source charges. This finite component-trace law does not verify C
pointer lifetimes, heap evacuation, arbitrary source control or foreign clients.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeParentFusion

open NativeCallReturn (Returned Packet)
open OwnedPullDriver
open OwnedBind (Event Exit raised reference)

variable {Value Fault Delay Context : Type}
local notation "Entry" => Returned Value Fault Delay Context
local notation "Code" => Program (Exit Entry) (Event Entry)

def prepend (events : List (Event Entry)) (tail : Code) : Code :=
  events.foldr Program.emit tail

/-- Parent control carries the caller suffix itself instead of opening an
additional child machine for the same body. -/
def lower (body : Entry → Option (List Entry)) : List Entry → Code
  | [] => .done .complete
  | item :: rest =>
      .emit (.pull item)
        (if raised item then
          .emit (.publish item) (.emit (.accept item) (lower body rest))
        else .emit (.admit item) (match body item with
          | none => .done (.handoff item rest)
          | some rows => prepend (rows.map Event.publish)
              (.emit (.retireBody item) (.emit (.accept item) (lower body rest)))))

theorem prepend_costed (events : List (Event Entry)) (tail : Code)
    (trace : List (Event Entry)) (result : Exit Entry)
    (run : CostedRuns tail trace result 0 0) :
    CostedRuns (prepend events tail) (events ++ trace) result 0 0 := by
  induction events with
  | nil => exact run
  | cons event rest ih => exact .emit ih

/-- Direct caller execution realizes the recursive specification without a
child-frame birth, including empty bodies and conditional or raised packets. -/
theorem parent_costed (body : Entry → Option (List Entry)) (items : List Entry) :
    CostedRuns (lower body items) (reference body items).1
      (reference body items).2 0 0 := by
  induction items with
  | nil => exact .done
  | cons item rest ih =>
      cases role : raised item with
      | true => simpa [lower, reference, role] using
          CostedRuns.emit (CostedRuns.emit (CostedRuns.emit ih))
      | false =>
          cases admission : body item with
          | none => simp only [lower, reference, role, Bool.false_eq_true,
                               ↓reduceIte, admission]; exact .emit (.emit .done)
          | some rows =>
              simpa [lower, reference, role, admission] using
                CostedRuns.emit (CostedRuns.emit
                  (prepend_costed (rows.map Event.publish) _ _ _
                    (CostedRuns.emit (CostedRuns.emit ih))))

theorem parent_exact_transitions (body : Entry → Option (List Entry)) (items : List Entry) :
    PathWithin 0 ⟨lower body items, []⟩ (reference body items).1
      (reference body items).1.length ⟨.done (reference body items).2, []⟩ := by
  simpa using (parent_costed body items).driver []

/-- Both implementations expose the same contextual trace and actual stop;
only the physical child-entry/return transitions differ. -/
theorem child_parent_refinement (body : Entry → Option (List Entry)) (items : List Entry) :
    advance ((reference body items).1.length + 2 * OwnedBind.admittedBodies body items)
        ⟨OwnedBind.lower body items, []⟩ =
      advance (reference body items).1.length ⟨lower body items, []⟩ := by
  obtain ⟨_, _, run⟩ := OwnedBind.lower_costed body items
  rw [run.executes []]
  simpa using ((parent_costed body items).executes []).symm

theorem split_retains_parent_state (body : Entry → Option (List Entry)) (items : List Entry)
    (first rest : Nat) :
    advance (first + rest) ⟨lower body items, []⟩ =
      let earlier := advance first ⟨lower body items, []⟩
      let later := advance rest earlier.2
      (earlier.1 ++ later.1, later.2) := advance_add first rest _

theorem world_and_effects_continue_once {World : Type}
    (action : Event Entry → World → World)
    (body : Entry → Option (List Entry)) (items : List Entry)
    (world : World) (first rest : Nat) :
    Session.resume action (first + rest) (Session.begin (lower body items) world) =
      Session.resume action rest (Session.resume action first
        (Session.begin (lower body items) world)) := Session.resume_add action first rest _

namespace Controls

abbrev Item := Returned Nat Nat Nat Nat

def held : Item := (7, .conditional 9 42)
def next : Item := (8, .value .completed 10)
def rows : Item → Option (List Item) := fun item => some [item, item]

theorem pending_packet_lives_until_body_retirement :
    (advance 4 ⟨lower rows [held], []⟩).1 =
      [.pull held, .admit held, .publish held, .publish held] := rfl

theorem retirement_precedes_source_acceptance :
    (advance 6 ⟨lower rows [held], []⟩).1 =
      [.pull held, .admit held, .publish held, .publish held,
       .retireBody held, .accept held] := rfl

theorem refusal_is_not_logical_exhaustion :
    advance 2 ⟨lower (fun _ => none) [held, next], []⟩ =
      ([.pull held, .admit held], ⟨.done (.handoff held [next]), []⟩) := rfl

theorem entered_empty_body_has_no_publication :
    (advance 4 ⟨lower (fun _ => some []) [held], []⟩).1 =
      [.pull held, .admit held, .retireBody held, .accept held] := rfl

theorem raised_control_bypasses_body :
    let fault : Item := (7, .raised 99)
    (advance 3 ⟨lower (fun _ => none) [fault], []⟩).1 =
      [.pull fault, .publish fault, .accept fault] := rfl

end Controls
end Mettapedia.Machines.NativeParentFusion
