import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveProgress
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies

/-!
# Source and independent-specification join for retained raw arguments

For arbitrary syntax, bindings, pending continuations and prior observations,
the first-success recursive controller constructs a finite silent path from a
raw argument request to its exact packet. The path retains every surrounding
continuation and does not re-evaluate selected heads. The source evaluator and
the independent argument judgment both produce that same ordered packet.

The common machine run theorem realizes these paths at arbitrary later
budgets. Encoded execution inherits the result through the constructed
representation stage. Raw error-shaped values remain data in the packet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessRawExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev SilentPath (dispatch : GroundedDispatch) :=
  Relation.ReflTransGen (machine dispatch).reading.silent

theorem enter_request (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (stack : List Frame) (emitted : ResultSet) :
    SilentPath dispatch ⟨space, .work task, stack, emitted⟩
      ⟨space, (FirstSuccessRecursiveStrategy.enter space dispatch task).1,
        (FirstSuccessRecursiveStrategy.enter space dispatch task).2 ++ stack, emitted⟩ :=
  Relation.ReflTransGen.single rfl

theorem consume_continuation (space : Space) (dispatch : GroundedDispatch)
    (frame : Frame) (results : ResultSet) (stack : List Frame) (emitted : ResultSet) :
    SilentPath dispatch ⟨space, .returning results, frame :: stack, emitted⟩
      ⟨space, (RecursiveMachine.resume space frame results).1,
        (RecursiveMachine.resume space frame results).2 ++ stack, emitted⟩ :=
  Relation.ReflTransGen.single rfl

theorem raw_atom (space : Space) (dispatch : GroundedDispatch) (value : Atom)
    (bindings : Bindings) (fuel : Nat) (stack : List Frame) (emitted : ResultSet) :
    SilentPath dispatch ⟨space, .work (.atom value Atom.atomType bindings (fuel + 1)), stack, emitted⟩
      ⟨space, .returning [(value, bindings)], stack, emitted⟩ := by
  have expanded : FirstSuccessRecursiveStrategy.enter space dispatch
      (.atom value Atom.atomType bindings (fuel + 1)) = (.returning [(value, bindings)], []) := by
    by_cases failed : isEmptyOrError value = true
    · simp [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, failed]
    · have clean : isEmptyOrError value = false := by
        cases found : isEmptyOrError value <;> simp_all
      simp [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, clean]
  simpa only [expanded, List.nil_append] using
    enter_request space dispatch (.atom value Atom.atomType bindings (fuel + 1)) stack emitted

/-- Arbitrary raw argument lists are replayed under their retained surrounding
stack. Each original head is used once and survives raw error/quotation data. -/
theorem raw_arguments (space : Space) (dispatch : GroundedDispatch) (values : List Atom)
    (bindings : Bindings) (fuel : Nat) (enough : values.length < fuel)
    (stack : List Frame) (emitted : ResultSet) :
    SilentPath dispatch
      ⟨space, .work (.args values (List.replicate values.length Atom.atomType) bindings fuel),
        stack, emitted⟩
      ⟨space, .returning [(argumentPacket values, bindings)], stack, emitted⟩ := by
  induction values generalizing fuel stack with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
            List.length_nil, List.replicate_zero, List.nil_append] using
            enter_request space dispatch (.args [] [] bindings (fuel + 1)) stack emitted
  | cons value values ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              have tailEnough : values.length < fuel + 1 := by
                simp only [List.length_cons] at enough
                omega
              let pending := Frame.append
                (.argumentHeads value values (List.replicate values.length Atom.atomType)
                  (fuel + 1) [])
              have first : SilentPath dispatch
                  ⟨space, .work (.args (value :: values)
                    (List.replicate (value :: values).length Atom.atomType)
                    bindings (fuel + 1 + 1)), stack, emitted⟩
                  ⟨space, .work (.atom value Atom.atomType bindings (fuel + 1)),
                    .argumentHeads value values (List.replicate values.length Atom.atomType)
                      (fuel + 1) :: stack, emitted⟩ := by
                simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
                  List.length_cons, List.replicate_succ, List.cons_append, List.nil_append] using
                  enter_request space dispatch (.args (value :: values)
                    (List.replicate (value :: values).length Atom.atomType)
                    bindings (fuel + 1 + 1)) stack emitted
              have second := raw_atom space dispatch value bindings fuel
                (.argumentHeads value values (List.replicate values.length Atom.atomType)
                  (fuel + 1) :: stack) emitted
              have third := consume_continuation space dispatch
                (.argumentHeads value values (List.replicate values.length Atom.atomType) (fuel + 1))
                [(value, bindings)] stack emitted
              have fourth : SilentPath dispatch
                  ⟨space, .work (.argumentHeads value values
                    (List.replicate values.length Atom.atomType) (fuel + 1) [(value, bindings)]),
                    stack, emitted⟩
                  ⟨space, .work (.args values (List.replicate values.length Atom.atomType)
                    bindings (fuel + 1)), .argumentTail value :: pending :: stack, emitted⟩ := by
                simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
                  bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false,
                  List.cons_append, List.nil_append] using
                  enter_request space dispatch (.argumentHeads value values
                    (List.replicate values.length Atom.atomType) (fuel + 1) [(value, bindings)])
                    stack emitted
              have tail := ih (fuel + 1) tailEnough (.argumentTail value :: pending :: stack)
              have fifth : SilentPath dispatch
                  ⟨space, .returning [(argumentPacket values, bindings)],
                    .argumentTail value :: pending :: stack, emitted⟩
                  ⟨space, .returning [(argumentPacket (value :: values), bindings)],
                    pending :: stack, emitted⟩ := by
                simpa [RecursiveMachine.resume, RecursiveTasks.argumentTail] using
                  consume_continuation space dispatch (.argumentTail value)
                    [(argumentPacket values, bindings)] (pending :: stack) emitted
              have sixth := consume_continuation space dispatch pending
                [(argumentPacket (value :: values), bindings)] stack emitted
              have seventh := enter_request space dispatch
                (.argumentHeads value values (List.replicate values.length Atom.atomType)
                  (fuel + 1) [])
                (.prepend [(argumentPacket (value :: values), bindings)] :: stack) emitted
              have eighth := consume_continuation space dispatch
                (.prepend [(argumentPacket (value :: values), bindings)]) [] stack emitted
              exact first.trans (second.trans (by
                simpa only [RecursiveMachine.resume, List.nil_append] using third.trans
                  (fourth.trans (tail.trans (fifth.trans (by
                    simpa only [pending, RecursiveMachine.resume, List.cons_append, List.nil_append,
                      FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.append_nil]
                      using sixth.trans (seventh.trans eighth)))))))

/-- The same packet is computed by separate source and machine procedures,
and earned by the independent specification. The saved continuation is data. -/
theorem source_specification_join (space : Space) (source : GroundedDispatch)
    (semantic : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : Spec.Eval.EvalTypeService) (values : List Atom) (bindings : Bindings)
    (fuel : Nat) (enough : values.length < fuel) (stack : List Frame) (emitted : ResultSet) :
    (interpretArgs space source values (List.replicate values.length Atom.atomType)
      bindings fuel = [(argumentPacket values, bindings)]) ∧
    Spec.Eval.InterpretArgsRel space semantic live (typing := typing)
      values (List.replicate values.length Atom.atomType)
      bindings (argumentPacket values, bindings) ∧
    ∃ budget, ∀ later, (machine source).run (budget + later)
      ⟨space, .work (.args values (List.replicate values.length Atom.atomType) bindings fuel),
        stack, emitted⟩ =
      (machine source).run later
        ⟨space, .returning [(argumentPacket values, bindings)], stack, emitted⟩ := by
  refine ⟨interpretArgs_raw space source values bindings fuel enough, ?_, ?_⟩
  · exact (FirstSuccessSourceReplies.source_raw_arguments_iff space source semantic live typing
      values bindings fuel enough _).mp (by rw [interpretArgs_raw space source values bindings fuel enough]; simp)
  · exact (machine source).silent_run (raw_arguments space source values bindings fuel enough stack emitted)

/-- Completion publishes the packet once and retains all prior observations
in the complete verdict. Inspection of raw syntax commits no effects. -/
theorem completed_raw_arguments (space : Space) (source : GroundedDispatch)
    (values : List Atom) (bindings : Bindings) (fuel : Nat)
    (enough : values.length < fuel) (emitted : ResultSet) :
    ∃ administrative, ∀ later,
      (machine source).run (administrative + 2 + later)
        ⟨space, .work (.args values (List.replicate values.length Atom.atomType) bindings fuel),
          [], emitted⟩ =
      ([(argumentPacket values, bindings)], .finished
        ⟨space, .returning [], [], emitted ++ [(argumentPacket values, bindings)]⟩) := by
  obtain ⟨administrative, realized⟩ := (machine source).silent_run
    (raw_arguments space source values bindings fuel enough [] emitted)
  refine ⟨administrative, fun later => ?_⟩
  rw [show administrative + 2 + later = administrative + (later + 1 + 1) by omega,
    realized (later + 1 + 1)]
  simp only [Machine.run, machine, next, List.singleton_append]

/-- The encoded interface finishes with the independently computed packet
and its complete retained verdict at the same finite budget. -/
theorem represented_completed_raw_arguments (space : Space) (source : GroundedDispatch)
    (values : List Atom) (bindings : Bindings) (fuel : Nat)
    (enough : values.length < fuel) (emitted : ResultSet) :
    ∃ administrative, ∀ later,
      (dataMachine source).run (administrative + 2 + later)
        (RecursiveEncoding.configurationData
          ⟨space, .work (.args values (List.replicate values.length Atom.atomType) bindings fuel),
            [], emitted⟩) =
      ([(argumentPacket values, bindings)], .finished
        ⟨space, .returning [], [], emitted ++ [(argumentPacket values, bindings)]⟩) := by
  obtain ⟨administrative, completed⟩ := completed_raw_arguments space source values bindings fuel enough emitted
  refine ⟨administrative, fun later => ?_⟩
  rw [run_representation, completed later]
  rfl

end Mettapedia.Languages.MeTTa.HE.FirstSuccessRawExecution
