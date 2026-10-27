import Mettapedia.Machines.HEInstructionControl
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Planned HE instructions and the maintained minimal source judgment

Operand coordinates lower to a control entry without reading the physical
wrapper. The entry schedules the producer under its saved chain/function
source image. Child invocation, binding materialization and complete collection
are premises supplied by the maintained HE judgments, rather than redefined
leaf evaluators. The refinement covers force, chain, successful function
return and complete collection. Malformed instructions, profile-specific
NoReturn readback, native source debit and pointer safety are separate joins.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HEInstructionSource

open ExecutionControl
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space ResultSet)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval

inductive Entry where
  | force (operand : Atom)
  | sequence (producer : Atom) (name : String) (body : Atom)
  | returnScope (body : Atom)
  | collect (body : Atom)
  deriving DecidableEq

def Entry.sourceImage : Entry → Atom
  | .force operand => .expression [.symbol "eval", operand]
  | .sequence producer name body =>
      .expression [.symbol "chain", producer, .var name, body]
  | .returnScope body => .expression [.symbol "function", body]
  | .collect body => .expression [.symbol "collapse-bind", body]

private def operand (fields : Array Atom) (position : Option Nat) : Option Atom :=
  position.bind (fields[·]?)

def decode (plan : Plan) (fields : Array Atom) : Option Entry := do
  let source ← operand fields plan.source
  match plan.operation with
  | .force => return .force source
  | .sequence =>
      let .var name ← operand fields plan.first | none
      let body ← operand fields plan.last
      return .sequence source name body
  | .returnScope => return .returnScope source
  | .collect => return .collect source
  | _ => none

/-- Independent source-list admission; the chain destination must be a variable. -/
def reference : Head → List Atom → Option Entry
  | .evaluate, [body] => some (.force body)
  | .chain, [producer, .var name, body] => some (.sequence producer name body)
  | .function, [body] => some (.returnScope body)
  | .collect, [body] => some (.collect body)
  | _, _ => none

theorem elaboration_refines (head : Head) (fields : List Atom) :
    (HEInstructionControl.elaborate head fields.length).bind
      (fun plan => decode plan fields.toArray) = reference head fields := by
  cases fields with
  | nil => cases head <;> rfl
  | cons first rest =>
      cases rest with
      | nil => cases head <;> rfl
      | cons second rest =>
          cases rest with
          | nil => cases head <;> cases second <;> rfl
          | cons third rest =>
              cases rest with
              | nil => cases head <;> cases second <;> rfl
              | cons fourth tail => cases head <;> cases second <;> rfl

inductive Step (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (protectedScope : List String) (typing : EvalTypeService) (caller : Option Atom) :
    Entry → BindingFrame → FrameResult → Prop where
  | force (atom materialized : Atom) (bindings : BindingFrame) (result : FrameResult) :
      BindingFrame.Materialization bindings atom materialized →
      Minimal.CoreInvocationRel space dispatch live materialized bindings result
        (protectedScope := protectedScope) (typing := typing) (caller := caller) →
      Step space dispatch live protectedScope typing caller (.force atom) bindings result
  | sequence (producer : Atom) (name : String) (body materialized : Atom)
      (bindings : BindingFrame) (selected : FrameResult) :
      Minimal.CoreRunRel space dispatch
        ((Entry.sequence producer name body).sourceImage :: live)
        producer bindings selected (protectedScope := protectedScope) (typing := typing)
        (caller := some (Entry.sequence producer name body).sourceImage) →
      BindingFrame.Materialization selected.2 selected.1 materialized →
      Step space dispatch live protectedScope typing caller (.sequence producer name body)
        bindings (Minimal.substituteName name materialized body, selected.2)
  | returnScope (body returned : Atom) (bindings output : BindingFrame) :
      (∃ fields, body = .expression fields) →
      Minimal.CoreFunctionBodyRel space dispatch
        ((Entry.returnScope body).sourceImage :: live)
        body bindings (.expression [.symbol "return", returned], output)
        (protectedScope := protectedScope) (typing := typing)
        (caller := some (Entry.returnScope body).sourceImage) →
      Step space dispatch live protectedScope typing caller (.returnScope body)
        bindings (returned, output)
  | collect (body : Atom) (bindings : BindingFrame) (results : ResultSet)
      (services : Minimal.Services) (enumeration : Minimal.Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Historical bindings →
      enumeration.minimalResults space body bindings results →
      Step space dispatch live protectedScope typing caller (.collect body)
        bindings (Minimal.encodeResults services results, bindings)

theorem step_refines {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {protectedScope : List String} {typing : EvalTypeService} {caller : Option Atom}
    {entry : Entry} {bindings : BindingFrame} {result : FrameResult}
    (stepped : Step space dispatch live protectedScope typing caller entry bindings result) :
    Minimal.CoreStepRel space dispatch live entry.sourceImage bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller) := by
  cases stepped with
  | force atom materialized bindings result materialization invoked =>
      exact .eval space atom materialized bindings result materialization invoked
  | sequence producer name body materialized bindings selected ran materialization =>
      exact .chain space producer name body bindings selected materialized ran materialization
  | returnScope body returned bindings output expression ran =>
      exact .functionReturn space body returned bindings output expression ran
  | collect body bindings results services enumeration available historical complete =>
      exact .collapseBind space body bindings results services enumeration available historical complete

/-- The storage carrier can be unrelated syntax. The retained source image is
read back from the admitted operands, and the child relations retain that image. -/
theorem retained_image_refines {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {protectedScope : List String} {typing : EvalTypeService} {caller : Option Atom}
    {plan : Plan} {fields : Array Atom} {entry : Entry} {sourceImage : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (decoded : decode plan fields = some entry)
    (image : entry.sourceImage = sourceImage)
    (stepped : Step space dispatch live protectedScope typing caller entry bindings result) :
    ∃ admitted, decode plan fields = some admitted ∧
      Minimal.CoreStepRel space dispatch live sourceImage bindings result
        (protectedScope := protectedScope) (typing := typing) (caller := caller) := by
  exact ⟨entry, decoded, image ▸ step_refines stepped⟩

theorem normalized_sequence_reads_relocated_operands (producer body : Atom) (name : String) :
    decode ⟨.sequence, some 2, some 0, some 1⟩ #[.var name, body, producer] =
      some (.sequence producer name body) := rfl

theorem nonvariable_destination_declines (producer body : Atom) :
    decode ⟨.sequence, some 2, some 0, some 1⟩ #[.symbol "destination", body, producer] =
      none := rfl

theorem distinct_force_and_scope (body : Atom) :
    decode ⟨.force, some 0, none, none⟩ #[body] ≠
      decode ⟨.returnScope, some 0, none, none⟩ #[body] := by
  simp [decode, operand]

end Mettapedia.Machines.HEInstructionSource

#print axioms Mettapedia.Machines.HEInstructionSource.elaboration_refines
#print axioms Mettapedia.Machines.HEInstructionSource.step_refines
#print axioms Mettapedia.Machines.HEInstructionSource.retained_image_refines
#print axioms Mettapedia.Machines.HEInstructionSource.normalized_sequence_reads_relocated_operands
#print axioms Mettapedia.Machines.HEInstructionSource.nonvariable_destination_declines
#print axioms Mettapedia.Machines.HEInstructionSource.distinct_force_and_scope
