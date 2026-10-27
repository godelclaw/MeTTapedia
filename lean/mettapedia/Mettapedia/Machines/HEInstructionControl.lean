import Mettapedia.Machines.ExecutionControl

/-!
# Environment staging for HE instruction operands

A chain's binder and template stay opaque while the producer receives the
environment. Function and collection bodies recurse through that staging;
force operands use ordinary substitution. The indexed implementation is
compared with independent source-list destructuring. This is an operand and
source-image law, not a complete HE evaluator or a native-pointer refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HEInstructionControl

open ExecutionControl

variable {Operand : Type}

def elaborate (head : Head) (arity : Nat) : Option Plan :=
  match head with
  | .chain | .function | .collect | .evaluate => ExecutionControl.elaborate head arity
  | _ => none

private def replace (fields : Array Operand) (position : Option Nat) (value : Operand) :
    Option (Array Operand) := do
  let index ← position
  if index < fields.size then
    return fields.mapIdx fun current old => if current == index then value else old
  else none

private def operand (fields : Array Operand) (position : Option Nat) : Option Operand :=
  position.bind (fields[·]?)

def applyPlan (nested plain : Operand → Operand) (isVariable : Operand → Bool)
    (plan : Plan) (fields : Array Operand) : Option (Array Operand) := do
  let source ← operand fields plan.source
  match plan.operation with
  | .sequence =>
      let binder ← operand fields plan.first
      let _ ← operand fields plan.last
      if isVariable binder then replace fields plan.source (nested source)
      else return fields.map plain
  | .returnScope | .collect => replace fields plan.source (nested source)
  | .force => return fields.map plain
  | _ => none

def reference (nested plain : Operand → Operand) (isVariable : Operand → Bool) :
    Head → List Operand → Option (List Operand)
  | .chain, [producer, binder, body] =>
      if isVariable binder then some [nested producer, binder, body]
      else some [plain producer, plain binder, plain body]
  | .function, [body] | .collect, [body] => some [nested body]
  | .evaluate, [body] => some [plain body]
  | _, _ => none

theorem environment_layout_refines (nested plain : Operand → Operand)
    (isVariable : Operand → Bool) (head : Head) (fields : List Operand) :
    (elaborate head fields.length).bind
        (fun plan => applyPlan nested plain isVariable plan fields.toArray) =
      (reference nested plain isVariable head fields).map List.toArray := by
  cases fields with
  | nil => cases head <;> simp [elaborate, ExecutionControl.elaborate, applyPlan, reference, replace, operand]
  | cons first rest =>
      cases rest with
      | nil => cases head <;> simp [elaborate, ExecutionControl.elaborate, applyPlan, reference, replace, operand]
      | cons second rest =>
          cases rest with
          | nil => cases head <;> simp [elaborate, ExecutionControl.elaborate, applyPlan, reference, replace, operand]
          | cons third rest =>
              cases rest with
              | nil =>
                  cases head <;> try rfl
                  cases chosen : isVariable second <;>
                    simp [elaborate, ExecutionControl.elaborate, applyPlan, reference, replace, operand, chosen]
              | cons fourth tail => cases head <;> rfl

theorem normalized_chain_preserves_binder_template (nested plain : Operand → Operand)
    (isVariable : Operand → Bool) (producer binder body : Operand)
    (binderIsVariable : isVariable binder = true) :
    applyPlan nested plain isVariable ⟨.sequence, some 2, some 0, some 1⟩
      #[binder, body, producer] = some #[binder, body, nested producer] := by
  change (if isVariable binder then
    replace #[binder, body, producer] (some 2) (nested producer)
    else some (#[binder, body, producer].map plain)) = _
  simp [binderIsVariable, replace]

theorem source_chain_preserves_binder_template (nested plain : Operand → Operand)
    (isVariable : Operand → Bool) (producer binder body : Operand)
    (binderIsVariable : isVariable binder = true) :
    (elaborate .chain 3).bind
        (fun plan => applyPlan nested plain isVariable plan #[producer, binder, body]) =
      some #[nested producer, binder, body] := by
  simpa [reference, binderIsVariable] using
    environment_layout_refines nested plain isVariable .chain [producer, binder, body]

/-- The source image has its own environment transformation. Relocating the
operand array cannot replace it with the physical instruction carrier. -/
structure Frame (Syntax Operand : Type) where
  sourceImage : Syntax
  plan : Plan
  operands : Array Operand

def applyFrame {Syntax : Type} (source : Syntax → Syntax)
    (nested plain : Operand → Operand) (isVariable : Operand → Bool)
    (frame : Frame Syntax Operand) : Option (Frame Syntax Operand) := do
  let fields ← applyPlan nested plain isVariable frame.plan frame.operands
  return {frame with sourceImage := source frame.sourceImage, operands := fields}

theorem source_image_retained {Syntax : Type} (source : Syntax → Syntax)
    (nested plain : Operand → Operand) (isVariable : Operand → Bool)
    (before after : Frame Syntax Operand)
    (applied : applyFrame source nested plain isVariable before = some after) :
    after.sourceImage = source before.sourceImage ∧ after.plan = before.plan := by
  unfold applyFrame at applied
  cases mapped : applyPlan nested plain isVariable before.plan before.operands with
  | none => simp [mapped] at applied
  | some fields =>
      rw [mapped] at applied
      change some (Frame.mk (source before.sourceImage) before.plan fields) =
        some after at applied
      cases Option.some.inj applied
      exact ⟨rfl, rfl⟩

theorem ordinary_mapping_crosses_binder_boundary :
    applyPlan (· + 10) (· + 100) (· == 1)
        ⟨.sequence, some 0, some 1, some 2⟩ #[5, 1, 1] ≠
      some (#[5, 1, 1].map (· + 100)) := by
  decide +kernel

theorem normalized_control_is_not_wrapper_layout :
    applyPlan (· + 10) (· + 100) (· == 1)
        ⟨.sequence, some 2, some 0, some 1⟩ #[1, 1, 5] ≠
      applyPlan (· + 10) (· + 100) (· == 1)
        ⟨.sequence, some 0, some 1, some 2⟩ #[1, 1, 5] := by
  decide +kernel

end Mettapedia.Machines.HEInstructionControl

#print axioms Mettapedia.Machines.HEInstructionControl.environment_layout_refines
#print axioms Mettapedia.Machines.HEInstructionControl.normalized_chain_preserves_binder_template
#print axioms Mettapedia.Machines.HEInstructionControl.source_chain_preserves_binder_template
#print axioms Mettapedia.Machines.HEInstructionControl.source_image_retained
#print axioms Mettapedia.Machines.HEInstructionControl.ordinary_mapping_crosses_binder_boundary
#print axioms Mettapedia.Machines.HEInstructionControl.normalized_control_is_not_wrapper_layout
