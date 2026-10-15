import Mettapedia.OSLF.Syntax.RhoScopedEquationEventControls

/-!+# An equation-compatible input inventory for the authored rho profile

Every communication requires an input occurrence as well as an output.
The complete source equations preserve this inventory beneath all declared
binders. Its zero value therefore excludes communication on the actual
equation classes, without choosing representatives or restricting which
equation derivations can be used.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceInputInventory

open RhoSchema ScopedEncoding ScopedEquationEvents RhoScopedEquationEventControls

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def inputHeadCount {sort : Srt} : Op sort → Nat
  | .inp => 1
  | _ => 0

mutual
def inputCount : {context : Ctx sig} → {sort : Srt} → Term sig context sort → Nat
  | _, _, .var _ => 0
  | _, _, .op operator arguments => inputHeadCount operator + inputCountArgs arguments

def inputCountArgs : {context : Ctx sig} → {arity : List (List Srt × Srt)} →
    Args sig arity context → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => inputCount head + inputCountArgs tail
end

theorem inputCount_source_equation : ∀ (index : Fin rhoSourceE.length) {ambient target : Ctx sig}
    (body : ContextualAssignment sig metas ambient) (change : Sub sig ambient target)
    (close : Sub sig (rhoSourceE.get index).ctx target),
    inputCount (ContextualAssignment.instantiate body change close (rhoSourceE.get index).lhs) =
      inputCount (ContextualAssignment.instantiate body change close (rhoSourceE.get index).rhs)
  | ⟨0, _⟩, _, _, body, change, close => by
    show inputCount (ContextualAssignment.instantiate body change close commPar.lhs) =
      inputCount (ContextualAssignment.instantiate body change close commPar.rhs)
    simp only [commPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
      liftSub, inputCount, inputCountArgs, inputHeadCount]
    omega
  | ⟨1, _⟩, _, _, body, change, close => by
    show inputCount (ContextualAssignment.instantiate body change close assocPar.lhs) =
      inputCount (ContextualAssignment.instantiate body change close assocPar.rhs)
    simp only [assocPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
      liftSub, inputCount, inputCountArgs, inputHeadCount]
    omega
  | ⟨2, _⟩, _, _, body, change, close => by
    show inputCount (ContextualAssignment.instantiate body change close rightUnitPar.lhs) =
      inputCount (ContextualAssignment.instantiate body change close rightUnitPar.rhs)
    simp only [rightUnitPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
      liftSub, inputCount, inputCountArgs, inputHeadCount]
    omega
  | ⟨3, _⟩, _, _, body, change, close => by
    show inputCount (ContextualAssignment.instantiate body change close quoteDrop.lhs) =
      inputCount (ContextualAssignment.instantiate body change close quoteDrop.rhs)
    simp only [quoteDrop, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
      liftSub, inputCount, inputCountArgs, inputHeadCount]
    omega
  | ⟨_ + 4, bound⟩, _, _, _, _, _ => by simp [rhoSourceE] at bound

mutual
theorem inputCount_congruence : ∀ {context : Ctx sig} {sort : Srt}
    {first second : Term sig context sort}, EqClosure rhoSourceE first second →
      inputCount first = inputCount second
  | _, _, _, _, .ax index body change close => inputCount_source_equation index body change close
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm related => (inputCount_congruence related).symm
  | _, _, _, _, .trans first second =>
    (inputCount_congruence first).trans (inputCount_congruence second)
  | _, _, _, _, .cong _ related => by
    simp only [inputCount, inputCountArgs_congruence related]

theorem inputCountArgs_congruence : ∀ {context : Ctx sig} {arity : List (List Srt × Srt)}
    {first second : Args sig arity context}, EqArgs rhoSourceE first second →
      inputCountArgs first = inputCountArgs second
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
    simp only [inputCountArgs, inputCount_congruence head, inputCountArgs_congruence tail]
end

def count {context : Ctx sig} {sort : Srt} : TermQ rhoSourceE context sort → Nat :=
  Quotient.lift inputCount (fun _ _ related => inputCount_congruence related)

theorem count_mk {context : Ctx sig} {sort : Srt} (term : Term sig context sort) :
    count (Quotient.mk _ term : TermQ rhoSourceE context sort) = inputCount term := rfl

theorem root_source_has_input {context : Ctx sig}
    (root : ContextualRootEvents.Instance comm.unpositioned context) :
    0 < inputCount root.source := by
  change 0 < inputCount (ContextualAssignment.instantiate root.body
    (fun _ position => .var position) root.close commLhs)
  simp only [commLhs, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    liftSub, inputCount, inputCountArgs, inputHeadCount]
  omega

theorem frame_retains_input {source target : Scope sig} (frame : BindingFrame sig source target)
    (value : Term sig source.1 source.2) :
    inputCount value ≤ inputCount (frame.fill value) := by
  cases frame with
  | slot context sort operator position siblings =>
    cases operator <;> fin_cases position <;>
      simp [BindingFrame.fill, assembleArguments, inputCount, inputCountArgs, inputHeadCount] <;>
      omega

theorem context_retains_input {source target : Scope sig}
    (context : BindingContext sig source target) (value : Term sig source.1 source.2) :
    inputCount value ≤ inputCount (fillContext context value) := by
  induction context with
  | nil => exact Nat.le_refl _
  | cons previous frame inductionHypothesis =>
    exact inductionHypothesis.trans (frame_retains_input frame _)

theorem event_source_has_input {scope : Scope sig} (event : Event rules parallelPermission scope) :
    0 < count (event.sourceClass rhoSourceE) :=
  (root_source_has_input event.root).trans_le (context_retains_input event.context _)

end Mettapedia.OSLF.Binding.RhoSourceInputInventory
