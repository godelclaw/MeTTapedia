import Mettapedia.OSLF.Syntax.RhoScopedParallelEvents
import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackConstructors
import Mettapedia.OSLF.Syntax.BindingEquationQuotientSubstitution

/-!
# Original scoped rho root instances and their complete constructor readouts

The communication continuation lives under a name binder and may also use
the ambient context. Its result substitutes the actual quoted payload in the
source equation quotient. Reflection retains the full process origin of the
quotation, rather than replacing it by one chosen body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedInstanceReadout

open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoEquationConstructorControls

/-- Substitute the received name while fixing every ambient variable. -/
def receiveRaw {context : Ctx sig} (name : Term sig context Srt.nm) :
    Sub sig (Srt.nm :: context) context := fun _ position =>
  match position with
  | .zero => name
  | .succ ambient => .var ambient

/-- The same substitution accepts an actual name class. -/
def receiveEnvironment {context : Ctx sig} (name : Name context) :
    BindingSubstitutionAlgebra.Environment sig (TermQ rhoSourceE)
      (Srt.nm :: context) context := fun _ position =>
  match position with
  | .zero => name
  | .succ ambient => project (.var ambient)

noncomputable def receive {context : Ctx sig} (name : Name context)
    (body : Process (Srt.nm :: context)) : Process context :=
  BindingEquationQuotientSubstitution.substitute rhoSourceE
    (receiveEnvironment name) body

theorem receive_project {context : Ctx sig} (name : Term sig context Srt.nm)
    (body : Term sig (Srt.nm :: context) Srt.pr) :
    receive (project name) (project body) = project (bind (receiveRaw name) body) := by
  unfold receive
  rw [BindingEquationQuotientSubstitution.substitute_eq_bindQ rhoSourceE _
    (receiveRaw name) (by intro sort position; cases position <;> rfl)]
  rfl

abbrev Communication (context : Ctx sig) :=
  ContextualRootEvents.Instance comm.unpositioned context

def Communication.channel {context : Ctx sig} (root : Communication context) :
    Term sig context Srt.nm := root.close _ .zero

def Communication.payload {context : Ctx sig} (root : Communication context) :
    Term sig context Srt.pr := root.close _ (.succ .zero)

def Communication.continuation {context : Ctx sig} (root : Communication context) :
    Term sig (Srt.nm :: context) Srt.pr := root.body 0

theorem Communication.source_readout {context : Ctx sig} (root : Communication context) :
    root.source = parallel (outputRaw root.channel root.payload)
      (inputRaw root.channel root.continuation) := by
  change parallel (outputRaw root.channel root.payload)
    (inputRaw root.channel (bind _ (root.body 0))) = _
  congr 2
  apply Eq.trans _ (bind_id _)
  congr 1
  funext sort position
  cases position <;> rfl

theorem Communication.target_readout {context : Ctx sig} (root : Communication context) :
    root.target = bind (receiveRaw (quoteRaw root.payload)) root.continuation := by
  change bind _ (root.body 0) = _
  congr 1
  funext sort position
  cases position with
  | zero => rfl
  | succ ambient => exact rename_id (.var ambient)

theorem Communication.source_class {context : Ctx sig} (root : Communication context) :
    project root.source = join (outputClass (project root.channel) (project root.payload))
      (inputClass (project root.channel) (project root.continuation)) := by
  rw [root.source_readout]
  rfl

theorem Communication.target_class {context : Ctx sig} (root : Communication context) :
    project root.target = receive (quote (project root.payload)) (project root.continuation) := by
  rw [quote_project, receive_project, root.target_readout]
  rfl

/-- Every sorted open continuation and pair of ordinary arguments supplies
an authored root instance. No quotation-sealing hypothesis is imposed. -/
def communication {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    Communication context where
  body := by intro index; have same : index = 0 := Fin.eq_zero index; cases same; exact body
  close := fun _ position => match position with
    | .zero => channel
    | .succ .zero => payload

theorem communication_channel {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    (communication channel payload body).channel = channel := rfl

theorem communication_payload {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    (communication channel payload body).payload = payload := rfl

theorem communication_continuation {context : Ctx sig} (channel : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) (body : Term sig (Srt.nm :: context) Srt.pr) :
    (communication channel payload body).continuation = body := rfl

abbrev Reflection (context : Ctx sig) :=
  ContextualRootEvents.Instance dropRule.unpositioned context

def Reflection.payload {context : Ctx sig} (root : Reflection context) :
    Term sig context Srt.pr := root.close _ .zero

theorem Reflection.source_readout {context : Ctx sig} (root : Reflection context) :
    root.source = dropRaw (quoteRaw root.payload) := rfl

theorem Reflection.target_readout {context : Ctx sig} (root : Reflection context) :
    root.target = root.payload := rfl

theorem Reflection.source_class {context : Ctx sig} (root : Reflection context) :
    project root.source = drop (quote (project root.payload)) := rfl

theorem Reflection.target_class {context : Ctx sig} (root : Reflection context) :
    project root.target = project root.payload := rfl

def reflection {context : Ctx sig} (payload : Term sig context Srt.pr)
    (unusedBody : Term sig (Srt.nm :: context) Srt.pr) : Reflection context where
  body := by intro index; have same : index = 0 := Fin.eq_zero index; cases same; exact unusedBody
  close := fun _ position => match position with
    | .zero => payload

end Mettapedia.OSLF.Binding.RhoScopedInstanceReadout
