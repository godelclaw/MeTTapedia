import Mettapedia.OSLF.Syntax.RhoScopedConstructorInventory

/-!
# Complete dependent endpoint readings of the original rho rules

A communication reading retains the name, payload and bound continuation
classes. A reflection reading retains the particular process origin of the
quotation. Each reading is realized by an original contextual root instance,
and every original instance has these independently constructed endpoints.
The original receipt remains separate from this endpoint reading.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedReactionReadout

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoIntrinsicReadback RhoScopedInstanceReadout RhoScopedParallelEvents

inductive Reading (context : Ctx sig) where
  | communication (channel : Name context) (payload : Process context)
      (continuation : Process (Srt.nm :: context))
  | reflection (payload : Process context)

def Reading.rule {context : Ctx sig} : Reading context → SourceRule
  | .communication _ _ _ => .communication
  | .reflection _ => .reflection

def Reading.source {context : Ctx sig} : Reading context → Process context
  | .communication channel payload continuation =>
      join (outputClass channel payload) (inputClass channel continuation)
  | .reflection payload => drop (quote payload)

noncomputable def Reading.target {context : Ctx sig} : Reading context → Process context
  | .communication _ payload continuation => receive (quote payload) continuation
  | .reflection payload => payload

/-- Actual supplied assignments are read, not reconstructed from endpoints. -/
def rootReading {context : Ctx sig} {admitted : SourceRule → Prop} :
    Root sourceRules admitted context → Reading context
  | ⟨⟨.communication, _⟩, root⟩ => .communication
      (project (Communication.channel root)) (project (Communication.payload root))
      (project (Communication.continuation root))
  | ⟨⟨.reflection, _⟩, root⟩ => .reflection (project (Reflection.payload root))

theorem rootReading_rule {context : Ctx sig} {admitted : SourceRule → Prop}
    (root : Root sourceRules admitted context) : (rootReading root).rule = root.1.val := by
  rcases root with ⟨⟨index, allowed⟩, root⟩
  cases index <;> rfl

theorem rootReading_source {context : Ctx sig} {admitted : SourceRule → Prop}
    (root : Root sourceRules admitted context) : (rootReading root).source = root.source := by
  rcases root with ⟨⟨index, allowed⟩, root⟩
  cases index with
  | communication => exact Communication.source_class root |>.symm
  | reflection => exact Reflection.source_class root |>.symm

theorem rootReading_target {context : Ctx sig} {admitted : SourceRule → Prop}
    (root : Root sourceRules admitted context) : (rootReading root).target = root.target := by
  rcases root with ⟨⟨index, allowed⟩, root⟩
  cases index with
  | communication => exact Communication.target_class root |>.symm
  | reflection => rfl

noncomputable def realize {context : Ctx sig} (admitted : SourceRule → Prop)
    (reading : Reading context) (allowed : admitted reading.rule) :
    Root sourceRules admitted context := match reading with
  | .communication channel payload continuation =>
      ⟨⟨.communication, allowed⟩,
        RhoScopedInstanceReadout.communication (Quotient.out channel)
          (Quotient.out payload) (Quotient.out continuation)⟩
  | .reflection payload =>
      ⟨⟨.reflection, allowed⟩,
        RhoScopedInstanceReadout.reflection (Quotient.out payload) null⟩

theorem rootReading_realize {context : Ctx sig} (admitted : SourceRule → Prop)
    (reading : Reading context) (allowed : admitted reading.rule) :
    rootReading (realize admitted reading allowed) = reading := by
  cases reading with
  | communication channel payload continuation =>
      change Reading.communication (project (Quotient.out channel))
        (project (Quotient.out payload)) (project (Quotient.out continuation)) = _
      simp only [project, Quotient.out_eq]
  | reflection payload =>
      change Reading.reflection (project (Quotient.out payload)) = _
      simp only [project, Quotient.out_eq]

theorem realize_source {context : Ctx sig} (admitted : SourceRule → Prop)
    (reading : Reading context) (allowed : admitted reading.rule) :
    (realize admitted reading allowed).source = reading.source := by
  rw [← rootReading_source, rootReading_realize]

theorem realize_target {context : Ctx sig} (admitted : SourceRule → Prop)
    (reading : Reading context) (allowed : admitted reading.rule) :
    (realize admitted reading allowed).target = reading.target := by
  rw [← rootReading_target, rootReading_realize]

/-- The fibre stores the complete authored root, including its unused data. -/
def Receipt {context : Ctx sig} (admitted : SourceRule → Prop) (reading : Reading context) :=
  {root : Root sourceRules admitted context // rootReading root = reading}

theorem admitted_receipt_inhabited {context : Ctx sig} (admitted : SourceRule → Prop)
    (reading : Reading context) (allowed : admitted reading.rule) :
    Nonempty (Receipt admitted reading) :=
  ⟨⟨realize admitted reading allowed, rootReading_realize admitted reading allowed⟩⟩

end Mettapedia.OSLF.Binding.RhoScopedReactionReadout
