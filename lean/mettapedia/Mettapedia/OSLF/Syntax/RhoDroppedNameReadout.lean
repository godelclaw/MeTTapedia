import Mettapedia.OSLF.Syntax.RhoFiniteQuotationOrigins

/-!
# Exact optional readout of a dropped source name class

The source equations do not identify drop followed by quotation with process
evaluation. Canonical readback therefore supplies the unique child of an
actual dropped name, with both directions proved on the full intrinsic source
quotient. This positive constructor readout is separate from future-stable
negation of constructor availability.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoDroppedNameReadout

open RhoSchema RhoQuotationClassFibres RhoCanonicalNamePairs RhoIntrinsicReadback
open RhoSchema.IntrinsicEncoding RhoFiniteQuotationOrigins

def child? {context : Ctx sig} (process : Process context) : Option (Name context) :=
  (dropBody (encodeEquationClass process)).bind (readNameClass context)

theorem child_sound {context : Ctx sig} {process : Process context} {name : Name context}
    (readout : child? process = some name) : drop name = process := by
  obtain ⟨pattern, shape, decoded⟩ := Option.bind_eq_some_iff.mp readout
  have processReadout := read_encoded_equation_class process
  change readProcessClass context (encodeEquationClass process) = some process at processReadout
  rw [dropBody_shape shape, readProcessClass_drop, decoded] at processReadout
  exact Option.some.inj processReadout

theorem child_drop {context : Ctx sig} (name : Name context) : child? (drop name) = some name := by
  unfold child?
  rw [encode_drop]
  change readNameClass context (encodeEquationClass name) = some name
  exact read_encoded_equation_class name

theorem child_iff {context : Ctx sig} (process : Process context) (name : Name context) :
    child? process = some name ↔ drop name = process := by
  constructor
  · exact child_sound
  · rintro rfl
    exact child_drop name

theorem drop_injective (context : Ctx sig) : Function.Injective (drop (context := context)) := by
  intro first second same
  exact Option.some.inj ((child_drop first).symm.trans
    ((congrArg child? same).trans (child_drop second)))

end Mettapedia.OSLF.Binding.RhoDroppedNameReadout
