import Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterTypes

/-!
# Ordered native parameter headers from authored scoped slots

Each parameter retains its declared name, local dependencies and result sort.
The carrier decoder and the slot decoder both run on the supplied declaration.
Their equations are retained with the generated header.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeModalParameters

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open NativeSignature Modal.NativeEventParameters Modal.NativeScopedParameterTypes

variable {plan : Plan} (schema : Modal.Rules.Schema plan)

structure Parameter where
  slot : Slot schema
  carrier : Carrier plan.snapshot.language
  decoded : decodeSlot? slot = some carrier

def decode? (name : String) : Option (Parameter schema) :=
  match slot? schema name with
  | none => none
  | some slot => match decoded : decodeSlot? slot with
    | none => none
    | some carrier => some ⟨slot, carrier, decoded⟩

def decodeAll? (names : List String) : Option (List (Parameter schema)) :=
  decodeList (decode? schema) names

theorem decode_name {name : String} {parameter : Parameter schema}
    (decoded : decode? schema name = some parameter) : parameter.slot.name = name := by
  cases slot : slot? schema name with
  | none => simp [decode?, slot] at decoded
  | some actual =>
      unfold decode? at decoded
      simp only [slot] at decoded
      split at decoded
      · cases decoded
      · cases Option.some.inj decoded
        exact slot?_name slot

theorem decodeAll_names {names : List String} {parameters : List (Parameter schema)}
    (decoded : decodeAll? schema names = some parameters) :
    parameters.map (fun parameter => parameter.slot.name) = names := by
  have ordered := decodeList_sound decoded
  clear decoded
  induction ordered with
  | nil => rfl
  | cons first _ ih => simp only [List.map_cons, decode_name schema first, ih]

theorem source (parameter : Parameter schema) :
    parameter.carrier.source = authoredType parameter.slot := decodeSlot?_sound parameter.decoded

theorem decode_complete (name : String) (slot : Slot schema)
    (found : slot? schema name = some slot) (admitted : Admitted slot) :
    ∃ parameter, decode? schema name = some parameter := by
  obtain ⟨carrier, decoded⟩ := decodeSlot?_complete admitted
  unfold decode?
  simp only [found]
  split
  · rename_i rejected
    rw [decoded] at rejected
    cases rejected
  · exact ⟨_, rfl⟩

end Mettapedia.OSLF.NativeTypes.Generation.NativeModalParameters
