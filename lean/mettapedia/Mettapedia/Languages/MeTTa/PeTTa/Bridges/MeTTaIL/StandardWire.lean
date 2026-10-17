import Mettapedia.OSLF.MeTTaIL.Complete.Normalized
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Declared laws as MeTTa data

`(CollectionLaw kind unit)` with unit `UNone` or `(USome label)`, `(Extrusion kind binder)`, and a
plan's standard-form data `(Standard laws extrusions)`, read by `gslt_collection_laws.metta` and
`gslt_runner.metta`. Shared by the bridges, the emitter and the controls generators.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws

/-- How a law's unit is written. -/
def unitTerm : Option String → Term
  | none => .symbol "UNone"
  | some label => .application "USome" [.string label]

def lawTerm (law : Laws) : Term :=
  .application "CollectionLaw" [encodeCollectionType law.kind, unitTerm law.unit]

def extrusionTerm (extrusion : Extrusion) : Term :=
  .application "Extrusion" [encodeCollectionType extrusion.kind, .string extrusion.binder]

/-- The standard-form data of a plan: its declared collection and scope-extrusion laws. -/
def standardTerm (plan : GeneralExecutionAdmission.Plan) : Term :=
  .application "Standard" [CettaWire.encodeList lawTerm (Complete.Normalized.laws plan),
    CettaWire.encodeList extrusionTerm (Complete.Normalized.extrusions plan)]

theorem encodeCollectionType_injective : Function.Injective encodeCollectionType := by
  intro first second same
  cases first <;> cases second <;> first | rfl | simp [encodeCollectionType] at same

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
