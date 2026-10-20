import Mettapedia.OSLF.MeTTaIL.Complete.Normalized
import Mettapedia.OSLF.MeTTaIL.CanonicalTable
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesChecked
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Declared laws as MeTTa data

`(CollectionLaw kind unit)` with unit `UNone` or `(USome label)`, `(Extrusion kind binder)`, and
what a run commits targets with: the standard form `(Standard laws extrusions)`, the canonical
form `(Canonical laws extrusions table)` sorted by a name table, the canonical form of the
quote-drop normal form `(Reflective quote drop laws extrusions table)`, or the canonical form of the model
normal form `(Model quote drop laws extrusions table)`, read by `gslt_collection_laws.metta`,
`gslt_canonical.metta` and `gslt_runner.metta`. Shared by the bridges, the emitter and the controls
generators.

`planTable` lists a plan's constructors, the units of its declared laws and its declared free names
(`planTable_for`), which cover every well-sorted state of the plan and every model normal form of one.
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

/-- The canonical-form data of a plan: its declared laws and a name table. -/
def canonicalTerm (plan : GeneralExecutionAdmission.Plan) (table : List String) : Term :=
  .application "Canonical" [CettaWire.encodeList lawTerm (Complete.Normalized.laws plan),
    CettaWire.encodeList extrusionTerm (Complete.Normalized.extrusions plan), CettaWire.encodeList Term.string table]

/-- The data of the canonical form of the quote-drop normal form: the presentation's quote and drop
constructors, the plan's declared laws and a name table. -/
def reflectiveTerm (plan : GeneralExecutionAdmission.Plan) (declaration : ReflectivePresentationDecl)
    (table : List String) : Term :=
  .application "Reflective" [.string declaration.quoteConstructor, .string declaration.dropConstructor,
    CettaWire.encodeList lawTerm (Complete.Normalized.laws plan),
    CettaWire.encodeList extrusionTerm (Complete.Normalized.extrusions plan), CettaWire.encodeList Term.string table]

/-- The data of the canonical form of the model normal form: the presentation's quote and drop
constructors, the plan's declared laws and a name table. -/
def modelTerm (plan : GeneralExecutionAdmission.Plan) (declaration : ReflectivePresentationDecl)
    (table : List String) : Term :=
  .application "Model" [.string declaration.quoteConstructor, .string declaration.dropConstructor,
    CettaWire.encodeList lawTerm (Complete.Normalized.laws plan),
    CettaWire.encodeList extrusionTerm (Complete.Normalized.extrusions plan), CettaWire.encodeList Term.string table]

/-- What a run commits targets with. -/
def commitTerm (plan : GeneralExecutionAdmission.Plan) : Complete.Normalized.Commit → List String → Term
  | .standard, _ => standardTerm plan
  | .canonical, table => canonicalTerm plan table
  | .reflective declaration, table => reflectiveTerm plan declaration table
  | .model declaration, table => modelTerm plan declaration table

/-- A name table of a plan: in the order of serializations, holding its constructors, the units of its
declared laws and its declared free names. -/
structure TableFor (plan : GeneralExecutionAdmission.Plan) (table : List String) : Prop where
  ordered : CanonicalCompare.NameOrdered table
  constructors : ∀ rule ∈ (GeneralPlanEnvironment.environment plan).language.terms, rule.label ∈ table
  units : ∀ law ∈ Complete.Normalized.laws plan, ∀ label, law.unit = some label → label ∈ table
  declared : ∀ name type, plan.snapshot.free name = some type → name ∈ table

/-- A plan's constructors, the units of its declared laws and the given free names, once each in the
order of their serializations. -/
def planTable (plan : GeneralExecutionAdmission.Plan) (free : List String) : List String :=
  CanonicalCompare.nameTable (CanonicalCompare.labels (GeneralPlanEnvironment.environment plan).language ++
    (Complete.Normalized.laws plan).filterMap (·.unit) ++ free)

theorem planTable_for (plan : GeneralExecutionAdmission.Plan) {free : List String}
    (declared : ∀ name type, plan.snapshot.free name = some type → name ∈ free) :
    TableFor plan (planTable plan free) where
  ordered := CanonicalCompare.nameTable_ordered _
  constructors rule member := CanonicalCompare.mem_nameTable.mpr
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨rule, member, rfl⟩)))
  units law member _ unit := CanonicalCompare.mem_nameTable.mpr
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_filterMap.mpr ⟨law, member, unit⟩)))
  declared name type found := CanonicalCompare.mem_nameTable.mpr (List.mem_append_right _ (declared name type found))

/-- A checked pattern is covered by a table of the plan. -/
theorem TableFor.covered {plan : GeneralExecutionAdmission.Plan} {table : List String} (tabled : TableFor plan table)
    {bound : List TypeExpr} {expected : TypeExpr} {pattern : Pattern}
    (checked : Complete.Classes.Checked plan bound expected pattern) : CanonicalCompare.Covered table pattern :=
  CanonicalCompare.covered_of_checked tabled.constructors tabled.declared checked

theorem encodeCollectionType_injective : Function.Injective encodeCollectionType := by
  intro first second same
  cases first <;> cases second <;> first | rfl | simp [encodeCollectionType] at same

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
