import Mettapedia.OSLF.NativeTypes.Generation.Schemas

open Mettapedia.OSLF.Framework

/-!+# Computed admission of complete generated modal schemas

A contextual address alone does not identify a generated typing judgment.
The executable gate compares the selected ordinal, authored origin, address,
ambient context, and both source and focus carriers against the actual
catalogue. The selected ordinal determines the complete authored declaration;
its proof of selection does not introduce an extra runtime choice.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)

structure SchemaFingerprint where
  ordinal : Nat
  declarationIndex : Nat
  position : RedexPosition.Position
  bound : List TypeExpr
  programCarrier : TypeExpr
  focusBound : List TypeExpr
  focusCarrier : TypeExpr
  deriving DecidableEq, Repr

def schemaFingerprint {plan : Plan} (schema : Schema plan) : SchemaFingerprint :=
  ⟨schema.ordinal, schema.declaration.declarationIndex, schema.position,
    schema.bound, schema.programCarrier, schema.focusBound, schema.focusCarrier⟩

/-- Original rule payloads cannot vary at a fixed selected ordinal. -/
theorem same_ordinal_declaration {plan : Plan} {first second : Schema plan}
    (same : first.ordinal = second.ordinal) : first.declaration = second.declaration := by
  have firstAt := List.mk_mem_zipIdx_iff_getElem?.mp first.declared
  have secondAt := List.mk_mem_zipIdx_iff_getElem?.mp second.declared
  rw [same] at firstAt
  exact Option.some.inj (firstAt.symm.trans secondAt)

theorem schema_fingerprint_injective {plan : Plan} :
    Function.Injective (schemaFingerprint (plan := plan)) := by
  intro first second same
  have declaration := same_ordinal_declaration (congrArg SchemaFingerprint.ordinal same)
  cases first with
  | mk firstOrdinal firstDeclaration firstDeclared firstPosition firstBound firstCarrier
      firstFocusBound firstFocusCarrier =>
    cases second with
    | mk secondOrdinal secondDeclaration secondDeclared secondPosition secondBound secondCarrier
        secondFocusBound secondFocusCarrier =>
      simp only [schemaFingerprint, SchemaFingerprint.mk.injEq] at same
      rcases same with ⟨ordinal, _, position, bound, carrier, focusBound, focusCarrier⟩
      cases ordinal
      cases position
      cases bound
      cases carrier
      cases focusBound
      cases focusCarrier
      cases declaration
      rfl

def schemaMatches {plan : Plan} (first second : Schema plan) : Bool :=
  decide (schemaFingerprint first = schemaFingerprint second)

theorem schema_matches_iff {plan : Plan} (first second : Schema plan) :
    schemaMatches first second = true ↔ first = second := by
  simp only [schemaMatches, decide_eq_true_eq]
  exact ⟨fun same => schema_fingerprint_injective same, congrArg schemaFingerprint⟩

def Generated.schemaAdmitted? (generated : Generated) (schema : Schema generated.plan) : Bool :=
  generated.modalCatalogue.any fun candidate => schemaMatches candidate schema

theorem schema_admitted_iff (generated : Generated) (schema : Schema generated.plan) :
    generated.schemaAdmitted? schema = true ↔ schema ∈ generated.modalCatalogue := by
  simp only [Generated.schemaAdmitted?, List.any_eq_true]
  constructor
  · rintro ⟨candidate, member, same⟩
    exact ((schema_matches_iff candidate schema).mp same) ▸ member
  · intro member
    exact ⟨schema, member, (schema_matches_iff schema schema).mpr rfl⟩

theorem generated_schema_admitted {generated : Generated} {schema : Schema generated.plan}
    (member : schema ∈ generated.modalCatalogue) : generated.schemaAdmitted? schema = true :=
  (schema_admitted_iff generated schema).mpr member

theorem generated_schema_rejected {generated : Generated} {schema : Schema generated.plan}
    (absent : schema ∉ generated.modalCatalogue) : generated.schemaAdmitted? schema = false := by
  cases checked : generated.schemaAdmitted? schema
  · rfl
  · exact False.elim (absent ((schema_admitted_iff generated schema).mp checked))

/-- An address match cannot override a different carrier or bound context. -/
theorem mismatched_fingerprint_rejected {generated : Generated} {schema : Schema generated.plan}
    (different : ∀ candidate ∈ generated.modalCatalogue,
      schemaFingerprint candidate ≠ schemaFingerprint schema) :
    generated.schemaAdmitted? schema = false := by
  apply generated_schema_rejected
  intro member
  exact different schema member rfl

end Mettapedia.OSLF.NativeTypes.Generation
