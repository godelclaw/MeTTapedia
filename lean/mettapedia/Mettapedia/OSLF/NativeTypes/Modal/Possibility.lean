import Mettapedia.OSLF.NativeTypes.Modal.Equations

open Mettapedia.OSLF.Framework

/-!
# Empty-context possibility and the independent existential transition law

The modality's receipt target is an actual primitive result. The independent
GSLT relation may additionally choose an equation-equivalent target. Their
existential meanings agree for equation-invariant continuation support.
Carrier-sorted support earns this condition from the generated equation
semantics, without an externally supplied equation-closure oracle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Possibility

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules

/-- Support invariance is the condition imposed by interpreting a type on
equation classes; it does not assert completeness of operational search. -/
def SupportInvariant (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (B : Pattern → Type) : Prop :=
  ∀ source target, Relation.EqvGen (Equation plan bound carrier) source target →
    (Nonempty (B source) ↔ Nonempty (B target))

theorem possibility_iff_existential_step {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {B : Pattern → Type} {source : Pattern}
    (invariant : SupportInvariant plan bound carrier B) :
    Possibility plan bound carrier B source ↔
      ∃ target, (gslt plan bound carrier).Step source target ∧ Nonempty (B target) := by
  constructor
  · exact possibility_step
  · rintro ⟨target, ⟨representative, primitive, before, firing, after⟩, certificate⟩
    obtain ⟨conversions, path⟩ :=
      (Mettapedia.OSLF.NativeTypes.Modal.Equations.conversion_iff_path plan bound carrier source representative).mp before
    let receipt : Receipt := ⟨representative, conversions, primitive⟩
    refine ⟨receipt, ⟨path, firing⟩, ?_⟩
    exact (invariant primitive.target target after).mpr certificate

def SortedSupport (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr) (target : Pattern) : Type :=
  PLift (OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound carrier target)

theorem sorted_support_invariant (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr) :
    SupportInvariant plan bound carrier (SortedSupport plan bound carrier) := by
  intro source target equivalent
  have preserved := Mettapedia.OSLF.NativeTypes.Modal.Equations.conversion_sorted_iff equivalent
  constructor
  · rintro ⟨typed⟩
    exact ⟨⟨preserved.mp typed.down⟩⟩
  · rintro ⟨typed⟩
    exact ⟨⟨preserved.mpr typed.down⟩⟩

/-- This whole-language instance discharges the quotient condition through
the actual sorted equation semantics, for every ambient context. -/
theorem sorted_possibility_iff_step (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) :
    Possibility plan bound carrier (SortedSupport plan bound carrier) source ↔
      ∃ target, (gslt plan bound carrier).Step source target := by
  rw [possibility_iff_existential_step (sorted_support_invariant plan bound carrier)]
  constructor
  · rintro ⟨target, transition, _⟩
    exact ⟨target, transition⟩
  · rintro ⟨target, ⟨representative, primitive, before, firing, after⟩⟩
    obtain ⟨conversions, path⟩ :=
      (Mettapedia.OSLF.NativeTypes.Modal.Equations.conversion_iff_path plan bound carrier source representative).mp before
    let receipt : Receipt := ⟨representative, conversions, primitive⟩
    have typed := GeneralOccurrenceNativeReceipts.target_typed plan bound carrier
      (⟨receipt, ⟨path, firing⟩⟩ : GeneralOccurrenceNativeReceipts.ReceiptFamily plan bound carrier source)
    refine ⟨target, ⟨representative, primitive, before, firing, after⟩, ?_⟩
    exact ⟨⟨(Mettapedia.OSLF.NativeTypes.Modal.Equations.conversion_sorted_iff after).mp typed⟩⟩

end Mettapedia.OSLF.NativeTypes.Modal.Possibility
