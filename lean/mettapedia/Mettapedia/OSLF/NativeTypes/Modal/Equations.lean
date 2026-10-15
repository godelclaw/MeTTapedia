import Mettapedia.OSLF.NativeTypes.Modal.Rules

open Mettapedia.OSLF.Framework

/-!
# Equation transport of complete modal receipts

Every proof of conversion in the independently generated equation relation
has a retained conversion path. Rebasing appends that path to the receipt and
keeps the primitive declaration, matcher alternatives and premise history.
The conversion is administrative justification, not another physical event.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Equations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

def inverse : Conversion → Conversion
  | .forward receipt => .reverse receipt
  | .reverse receipt => .forward receipt

def reverse (receipts : List Conversion) : List Conversion := receipts.reverse.map inverse

theorem reverse_cons (receipt : Conversion) (receipts : List Conversion) :
    reverse (receipt :: receipts) = reverse receipts ++ [inverse receipt] := by
  simp [reverse]

theorem reverse_path {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source target : Pattern} {receipts : List Conversion}
    (path : ConversionPath plan bound carrier source target receipts) :
    ConversionPath plan bound carrier target source (reverse receipts) := by
  induction path with
  | nil source => exact .nil source
  | @cons source middle target receipt receipts completed endpoint _ ih =>
      rw [reverse_cons]
      exact ConversionPath.append plan bound carrier ih (.back completed endpoint (.nil source))
  | @back source middle target receipt receipts completed endpoint _ ih =>
      rw [reverse_cons]
      exact ConversionPath.append plan bound carrier ih (.cons completed endpoint (.nil source))

/-- The conversion semantics and retained path semantics agree for arbitrary
lengths, independent of finite equation enumeration or search budgets. -/
theorem conversion_iff_path (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (source target : Pattern) :
    Relation.EqvGen (Equation plan bound carrier) source target ↔
      ∃ receipts, ConversionPath plan bound carrier source target receipts := by
  constructor
  · intro conversion
    induction conversion with
    | rel source target edge =>
        obtain ⟨receipt, completed, endpoint⟩ := edge
        exact ⟨[.forward receipt], .cons completed endpoint (.nil target)⟩
    | refl source => exact ⟨[], .nil source⟩
    | symm _ _ _ ih =>
        obtain ⟨receipts, path⟩ := ih
        exact ⟨reverse receipts, reverse_path path⟩
    | trans _ _ _ _ _ first second =>
        obtain ⟨firstReceipts, firstPath⟩ := first
        obtain ⟨secondReceipts, secondPath⟩ := second
        exact ⟨firstReceipts ++ secondReceipts, ConversionPath.append plan bound carrier firstPath secondPath⟩
  · rintro ⟨receipts, path⟩
    exact path.equivalent

/-- Rebasing is a concrete operation on retained proof data. -/
def rebase (front : List Conversion) (receipt : Receipt) : Receipt :=
  { receipt with conversions := front ++ receipt.conversions }

theorem rebase_valid {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source rebasedSource : Pattern} {front : List Conversion} {receipt : Receipt}
    (path : ConversionPath plan bound carrier rebasedSource source front)
    (valid : receipt.Valid plan bound carrier source) :
    (rebase front receipt).Valid plan bound carrier rebasedSource :=
  ⟨ConversionPath.append plan bound carrier path valid.1, valid.2⟩

theorem rebase_firing (front : List Conversion) (receipt : Receipt) :
    (rebase front receipt).firing = receipt.firing := rfl

theorem rebase_target (front : List Conversion) (receipt : Receipt) :
    (rebase front receipt).target = receipt.target := rfl

/-- Every equation-equivalent source admits the same physical occurrence,
with its complete authored origin unchanged. -/
theorem receipt_transport {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source rebasedSource : Pattern} {receipt : Receipt}
    (equivalent : Relation.EqvGen (Equation plan bound carrier) rebasedSource source)
    (valid : receipt.Valid plan bound carrier source) :
    ∃ transported : Receipt, transported.Valid plan bound carrier rebasedSource ∧
      transported.firing = receipt.firing ∧ transported.target = receipt.target := by
  obtain ⟨front, path⟩ := (conversion_iff_path plan bound carrier rebasedSource source).mp equivalent
  exact ⟨rebase front receipt, rebase_valid path valid, rfl, rfl⟩

theorem equation_sorted {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source target : Pattern} (equation : Equation plan bound carrier source target) :
    OpenPatternWellSorted (Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound carrier source ∧
    OpenPatternWellSorted (Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound carrier target := by
  obtain ⟨receipt, complete, endpoint⟩ := equation
  refine ⟨complete.sourceTyped, ?_⟩
  rw [← endpoint, complete.endpoint]
  exact complete.accepted.2.2

/-- Every generated equation conversion preserves the actual open carrier. -/
theorem conversion_sorted_iff {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source target : Pattern} (equivalent : Relation.EqvGen (Equation plan bound carrier) source target) :
    OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound carrier source ↔
      OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound carrier target := by
  induction equivalent with
  | rel source target edge =>
      have typed := equation_sorted edge
      have first := (Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment.typing_iff plan bound carrier source).mp typed.1
      have second := (Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment.typing_iff plan bound carrier target).mp typed.2
      exact ⟨fun _ => second, fun _ => first⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem outcome_target_typed {plan : Plan} {schema : Mettapedia.OSLF.NativeTypes.Modal.Rules.Schema plan}
    {term : Pattern} {assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    {B : Mettapedia.OSLF.NativeTypes.Modal.Rules.Continuation}
    (outcome : Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema term assignment B) :
    OpenPatternWellSorted plan.snapshot.language plan.snapshot.free schema.bound
      schema.programCarrier outcome.target :=
  (conversion_sorted_iff outcome.targetConversion).mp
    (Receipt.target_sorted plan schema.bound schema.programCarrier outcome.valid)

/-- M-STEP remains valid at every equation representative of its filled
program. The exact RHS and substituted continuation are unchanged. -/
theorem outcome_step_at_equivalent_source {plan : Plan} {schema : Mettapedia.OSLF.NativeTypes.Modal.Rules.Schema plan}
    {term : Pattern} {assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    {B : Mettapedia.OSLF.NativeTypes.Modal.Rules.Continuation} {representative : Pattern}
    (outcome : Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema term assignment B)
    (equivalent : Relation.EqvGen (Equation plan schema.bound schema.programCarrier)
      representative outcome.source) :
    (gslt plan schema.bound schema.programCarrier).Step representative outcome.target := by
  obtain ⟨transported, valid, _, sameTarget⟩ := receipt_transport equivalent outcome.valid
  have converted : Relation.EqvGen (Equation plan schema.bound schema.programCarrier)
      transported.target outcome.target := by
    rw [sameTarget]
    exact outcome.targetConversion
  exact ⟨transported.representative, transported.firing, valid.1.equivalent, valid.2, converted⟩

/-- Possibility is invariant under every actual program-equation conversion. -/
theorem possibility_equation_iff {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {B : Pattern → Type} {source target : Pattern}
    (equivalent : Relation.EqvGen (Equation plan bound carrier) source target) :
    Mettapedia.OSLF.NativeTypes.Modal.Rules.Possibility plan bound carrier B source ↔
      Mettapedia.OSLF.NativeTypes.Modal.Rules.Possibility plan bound carrier B target := by
  constructor
  · rintro ⟨receipt, valid, certificate⟩
    obtain ⟨transported, valid', _, sameTarget⟩ := receipt_transport
      (Relation.EqvGen.symm source target equivalent) valid
    exact ⟨transported, valid', sameTarget.symm ▸ certificate⟩
  · rintro ⟨receipt, valid, certificate⟩
    obtain ⟨transported, valid', _, sameTarget⟩ := receipt_transport equivalent valid
    exact ⟨transported, valid', sameTarget.symm ▸ certificate⟩

end Mettapedia.OSLF.NativeTypes.Modal.Equations
