import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
import Mettapedia.OSLF.Framework.FiniteEquationCoverage

/-!
# Independently generated typed occurrence semantics

Equation completion and primitive rule completion have separate judgments.
Their equation-saturated relation is a GSLT over the selected typed
presentation. A retained conversion path justifies a source representative;
it does not turn its equation instances into extra primitive events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.FiniteEquationCoverage

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

def Equation (source target : Pattern) : Prop :=
  ∃ receipt : GeneralEquationJobs.Receipt,
    GeneralEquationJobs.Completion plan bound type source receipt ∧ receipt.target = target

def Primitive (source : Pattern) (receipt : GeneralRuleJobs.Receipt) : Prop :=
  receipt.Valid plan bound type source

def gslt : Mettapedia.GSLT.GSLT :=
  moduloGSLT (Equation plan bound type) (Primitive plan bound type) GeneralRuleJobs.Receipt.target

inductive Conversion where
  | forward (receipt : GeneralEquationJobs.Receipt)
  | reverse (receipt : GeneralEquationJobs.Receipt)
  deriving Repr

inductive ConversionPath : Pattern → Pattern → List Conversion → Prop where
  | nil (source : Pattern) : ConversionPath source source []
  | cons {source middle target : Pattern} {receipt : GeneralEquationJobs.Receipt}
      {receipts : List Conversion} :
      GeneralEquationJobs.Completion plan bound type source receipt →
      receipt.target = middle → ConversionPath middle target receipts →
      ConversionPath source target (.forward receipt :: receipts)
  | back {source middle target : Pattern} {receipt : GeneralEquationJobs.Receipt}
      {receipts : List Conversion} :
      GeneralEquationJobs.Completion plan bound type middle receipt →
      receipt.target = source → ConversionPath middle target receipts →
      ConversionPath source target (.reverse receipt :: receipts)

theorem ConversionPath.equivalent {source target : Pattern} {receipts : List Conversion}
    (path : ConversionPath plan bound type source target receipts) :
    Relation.EqvGen (Equation plan bound type) source target := by
  induction path with
  | nil source => exact .refl source
  | @cons source middle target receipt receipts complete endpoint _ ih =>
    exact .trans source middle target (.rel source middle ⟨receipt, complete, endpoint⟩) ih
  | @back source middle target receipt receipts complete endpoint _ ih =>
    exact .trans source middle target
      (.symm middle source (.rel middle source ⟨receipt, complete, endpoint⟩)) ih

theorem ConversionPath.append {source middle target : Pattern}
    {first second : List Conversion}
    (front : ConversionPath plan bound type source middle first)
    (back : ConversionPath plan bound type middle target second) :
    ConversionPath plan bound type source target (first ++ second) := by
  induction front with
  | nil => exact back
  | cons complete endpoint _ ih => exact .cons complete endpoint (ih back)
  | back complete endpoint _ ih => exact .back complete endpoint (ih back)

structure Receipt where
  representative : Pattern
  conversions : List Conversion
  firing : GeneralRuleJobs.Receipt
  deriving Repr

def Receipt.target (receipt : Receipt) : Pattern := receipt.firing.target

def Receipt.Valid (source : Pattern) (receipt : Receipt) : Prop :=
  ConversionPath plan bound type source receipt.representative receipt.conversions ∧
    receipt.firing.Valid plan bound type receipt.representative

theorem Receipt.semantic_step {source : Pattern} {receipt : Receipt}
    (valid : receipt.Valid plan bound type source) :
    (gslt plan bound type).Step source receipt.target :=
  ⟨receipt.representative, receipt.firing, valid.1.equivalent, valid.2, .refl _⟩

theorem Receipt.target_sorted {source : Pattern} {receipt : Receipt}
    (valid : receipt.Valid plan bound type source) :
    OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type receipt.target :=
  (GeneralPlanEnvironment.typing_iff plan bound type receipt.target).mp valid.2.2.2.2.2

theorem Receipt.source_declaration {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {receipt : Receipt}
    (valid : receipt.Valid (compile snapshot permissions) bound type source) :
    ∃ rule index, (rule, index) ∈ snapshot.language.rewrites.zipIdx ∧
      selected permissions.ruleIndices index = true ∧
      rulePlan? snapshot index rule = some receipt.firing.job.declaration := by
  have member := List.fst_mem_of_mem_zipIdx valid.2.1.1
  exact compiled_rule_origin member

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
