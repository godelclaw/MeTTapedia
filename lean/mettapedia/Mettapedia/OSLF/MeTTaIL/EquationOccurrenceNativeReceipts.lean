import Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSemantics
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.TypeTheory.GuardEvidenceComprehension

/-!
# Equation-aware occurrences as interactions and dependent native receipts

The same complete runtime receipt enters the existing interaction presentation
and a dependent certificate family. Equation conversions stay in its retained
justification; the primitive event and its one-step history remain separate.
The postcondition is indexed by the actual target and can retain arbitrary
evidence. Predicate support is an additional erasure, never a receipt decoder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationOccurrenceNativeReceipts

open Mettapedia.OSLF.MeTTaIL.Syntax Engine
open Mettapedia.GSLT.LanguageDef.WellSorted

variable (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)

abbrev RuntimeReceipt :=
  Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.Receipt Pattern
    ConditionalEquationExecution.EquationReceipt AuthoredEquationOccurrenceSearch.RuleOrigin

abbrev ReceiptFamily (source : Pattern) :=
  {receipt : RuntimeReceipt //
    receipt.Valid (AuthoredEquationOccurrenceSemantics.Equation relEnv language free bound expected)
      (AuthoredEquationOccurrenceSemantics.Firing relEnv language free bound expected) source}

theorem semantic_step {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    (AuthoredEquationOccurrenceSemantics.gslt relEnv language free bound expected).Step
      source receipt.val.target := by
  refine ⟨receipt.val.representative.state, (receipt.val.origin, receipt.val.target),
    ?_, receipt.property.2, .refl _⟩
  exact Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.TraceValid.equivalent
    (AuthoredEquationOccurrenceSemantics.Equation relEnv language free bound expected)
    source receipt.val.representative.state receipt.val.representative.conversions receipt.property.1

def interaction :
    Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation
      (AuthoredEquationOccurrenceSemantics.gslt relEnv language free bound expected) where
  Site := Nat
  Event index source target :=
    {receipt : ReceiptFamily relEnv language free bound expected source //
      receipt.val.origin.ruleIndex = index ∧ receipt.val.target = target}
  sound := by
    intro index source target event
    rw [← event.property.2]
    exact semantic_step relEnv language free bound expected event.val

def asInteraction {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    (interaction relEnv language free bound expected).Enabled source where
  site := receipt.val.origin.ruleIndex
  target := receipt.val.target
  evidence := ⟨receipt, rfl, rfl⟩

/-- A concrete emitted receipt is admitted without waiting for exhaustive search. -/
def emitted (source : Pattern) (fuel : Nat) (receipt : RuntimeReceipt)
    (present : receipt ∈
      (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.run
        (AuthoredEquationOccurrenceSearch.model relEnv language free bound expected) fuel
        (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.initial source)).receipts) :
    ReceiptFamily relEnv language free bound expected source :=
  ⟨receipt, (AuthoredEquationOccurrenceSemantics.run_sound relEnv language free bound expected
    source fuel).receipts receipt present⟩

def history {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    (AuthoredEquationOccurrenceSemantics.gslt relEnv language free bound expected).RewritePath
      source receipt.val.target :=
  .cons (semantic_step relEnv language free bound expected receipt) (.nil _)

def administration {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) : Nat :=
  receipt.val.representative.conversions.length

theorem history_primitive_count {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    (history relEnv language free bound expected receipt).length = 1 := rfl

theorem complete_origin_readout {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    (asInteraction relEnv language free bound expected receipt).evidence.val.val.origin =
      receipt.val.origin ∧
    (asInteraction relEnv language free bound expected receipt).evidence.val.val.representative =
      receipt.val.representative := ⟨rfl, rfl⟩

variable (Evidence : Pattern → Type)

/-- Native comprehension retains the complete occurrence and a witness at its
actual target. This is a family over sources, not merely enabled-source support. -/
abbrev NativeFamily (source : Pattern) :=
  Σ receipt : ReceiptFamily relEnv language free bound expected source, Evidence receipt.val.target

def introduce {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source)
    (certificate : Evidence receipt.val.target) :
    NativeFamily relEnv language free bound expected Evidence source := ⟨receipt, certificate⟩

def receiptReadout :
    (Sigma (NativeFamily relEnv language free bound expected Evidence)) →
      Sigma (ReceiptFamily relEnv language free bound expected)
  | ⟨source, receipt, _⟩ => ⟨source, receipt⟩

def targetReadout :
    (Sigma (NativeFamily relEnv language free bound expected Evidence)) → Sigma Evidence
  | ⟨_, receipt, certificate⟩ => ⟨receipt.val.target, certificate⟩

theorem target_readout_square
    (point : Sigma (NativeFamily relEnv language free bound expected Evidence)) :
    (targetReadout relEnv language free bound expected Evidence point).1 =
      (receiptReadout relEnv language free bound expected Evidence point).2.val.target := by
  cases point
  rfl

theorem introduction_retains_certificate {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source)
    (certificate : Evidence receipt.val.target) :
    targetReadout relEnv language free bound expected Evidence
      ⟨source, introduce relEnv language free bound expected Evidence receipt certificate⟩ =
        ⟨receipt.val.target, certificate⟩ := rfl

theorem introduction_retains_origin {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source)
    (certificate : Evidence receipt.val.target) :
    (introduce relEnv language free bound expected Evidence receipt certificate).1.val.origin =
      receipt.val.origin := rfl

/-- Genuine target typing supplies a nonconstant postcondition certificate. -/
def targetSorted {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    PLift (OpenPatternWellSorted language free bound expected receipt.val.target) := by
  refine ⟨?_⟩
  obtain ⟨rule, _, firing, targetEq⟩ := receipt.property.2
  cases firing with
  | fire _ _ _ _ _ _ _ _ _ sorted =>
    exact targetEq.symm ▸ sorted

def sortedNative {source : Pattern}
    (receipt : ReceiptFamily relEnv language free bound expected source) :
    NativeFamily relEnv language free bound expected
      (fun target => PLift (OpenPatternWellSorted language free bound expected target)) source :=
  ⟨receipt, targetSorted relEnv language free bound expected receipt⟩

/-- Existing support erasure has a precise information-loss criterion for
this actual native family. Equal support never establishes receipt equality. -/
theorem support_projection_injective_iff :
    Function.Injective
      (Mettapedia.TypeTheory.GuardEvidenceComprehension.supportProjection
        (Evidence := NativeFamily relEnv language free bound expected Evidence)) ↔
      ∀ source, Subsingleton (NativeFamily relEnv language free bound expected Evidence source) :=
  Mettapedia.TypeTheory.GuardEvidenceComprehension.supportProjection_injective_iff _

end Mettapedia.OSLF.MeTTaIL.EquationOccurrenceNativeReceipts
