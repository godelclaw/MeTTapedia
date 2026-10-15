import Mettapedia.OSLF.Framework.RhoScopeMinimumReceipts
import Mettapedia.GSLT.Causality.ComplementaryAssay

/-!
# Complementary scope assays with constructed dependent receipts

An actual intrinsic name is checked against the independently generated
scope. Confirmation retains a constructed minimum-depth derivation;
refutation proves exclusion at the supplied context. This complement does
not assert exclusion at all future substitutions. The dependent readout
applies to independently authored guard firings of the resource assay.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeAssayReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationGeneratedScope
open RhoGeneratedScopeDecision RhoScopeMinimumReceipts
open Mettapedia.GSLT.Causality.ComplementaryAssay

inductive DecisionReceipt {context : Ctx sig} (left right : Process context → Prop)
    (name : Name context) : Verdict → Type where
  | confirm (certificate : Certificate left right name)
      (least : ∀ other : Certificate left right name, certificate.depth ≤ other.depth) :
      DecisionReceipt left right name .confirm
  | refute (excluded : ¬ generated left right name) : DecisionReceipt left right name .refute

def verdictPredicate {context : Ctx sig} (left right : Process context → Prop)
    (name : Name context) : Verdict → Prop
  | .confirm => generated left right name
  | .refute => ¬ generated left right name

def positiveCertificate {context : Ctx sig} {left right : Process context → Prop}
    {name : Name context} : DecisionReceipt left right name .confirm → Certificate left right name
  | .confirm certificate _ => certificate

theorem positiveCertificate_least {context : Ctx sig} {left right : Process context → Prop}
    {name : Name context} (receipt : DecisionReceipt left right name .confirm)
    (other : Certificate left right name) : (positiveCertificate receipt).depth ≤ other.depth := by
  cases receipt with
  | confirm _ least => exact least other

def decisionReceipt {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    DecisionReceipt left right name (verdictOf (guard left right name)) := by
  rw [← minimumReceipt?_presence_agrees_with_guard]
  cases readout : minimumReceipt? left right name with
  | none =>
    exact .refute ((minimumReceipt?_none_iff left right name).mp readout)
  | some certificate =>
    exact .confirm certificate (minimumReceipt?_least left right name readout)

theorem decisionReceipt_sound {context : Ctx sig} {left right : Process context → Prop}
    {name : Name context} {branch : Verdict} (receipt : DecisionReceipt left right name branch) :
    verdictPredicate left right name branch := by
  cases receipt with
  | confirm certificate _ => exact certificate_sound certificate
  | refute excluded => exact excluded

def firingReceipt {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] {Origins : Type*} {branch : Verdict}
    (firing : Firing Origins (guard left right) branch) :
    DecisionReceipt left right firing.value branch :=
  Eq.mp (congrArg (fun selected => DecisionReceipt left right firing.value selected)
    (branch_of_guard (guard left right) firing).symm) (decisionReceipt left right firing.value)

theorem firing_semantics {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] {Origins : Type*} {branch : Verdict}
    (firing : Firing Origins (guard left right) branch) :
    match branch with
    | .confirm => generated left right firing.value
    | .refute => ¬ generated left right firing.value := by
  cases branch <;> exact decisionReceipt_sound (firingReceipt left right firing)

theorem confirmed_receipt_attains_minimum {context : Ctx sig}
    (left right : Process context → Prop) [DecidablePred left] [DecidablePred right]
    (name : Name context) {certificate : Certificate left right name}
    (readout : minimumReceipt? left right name = some certificate) :
    RhoGeneratedScopeMinimum.minimumDepth? left right name = some certificate.depth ∧
      generated left right name :=
  ⟨minimumReceipt?_some_depth left right name readout, certificate_sound certificate⟩

end Mettapedia.OSLF.Framework.RhoScopeAssayReceipts
