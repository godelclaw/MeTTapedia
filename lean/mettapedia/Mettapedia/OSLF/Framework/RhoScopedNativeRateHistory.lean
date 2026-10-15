import Mettapedia.OSLF.Framework.RhoScopedDependentEventFutures
import Mettapedia.OSLF.Syntax.ScopedBindingEquationResources

/-!
# Configured original reaction prices with retained native certificates

The original contextual root and a supplied raw surrounding process give an
actual permitted parallel occurrence. Its paid history is the existing
consumptive resource presentation, with its complete event word retained.
Every native event certificate has such a realization at its exact source
and target. Configured rule prices preserve financial admission across the
earned native future action; arbitrary state-sensitive prices are not inferred.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedNativeRateHistory

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open ScopedEncoding ScopedEquationEvents RhoScopedParallelPathReadout RhoScopedEquationContextControls
open RhoScopedEquationEventControls
open RhoScopedDependentEventFutures DisplayedPresheafComprehension DisplayedPresheafTransport
open PresheafEventCertificates

variable {admitted : SourceRule → Prop}

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def originalOccurrence {context : Ctx sig} (root : Root sourceRules admitted context)
    (surrounding : Term sig context Srt.pr) : Occurrence sourceRules admitted context :=
  ⟨root.1, context, root.2, single (parallelFrame context surrounding),
    .cons (.nil _) (by trivial)⟩

theorem original_occurrence_index {context : Ctx sig} (root : Root sourceRules admitted context)
    (surrounding : Term sig context Srt.pr) :
    (originalOccurrence root surrounding).index = root.1 := rfl

theorem original_occurrence_root {context : Ctx sig} (root : Root sourceRules admitted context)
    (surrounding : Term sig context Srt.pr) :
    (originalOccurrence root surrounding).root = root.2 := rfl

theorem original_occurrence_source {context : Ctx sig} (root : Root sourceRules admitted context)
    (surrounding : Term sig context Srt.pr) :
    (originalOccurrence root surrounding).sourceClass rhoSourceE =
      join root.source (project surrounding) :=
  left_slot_readout context _ root.source

theorem original_occurrence_target {context : Ctx sig} (root : Root sourceRules admitted context)
    (surrounding : Term sig context Srt.pr) :
    (originalOccurrence root surrounding).targetClass rhoSourceE =
      join root.target (project surrounding) :=
  left_slot_readout context _ root.target

theorem original_occurrence_substitution {context destination : Ctx sig}
    (change : Sub sig context destination) (root : Root sourceRules admitted context)
    (surrounding : Term sig context Srt.pr) :
    (originalOccurrence root surrounding).map destination change =
      originalOccurrence (root.map change) (bind change surrounding) := by
  unfold originalOccurrence ScopedEquationEvents.Event.map
  dsimp only [single, substituteContext, parallelFrame, substituteFrameSlot]
  congr 2
  congr 1
  funext other excluding
  fin_cases other
  · exact False.elim (excluding rfl)
  · rfl

abbrev profile (rates : SourceRule → Nat) : Selected admitted → Nat := fun selected => rates selected.val

abbrev Paid {context : Ctx sig} (rates : SourceRule → Nat)
    (root : Root sourceRules admitted context) (surrounding : Term sig context Srt.pr) (amount : Nat) :=
  ScopedEquationResources.PaidHistory rhoSourceE (schemas sourceRules admitted)
    parallelPermission (context, Srt.pr) (profile rates) (originalOccurrence root surrounding) amount

theorem paid_iff_rate {context : Ctx sig} (rates : SourceRule → Nat)
    (root : Root sourceRules admitted context) (surrounding : Term sig context Srt.pr) (amount : Nat) :
    Nonempty (Paid rates root surrounding amount) ↔ rates root.1.val ≤ amount :=
  ScopedEquationResources.paid_history_nonempty_iff rhoSourceE (schemas sourceRules admitted)
    parallelPermission (context, Srt.pr) (profile rates) (originalOccurrence root surrounding) amount

theorem paid_word_retains_original_root {context : Ctx sig} (rates : SourceRule → Nat)
    (root : Root sourceRules admitted context) (surrounding : Term sig context Srt.pr) (amount : Nat)
    (funding : Paid rates root surrounding amount) :
    funding.eventWord = [originalOccurrence root surrounding] :=
  ScopedEquationResources.PaidHistory.eventWord_eq rhoSourceE (schemas sourceRules admitted)
    parallelPermission (context, Srt.pr) funding

theorem substitution_keeps_financial_admission {context destination : Ctx sig}
    (rates : SourceRule → Nat) (change : Sub sig context destination)
    (root : Root sourceRules admitted context) (surrounding : Term sig context Srt.pr) (amount : Nat) :
    Nonempty (Paid rates (root.map change) (bind change surrounding) amount) ↔
      Nonempty (Paid rates root surrounding amount) := by
  rw [paid_iff_rate, paid_iff_rate]
  rfl

variable (admitted : SourceRule → Prop) (family : DisplayedFamily (RhoScopedEventPresheaf.terms .pr))
variable {world : (Syntactic.Ctxt sig)ᵒᵖ}

def nativeEvent (receipt : (totalSpace (certificates admitted family)).obj world) :
    (RhoScopedEventPresheaf.events admitted).obj world :=
  ((span admitted).eventReadout family).app world receipt

def nativeOccurrence (receipt : (totalSpace (certificates admitted family)).obj world) :
    Occurrence sourceRules admitted world.unop.vars :=
  originalOccurrence (nativeEvent admitted family receipt).1
    (Quotient.out (nativeEvent admitted family receipt).2)

abbrev NativePaid (rates : SourceRule → Nat)
    (receipt : (totalSpace (certificates admitted family)).obj world) (amount : Nat) :=
  ScopedEquationResources.PaidHistory rhoSourceE (schemas sourceRules admitted)
    parallelPermission (world.unop.vars, Srt.pr) (profile rates)
    (nativeOccurrence admitted family receipt) amount

theorem native_paid_iff (rates : SourceRule → Nat)
    (receipt : (totalSpace (certificates admitted family)).obj world) (amount : Nat) :
    Nonempty (NativePaid admitted family rates receipt amount) ↔
      rates ((receiptOrigin admitted family).app world receipt).val ≤ amount :=
  paid_iff_rate rates (nativeEvent admitted family receipt).1
    (Quotient.out (nativeEvent admitted family receipt).2) amount

theorem native_occurrence_source
    (receipt : (totalSpace (certificates admitted family)).obj world) :
    (nativeOccurrence admitted family receipt).sourceClass rhoSourceE = receipt.1 := by
  have sourceReadout := congrArg (fun map => map.app world receipt)
    ((span admitted).eventReadout_source family)
  change join (nativeEvent admitted family receipt).1.source
    (nativeEvent admitted family receipt).2 = receipt.1 at sourceReadout
  have original := original_occurrence_source (nativeEvent admitted family receipt).1
    (Quotient.out (nativeEvent admitted family receipt).2)
  have representative : project (Quotient.out (nativeEvent admitted family receipt).2) =
      (nativeEvent admitted family receipt).2 := Quotient.out_eq _
  exact original.trans ((congrArg (join (nativeEvent admitted family receipt).1.source) representative).trans
    sourceReadout)

theorem native_occurrence_target
    (receipt : (totalSpace (certificates admitted family)).obj world) :
    (nativeOccurrence admitted family receipt).targetClass rhoSourceE =
      ((targetReadout admitted family).app world receipt).1 := by
  have targetReadout := congrArg (fun map => map.app world receipt)
    ((span admitted).resultReadout_target family)
  change ((RhoScopedDependentEventFutures.targetReadout admitted family).app world receipt).1 =
    join (nativeEvent admitted family receipt).1.target (nativeEvent admitted family receipt).2
    at targetReadout
  have original := original_occurrence_target (nativeEvent admitted family receipt).1
    (Quotient.out (nativeEvent admitted family receipt).2)
  have representative : project (Quotient.out (nativeEvent admitted family receipt).2) =
      (nativeEvent admitted family receipt).2 := Quotient.out_eq _
  exact original.trans ((congrArg (join (nativeEvent admitted family receipt).1.target) representative).trans
    targetReadout.symm)

theorem native_paid_word (rates : SourceRule → Nat)
    (receipt : (totalSpace (certificates admitted family)).obj world) (amount : Nat)
    (funding : NativePaid admitted family rates receipt amount) :
    funding.eventWord = [nativeOccurrence admitted family receipt] :=
  ScopedEquationResources.PaidHistory.eventWord_eq rhoSourceE (schemas sourceRules admitted)
    parallelPermission (world.unop.vars, Srt.pr) funding

theorem native_funding_preserved_at_future {future : (Syntactic.Ctxt sig)ᵒᵖ}
    (rates : SourceRule → Nat) (change : world ⟶ future)
    (receipt : (totalSpace (certificates admitted family)).obj world) (amount : Nat) :
    Nonempty (NativePaid admitted family rates
      ((totalSpace (certificates admitted family)).map change receipt) amount) ↔
        Nonempty (NativePaid admitted family rates receipt amount) := by
  rw [native_paid_iff, native_paid_iff, future_rule_origin]

end Mettapedia.OSLF.Framework.RhoScopedNativeRateHistory
