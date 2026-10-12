import Mettapedia.OSLF.Framework.RhoQuotationDependentAccess
import Mettapedia.OSLF.Framework.RhoGeneratedScopeInventory
import Mettapedia.OSLF.Syntax.BindingGroundedPredicates
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Compatible consumers and retained rho process origins

An output inventory supplies a genuinely varying dependent consumer of
quoted names. Its comparison with the independently counted process is
earned from the actual source equations.

A singleton of a supplied closed process is also a native predicate.
It distinguishes an output from its suspension, although their quotations
are equal. The existential quotation image remains a native name predicate;
it cannot be read as a test of every supplied process origin of that name.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoQuotationAccessControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingConstructorPredicates BindingGroundedPredicates
open RhoQuotationDependentAccess RhoGeneratedScopeInventory
open Mettapedia.GSLT.Core.NonFactorization

open Mettapedia.TypeTheory

def inventoryFamily {context : Ctx sig} (name : Name context) : Type :=
  Fin (RhoSourceOutputPredicate.count name + 1)

def inventoryConsumer {context : Ctx sig} (process : Process context) :
    inventoryFamily (quote process) :=
  ⟨RhoSourceOutputPredicate.count process, by
    rw [count_quote]
    exact Nat.lt_succ_self _⟩

def inventoryNameConsumer {context : Ctx sig} (name : Name context) : inventoryFamily name :=
  Fin.last (RhoSourceOutputPredicate.count name)

theorem inventory_readout {context : Ctx sig} (process : Process context) :
    inventoryConsumer process = inventoryNameConsumer (quote process) :=
  Fin.ext (count_quote process).symm

theorem inventory_compatible {context : Ctx sig} :
    Compatible (context := context) inventoryFamily inventoryConsumer := by
  intro first second same
  rw [inventory_readout first, inventory_readout second]
  exact RetractionDependentDescent.section_congr inventoryFamily inventoryNameConsumer same

theorem inventory_descent {context : Ctx sig} :
    descend (context := context) inventoryFamily inventoryConsumer = inventoryNameConsumer := by
  exact (unique_descent inventoryFamily inventoryConsumer inventoryNameConsumer
    (funext fun process => (inventory_readout process).symm)).symm

theorem inventory_family_varies :
    inventoryFamily (quote (zero [])) = Fin 1 ∧
      inventoryFamily (quote visible) = Fin 2 := by
  constructor
  · unfold inventoryFamily
    rw [count_quote]
    rfl
  · unfold inventoryFamily
    rw [count_quote]
    rfl

theorem positive_inventory_compatible :
    PredicateCompatible (RhoSourceOutputPredicate.positive Srt.pr) := by
  intro context first second same
  change (0 < RhoSourceOutputPredicate.count first) ↔
    (0 < RhoSourceOutputPredicate.count second)
  have counted := congrArg RhoSourceOutputPredicate.count same
  rw [count_quote, count_quote] at counted
  rw [counted]

theorem positive_quotation_reflects {context : Ctx sig} (process : Process context) :
    (quoted (RhoSourceOutputPredicate.positive Srt.pr)).holds (quote process) ↔
      (RhoSourceOutputPredicate.positive Srt.pr).holds process :=
  (quoted_reflects_origin_iff _).mpr positive_inventory_compatible process

def singletonOrigin (origin : Process []) : Predicate model Srt.pr where
  holds := fun {context} process => process = ground (A := model) context origin
  substitute := by
    intro source target env process same
    rw [same, substitute_ground]

theorem singleton_closed_iff (origin process : Process []) :
    (singletonOrigin origin).holds process ↔ process = origin := by
  change process = ground (A := model) [] origin ↔ _
  rw [ground_empty]

theorem supplied_visible_admitted : (singletonOrigin visible).holds visible :=
  (singleton_closed_iff _ _).mpr rfl

theorem supplied_suspension_rejected : ¬ (singletonOrigin visible).holds suspended :=
  fun admitted => suspended_not_visible ((singleton_closed_iff _ _).mp admitted)

theorem visible_name_admitted : (quoted (singletonOrigin visible)).holds (quote visible) :=
  ⟨receiptOf _ visible supplied_visible_admitted⟩

theorem suspended_name_admitted : (quoted (singletonOrigin visible)).holds (quote suspended) := by
  rw [same_actual_name]
  exact visible_name_admitted

theorem singleton_not_compatible : ¬ PredicateCompatible (singletonOrigin visible) := by
  intro compatible
  exact supplied_suspension_rejected
    ((compatible visible suspended same_actual_name.symm).mp supplied_visible_admitted)

theorem singleton_cannot_reflect_every_origin :
    ¬ ∀ {context : Ctx sig} (process : Process context),
      (quoted (singletonOrigin visible)).holds (quote process) ↔
        (singletonOrigin visible).holds process := by
  intro reflects
  exact supplied_suspension_rejected ((reflects suspended).mp suspended_name_admitted)

def visibleReceipt : QuotationReceipt (top model Srt.pr) (quote visible) :=
  receiptOf _ visible (by trivial)

def suspendedReceipt : QuotationReceipt (top model Srt.pr) (quote visible) where
  arguments := .cons suspended .nil
  admitted := ⟨by trivial, by trivial⟩
  output := (RhoGeneratedScopeSubstitution.quote_operation suspended).symm.trans same_actual_name

theorem quotation_receipts_retain_distinct_origins : visibleReceipt ≠ suspendedReceipt := by
  intro same
  have origins := congrArg QuotationReceipt.origin same
  exact suspended_not_visible origins.symm

def originSeparator : NonTrivialFiber (quote : Process [] → Name []) id where
  left := suspended
  right := visible
  sameShadow := same_actual_name
  differentValue := suspended_not_visible

theorem no_exact_origin_from_name : ¬ Factors (quote : Process [] → Name []) id :=
  originSeparator.not_factors

end Mettapedia.OSLF.Framework.RhoQuotationAccessControls
