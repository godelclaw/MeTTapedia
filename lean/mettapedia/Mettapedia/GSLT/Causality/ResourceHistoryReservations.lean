import Mettapedia.GSLT.Causality.ResourceNaturalPrices
import Mettapedia.GSLT.Dynamics.LeaseReservations

/-!
# Preaccepted resource histories and exact reservation refunds

The same supplied history determines the funded resource word and the lease's
ordered charge word. A declared upper bound which covers that word gives
both actual paid resource execution and the admitted grant/spend/refund
execution. All prefixes remain valid; the final refund returns precisely the
unused upper bound, without changing the spent account.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory
open Mettapedia.GSLT.Dynamics.ParallelFuelLease

universe uRes uRule uOwner

noncomputable section

variable {R : Type uRes} {Owner : Type uOwner}
  (S : System.{uRes, uRule} R) [DecidableEq R]
  (charge : ∀ {site : S.Site}, S.Instance site → Nat)

theorem reserved_history {source target : Multiset R}
    (history : OccurrencePath S.presentation source target)
    (ledger : Ledger Owner) (parent child : Owner) (distinct : child ≠ parent) (upper : Nat)
    (valid : ledger.Nonnegative) (empty : ledger.balances child = 0)
    (available : (upper : ℤ) ≤ ledger.balances parent)
    (bounded : (wordCharges S @charge (S.pathEntries history)).sum ≤ upper) :
    (∃ paid : OccurrencePath (funded S (unitPrice S @charge)).presentation
      (marking source (Multiset.replicate upper ()))
      (marking target (Multiset.replicate upper () -
        Multiset.replicate ((wordCharges S @charge (S.pathEntries history)).sum) ())),
        (funded S (unitPrice S @charge)).pathEntries paid = S.pathEntries history) ∧
    Execution ledger (finishReservation parent child distinct ledger upper
      (wordCharges S @charge (S.pathEntries history))) ∧
    (finishReservation parent child distinct ledger upper
      (wordCharges S @charge (S.pathEntries history))).balances parent =
        ledger.balances parent - ((wordCharges S @charge (S.pathEntries history)).sum : ℤ) ∧
    (finishReservation parent child distinct ledger upper
      (wordCharges S @charge (S.pathEntries history))).spent =
        ledger.spent + ((wordCharges S @charge (S.pathEntries history)).sum : ℤ) ∧
    ∀ count, (spendWord child ((wordCharges S @charge (S.pathEntries history)).take count)
      (reserved parent child distinct ledger upper)).Nonnegative :=
  ⟨(natural_price_history_iff S @charge history upper).mpr bounded,
    reservation_execution parent child distinct ledger upper _ valid empty available bounded,
    reservation_final_parent parent child distinct ledger upper _ empty,
    reservation_spent parent child distinct ledger upper _,
    reservation_prefix_valid parent child distinct ledger upper _ valid empty available bounded⟩

end

end Mettapedia.GSLT.Causality.ResourceInteraction
