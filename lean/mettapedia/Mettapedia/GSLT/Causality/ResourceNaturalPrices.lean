import Mettapedia.GSLT.Causality.ResourceFundingCompleteness
import Mathlib.Data.Multiset.Replicate

/-!
# Natural charges retain the complete resource history

The sum of the charges is calculated independently from the actual firing
word. Its unit-token expansion is exactly the price bag used by the existing
funded resource system. The comparison constructs actual paid paths.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule

variable {R : Type uRes} (S : System.{uRes, uRule} R)
  (charge : ∀ {site : S.Site}, S.Instance site → Nat)

def unitPrice : ∀ {site : S.Site}, S.Instance site → Multiset Unit :=
  fun {_site} firing => Multiset.replicate (charge firing) ()

def wordCharges (word : List S.Entry) : List Nat := word.map fun entry => charge entry.2

theorem unitPrice_word (word : List S.Entry) :
    historyPrice S (unitPrice S @charge) word =
      Multiset.replicate ((wordCharges S @charge word).sum) () := by
  induction word with
  | nil => rfl
  | cons entry rest ih =>
      rw [historyPrice_cons, ih]
      simp only [wordCharges, List.map_cons, List.sum_cons, Multiset.replicate_add]
      rfl

variable [DecidableEq R]

theorem natural_price_history_iff {source target : Multiset R}
    (history : OccurrencePath S.presentation source target) (amount : Nat) :
    (∃ paid : OccurrencePath (funded S (unitPrice S @charge)).presentation
      (marking source (Multiset.replicate amount ()))
      (marking target (Multiset.replicate amount () -
        Multiset.replicate ((wordCharges S @charge (S.pathEntries history)).sum) ())),
      (funded S (unitPrice S @charge)).pathEntries paid = S.pathEntries history) ↔
      (wordCharges S @charge (S.pathEntries history)).sum ≤ amount := by
  have comparison := original_history_has_funding_iff S (unitPrice S @charge)
    history (Multiset.replicate amount ())
  rw [unitPrice_word] at comparison
  exact comparison.trans (Multiset.replicate_le_replicate ())

end Mettapedia.GSLT.Causality.ResourceInteraction
