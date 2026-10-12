import Mettapedia.GSLT.Causality.LayeredFundingHistory
import Mettapedia.GSLT.Causality.ResourceFundingCompletenessControls

/-!
# Pooled money does not certify separate funding layers

The actual two-receive history needs three tokens in its value-priced layer
and two in its per-step layer. The allocation (3,2) funds the history.
The allocation (0,5) has the same pooled money but fails the separate
admission; pouring it funds the pooled price instead.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.LayeredFundingHistoryControls

open OccurrenceHistory Controls ResourceFundingCompletenessControls

def stepPrice : ∀ {site : persistentReceiver.Site},
    persistentReceiver.Instance site → Multiset Unit :=
  fun {_site} => fun _value : Nat => Multiset.replicate 1 ()

def sumPrice : ∀ {site : persistentReceiver.Site},
    persistentReceiver.Instance site → Multiset Unit :=
  fun {site} => fun value : Nat => messagePrice (site := site) value + stepPrice (site := site) value

def separateSystem : System ((Res ⊕ Unit) ⊕ Unit) :=
  fundedTwice persistentReceiver @messagePrice @stepPrice

def pooledSystem : System (Res ⊕ Unit) := funded persistentReceiver @sumPrice

theorem complete_step_price :
    historyPrice persistentReceiver @stepPrice originalWord = Multiset.replicate 2 () := by decide

theorem complete_pooled_price :
    historyPrice persistentReceiver @sumPrice originalWord = Multiset.replicate 5 () := by
  have comparison := pooled_price persistentReceiver @messagePrice @stepPrice originalWord
  change historyPrice persistentReceiver @sumPrice originalWord =
    historyPrice persistentReceiver @messagePrice originalWord +
      historyPrice persistentReceiver @stepPrice originalWord at comparison
  rw [complete_price, complete_step_price] at comparison
  exact comparison.trans (by decide)

theorem separately_funded_actual_history :
    ∃ paid : OccurrencePath separateSystem.presentation
      (marking (marking twoMessages (Multiset.replicate 3 ())) (Multiset.replicate 2 ()))
      (marking (marking collected (Multiset.replicate 3 () - Multiset.replicate 3 ()))
        (Multiset.replicate 2 () - Multiset.replicate 2 ())),
        separateSystem.pathEntries paid = originalWord := by
  have comparison := layered_history_iff persistentReceiver @messagePrice @stepPrice originalWord
    twoMessages collected (Multiset.replicate 3 ()) (Multiset.replicate 2 ())
  rw [complete_price, complete_step_price] at comparison
  exact comparison.mpr ⟨original_word_actually_fires, le_refl _, le_refl _⟩

theorem misallocated_money_cannot_fund_the_layers :
    ¬ ∃ paid : OccurrencePath separateSystem.presentation
      (marking (marking twoMessages (0 : Multiset Unit)) (Multiset.replicate 5 ()))
      (marking (marking collected ((0 : Multiset Unit) - Multiset.replicate 3 ()))
        (Multiset.replicate 5 () - Multiset.replicate 2 ())),
        separateSystem.pathEntries paid = originalWord := by
  intro paid
  have comparison := layered_history_iff persistentReceiver @messagePrice @stepPrice originalWord
    twoMessages collected (0 : Multiset Unit) (Multiset.replicate 5 ())
  rw [complete_price, complete_step_price] at comparison
  have impossible := (comparison.mp paid).2.1
  exact (by decide : ¬ Multiset.replicate 3 () ≤ (0 : Multiset Unit)) impossible

theorem pouring_that_money_funds_the_pooled_history :
    ∃ paid : OccurrencePath pooledSystem.presentation
      (marking twoMessages (Multiset.replicate 5 ()))
      (marking collected (Multiset.replicate 5 () - Multiset.replicate 5 ())),
        pooledSystem.pathEntries paid = originalWord := by
  have comparison := funded_history_iff persistentReceiver @sumPrice originalWord
    twoMessages collected (Multiset.replicate 5 ())
  rw [complete_pooled_price] at comparison
  exact comparison.mpr ⟨original_word_actually_fires, le_refl _⟩

theorem both_allocations_have_five_tokens :
    ((0 : Multiset Unit) + Multiset.replicate 5 ()).card =
      (Multiset.replicate 3 () + Multiset.replicate 2 ()).card := by decide

end Mettapedia.GSLT.Causality.ResourceInteraction.LayeredFundingHistoryControls
