import Mettapedia.GSLT.Causality.ResourceFundingCompleteness

/-!
# Nonconstant prices on an actual two-receive resource history

Two original receives are executable. Their declared prices are one and two
tokens, so funding needs three tokens while the firing count remains two.
The exact comparison rejects budget two and accounts for every retained
prefix. Prices in this example are a policy, not measured runtime work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.ResourceFundingCompletenessControls

open OccurrenceHistory Controls

def messagePrice : ∀ {site : persistentReceiver.Site},
    persistentReceiver.Instance site → Multiset Unit :=
  fun {_site} => fun value : Nat => Multiset.replicate value ()

def originalWord : List persistentReceiver.Entry :=
  [⟨(), takeAgain 1⟩, ⟨(), takeAgain 2⟩]

def collected : Multiset Res := {Res.receiver, Res.received 1, Res.received 2}

def pricedSystem : System (Res ⊕ Unit) := funded persistentReceiver @messagePrice

theorem original_word_actually_fires :
    persistentReceiver.Fires originalWord twoMessages collected := by
  simp only [originalWord, System.Fires, System.Enables, System.fire, persistentReceiver]
  decide

theorem complete_price :
    historyPrice persistentReceiver @messagePrice originalWord = Multiset.replicate 3 () := by
  decide

theorem exact_budget_for_complete_history (amount : Nat) :
    (∃ paid : OccurrencePath pricedSystem.presentation
      (marking twoMessages (Multiset.replicate amount ()))
      (marking collected (Multiset.replicate amount () - Multiset.replicate 3 ())),
        pricedSystem.pathEntries paid = originalWord) ↔ 3 ≤ amount := by
  have comparison := funded_history_iff persistentReceiver @messagePrice originalWord
    twoMessages collected (Multiset.replicate amount ())
  rw [complete_price] at comparison
  exact comparison.trans
    ((and_iff_right original_word_actually_fires).trans (Multiset.replicate_le_replicate ()))

theorem three_tokens_supply_an_actual_history :
    ∃ paid : OccurrencePath pricedSystem.presentation
      (marking twoMessages (Multiset.replicate 3 ()))
      (marking collected (Multiset.replicate 3 () - Multiset.replicate 3 ())),
        pricedSystem.pathEntries paid = originalWord :=
  (exact_budget_for_complete_history 3).mpr (le_refl 3)

theorem two_tokens_cannot_supply_that_history :
    ¬ ∃ paid : OccurrencePath pricedSystem.presentation
      (marking twoMessages (Multiset.replicate 2 ()))
      (marking collected (Multiset.replicate 2 () - Multiset.replicate 3 ())),
        pricedSystem.pathEntries paid = originalWord := by
  intro supplied
  exact (by decide : ¬ (3 ≤ 2)) ((exact_budget_for_complete_history 2).mp supplied)

theorem price_is_not_the_firing_count :
    (historyPrice persistentReceiver @messagePrice originalWord).card = 3 ∧
      originalWord.length = 2 := by
  rw [complete_price]
  exact ⟨Multiset.card_replicate _ _, rfl⟩

theorem actual_prefix_has_the_exact_remaining_budget :
    historyPrice persistentReceiver @messagePrice [⟨(), takeAgain 1⟩] ≤ Multiset.replicate 3 () ∧
      historyPrice persistentReceiver @messagePrice [⟨(), takeAgain 2⟩] ≤
        Multiset.replicate 3 () -
          historyPrice persistentReceiver @messagePrice [⟨(), takeAgain 1⟩] := by
  apply affordable_prefix persistentReceiver @messagePrice
  change historyPrice persistentReceiver @messagePrice originalWord ≤ Multiset.replicate 3 ()
  rw [complete_price]

end Mettapedia.GSLT.Causality.ResourceInteraction.ResourceFundingCompletenessControls
