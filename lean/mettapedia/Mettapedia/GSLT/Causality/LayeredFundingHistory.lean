import Mettapedia.GSLT.Causality.ResourceFundingCompleteness

/-!
# Complete histories funded from separate layers

Each layer must afford its own complete price word. Pooling the two purses
can authorize a history that neither layered allocation authorizes. The
comparison retains the actual original instances and chronological order,
and instantiates the existing graded paying construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule uTok

variable {R : Type uRes} {T : Type uTok}
  (S : System.{uRes, uRule} R)
  (inner outer : ∀ {site : S.Site}, S.Instance site → Multiset T)
  [DecidableEq R] [DecidableEq T]

theorem layered_fires_iff (order : List S.Entry)
    (source target : Multiset R)
    (innerBudget innerRemaining outerBudget outerRemaining : Multiset T) :
    (fundedTwice S @inner @outer).Fires order
      (marking (marking source innerBudget) outerBudget)
      (marking (marking target innerRemaining) outerRemaining) ↔
      S.Fires order source target ∧
        innerBudget = innerRemaining + historyPrice S @inner order ∧
        outerBudget = outerRemaining + historyPrice S @outer order := by
  have outside := funded_fires_iff (funded S @inner) @outer order
    (marking source innerBudget) (marking target innerRemaining) outerBudget outerRemaining
  have inside := funded_fires_iff S @inner order source target innerBudget innerRemaining
  have outerPrice : historyPrice (funded S @inner) @outer order = historyPrice S @outer order := rfl
  rw [inside, outerPrice] at outside
  exact outside.trans and_assoc

theorem layered_history_iff (order : List S.Entry)
    (source target : Multiset R) (innerBudget outerBudget : Multiset T) :
    (∃ paid : OccurrencePath (fundedTwice S @inner @outer).presentation
      (marking (marking source innerBudget) outerBudget)
      (marking (marking target (innerBudget - historyPrice S @inner order))
        (outerBudget - historyPrice S @outer order)),
        (fundedTwice S @inner @outer).pathEntries paid = order) ↔
      S.Fires order source target ∧
        historyPrice S @inner order ≤ innerBudget ∧
        historyPrice S @outer order ≤ outerBudget := by
  have word := ((fundedTwice S @inner @outer).fires_iff_exists_path order).symm.trans
    (layered_fires_iff S @inner @outer order source target innerBudget
      (innerBudget - historyPrice S @inner order) outerBudget
      (outerBudget - historyPrice S @outer order))
  exact word.trans (and_congr_right'
    (and_congr (eq_comm.trans tsub_add_cancel_iff_le) (eq_comm.trans tsub_add_cancel_iff_le)))

omit [DecidableEq R] [DecidableEq T] in
theorem pooled_price (order : List S.Entry) :
    historyPrice S (fun firing => inner firing + outer firing) order =
      historyPrice S @inner order + historyPrice S @outer order := by
  induction order with
  | nil => simp only [historyPrice_nil, add_zero]
  | cons entry rest ih =>
      simp only [historyPrice_cons, ih]
      exact add_add_add_comm _ _ _ _

omit [DecidableEq R] [DecidableEq T] in
theorem layered_affordability_implies_pooled (order : List S.Entry)
    (innerBudget outerBudget : Multiset T)
    (inside : historyPrice S @inner order ≤ innerBudget)
    (outside : historyPrice S @outer order ≤ outerBudget) :
    historyPrice S (fun firing => inner firing + outer firing) order ≤ innerBudget + outerBudget := by
  rw [pooled_price]
  exact add_le_add inside outside

end Mettapedia.GSLT.Causality.ResourceInteraction
