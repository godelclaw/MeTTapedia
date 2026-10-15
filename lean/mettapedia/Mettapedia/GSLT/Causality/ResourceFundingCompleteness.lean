import Mettapedia.GSLT.Causality.ResourceRuns

/-!+# Exact funding of an independently supplied resource history

An unordered token purse funds a complete firing word exactly when the
original word is executable and the purse contains the sum of its prices.
The construction retains the original instances in their original order.
Prices are additional data; they need not be firing counts or host work.

This comparison concerns consumptive, unordered funding. Located ordered
keys require their own head and location tests.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule uTok

variable {R : Type uRes} {T : Type uTok}
  (S : System.{uRes, uRule} R)
  (price : ∀ {site : S.Site}, S.Instance site → Multiset T)

def historyPrice (order : List S.Entry) : Multiset T :=
  (order.map fun entry => price entry.2).sum

@[simp] theorem historyPrice_nil : historyPrice S @price [] = 0 := rfl

@[simp] theorem historyPrice_cons (entry : S.Entry) (rest : List S.Entry) :
    historyPrice S @price (entry :: rest) = price entry.2 + historyPrice S @price rest := rfl

theorem historyPrice_append (first second : List S.Entry) :
    historyPrice S @price (first ++ second) =
      historyPrice S @price first + historyPrice S @price second := by
  simp only [historyPrice, List.map_append, List.sum_append]

variable [DecidableEq R] [DecidableEq T]

theorem funded_fires_iff (order : List S.Entry)
    (source target : Multiset R) (budget remaining : Multiset T) :
    (funded S @price).Fires order (marking source budget) (marking target remaining) ↔
      S.Fires order source target ∧ budget = remaining + historyPrice S @price order := by
  constructor
  · intro fired
    obtain ⟨path, entries⟩ := (funded S @price).exists_path_of_fires order fired
    obtain ⟨originalTarget, remaining', endpoints, ⟨original, reads⟩, ledger⟩ :=
      S.funded_path_parts @price path
    have originalTargetEq : target = originalTarget := by
      simpa only [leftPart_marking] using congrArg leftPart endpoints
    have remainingEq : remaining = remaining' := by
      simpa only [rightPart_marking] using congrArg rightPart endpoints
    subst originalTarget
    subst remaining'
    refine ⟨?_, ?_⟩
    · have fires := S.fires_pathEntries original
      rwa [reads, entries] at fires
    · rwa [(funded S @price).instanceValuation_onPath @price, entries] at ledger
  · generalize order = word
    intro supplied
    induction word generalizing source budget with
    | nil =>
        obtain ⟨original, ledger⟩ := supplied
        change target = source at original
        have sameBudget : budget = remaining := by simpa only [historyPrice_nil, add_zero] using ledger
        subst target
        rw [sameBudget]
        rfl
    | cons entry rest ih =>
        obtain ⟨⟨enabled, originalRest⟩, ledger⟩ := supplied
        rw [historyPrice_cons] at ledger
        have present : price entry.2 ≤ budget := by
          rw [ledger]
          exact le_add_left (le_add_right (le_refl _))
        have remainder : budget - price entry.2 = remaining + historyPrice S @price rest := by
          rw [ledger, ← add_assoc, add_right_comm remaining (price entry.2),
            add_tsub_cancel_right]
        refine ⟨(funded_enables_iff S @price source budget entry.2).mpr ⟨enabled, present⟩, ?_⟩
        rw [funded_fire]
        exact ih (S.fire source entry.2) (budget - price entry.2) ⟨originalRest, remainder⟩

theorem funded_history_iff (order : List S.Entry)
    (source target : Multiset R) (budget : Multiset T) :
    (∃ path : OccurrencePath (funded S @price).presentation
      (marking source budget) (marking target (budget - historyPrice S @price order)),
        (funded S @price).pathEntries path = order) ↔
      S.Fires order source target ∧ historyPrice S @price order ≤ budget :=
  ((funded S @price).fires_iff_exists_path order).symm.trans
    ((funded_fires_iff S @price order source target budget _).trans
      (and_congr_right' (eq_comm.trans tsub_add_cancel_iff_le)))

theorem original_history_has_funding_iff {source target : Multiset R}
    (path : OccurrencePath S.presentation source target) (budget : Multiset T) :
    (∃ paid : OccurrencePath (funded S @price).presentation
      (marking source budget) (marking target (budget - historyPrice S @price (S.pathEntries path))),
        (funded S @price).pathEntries paid = S.pathEntries path) ↔
      historyPrice S @price (S.pathEntries path) ≤ budget := by
  rw [funded_history_iff]
  exact and_iff_right (S.fires_pathEntries path)

omit [DecidableEq R] in
theorem affordable_prefix (first rest : List S.Entry) (budget : Multiset T)
    (affordable : historyPrice S @price (first ++ rest) ≤ budget) :
    historyPrice S @price first ≤ budget ∧
      historyPrice S @price rest ≤ budget - historyPrice S @price first := by
  rw [historyPrice_append] at affordable
  exact ⟨(le_add_right (le_refl _)).trans affordable,
    le_tsub_of_add_le_left affordable⟩

end Mettapedia.GSLT.Causality.ResourceInteraction
