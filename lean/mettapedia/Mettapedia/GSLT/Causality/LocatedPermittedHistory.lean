import Mettapedia.GSLT.Causality.ResourceInstancePermission

/-!
# Located funding, permitted firings and complete history accounts

The construction pays only independently permitted instances, using the
existing located purse with the required key at its head. A supplied paid
path projects to an actual original path with exactly the original ordered
firings. Its cell account equals the number of those firings, while its
remaining purses retain their places and ordered tails.

The permission predicate and the physical purse are independent inputs.
Nothing here identifies their conjunction with a cost bound or asserts a
distributive law for arbitrary theory transformers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule

variable {R : Type uRes} {Place Cell : Type uRule}
  (S : System.{uRes, uRule} R)
  (permitted : ∀ {site : S.Site}, S.Instance site → Prop)
  (place : ∀ {site : S.Site}, S.Instance site → Place)
  (key : ∀ {site : S.Site}, S.Instance site → Cell)

def locatedPermitted : System.{max uRes uRule, uRule} (R ⊕ (Place × List Cell)) :=
  fundedAt (permittedSystem S permitted) (fun firing => place firing.val) (fun firing => key firing.val)

theorem locatedPermitted_enables_iff (resources : Multiset R)
    (purses : Multiset (Place × List Cell)) {site : S.Site}
    (firing : (permittedSystem S permitted).Instance site) (tail : List Cell) :
    (locatedPermitted S permitted place key).Enables (marking resources purses) (firing, tail) ↔
      S.Enables resources firing.val ∧ (place firing.val, key firing.val :: tail) ∈ purses :=
  fundedAt_enables_iff (permittedSystem S permitted) _ _ resources purses firing tail

theorem locatedPermitted_admission_iff (resources : Multiset R)
    (purses : Multiset (Place × List Cell)) {site : S.Site} (firing : S.Instance site) :
    (∃ admitted : (permittedSystem S permitted).Instance site,
      admitted.val = firing ∧ ∃ tail : List Cell,
        (locatedPermitted S permitted place key).Enables (marking resources purses) (admitted, tail)) ↔
      permitted firing ∧ S.Enables resources firing ∧
        ∃ tail : List Cell, (place firing, key firing :: tail) ∈ purses := by
  constructor
  · rintro ⟨admitted, rfl, tail, enabled⟩
    obtain ⟨enabledOriginal, present⟩ :=
      (locatedPermitted_enables_iff S permitted place key resources purses admitted tail).mp enabled
    exact ⟨admitted.property, enabledOriginal, tail, present⟩
  · rintro ⟨permission, enabled, tail, present⟩
    exact ⟨⟨firing, permission⟩, rfl, tail,
      (locatedPermitted_enables_iff S permitted place key resources purses ⟨firing, permission⟩ tail).mpr
        ⟨enabled, present⟩⟩

def locatedOriginalEntry (entry : (locatedPermitted S permitted place key).Entry) : S.Entry :=
  ⟨entry.1, entry.2.1.val⟩

variable [DecidableEq R] [DecidableEq Place] [DecidableEq Cell]

theorem locatedPermitted_fire (resources : Multiset R) (purses : Multiset (Place × List Cell))
    {site : S.Site} (firing : (permittedSystem S permitted).Instance site) (tail : List Cell) :
    (locatedPermitted S permitted place key).fire (marking resources purses) (firing, tail) =
      marking (S.fire resources firing.val)
        ((place firing.val, tail) ::ₘ purses.erase (place firing.val, key firing.val :: tail)) :=
  fundedAt_fire (permittedSystem S permitted) _ _ resources purses firing tail

theorem locatedPermitted_original_path {resources : Multiset R}
    {purses : Multiset (Place × List Cell)} {target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation
      (marking resources purses) target) :
    ∃ original : OccurrencePath S.presentation resources (leftPart target),
      S.pathEntries original =
        ((locatedPermitted S permitted place key).pathEntries path).map
          (locatedOriginalEntry S permitted place key) := by
  obtain ⟨resources', purses', same, ⟨admitted, entries⟩, _⟩ :=
    (permittedSystem S permitted).product_path_parts (pursesMany Place Cell)
      (Site := S.Site)
      (Joint := fun site => (permittedSystem S permitted).Instance site × List Cell)
      (fun {site} (firing : (permittedSystem S permitted).Instance site × List Cell) => ⟨site, firing.1⟩)
      (fun {site} (firing : (permittedSystem S permitted).Instance site × List Cell) =>
        ⟨place firing.1.val, ({(key firing.1.val, firing.2)} : Multiset (Cell × List Cell))⟩)
      (A := resources) (B := purses) (N := target) path
  subst same
  rw [leftPart_marking]
  refine ⟨forgetPermissionPath S permitted admitted, ?_⟩
  rw [forgetPermissionPath_entries, entries, List.map_map]
  rfl

theorem locatedPermitted_entries_permitted {source target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation source target) :
    ∀ entry ∈ ((locatedPermitted S permitted place key).pathEntries path).map
      (locatedOriginalEntry S permitted place key), permitted entry.2 := by
  intro entry member
  obtain ⟨paid, _, rfl⟩ := List.mem_map.mp member
  exact paid.2.1.property

private theorem unit_account_eq_length
    {Q : Type uRes} [DecidableEq Q] (system : System.{uRes, uRule} Q) :
    ∀ {source target : Multiset Q} (path : OccurrencePath system.presentation source target),
      (system.instanceValuation fun _ => (1 : Nat)).onPath path = (system.pathEntries path).length
  | _, _, .refl _ => rfl
  | _, _, .cons _ rest => by
      change 1 + (system.instanceValuation fun _ => (1 : Nat)).onPath rest =
        (system.pathEntries rest).length + 1
      rw [unit_account_eq_length system rest, Nat.add_comm]

theorem locatedPermitted_history_ledger {resources : Multiset R}
    {purses : Multiset (Place × List Cell)} {target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation
      (marking resources purses) target) :
    cells purses = cells (rightPart target) +
      ((locatedPermitted S permitted place key).pathEntries path).length := by
  have ledger := fundedAt_run_cells (permittedSystem S permitted)
    (fun firing => place firing.val) (fun firing => key firing.val) path
  exact ledger.trans (congrArg (cells (rightPart target) + ·)
    (unit_account_eq_length (locatedPermitted S permitted place key) path))

theorem locatedPermitted_original_history_ledger {resources : Multiset R}
    {purses : Multiset (Place × List Cell)} {target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation
      (marking resources purses) target) :
    ∃ original : OccurrencePath S.presentation resources (leftPart target),
      S.pathEntries original =
        ((locatedPermitted S permitted place key).pathEntries path).map
          (locatedOriginalEntry S permitted place key) ∧
      (∀ entry ∈ S.pathEntries original, permitted entry.2) ∧
      cells purses = cells (rightPart target) + (S.pathEntries original).length := by
  obtain ⟨original, reads⟩ := locatedPermitted_original_path S permitted place key path
  refine ⟨original, reads, ?_, ?_⟩
  · rw [reads]
    exact locatedPermitted_entries_permitted S permitted place key path
  · rw [reads, List.length_map]
    exact locatedPermitted_history_ledger S permitted place key path

theorem locatedPermitted_firing_bound {resources : Multiset R}
    {purses : Multiset (Place × List Cell)} {target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation
      (marking resources purses) target) :
    ((locatedPermitted S permitted place key).pathEntries path).length ≤ cells purses := by
  have ledger := locatedPermitted_history_ledger S permitted place key path
  omega

theorem locatedPermitted_total_payment_recoverable (resources : Multiset R)
    (purses : Multiset (Place × List Cell)) :
    HistoryMonad.StateRecoverable
      (P := (locatedPermitted S permitted place key).presentation) (root := marking resources purses)
      (fun {_} path => ((locatedPermitted S permitted place key).pathEntries path).length) := by
  refine ⟨fun target => cells purses - cells (rightPart target), fun {target} path => ?_⟩
  change ((locatedPermitted S permitted place key).pathEntries path).length =
    cells purses - cells (rightPart target)
  have ledger := locatedPermitted_history_ledger S permitted place key path
  omega

def locatedPermittedSpentKeys {source target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation source target) : Multiset Cell :=
  (((locatedPermitted S permitted place key).pathEntries path).map
    (fun entry => ({key entry.2.1.val} : Multiset Cell))).sum

theorem locatedPermitted_exact_key_ledger {resources : Multiset R}
    {purses : Multiset (Place × List Cell)} {target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation
      (marking resources purses) target) :
    cellBag purses = cellBag (rightPart target) +
      locatedPermittedSpentKeys S permitted place key path := by
  have ledger := (locatedPermitted S permitted place key).balance_taken
    (fun marking => cellBag (rightPart marking)) rfl
    (fun first second => by rw [rightPart_add, cellBag_add])
    (fun firing => ({key firing.1.val} : Multiset Cell))
    (fun firing => by
      change cellBag (rightPart (marking (S.consume firing.1.val)
          (({(key firing.1.val, firing.2)} : Multiset (Cell × List Cell)).map
            fun purse => (place firing.1.val, purse.1 :: purse.2)))) =
        {key firing.1.val} + cellBag (rightPart (marking (S.produce firing.1.val)
          (({(key firing.1.val, firing.2)} : Multiset (Cell × List Cell)).map
            fun purse => (place firing.1.val, purse.2))))
      rw [rightPart_marking, rightPart_marking, cellBag_chosen, Multiset.map_singleton]) path
  rw [rightPart_marking, (locatedPermitted S permitted place key).instanceValuation_onPath] at ledger
  exact ledger

end Mettapedia.GSLT.Causality.ResourceInteraction
