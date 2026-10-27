import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# Escrow: a fungible budget spent without coordination

A budget of `total` units is split into **shares**, one per location. A location spends from its
own share without asking anyone. Coordination is needed only to **rebalance**: a location sends
part of its share to another as a transfer message, and the receiver adds it once.

**Fault model.** Locations do not lose their state. Transfer messages are kept in a durable outbox
(`sent`) and may be delivered late, out of order and any number of times; a delivery of a message
that was never sent is ignored (transfers are authenticated by their sender). Each transfer has a
fresh identifier, and the receiver remembers the identifiers it has applied (`applied`).

## Conservation and no overspend

* **Conservation** (`conservation`): in every run, the shares, the units spent and the transfers in
  flight add up to the budget.
* **No overspend** (`no_overspend`): the units spent never exceed the budget, whatever the
  interleaving of spends, transfers and repeated deliveries.

## Refinement of the central budget

* **Every step is a central step** (`step_refines`): read through the remaining budget and the log
  of spends, a local spend is a spend of the central budget that the central budget allows, and a
  transfer or delivery changes nothing.

## Costs and controls

* **Eight concurrent spenders** (`Controls.eight_spenders_bounded`, `Controls.eight_spend_all`):
  eight locations with one unit each never spend more than eight, and a ninth spend is refused
  locally.
* **A spend larger than the local share waits for a rebalance**
  (`Controls.large_spend_needs_rebalance`): it is refused although the central budget allows it,
  and accepted once a transfer arrives.
* **Replicated copies of the whole budget overspend** (`Controls.replicated_overspend`).
* **Applying a transfer twice creates budget** (`Controls.without_dedup_overspend`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.Escrow

open scoped BigOperators

universe u

/-- A transfer of part of a share. -/
structure Transfer (L : Type u) where
  id : ℕ
  source : L
  target : L
  amount : ℕ
  deriving DecidableEq

/-- The escrow state. -/
structure State (L : Type u) [DecidableEq L] where
  share : L → ℕ
  spent : L → ℕ
  sent : Finset (Transfer L)
  applied : L → Finset ℕ
  spends : List (L × ℕ)

/-- An event: a local spend, a transfer sent, or a delivery of a transfer. -/
inductive Event (L : Type u) where
  | spend (site : L) (amount : ℕ)
  | send (id : ℕ) (source target : L) (amount : ℕ)
  | deliver (transfer : Transfer L)

variable {L : Type u} [DecidableEq L] [Fintype L]

/-- One event. -/
def step (s : State L) : Event L → State L
  | .spend site amount =>
      if amount ≤ s.share site then
        { s with
          share := Function.update s.share site (s.share site - amount)
          spent := Function.update s.spent site (s.spent site + amount)
          spends := s.spends ++ [(site, amount)] }
      else s
  | .send id source target amount =>
      if amount ≤ s.share source ∧ ∀ t ∈ s.sent, t.id ≠ id then
        { s with
          share := Function.update s.share source (s.share source - amount)
          sent := insert ⟨id, source, target, amount⟩ s.sent }
      else s
  | .deliver t =>
      if t ∈ s.sent ∧ t.id ∉ s.applied t.target then
        { s with
          share := Function.update s.share t.target (s.share t.target + t.amount)
          applied := Function.update s.applied t.target (insert t.id (s.applied t.target)) }
      else s

/-- A run. -/
def run (s : State L) : List (Event L) → State L
  | [] => s
  | e :: es => run (step s e) es

/-- The units in flight: sent and not yet applied. -/
def inflight (s : State L) : ℕ :=
  ∑ t ∈ s.sent, if t.id ∈ s.applied t.target then 0 else t.amount

/-- The total held: shares, spent and in flight. -/
def held (s : State L) : ℕ := (∑ site, s.share site) + (∑ site, s.spent site) + inflight s

/-- The state's invariant: transfer identifiers are unique, and only sent transfers are applied. -/
structure Inv (s : State L) : Prop where
  uniqueIds : ∀ t ∈ s.sent, ∀ t' ∈ s.sent, t.id = t'.id → t = t'
  appliedSent : ∀ site, ∀ id ∈ s.applied site, ∃ t ∈ s.sent, t.id = id

omit [DecidableEq L] in
theorem sum_update_add (f : L → ℕ) (site : L) (value : ℕ) [DecidableEq L] :
    (∑ x, Function.update f site value x) + f site = (∑ x, f x) + value := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ site),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ site), Finset.sdiff_singleton_eq_erase]
  omega

theorem held_step {s : State L} (inv : Inv s) (e : Event L) : held (step s e) = held s := by
  cases e with
  | spend site amount =>
      simp only [step]
      split_ifs with enough
      · have shareSum := sum_update_add s.share site (s.share site - amount)
        have spentSum := sum_update_add s.spent site (s.spent site + amount)
        simp only [held, inflight]
        omega
      · rfl
  | send id source target amount =>
      simp only [step]
      split_ifs with ok
      · obtain ⟨enough, fresh⟩ := ok
        have notSent : (⟨id, source, target, amount⟩ : Transfer L) ∉ s.sent :=
          fun member => fresh _ member rfl
        have notApplied : id ∉ s.applied target := fun member => by
          obtain ⟨t, inSent, same⟩ := inv.appliedSent target id member
          exact fresh t inSent same
        have shareSum := sum_update_add s.share source (s.share source - amount)
        simp only [held, inflight, Finset.sum_insert notSent, notApplied, if_false]
        omega
      · rfl
  | deliver t =>
      simp only [step]
      split_ifs with ok
      · obtain ⟨inSent, notApplied⟩ := ok
        have shareSum := sum_update_add s.share t.target (s.share t.target + t.amount)
        -- in flight, only `t` changes: from its amount to nothing
        have flight : (∑ t' ∈ s.sent, if t'.id ∈ Function.update s.applied t.target
            (insert t.id (s.applied t.target)) t'.target then 0 else t'.amount) + t.amount =
            ∑ t' ∈ s.sent, if t'.id ∈ s.applied t'.target then 0 else t'.amount := by
          rw [← Finset.sum_erase_add _ _ inSent, ← Finset.sum_erase_add _ _ inSent]
          have others : ∀ t' ∈ s.sent.erase t,
              (if t'.id ∈ Function.update s.applied t.target (insert t.id (s.applied t.target))
                t'.target then 0 else t'.amount) =
              if t'.id ∈ s.applied t'.target then 0 else t'.amount := by
            intro t' member
            obtain ⟨apart, inSent'⟩ := Finset.mem_erase.mp member
            have idApart : t'.id ≠ t.id := fun same => apart (inv.uniqueIds t' inSent' t inSent same)
            by_cases sameTarget : t'.target = t.target
            · simp only [sameTarget, Function.update_self, Finset.mem_insert, idApart, false_or]
            · simp only [Function.update_of_ne sameTarget]
          rw [Finset.sum_congr rfl others]
          simp [notApplied]
        simp only [held, inflight] at flight ⊢
        omega
      · rfl

omit [Fintype L] in
theorem inv_step {s : State L} (inv : Inv s) (e : Event L) : Inv (step s e) := by
  cases e with
  | spend site amount =>
      simp only [step]
      split_ifs
      · exact ⟨inv.uniqueIds, inv.appliedSent⟩
      · exact inv
  | send id source target amount =>
      simp only [step]
      split_ifs with ok
      · obtain ⟨_, fresh⟩ := ok
        refine ⟨fun t member t' member' same => ?_, fun site i member => ?_⟩
        · rcases Finset.mem_insert.mp member with rfl | old <;>
            rcases Finset.mem_insert.mp member' with rfl | old'
          · rfl
          · exact absurd same.symm (fresh _ old')
          · exact absurd same (fresh _ old)
          · exact inv.uniqueIds t old t' old' same
        · obtain ⟨t, inSent, same⟩ := inv.appliedSent site i member
          exact ⟨t, Finset.mem_insert_of_mem inSent, same⟩
      · exact inv
  | deliver t =>
      simp only [step]
      split_ifs with ok
      · refine ⟨inv.uniqueIds, fun site i member => ?_⟩
        by_cases same : site = t.target
        · subst same
          simp only [Function.update_self, Finset.mem_insert] at member
          rcases member with rfl | old
          · exact ⟨t, ok.1, rfl⟩
          · exact inv.appliedSent _ i old
        · simp only [Function.update_of_ne same] at member
          exact inv.appliedSent site i member
      · exact inv

/-- A start: shares, nothing spent or sent. -/
def start (shares : L → ℕ) : State L := ⟨shares, fun _ => 0, ∅, fun _ => ∅, []⟩

omit [Fintype L] in
theorem inv_start (shares : L → ℕ) : Inv (start shares) :=
  ⟨fun _ member => by simp [start] at member, fun _ _ member => by simp [start] at member⟩

omit [Fintype L] in
theorem inv_run {s : State L} (inv : Inv s) (events : List (Event L)) : Inv (run s events) := by
  induction events generalizing s with
  | nil => exact inv
  | cons e rest ih => exact ih (inv_step inv e)

theorem held_run {s : State L} (inv : Inv s) (events : List (Event L)) :
    held (run s events) = held s := by
  induction events generalizing s with
  | nil => rfl
  | cons e rest ih => exact (ih (inv_step inv e)).trans (held_step inv e)

/-- **Conservation**: shares, units spent and transfers in flight add up to the budget. -/
theorem conservation (shares : L → ℕ) (events : List (Event L)) :
    held (run (start shares) events) = ∑ site, shares site := by
  rw [held_run (inv_start shares) events]
  simp [held, inflight, start]

/-- **No overspend.** -/
theorem no_overspend (shares : L → ℕ) (events : List (Event L)) :
    (∑ site, (run (start shares) events).spent site) ≤ ∑ site, shares site := by
  have := conservation shares events
  simp only [held] at this
  omega

/-! ## Refinement of the central budget -/

/-- The central budget: what remains, and the spends in order. -/
structure Central (L : Type u) where
  remaining : ℕ
  log : List (L × ℕ)

/-- A central spend. -/
def Central.spend (c : Central L) (site : L) (amount : ℕ) : Central L :=
  ⟨c.remaining - amount, c.log ++ [(site, amount)]⟩

/-- What the escrow shows of the central budget. -/
def central (total : ℕ) (s : State L) : Central L := ⟨total - ∑ site, s.spent site, s.spends⟩

/-- **Every step is a central step**: a transfer or a delivery changes nothing central, and an
accepted local spend is a spend the central budget allows. -/
theorem step_refines {total : ℕ} {s : State L} (bounded : held s = total)
    (e : Event L) :
    central total (step s e) = central total s ∨
      ∃ site amount, amount ≤ (central total s).remaining ∧
        central total (step s e) = (central total s).spend site amount := by
  cases e with
  | spend site amount =>
      simp only [step]
      split_ifs with enough
      · right
        refine ⟨site, amount, ?_, ?_⟩
        · have shareLe : s.share site ≤ ∑ x, s.share x :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ site)
          simp only [central, held] at bounded ⊢
          omega
        · have spentSum := sum_update_add s.spent site (s.spent site + amount)
          simp only [central, Central.spend, Central.mk.injEq, and_true]
          omega
      · left; rfl
  | send id source target amount =>
      left
      simp only [step]
      split_ifs <;> rfl
  | deliver t =>
      left
      simp only [step]
      split_ifs <;> rfl

/-! ## Controls -/

namespace Controls

/-- Eight locations with one unit each. -/
def eightShares : Fin 8 → ℕ := fun _ => 1

/-- **Eight concurrent spenders never spend more than eight**, in any interleaving. -/
theorem eight_spenders_bounded (events : List (Event (Fin 8))) :
    (∑ site, (run (start eightShares) events).spent site) ≤ 8 := by
  have := no_overspend eightShares events
  simpa [eightShares, Finset.card_univ, Fintype.card_fin] using this

/-- Each of the eight spends its unit; a ninth spend, at any location, is refused locally. -/
def allSpend : List (Event (Fin 8)) := (List.finRange 8).map fun site => .spend site 1

theorem eight_spend_all :
    (∑ site, (run (start eightShares) allSpend).spent site) = 8 ∧
      (run (start eightShares) (allSpend ++ [.spend 3 1])).spends.length = 8 := by
  decide

/-- Two locations with one unit each. -/
def twoShares : Bool → ℕ := fun _ => 1

/-- **A spend larger than the local share waits for a rebalance**: spending two at `true` is
refused although two units remain centrally; after `false` sends its unit and it arrives, it is
accepted. -/
theorem large_spend_needs_rebalance :
    (run (start twoShares) [.spend true 2]).spends = [] ∧
      (run (start twoShares) [.send 7 false true 1, .deliver ⟨7, false, true, 1⟩, .spend true 2]).spends =
        [(true, 2)] := by
  decide

/-- Repeated delivery of one transfer is applied once. -/
theorem repeated_delivery_once :
    (run (start twoShares) [.send 7 false true 1, .deliver ⟨7, false, true, 1⟩,
      .deliver ⟨7, false, true, 1⟩]).share true = 2 := by
  decide

/-- **Replicated copies of the whole budget overspend**: each location keeps a counter of the
spends it has heard of, checks the whole budget against it, and merges counters by maximum. Two
locations each spend the whole budget of `2` before hearing of the other. -/
theorem replicated_overspend :
    let spendAt := fun (seen : Bool → ℕ) (site : Bool) (amount : ℕ) =>
      if seen true + seen false + amount ≤ 2 then Function.update seen site (seen site + amount) else seen
    let atTrue := spendAt (fun _ => 0) true 2
    let atFalse := spendAt (fun _ => 0) false 2
    let merged := fun site => max (atTrue site) (atFalse site)
    merged true + merged false = 4 := by
  decide

/-- The delivery rule without deduplication. -/
def deliverBlind (s : State Bool) (t : Transfer Bool) : State Bool :=
  if t ∈ s.sent then
    { s with share := Function.update s.share t.target (s.share t.target + t.amount) }
  else s

/-- **Applying a transfer twice creates budget**: with a budget of two, `false` ends up spending
two after receiving one unit twice, so three units are spent. -/
theorem without_dedup_overspend :
    let afterSend := run (start twoShares) [.send 7 true false 1]
    let doubled := deliverBlind (deliverBlind afterSend ⟨7, true, false, 1⟩) ⟨7, true, false, 1⟩
    let spentAll := run doubled [.spend false 3]
    spentAll.spent false = 3 ∧ (∑ site, twoShares site) = 2 := by
  decide

end Controls

end Mettapedia.GSLT.Coordination.Escrow
