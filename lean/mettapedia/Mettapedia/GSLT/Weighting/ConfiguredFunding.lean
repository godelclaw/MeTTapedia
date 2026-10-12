import Mettapedia.GSLT.Weighting.WeightTheory
import Mettapedia.GSLT.Causality.ResourceFundingCompleteness
import Mathlib.Data.Multiset.Replicate

/-!
# Funding actual weighted configurations

An instance retains a presented event and its complete input weight map. Its
linear state presentation consumes that configuration and produces the actual
updated configuration. The unordered purse comparison retains the whole
instance, including the event's origin and the map used to price it.

This presentation concerns supplied events at their actual representatives.
Equation-invariant classification, a complete event catalogue and a concrete
execution backend are separate admission conditions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.ConfiguredFunding

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe uTerm uSite uEvent uKey uCtx uR

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}
  {K : Keyed.{uTerm, uSite, uEvent, uKey} P} {R : Type uR}

structure Firing (K : Keyed P) (R : Type uR) (site : P.Site) where
  source : theory.Term
  target : theory.Term
  evidence : P.Event site source target
  weights : WeightMap K R

variable (A : Augmented.{uTerm, uSite, uEvent, uKey, uCtx, uR} K R)

def before {site : P.Site} (firing : Firing K R site) : theory.Term × WeightMap K R :=
  (firing.source, firing.weights)

def after {site : P.Site} (firing : Firing K R site) : theory.Term × WeightMap K R :=
  (firing.target, A.next firing.evidence firing.weights)

def resources : System.{max uTerm uSite uKey uR, max uTerm uSite uEvent uKey uR}
    (theory.Term × WeightMap K R) where
  Site := ULift.{max uTerm uEvent uKey uR} P.Site
  Instance site := Firing K R site.down
  consume firing := {before firing}
  read _ := 0
  produce firing := {after A firing}

def entry {site : P.Site} (firing : Firing K R site) : (resources A).Entry :=
  ⟨⟨site⟩, firing⟩

theorem enabled_iff (inventory : Multiset (theory.Term × WeightMap K R))
    {site : P.Site} (firing : Firing K R site) :
    (resources A).Enables inventory (site := ⟨site⟩) firing ↔ before firing ∈ inventory := by
  simp only [System.Enables, resources, add_zero, Multiset.singleton_le]

theorem weighted_step {site : P.Site} (firing : Firing K R site) :
    A.weightedTheory.Step (before firing) (after A firing) :=
  A.step_of_event firing.evidence firing.weights

noncomputable section

local instance : DecidableEq (theory.Term × WeightMap K R) := Classical.decEq _

def occurrence {site : P.Site} (firing : Firing K R site) :
    Occurrence (resources A).presentation
      ({before firing} : Multiset (theory.Term × WeightMap K R))
      ({after A firing} : Multiset (theory.Term × WeightMap K R)) :=
  ⟨⟨site⟩, ⟨firing,
    (enabled_iff A _ firing).mpr (Multiset.mem_singleton_self _), by
      change {after A firing} = ({before firing} : Multiset _) - {before firing} + {after A firing}
      rw [tsub_self, zero_add]⟩⟩

def history {site : P.Site} (firing : Firing K R site) :
    OccurrencePath (resources A).presentation
      ({before firing} : Multiset (theory.Term × WeightMap K R))
      ({after A firing} : Multiset (theory.Term × WeightMap K R)) :=
  .cons (occurrence A firing) (.refl _)

theorem history_entries {site : P.Site} (firing : Firing K R site) :
    (resources A).pathEntries (history A firing) = [entry A firing] := rfl

def price (profile : (Σ site, K.Key site) → WeightMap K R → Nat) :
    ∀ {site : (resources A).Site}, (resources A).Instance site → Multiset Unit :=
  fun {_site} firing => Multiset.replicate
    (profile (Augmented.keyOf (K := K) firing.evidence) firing.weights) ()

def paid (profile : (Σ site, K.Key site) → WeightMap K R → Nat) :
    System ((theory.Term × WeightMap K R) ⊕ Unit) :=
  funded (resources A) (price A profile)

def budget (amount : Nat) : Multiset Unit := Multiset.replicate amount ()

structure PaidHistory (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    {site : P.Site} (firing : Firing K R site) (amount : Nat) where
  path : OccurrencePath (paid A profile).presentation
    (marking {before firing} (budget amount))
    (marking {after A firing}
      (budget amount - budget (profile (Augmented.keyOf (K := K) firing.evidence) firing.weights)))
  entries : (paid A profile).pathEntries path = [entry A firing]

theorem paid_history_iff (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    {site : P.Site} (firing : Firing K R site) (amount : Nat) :
    Nonempty (PaidHistory A profile firing amount) ↔
      profile (Augmented.keyOf (K := K) firing.evidence) firing.weights ≤ amount := by
  have charge : historyPrice (resources A) (price A profile) [entry A firing] =
      budget (profile (Augmented.keyOf (K := K) firing.evidence) firing.weights) := by
    change budget _ + 0 = budget _
    exact add_zero _
  have executable := (resources A).fires_pathEntries (history A firing)
  rw [history_entries] at executable
  have comparison := funded_history_iff (resources A) (price A profile)
    [entry A firing] {before firing} {after A firing} (budget amount)
  rw [charge] at comparison
  have exactPrice := comparison.trans
    ((and_iff_right executable).trans (Multiset.replicate_le_replicate ()))
  constructor
  · rintro ⟨funding⟩
    exact exactPrice.mp ⟨funding.path, funding.entries⟩
  · intro affordable
    obtain ⟨path, entries⟩ := exactPrice.mpr affordable
    exact ⟨⟨path, entries⟩⟩

theorem PaidHistory.retains_firing
    {profile : (Σ site, K.Key site) → WeightMap K R → Nat}
    {site : P.Site} {firing : Firing K R site} {amount : Nat}
    (funding : PaidHistory A profile firing amount) :
    ((paid A profile).pathEntries funding.path).map
      (fun item => (⟨item.1.down, item.2⟩ : (Σ site, Firing K R site))) =
        [⟨site, firing⟩] := by
  rw [funding.entries]
  rfl

end

end Mettapedia.GSLT.Weighting.ConfiguredFunding
