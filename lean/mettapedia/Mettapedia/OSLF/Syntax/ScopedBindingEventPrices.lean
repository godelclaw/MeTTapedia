import Mettapedia.OSLF.Syntax.ScopedBindingEquationResources

/-!
# Event-sensitive prices and exact substitution admission

Prices may inspect a complete permitted event, including its equation-class
endpoints and binding origin. Funding is still an actual paid occurrence
path. Preserving funding at every budget under a supplied substitution is
equivalent to equality of the two event prices. A bound or a transported
native certificate alone cannot replace this condition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedBindingEventPrices

open ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe r

variable {S : Signature} {M : List (MetaArity S)} {Index : Type r}
  (E : List (EqAxiom S M)) (rules : Index → UnpositionedRewrite (withMetas S M))
  (permission : PositionPermission S) (scope : Scope S)

noncomputable section

local instance : DecidableEq (State E scope) := Classical.decEq _

def price (profile : Event rules permission scope → Nat) :
    ∀ {index : Index}, (ScopedEquationResources.resources E rules permission scope).Instance index → Multiset Unit :=
  fun {_index} firing => Multiset.replicate (profile firing.val) ()

def paid (profile : Event rules permission scope → Nat) : System (State E scope ⊕ Unit) :=
  funded (ScopedEquationResources.resources E rules permission scope) (price E rules permission scope profile)

structure Funding (profile : Event rules permission scope → Nat)
    (event : Event rules permission scope) (amount : Nat) where
  path : OccurrencePath (paid E rules permission scope profile).presentation
    (marking {event.sourceClass E} (Multiset.replicate amount ()))
    (marking {event.targetClass E} (Multiset.replicate amount () - Multiset.replicate (profile event) ()))
  entries : (paid E rules permission scope profile).pathEntries path =
    [ScopedEquationResources.entry E rules permission scope event]

theorem funding_iff (profile : Event rules permission scope → Nat)
    (event : Event rules permission scope) (amount : Nat) :
    Nonempty (Funding E rules permission scope profile event amount) ↔ profile event ≤ amount := by
  let system := ScopedEquationResources.resources E rules permission scope
  let entry := ScopedEquationResources.entry E rules permission scope event
  have charge : historyPrice system (price E rules permission scope profile) [entry] =
      Multiset.replicate (profile event) () := by
    change Multiset.replicate (profile event) () + 0 = _
    exact add_zero _
  have executable := system.fires_pathEntries (ScopedEquationResources.history E rules permission scope event)
  rw [ScopedEquationResources.history_entries] at executable
  have comparison := funded_history_iff system (price E rules permission scope profile)
    [entry] ({event.sourceClass E} : Multiset (State E scope))
    ({event.targetClass E} : Multiset (State E scope)) (Multiset.replicate amount ())
  rw [charge] at comparison
  have exactPrice := comparison.trans ((and_iff_right executable).trans (Multiset.replicate_le_replicate ()))
  constructor
  · rintro ⟨funding⟩
    exact exactPrice.mp ⟨funding.path, funding.entries⟩
  · intro affordable
    obtain ⟨path, entries⟩ := exactPrice.mpr affordable
    exact ⟨⟨path, entries⟩⟩

theorem Funding.retains_event {profile : Event rules permission scope → Nat}
    {event : Event rules permission scope} {amount : Nat}
    (funding : Funding E rules permission scope profile event amount) :
    ((paid E rules permission scope profile).pathEntries funding.path).map (fun entry => entry.2.val) =
      [event] := by
  rw [funding.entries]
  rfl

theorem substitution_funding_iff_price
    (profile : Event rules permission scope → Nat) (destination : Ctx S)
    (destinationProfile : Event rules permission (destination, scope.2) → Nat)
    (sigma : Sub S scope.1 destination) (event : Event rules permission scope) :
    (∀ amount, Nonempty (Funding E rules permission (destination, scope.2)
      destinationProfile (event.map destination sigma) amount) ↔
        Nonempty (Funding E rules permission scope profile event amount)) ↔
      destinationProfile (event.map destination sigma) = profile event := by
  constructor
  · intro compares
    have lower := (compares (profile event)).mpr
      ((funding_iff E rules permission scope profile event _).mpr (le_refl _))
    have upper := (compares (destinationProfile (event.map destination sigma))).mp
      ((funding_iff E rules permission _ destinationProfile (event.map destination sigma) _).mpr (le_refl _))
    exact Nat.le_antisymm
      ((funding_iff E rules permission _ destinationProfile _ _).mp lower)
      ((funding_iff E rules permission scope profile event _).mp upper)
  · intro equal amount
    rw [funding_iff, funding_iff, equal]

end

end Mettapedia.OSLF.Binding.ScopedBindingEventPrices
