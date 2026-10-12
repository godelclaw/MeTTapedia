import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Consume
import Mettapedia.Logic.HostingStyles.ContextReadings.Conservation

/-!
# `consume` keeps tokens; the read of the two-step form doubles them

`Logic.HostingStyles.ContextReadings.Conservation` separates two readings of a
store.  In a presented language, the consuming receive keeps the tokens of the
datum (`take_keeps_tokens`) and the read doubles them (`read_doubles_tokens`).
On a network of occurrence stores, a consuming receive between two locations
keeps the occurrences of every atom (`consumingReceive_count`) and an observing
one adds an occurrence of the datum (`observingReceive_count`).

This module places the two forms of `Regions.Consume` on both pairs.

* `consume_then_add_keeps_count`: a `consume` of a datum followed by handing the
  datum to a receiver is a consuming receive: over the two locations the number
  of occurrences of every atom is what it was.
* `observe_then_add_adds_one`: the read of the two-step form followed by handing
  the datum over is an observing receive: there is one occurrence of the datum
  more.
* `consume_tokens_eq_take` and `consume_keeps_tokens`: when the space holds one
  datum of the presented language of the cell, the two stores hold, before and
  after the `consume`, the tokens of the two sides of the consuming receive; so
  the conservation on the stores is `take_keeps_tokens`.
* `observe_tokens_eq_read` and `observe_doubles_tokens`: the same for the read of
  the two-step form and the two sides of the read, with `read_doubles_tokens`.

So a `consume` is the linear reading of the store, and a read followed by a
separate removal is the copying reading until the removal happens; between the
two steps the datum exists twice, which is the state the interleaving of
`TokenRace.both_proceed_past_the_read` uses.

`TokenRace.token_kept` and `TokenRace.token_doubled` are the two counts on one
token.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Logic.HostingStyles.ContextReadings (consumingReceive_count observingReceive_count)

universe u v

variable {Location : Type u} {Atom : Type v} [DecidableEq Location] [DecidableEq Atom]

omit [DecidableEq Atom] in
/-- Adding one occurrence at a location is the publication of that occurrence by
a continuation. -/
theorem add_single_eq_publish (receiver : Location) (datum : Atom)
    (state : Network Location Atom) :
    state + Pi.single receiver {datum} = GuardedTransaction.publish ⟨receiver, datum⟩ state := by
  funext location
  by_cases same : location = receiver
  · subst same
    show state location + (Pi.single location {datum} : Location → Multiset Atom) location =
      Function.update state location (datum ::ₘ state location) location
    rw [Pi.single_eq_same, Function.update_self, add_comm, Multiset.singleton_add]
  · simp [GuardedTransaction.publish, same]

/-- **`consume` keeps tokens.**  Consuming a datum at a space and handing it to a
receiver keeps the number of occurrences of every atom over the two locations. -/
theorem consume_then_add_keeps_count {space receiver : Location} (apart : space ≠ receiver)
    (datum : Atom) (guard : Readout Location (Multiset Atom) Prop)
    (decideGuard : DecidablePred guard.value) {source target : Network Location Atom}
    (published : publish [Step.consume space datum guard decideGuard,
      Step.addAtom receiver datum] source = some target) (atom : Atom) :
    (target space).count atom + (target receiver).count atom =
      (source space).count atom + (source receiver).count atom := by
  simp only [publish_cons, publish_nil, Option.bind_eq_some_iff] at published
  obtain ⟨middle, consumed, afterAdd, added, same⟩ := published
  cases same
  have step : LocatedStep .consume space datum source middle :=
    ((SpaceRules.consume_fires_iff space datum guard source middle).mp
      ((Step.consume space datum guard decideGuard).fire_eq_some_iff.mp consumed)).2
  rw [Step.fire_addAtom] at added
  cases added
  rw [add_single_eq_publish]
  exact consumingReceive_count apart step atom

/-- **The read of the two-step form doubles.**  Seeing a datum at a space and
handing it to a receiver adds one occurrence of the datum over the two
locations. -/
theorem observe_then_add_adds_one {space receiver : Location} (apart : space ≠ receiver)
    (datum : Atom) {source target : Network Location Atom}
    (published : publish [Step.observeAtom space datum, Step.addAtom receiver datum] source =
      some target) (atom : Atom) :
    (target space).count atom + (target receiver).count atom =
      (source space).count atom + (source receiver).count atom +
        if atom = datum then 1 else 0 := by
  simp only [publish_cons, publish_nil, Option.bind_eq_some_iff] at published
  obtain ⟨middle, observed, afterAdd, added, same⟩ := published
  cases same
  have step : LocatedStep .observe space datum source middle :=
    (SpaceRules.observeAtom_fires_iff space datum source middle).mp
      ((Step.observeAtom space datum).fire_eq_some_iff.mp observed)
  rw [Step.fire_addAtom] at added
  cases added
  rw [add_single_eq_publish]
  exact observingReceive_count apart step atom

/-- **`consume` keeps the two stores together**: after a `consume` and the
handing over, the space and the receiver hold together what they held. -/
theorem consume_then_add_total {space receiver : Location} (apart : space ≠ receiver)
    (datum : Atom) (guard : Readout Location (Multiset Atom) Prop)
    (decideGuard : DecidablePred guard.value) {source target : Network Location Atom}
    (published : publish [Step.consume space datum guard decideGuard,
      Step.addAtom receiver datum] source = some target) :
    target space + target receiver = source space + source receiver :=
  Multiset.ext.mpr fun atom => by
    rw [Multiset.count_add, Multiset.count_add]
    exact consume_then_add_keeps_count apart datum guard decideGuard published atom

/-- **The read adds the datum**: after a read and the handing over, the space and
the receiver hold together what they held and one more occurrence of the datum. -/
theorem observe_then_add_total {space receiver : Location} (apart : space ≠ receiver)
    (datum : Atom) {source target : Network Location Atom}
    (published : publish [Step.observeAtom space datum, Step.addAtom receiver datum] source =
      some target) :
    target space + target receiver = source space + source receiver + {datum} :=
  Multiset.ext.mpr fun atom => by
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_add, Multiset.count_singleton]
    exact observe_then_add_adds_one apart datum published atom

/-! ## The two sides of the presented rules -/

section Presented

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.ContextReadings

omit [DecidableEq Atom]

variable (base : BasePremiseEvaluator)

/-- **The stores around a `consume` hold the tokens of the two sides of the
consuming receive.**  A space holds one datum of the presented language of the
cell; the datum is consumed and handed to a receiver.  Before, the two stores
hold the tokens of `take (cell datum)`; after, those of `got datum`. -/
theorem consume_tokens_eq_take (counted : String → Bool) (take : counted "take" = false)
    (cell : counted "cell" = false) (got : counted "got" = false)
    {space receiver : Location} (apart : space ≠ receiver)
    (datum : Contexts.Term cellLanguage datumInterface)
    (guard : Readout Location (Multiset Pattern) Prop) (decideGuard : DecidablePred guard.value)
    {target : Network Location Pattern}
    (published : publish [Step.consume space datum.1 guard decideGuard,
      Step.addAtom receiver datum.1] (Pi.single space {datum.1}) = some target) :
    (((Pi.single space {datum.1} : Network Location Pattern) space +
          (Pi.single space {datum.1} : Network Location Pattern) receiver).map
        (tokens counted)).sum =
        tokens counted ((contextTheory base cellPresentation).apply (takeBefore base) datum).1 ∧
      ((target space + target receiver).map (tokens counted)).sum =
        tokens counted ((contextTheory base cellPresentation).apply (takeAfter base) datum).1 := by
  have total := consume_then_add_total apart datum.1 guard decideGuard published
  have sourceTotal : (Pi.single space {datum.1} : Network Location Pattern) space +
      (Pi.single space {datum.1} : Network Location Pattern) receiver = {datum.1} := by
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm apart), add_zero]
  rw [total, sourceTotal, apply_takeBefore, apply_takeAfter]
  simp [tokens, tokensList, take, cell, got]

/-- **So `consume` keeps tokens as the consuming receive does**: the conservation
on the stores is `take_keeps_tokens`, read through the two sides. -/
theorem consume_keeps_tokens (counted : String → Bool) (take : counted "take" = false)
    (cell : counted "cell" = false) (got : counted "got" = false)
    {space receiver : Location} (apart : space ≠ receiver)
    (datum : Contexts.Term cellLanguage datumInterface)
    (guard : Readout Location (Multiset Pattern) Prop) (decideGuard : DecidablePred guard.value)
    {target : Network Location Pattern}
    (published : publish [Step.consume space datum.1 guard decideGuard,
      Step.addAtom receiver datum.1] (Pi.single space {datum.1}) = some target) :
    ((target space + target receiver).map (tokens counted)).sum =
      (((Pi.single space {datum.1} : Network Location Pattern) space +
          (Pi.single space {datum.1} : Network Location Pattern) receiver).map
        (tokens counted)).sum := by
  obtain ⟨before, after⟩ :=
    consume_tokens_eq_take (fun _ _ _ => []) counted take cell got apart datum guard decideGuard
      published
  rw [before, after]
  exact take_keeps_tokens (fun _ _ _ => []) counted take cell got datum

/-- **The stores around the read of the two-step form hold the tokens of the two
sides of the read.**  Before, the two stores hold the tokens of
`read (cell datum)`; after the read and the handing over, those of
`seen datum (cell datum)`. -/
theorem observe_tokens_eq_read (counted : String → Bool) (read : counted "read" = false)
    (cell : counted "cell" = false) (seen : counted "seen" = false)
    {space receiver : Location} (apart : space ≠ receiver)
    (datum : Contexts.Term cellLanguage datumInterface) {target : Network Location Pattern}
    (published : publish [Step.observeAtom space datum.1, Step.addAtom receiver datum.1]
      (Pi.single space {datum.1}) = some target) :
    (((Pi.single space {datum.1} : Network Location Pattern) space +
          (Pi.single space {datum.1} : Network Location Pattern) receiver).map
        (tokens counted)).sum =
        tokens counted ((contextTheory base cellPresentation).apply (readBefore base) datum).1 ∧
      ((target space + target receiver).map (tokens counted)).sum =
        tokens counted ((readAfter base).act fun _ => datum).1 := by
  have total := observe_then_add_total apart datum.1 published
  have sourceTotal : (Pi.single space {datum.1} : Network Location Pattern) space +
      (Pi.single space {datum.1} : Network Location Pattern) receiver = {datum.1} := by
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm apart), add_zero]
  rw [total, sourceTotal, apply_readBefore, act_readAfter]
  simp [tokens, tokensList, read, cell, seen]

/-- **So the read doubles tokens as the read of the cell does**: the stores hold
the tokens of the datum once more, by `read_doubles_tokens` read through the two
sides. -/
theorem observe_doubles_tokens (counted : String → Bool) (read : counted "read" = false)
    (cell : counted "cell" = false) (seen : counted "seen" = false)
    {space receiver : Location} (apart : space ≠ receiver)
    (datum : Contexts.Term cellLanguage datumInterface) {target : Network Location Pattern}
    (published : publish [Step.observeAtom space datum.1, Step.addAtom receiver datum.1]
      (Pi.single space {datum.1}) = some target) :
    ((target space + target receiver).map (tokens counted)).sum =
      (((Pi.single space {datum.1} : Network Location Pattern) space +
          (Pi.single space {datum.1} : Network Location Pattern) receiver).map
        (tokens counted)).sum + tokens counted datum.1 := by
  obtain ⟨before, after⟩ :=
    observe_tokens_eq_read (fun _ _ _ => []) counted read cell seen apart datum published
  rw [before, after]
  exact read_doubles_tokens (fun _ _ _ => []) counted read cell seen datum

end Presented

namespace TokenRace

/-- **Positive**: consumed and handed over, the one token is one token. -/
theorem token_kept :
    (publish [consumeToken, Step.addAtom .out .token] start).map
        (fun world => (world .pool).count Item.token + (world .out).count Item.token) =
      some 1 := by
  decide

/-- **Negative**: read and handed over, the one token is two tokens. -/
theorem token_doubled :
    (publish [Step.observeAtom .pool .token, Step.addAtom .out .token] start).map
        (fun world => (world .pool).count Item.token + (world .out).count Item.token) =
      some 2 := by
  decide

end TokenRace

#print axioms add_single_eq_publish
#print axioms consume_then_add_keeps_count
#print axioms observe_then_add_adds_one
#print axioms consume_then_add_total
#print axioms observe_then_add_total
#print axioms consume_tokens_eq_take
#print axioms consume_keeps_tokens
#print axioms observe_tokens_eq_read
#print axioms observe_doubles_tokens
#print axioms TokenRace.token_kept
#print axioms TokenRace.token_doubled

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
