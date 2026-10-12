import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Waves

/-!
# `consume`: the smallest step that is a publication

`consume` matches one occurrence of an atom in a store, checks a guard, and
removes the occurrence, as one local rule (`SpaceRules.consume`): removing an atom
with a guard that is a readout of a proposition.

* **One step** (`SpaceRules.consume_fires_iff`).  It fires exactly when the guard
  holds on the source and the located consume step is taken from the same source.
  There is no state between the check and the removal.
* **Footprint** (`SpaceRules.consume_footprint`,
  `SpaceRules.consume_effectFootprinted`).  It consumes the occurrence, produces
  nothing, writes the store, and reads what the guard reads.
* **One occurrence: a race** (`SpaceRules.consume_race`,
  `SpaceRules.consume_same_store_not_independent`).  After one `consume` of the
  only occurrence of an atom has fired, no `consume` of that atom in that store
  fires, whatever its guard.
* **Two occurrences: a wave.**  In two stores, with guards that do not read the
  other store, two `consume`s are independent and form a diamond
  (`SpaceRules.consume_independent`, `SpaceRules.consume_wave`).  In one store,
  with guards that do not read the store, both orders fire and reach one state
  (`SpaceRules.consume_two_occurrences`), although the two write one location and
  so are not independent: the wave is seen by the second validation and not by
  the first.
* **The two-step form** reads and then removes.
  `TokenRace.both_proceed_past_the_read`: with one token, two agents both read it,
  both act on what they read, one removes it, and the removal of the other finds
  nothing: two receipts for one token.  With `consume` in place of the read and
  the removal, the second agent does not get past its first step
  (`TokenRace.consume_excludes_the_second`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v

variable {Location : Type u} {Atom : Type v}

section Consume

variable [DecidableEq Location]

/-- The proposition that `atom` occurs in the store at `location`, read there. -/
def Readout.has (location : Location) (atom : Atom) : Readout Location (Multiset Atom) Prop :=
  ⟨{location}, fun state => atom ∈ state location,
    fun agrees => by rw [agrees location (Finset.mem_singleton_self location)]⟩

/-- **`consume`**: match one occurrence of `atom` in the store at `location`,
check `guard`, and remove the occurrence, as one local rule.  The guard is a
readout of a proposition: it declares the locations it reads. -/
def SpaceRules.consume (location : Location) (atom : Atom)
    (guard : Readout Location (Multiset Atom) Prop) : LocalRule Location (Multiset Atom) :=
  { SpaceRules.removeAtom location atom with
    guard := guard.value
    reads := guard.reads
    guard_local := fun agrees holds =>
      (guard.value_local (agreesOn_mono Finset.subset_union_left agrees)).mp holds }

/-- **`consume` is one step**: it fires exactly when the guard holds on the source
and the located consume step is taken from that source. -/
theorem SpaceRules.consume_fires_iff (location : Location) (atom : Atom)
    (guard : Readout Location (Multiset Atom) Prop) (source target : Network Location Atom) :
    (SpaceRules.consume location atom guard).Fires source target ↔
      guard.value source ∧ LocatedStep .consume location atom source target := by
  rw [← SpaceRules.removeAtom_fires_iff]
  constructor
  · rintro ⟨guarded, frame, consumedSeparate, producedSeparate, decomposition, result⟩
    exact ⟨guarded, trivial, frame, consumedSeparate, producedSeparate, decomposition, result⟩
  · rintro ⟨guarded, -, frame, consumedSeparate, producedSeparate, decomposition, result⟩
    exact ⟨guarded, frame, consumedSeparate, producedSeparate, decomposition, result⟩

/-- **The footprint of `consume`**: it consumes the occurrence, produces nothing,
writes the store, and reads what its guard reads. -/
theorem SpaceRules.consume_footprint (location : Location) (atom : Atom)
    (guard : Readout Location (Multiset Atom) Prop) :
    (SpaceRules.consume location atom guard).consumed = Pi.single location {atom} ∧
      (SpaceRules.consume location atom guard).produced = 0 ∧
      (SpaceRules.consume location atom guard).reads = guard.reads ∧
      (SpaceRules.consume location atom guard).writes = {location} :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- So it is certified with those reads and that one written location. -/
theorem SpaceRules.consume_effectFootprinted (location : Location) (atom : Atom)
    (guard : Readout Location (Multiset Atom) Prop) :
    EffectFootprinted (SpaceRules.consume location atom guard).Fires guard.reads {location} :=
  (SpaceRules.consume location atom guard).effectFootprinted

/-- **Two `consume`s of one occurrence are a race.**  After one has fired on a
store that held the atom once, no `consume` of that atom in that store fires,
whatever its guard. -/
theorem SpaceRules.consume_race [DecidableEq Atom] {location : Location} {atom : Atom}
    {source afterFirst : Network Location Atom} (once : (source location).count atom = 1)
    {firstGuard : Readout Location (Multiset Atom) Prop}
    (fires : (SpaceRules.consume location atom firstGuard).Fires source afterFirst)
    (secondGuard : Readout Location (Multiset Atom) Prop) :
    ¬ ∃ target, (SpaceRules.consume location atom secondGuard).Fires afterFirst target := by
  rintro ⟨target, second⟩
  obtain ⟨-, firstStep⟩ := (SpaceRules.consume_fires_iff _ _ _ _ _).mp fires
  obtain ⟨-, secondStep⟩ := (SpaceRules.consume_fires_iff _ _ _ _ _).mp second
  obtain ⟨rest, atLocation, rfl⟩ := LocatedStep.consume_iff.mp firstStep
  obtain ⟨later, atLocationLater, -⟩ := LocatedStep.consume_iff.mp secondStep
  rw [Function.update_self] at atLocationLater
  rw [atLocation, atLocationLater, Multiset.count_cons_self, Multiset.count_cons_self] at once
  omega

/-- And the certificates see it: two `consume`s in one store are not
independent. -/
theorem SpaceRules.consume_same_store_not_independent (location : Location) (first second : Atom)
    (firstGuard secondGuard : Readout Location (Multiset Atom) Prop) :
    ¬ IndependentEffects (SpaceRules.consume location first firstGuard).reads
      (SpaceRules.consume location first firstGuard).writes
      (SpaceRules.consume location second secondGuard).reads
      (SpaceRules.consume location second secondGuard).writes := by
  simp [IndependentEffects, SpaceRules.consume, SpaceRules.removeAtom, LocalRule.unguarded]

/-- **Two `consume`s in two stores are independent** when neither guard reads the
store of the other. -/
theorem SpaceRules.consume_independent {first second : Location} (apart : first ≠ second)
    (firstAtom secondAtom : Atom) {firstGuard secondGuard : Readout Location (Multiset Atom) Prop}
    (firstUnread : first ∉ secondGuard.reads) (secondUnread : second ∉ firstGuard.reads) :
    IndependentEffects (SpaceRules.consume first firstAtom firstGuard).reads
      (SpaceRules.consume first firstAtom firstGuard).writes
      (SpaceRules.consume second secondAtom secondGuard).reads
      (SpaceRules.consume second secondAtom secondGuard).writes := by
  simp [IndependentEffects, SpaceRules.consume, SpaceRules.removeAtom, LocalRule.unguarded,
    apart, Ne.symm apart, firstUnread, secondUnread]

/-- **Two occurrences in two stores are a wave**: each `consume` still fires after
the other, and the two orders reach one state. -/
theorem SpaceRules.consume_wave {first second : Location} (apart : first ≠ second)
    {firstAtom secondAtom : Atom} {firstGuard secondGuard : Readout Location (Multiset Atom) Prop}
    (firstUnread : first ∉ secondGuard.reads) (secondUnread : second ∉ firstGuard.reads)
    {source afterFirst afterSecond : Network Location Atom}
    (firstFires : (SpaceRules.consume first firstAtom firstGuard).Fires source afterFirst)
    (secondFires : (SpaceRules.consume second secondAtom secondGuard).Fires source afterSecond) :
    ∃ joined,
      (SpaceRules.consume second secondAtom secondGuard).Fires afterFirst joined ∧
        (SpaceRules.consume first firstAtom firstGuard).Fires afterSecond joined :=
  LocalRule.commute _ _
    (SpaceRules.consume_independent apart firstAtom secondAtom firstUnread secondUnread)
    firstFires secondFires

/-- **Two occurrences in one store are a wave too**, for guards that do not read
the store: both orders fire and reach the state with both occurrences removed. -/
theorem SpaceRules.consume_two_occurrences {location : Location} {first second : Atom}
    {rest : Multiset Atom} {source : Network Location Atom}
    (holds : source location = first ::ₘ second ::ₘ rest)
    {firstGuard secondGuard : Readout Location (Multiset Atom) Prop}
    (firstGuarded : firstGuard.value source) (secondGuarded : secondGuard.value source)
    (firstApart : location ∉ firstGuard.reads) (secondApart : location ∉ secondGuard.reads) :
    (∃ middle, (SpaceRules.consume location first firstGuard).Fires source middle ∧
        (SpaceRules.consume location second secondGuard).Fires middle
          (Function.update source location rest)) ∧
      ∃ middle, (SpaceRules.consume location second secondGuard).Fires source middle ∧
        (SpaceRules.consume location first firstGuard).Fires middle
          (Function.update source location rest) := by
  have keeps : ∀ (guard : Readout Location (Multiset Atom) Prop) (store : Multiset Atom),
      location ∉ guard.reads → guard.value source →
        guard.value (Function.update source location store) := by
    intro guard store apart guarded
    refine (guard.value_local fun other inside => ?_).mp guarded
    have different : other ≠ location := fun same => apart (same ▸ inside)
    rw [Function.update_of_ne different]
  have swapped : source location = second ::ₘ first ::ₘ rest := by
    rw [holds, Multiset.cons_swap]
  constructor
  · refine ⟨Function.update source location (second ::ₘ rest),
      (SpaceRules.consume_fires_iff _ _ _ _ _).mpr ⟨firstGuarded, .consume _ holds⟩,
      (SpaceRules.consume_fires_iff _ _ _ _ _).mpr ⟨keeps _ _ secondApart secondGuarded, ?_⟩⟩
    have step := LocatedStep.consume (location := location) (atom := second)
      (state := Function.update source location (second ::ₘ rest)) rest (Function.update_self ..)
    rwa [Function.update_idem] at step
  · refine ⟨Function.update source location (first ::ₘ rest),
      (SpaceRules.consume_fires_iff _ _ _ _ _).mpr ⟨secondGuarded, .consume _ swapped⟩,
      (SpaceRules.consume_fires_iff _ _ _ _ _).mpr ⟨keeps _ _ firstApart firstGuarded, ?_⟩⟩
    have step := LocatedStep.consume (location := location) (atom := first)
      (state := Function.update source location (first ::ₘ rest)) rest (Function.update_self ..)
    rwa [Function.update_idem] at step

/-- `consume`, as a step over a network of occurrence stores with a decidable
guard. -/
def Step.consume [DecidableEq Atom] (location : Location) (atom : Atom)
    (guard : Readout Location (Multiset Atom) Prop) (decideGuard : DecidablePred guard.value) :
    Step Location (Multiset Atom) :=
  .ofBagRule (SpaceRules.consume location atom guard) decideGuard

end Consume

/-! ## Controls -/

namespace TokenRace

/-- A pool that holds tokens, a gate, and the place where receipts are put. -/
inductive Place where
  | pool
  | gate
  | out
  deriving DecidableEq

/-- A token, a pass that opens the gate, and the receipts of two agents. -/
inductive Item where
  | token
  | pass
  | receiptA
  | receiptB
  deriving DecidableEq

/-- One token in the pool. -/
def start : Network Place Item := Pi.single .pool {.token}

/-- One token in the pool and the pass at the gate. -/
def startOpen : Network Place Item := Pi.single .pool {.token} + Pi.single .gate {.pass}

/-- Consume a token from the pool, with no condition. -/
def consumeToken : Step Place (Multiset Item) :=
  Step.consume .pool .token (Readout.const True) fun _ => isTrue trivial

/-- Consume a token from the pool if the pass is at the gate. -/
def consumeIfOpen : Step Place (Multiset Item) :=
  Step.consume .pool .token (Readout.has .gate .pass) fun state =>
    inferInstanceAs (Decidable (Item.pass ∈ state Place.gate))

/-- **Positive**: with the pass at the gate the guarded `consume` fires and takes
the token. -/
theorem consumeIfOpen_fires :
    (consumeIfOpen.fire startOpen).map (fun world => world .pool) = some 0 := by
  decide

/-- **Negative**: without the pass it does not fire, although the token is there. -/
theorem consumeIfOpen_refused : (consumeIfOpen.fire start).isSome = false := by
  decide

/-- The two-step form, interleaved: agent A reads the token, agent B reads the
token, each puts its receipt, and A removes the token. -/
def bothPastTheRead : List (Step Place (Multiset Item)) :=
  [Step.observeAtom .pool .token, Step.observeAtom .pool .token, Step.addAtom .out .receiptA,
    Step.addAtom .out .receiptB, Step.removeAtom .pool .token]

/-- **With a read and then a removal, both agents proceed past the read.**  Every
step of the interleaving fires on the one token: there are two receipts, the pool
is empty, and the removal of agent B then finds nothing. -/
theorem both_proceed_past_the_read :
    (publish bothPastTheRead start).map (fun world => (world .pool, world .out)) =
        some (0, {.receiptA, .receiptB}) ∧
      ((publish bothPastTheRead start).bind (Step.removeAtom .pool .token).fire).isSome =
        false := by
  decide

/-- **`consume` excludes it.**  After agent A has consumed the token and put its
receipt, the `consume` of agent B does not fire: one receipt for one token.  The
same holds when B tries at once after A's `consume`. -/
theorem consume_excludes_the_second :
    (publish [consumeToken, Step.addAtom .out .receiptA] start).map
        (fun world => (world .pool, world .out)) = some (0, {.receiptA}) ∧
      ((publish [consumeToken, Step.addAtom .out .receiptA] start).bind consumeToken.fire).isSome =
        false ∧
      ((publish [consumeToken] start).bind consumeToken.fire).isSome = false := by
  decide

end TokenRace

#print axioms SpaceRules.consume_fires_iff
#print axioms SpaceRules.consume_footprint
#print axioms SpaceRules.consume_effectFootprinted
#print axioms SpaceRules.consume_race
#print axioms SpaceRules.consume_same_store_not_independent
#print axioms SpaceRules.consume_independent
#print axioms SpaceRules.consume_wave
#print axioms SpaceRules.consume_two_occurrences
#print axioms TokenRace.consumeIfOpen_fires
#print axioms TokenRace.consumeIfOpen_refused
#print axioms TokenRace.both_proceed_past_the_read
#print axioms TokenRace.consume_excludes_the_second

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
