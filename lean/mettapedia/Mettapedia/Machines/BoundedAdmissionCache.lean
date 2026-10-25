import Mettapedia.Machines.RevisionedQueryFacts

/-!
# Bounded banks of revision-scoped admission facts

Several exact keys can share a hash bank. Collisions select a bank, never an
answer. A bounded linear probe still checks the complete stamp and key.
Publishing a stable fact can replace an arbitrary resident; a transient
observation does not change the bank. Neither replacement nor hashing changes
the result of a sound hit.

This refines the existing pure-fact cache with bounded probes and arbitrary
victim selection. The list describes occupied entries, not physical empty
slots. Native stamp completeness, truthful classification, locking, slot
layout and replacement-policy correspondence remain C obligations. The cost
bound counts exact entry comparisons; it is not a runtime optimality claim.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundedAdmissionCache

open RevisionedQueryFacts

variable {Stamp Key Fact : Type} [DecidableEq Stamp] [DecidableEq Key]

/-- Stop at the first exact match, recording comparisons including misses. -/
def probe (stamp : Stamp) (key : Key) : Cache Stamp Key Fact → Option (List Fact) × Nat
  | [] => (none, 0)
  | entry :: rest =>
      if entry.stamp = stamp ∧ entry.key = key then (some entry.facts, 1)
      else
        let later := probe stamp key rest
        (later.1, later.2 + 1)

theorem probe_exact (stamp : Stamp) (key : Key) (cache : Cache Stamp Key Fact) :
    (probe stamp key cache).1 = lookup stamp key cache := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
      by_cases same : entry.stamp = stamp ∧ entry.key = key
      · simp [probe, lookup, same]
      · simp [probe, lookup, same, ih]

theorem probe_comparisons_le (stamp : Stamp) (key : Key) (cache : Cache Stamp Key Fact) :
    (probe stamp key cache).2 ≤ cache.length := by
  induction cache with
  | nil => exact Nat.le_refl 0
  | cons entry rest ih =>
      by_cases same : entry.stamp = stamp ∧ entry.key = key
      · simp [probe, same]
      · simpa [probe, same] using Nat.add_le_add_right ih 1

theorem probe_sound (compute : Stamp → Key → List Fact)
    (cache : Cache Stamp Key Fact) (valid : Valid compute cache)
    (stamp : Stamp) (key : Key) {facts : List Fact}
    (found : (probe stamp key cache).1 = some facts) : facts = compute stamp key := by
  rw [probe_exact] at found
  exact lookup_sound compute cache valid stamp key found

/-- Fill available capacity, otherwise replace the selected resident. -/
def retain (ways victim : Nat) (entry : Entry Stamp Key Fact)
    (cache : Cache Stamp Key Fact) : Cache Stamp Key Fact :=
  if ways = 0 then []
  else if cache.length < ways then cache ++ [entry]
  else cache.set (victim % ways) entry

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem retain_valid (ways victim : Nat) (compute : Stamp → Key → List Fact)
    (entry : Entry Stamp Key Fact) (cache : Cache Stamp Key Fact)
    (entryValid : entry.facts = compute entry.stamp entry.key)
    (valid : Valid compute cache) : Valid compute (retain ways victim entry cache) := by
  intro observed member
  by_cases zero : ways = 0
  · simp [retain, zero] at member
  · by_cases room : cache.length < ways
    · simp only [retain, zero, ↓reduceIte, room, List.mem_append,
        List.mem_singleton] at member
      rcases member with old | rfl
      · exact valid observed old
      · exact entryValid
    · simp only [retain, zero, ↓reduceIte, room] at member
      rcases List.mem_or_eq_of_mem_set member with old | rfl
      · exact valid observed old
      · exact entryValid

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem retain_bounded (ways victim : Nat) (entry : Entry Stamp Key Fact)
    (cache : Cache Stamp Key Fact) (bounded : cache.length ≤ ways) :
    (retain ways victim entry cache).length ≤ ways := by
  by_cases zero : ways = 0
  · simp [retain, zero]
  · by_cases room : cache.length < ways
    · simp [retain, zero, room]
    · simpa [retain, zero, room] using bounded

abbrev Banks (sets : Nat) (Stamp Key Fact : Type) := Fin sets → Cache Stamp Key Fact

def ValidBanks {sets : Nat} (compute : Stamp → Key → List Fact)
    (banks : Banks sets Stamp Key Fact) : Prop := ∀ bank, Valid compute (banks bank)

def Bounded {sets : Nat} (ways : Nat) (banks : Banks sets Stamp Key Fact) : Prop :=
  ∀ bank, (banks bank).length ≤ ways

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem empty_valid {sets : Nat} (compute : Stamp → Key → List Fact) :
    ValidBanks compute (fun (_ : Fin sets) => []) := by
  intro bank
  exact valid_nil compute

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem empty_bounded {sets : Nat} (ways : Nat) :
    Bounded ways (fun (_ : Fin sets) => ([] : Cache Stamp Key Fact)) := by
  intro bank
  exact Nat.zero_le ways

/-- `stable = false` refuses publication even if the computed answer is a
negative admission. A hash function may have arbitrarily many collisions. -/
def publish {sets : Nat} (hash : Stamp → Key → Fin sets) (ways victim : Nat)
    (stable : Bool) (compute : Stamp → Key → List Fact)
    (stamp : Stamp) (key : Key) (banks : Banks sets Stamp Key Fact) :
    Banks sets Stamp Key Fact :=
  if stable then Function.update banks (hash stamp key)
    (retain ways victim ⟨stamp, key, compute stamp key⟩ (banks (hash stamp key)))
  else banks

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem publish_valid {sets : Nat} (hash : Stamp → Key → Fin sets) (ways victim : Nat)
    (stable : Bool) (compute : Stamp → Key → List Fact)
    (stamp : Stamp) (key : Key) (banks : Banks sets Stamp Key Fact)
    (valid : ValidBanks compute banks) :
    ValidBanks compute (publish hash ways victim stable compute stamp key banks) := by
  intro bank
  cases stable with
  | false => exact valid bank
  | true =>
      by_cases selected : bank = hash stamp key
      · subst bank
        simpa [publish] using retain_valid ways victim compute
          ⟨stamp, key, compute stamp key⟩ (banks (hash stamp key)) rfl
          (valid (hash stamp key))
      · simpa [publish, selected] using valid bank

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem publish_bounded {sets : Nat} (hash : Stamp → Key → Fin sets) (ways victim : Nat)
    (stable : Bool) (compute : Stamp → Key → List Fact)
    (stamp : Stamp) (key : Key) (banks : Banks sets Stamp Key Fact)
    (bounded : Bounded ways banks) :
    Bounded ways (publish hash ways victim stable compute stamp key banks) := by
  intro bank
  cases stable with
  | false => exact bounded bank
  | true =>
      by_cases selected : bank = hash stamp key
      · subst bank
        simpa [publish] using retain_bounded ways victim
          (⟨stamp, key, compute stamp key⟩ : Entry Stamp Key Fact)
          (banks (hash stamp key)) (bounded (hash stamp key))
      · simpa [publish, selected] using bounded bank

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem transient_does_not_publish {sets : Nat} (hash : Stamp → Key → Fin sets)
    (ways victim : Nat) (compute : Stamp → Key → List Fact)
    (stamp : Stamp) (key : Key) (banks : Banks sets Stamp Key Fact) :
    publish hash ways victim false compute stamp key banks = banks := by rfl

/-- Bank selection only affects hit rate. Every returned fact remains exact. -/
theorem hashed_hit_exact {sets : Nat} (hash : Stamp → Key → Fin sets)
    (compute : Stamp → Key → List Fact) (banks : Banks sets Stamp Key Fact)
    (valid : ValidBanks compute banks) (stamp : Stamp) (key : Key) {facts : List Fact}
    (found : (probe stamp key (banks (hash stamp key))).1 = some facts) :
    facts = compute stamp key :=
  probe_sound compute _ (valid (hash stamp key)) stamp key found

theorem hashed_probe_bounded {sets : Nat} (hash : Stamp → Key → Fin sets) (ways : Nat)
    (banks : Banks sets Stamp Key Fact) (bounded : Bounded ways banks)
    (stamp : Stamp) (key : Key) :
    (probe stamp key (banks (hash stamp key))).2 ≤ ways :=
  (probe_comparisons_le stamp key _).trans (bounded (hash stamp key))

namespace Controls

def compute (revision key : Nat) : List Nat := [revision + key, revision + key]
def collide (_revision _key : Nat) : Fin 1 := 0
def empty : Banks 1 Nat Nat Nat := fun _ => []
def two : Banks 1 Nat Nat Nat :=
  publish collide 4 0 true compute 7 20 (publish collide 4 0 true compute 7 10 empty)

-- Two colliding keys coexist, preserving duplicate facts and their order.
example : (probe 7 10 (two 0)).1 = some [17, 17] ∧
    (probe 7 20 (two 0)).1 = some [27, 27] := by decide

-- A collision is not equality, and a new revision cannot read an old fact.
example : (probe 7 30 (two 0)).1 = none ∧ (probe 8 10 (two 0)).1 = none := by decide

-- Replacement removes availability, never changes the remaining answer.
example : let replaced := publish collide 2 0 true compute 7 30 two
    (probe 7 10 (replaced 0)).1 = none ∧
      (probe 7 20 (replaced 0)).1 = some [27, 27] ∧
      (probe 7 30 (replaced 0)).1 = some [37, 37] := by decide

-- A transient negative result leaves the successful observation available.
example : (probe 7 10 ((publish collide 4 0 false (fun _ _ => []) 7 10 two) 0)).1 =
    some [17, 17] := by decide

end Controls

end Mettapedia.Machines.BoundedAdmissionCache
