import Mettapedia.Machines.Storage.SerialNumbers

/-!
# Publication through two versioned slots

A publication replaces the non-current slot by a complete, validated snapshot.
The serial arithmetic guarantees that the new snapshot wins recovery, including
when the serial wraps. The previously current slot remains unchanged.

The model deliberately exposes publication as an event. Establishing that
native byte writes and validation implement that event is a separate I/O and
codec obligation; a finite checksum is not a collision-free atomicity proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Storage.VersionedPair

open SerialNumbers

universe u

structure Snapshot (Value : Type u) where
  serial : Nat
  payload : Value
  deriving DecidableEq, Repr

structure Pair (Value : Type u) where
  a : Snapshot Value
  b : Snapshot Value
  deriving DecidableEq, Repr

def choosesA {Value : Type u} (space : Space) (pair : Pair Value) : Bool :=
  firstCurrent space pair.a.serial pair.b.serial

def current {Value : Type u} (space : Space) (pair : Pair Value) : Snapshot Value :=
  if choosesA space pair then pair.a else pair.b

def publish {Value : Type u} (space : Space) (pair : Pair Value) (value : Value) : Pair Value :=
  let fresh := Snapshot.mk (next space (current space pair).serial) value
  if choosesA space pair then { pair with b := fresh } else { pair with a := fresh }

theorem publish_selects_new {Value : Type u} (space : Space) (pair : Pair Value) (value : Value)
    (boundA : pair.a.serial ≤ space.modulus) (boundB : pair.b.serial ≤ space.modulus) :
    (current space (publish space pair value)).payload = value := by
  by_cases a : choosesA space pair = true
  · have wins := (successor_wins space boundA).2
    simp only [publish, current, a, ↓reduceIte]
    simp [choosesA, wins]
  · have b : choosesA space pair = false := by cases h : choosesA space pair <;> simp_all
    have wins := (successor_wins space boundB).1
    simp only [publish, current, b, Bool.false_eq_true, ↓reduceIte]
    simp [choosesA, wins]

theorem publish_preserves_previous {Value : Type u} (space : Space) (pair : Pair Value)
    (value : Value) :
    (if choosesA space pair then (publish space pair value).a else
      (publish space pair value).b) = current space pair := by
  unfold publish current
  cases choosesA space pair <;> rfl

theorem publish_versions_bounded {Value : Type u} (space : Space) (pair : Pair Value)
    (value : Value) (boundA : pair.a.serial ≤ space.modulus)
    (boundB : pair.b.serial ≤ space.modulus) :
    (publish space pair value).a.serial ≤ space.modulus ∧
    (publish space pair value).b.serial ≤ space.modulus := by
  unfold publish current
  cases h : choosesA space pair
  · simpa [h] using And.intro (next_valid space boundB).2 boundB
  · simpa [h] using And.intro boundA (next_valid space boundA).2

namespace Controls

def pairAtWrap : Pair Nat := ⟨⟨4294967295, 10⟩, ⟨4294967294, 9⟩⟩

theorem wrapped_publication_recovers_new_payload :
    (current SerialNumbers.Controls.word32
      (publish SerialNumbers.Controls.word32 pairAtWrap 11)).payload = 11 := by decide +kernel

theorem legacy_maximum_recovers_old_payload :
    let after := publish SerialNumbers.Controls.word32 pairAtWrap 11
    (if after.a.serial ≥ after.b.serial then after.a else after.b).payload = 10 := by decide +kernel

end Controls

end Mettapedia.Machines.Storage.VersionedPair
