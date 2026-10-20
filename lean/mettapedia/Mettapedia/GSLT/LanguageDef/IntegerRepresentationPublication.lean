import Mettapedia.GSLT.LanguageDef.IntegerRepresentationRetainedCall

/-!
# Publishing retained integers through a checked small-word guard

A provider may return storage whose value fits a machine word. Publication
can narrow that result, while declined narrowing retains the actual storage.
The existing guarded-transfer interface supplies the value law. Sequences
execute with each published result, so later dispatch sees its actual tag.

These laws preserve integers and provider faults. They do not preserve
storage identity, resource availability or costs across representation changes.
Native ownership and allocation behavior require separate qualification.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained.Publication

open Mettapedia.GSLT.Dynamics.RepresentationSwitching

variable {Storage Fault : Type*} {decode : Storage → Int}

abbrev Narrow (decode : Storage → Int) := GuardedTransfer decode Int64.toInt

def publish (narrow : Narrow decode) : Value Storage → Value Storage
  | .inl word => .inl word
  | .inr stored => match narrow.attempt stored with
    | none => .inr stored
    | some word => .inl word

@[simp] theorem publish_word (narrow : Narrow decode) (word : Int64) :
    publish narrow (.inl word) = .inl word := rfl

theorem publish_declined (narrow : Narrow decode) (stored : Storage)
    (declined : narrow.attempt stored = none) :
    publish narrow (.inr stored) = .inr stored := by simp [publish, declined]

theorem publish_meaning (narrow : Narrow decode) (value : Value Storage) :
    resultInteger decode (publish narrow value) = resultInteger decode value := by
  cases value with
  | inl word => rfl
  | inr stored =>
      cases attempted : narrow.attempt stored with
      | none => simp [publish, attempted]
      | some word =>
          simpa [publish, attempted, resultInteger] using narrow.correct stored word attempted

def add (narrow : Narrow decode) (encode : Int → Storage)
    (provider : Provider Storage Fault) (left right : Value Storage) :
    Except Fault (Value Storage) :=
  (Retained.add encode provider left right).map (publish narrow)

theorem add_sound (narrow : Narrow decode) (encode : Int → Storage)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Storage Fault) (sound : SuccessfulSound decode provider)
    (left right result : Value Storage)
    (returned : add narrow encode provider left right = .ok result) :
    resultInteger decode result = resultInteger decode left + resultInteger decode right := by
  cases called : Retained.add encode provider left right with
  | error fault => simp [add, called, Except.map] at returned
  | ok value =>
      simp only [add, called, Except.map, Except.ok.injEq] at returned
      rw [← returned, publish_meaning]
      exact Retained.add_sound encode decode roundtrip provider sound left right value called

theorem add_fault_iff (narrow : Narrow decode) (encode : Int → Storage)
    (provider : Provider Storage Fault) (left right : Value Storage) (fault : Fault) :
    add narrow encode provider left right = .error fault ↔
      Retained.add encode provider left right = .error fault := by
  cases called : Retained.add encode provider left right <;> simp [add, called, Except.map]

theorem add_available_iff (narrow : Narrow decode) (encode : Int → Storage)
    (provider : Provider Storage Fault) (left right : Value Storage) :
    (∃ result, add narrow encode provider left right = .ok result) ↔
      ∃ result, Retained.add encode provider left right = .ok result := by
  cases called : Retained.add encode provider left right <;> simp [add, called, Except.map]

/-- Publication is performed between calls, not only on the final result. -/
def addMany (narrow : Narrow decode) (encode : Int → Storage)
    (provider : Provider Storage Fault) :
    Value Storage → List (Value Storage) → Except Fault (Value Storage)
  | initial, [] => .ok initial
  | initial, next :: rest => do
      let current ← add narrow encode provider initial next
      addMany narrow encode provider current rest

theorem addMany_sound (narrow : Narrow decode) (encode : Int → Storage)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Storage Fault) (sound : SuccessfulSound decode provider)
    (values : List (Value Storage)) (initial result : Value Storage)
    (returned : addMany narrow encode provider initial values = .ok result) :
    resultInteger decode result = resultInteger decode initial +
      (values.map (resultInteger decode)).sum := by
  induction values generalizing initial with
  | nil =>
      simp only [addMany, Except.ok.injEq] at returned
      rw [← returned]
      simp
  | cons next rest ih =>
      cases called : add narrow encode provider initial next with
      | error fault => simp [addMany, called, bind, Except.bind] at returned
      | ok current =>
          have continued : addMany narrow encode provider current rest = .ok result := by
            simpa [addMany, called, bind, Except.bind] using returned
          rw [ih current continued, add_sound narrow encode roundtrip provider sound initial next current called]
          simp only [List.map_cons, List.sum_cons, Int.add_assoc]

/-- An executable guard for the mathematical storage model. Real native
adapters implement their own fitting test and must satisfy the same contract. -/
def integerNarrow : Narrow (id : Int → Int) where
  attempt value := if (Int64.ofInt value).toInt = value then some (Int64.ofInt value) else none
  correct value word accepted := by
    split at accepted
    · cases accepted; assumption
    · contradiction

#print axioms add_sound
#print axioms addMany_sound

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained.Publication
