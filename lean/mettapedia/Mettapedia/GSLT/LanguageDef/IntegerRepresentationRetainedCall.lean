import Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall

/-!
# Addition on retained integer representations

The existing signed-word path and external provider accept retained operands.
Stored operands pass directly to that provider; only machine words promoted
to storage are encoded. Decoding occurs in correctness statements, never in
the implementation's storage branch. Successful calls compose independently
of availability. Provider faults stop a sequence without becoming arithmetic
answers. Native allocation, borrowing and ownership remain adapter obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained

open ArithmeticExternalCallPilot

variable {Storage Fault : Type*}

abbrev Value (Storage : Type*) := Int64 ⊕ Storage

def stored (encode : Int → Storage) : Value Storage → Storage
  | .inl word => encode word.toInt
  | .inr value => value

@[simp] theorem stored_word (encode : Int → Storage) (word : Int64) :
    stored encode (.inl word) = encode word.toInt := rfl

@[simp] theorem stored_storage (encode : Int → Storage) (value : Storage) :
    stored encode (.inr value) = value := rfl

theorem stored_meaning (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (value : Value Storage) :
    decode (stored encode value) = resultInteger decode value := by
  cases value with
  | inl word => exact roundtrip word.toInt
  | inr value => rfl

def fast? : Value Storage → Value Storage → Option Int64
  | .inl left, .inl right => signedAddition? left right
  | _, _ => none

def add (encode : Int → Storage) (provider : Provider Storage Fault)
    (left right : Value Storage) : Except Fault (Value Storage) :=
  match fast? left right with
  | some word => .ok (.inl word)
  | none => (provider .add (stored encode left) (stored encode right)).map Sum.inr

/-- This execution equation has no storage decoder or encoder in its right
side: the existing operands reach the original provider unchanged. -/
theorem add_storage (encode : Int → Storage) (provider : Provider Storage Fault)
    (left right : Storage) :
    add encode provider (.inr left) (.inr right) =
      (provider .add left right).map Sum.inr := rfl

theorem fast_correct (decode : Storage → Int) (left right : Value Storage) (result : Int64)
    (accepted : fast? left right = some result) :
    result.toInt = resultInteger decode left + resultInteger decode right := by
  cases left <;> cases right <;> simp only [fast?] at accepted
  all_goals first | contradiction | exact signedAddition?_correct _ _ _ accepted

theorem add_sound (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Storage Fault) (sound : SuccessfulSound decode provider)
    (left right result : Value Storage)
    (returned : add encode provider left right = .ok result) :
    resultInteger decode result = resultInteger decode left + resultInteger decode right := by
  cases attempted : fast? left right with
  | some word =>
      simp only [add, attempted] at returned
      cases returned
      exact fast_correct decode left right word attempted
  | none =>
      cases called : provider .add (stored encode left) (stored encode right) with
      | error fault => simp [add, attempted, called, Except.map] at returned
      | ok value =>
          simp only [add, attempted, called, Except.map] at returned
          cases returned
          have correct := sound .add (stored encode left) (stored encode right) value
            (by simp [CompiledOp.undefinedAt, CompiledOp.guard]) called
          simpa only [resultInteger, Sum.elim_inr, CompiledOp.fn,
            stored_meaning encode decode roundtrip] using correct

/-- Availability is local to the actual retained fallback operands. It is
not inferred from correctness or from availability only on fresh encodings. -/
theorem add_available (encode : Int → Storage) (provider : Provider Storage Fault)
    (left right : Value Storage)
    (available : fast? left right = none →
      ∃ value, provider .add (stored encode left) (stored encode right) = .ok value) :
    ∃ result, add encode provider left right = .ok result := by
  cases attempted : fast? left right with
  | some word => exact ⟨.inl word, by simp [add, attempted]⟩
  | none =>
      obtain ⟨value, returned⟩ := available attempted
      exact ⟨.inr value, by simp [add, attempted, returned, Except.map]⟩

theorem fallback_fault (encode : Int → Storage) (provider : Provider Storage Fault)
    (left right : Value Storage) (fault : Fault) (fallback : fast? left right = none)
    (failed : provider .add (stored encode left) (stored encode right) = .error fault) :
    add encode provider left right = .error fault := by
  simp [add, fallback, failed, Except.map]

def addMany (encode : Int → Storage) (provider : Provider Storage Fault) :
    Value Storage → List (Value Storage) → Except Fault (Value Storage)
  | initial, [] => .ok initial
  | initial, next :: rest => do
      let current ← add encode provider initial next
      addMany encode provider current rest

theorem addMany_sound (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode)
    (provider : Provider Storage Fault) (sound : SuccessfulSound decode provider)
    (values : List (Value Storage)) (initial result : Value Storage)
    (returned : addMany encode provider initial values = .ok result) :
    resultInteger decode result = resultInteger decode initial +
      (values.map (resultInteger decode)).sum := by
  induction values generalizing initial with
  | nil =>
      simp only [addMany, Except.ok.injEq] at returned
      rw [← returned]
      simp
  | cons next rest ih =>
      cases called : add encode provider initial next with
      | error fault => simp [addMany, called, bind, Except.bind] at returned
      | ok current =>
          have continued : addMany encode provider current rest = .ok result := by
            simpa [addMany, called, bind, Except.bind] using returned
          rw [ih current continued, add_sound encode decode roundtrip provider sound initial next current called]
          simp only [List.map_cons, List.sum_cons, Int.add_assoc]

#print axioms add_sound
#print axioms addMany_sound

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained
