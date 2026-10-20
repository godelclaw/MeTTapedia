import Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning
import Mathlib.Data.UInt

/-!
# Guarded finite-word realization of unbounded natural successor

The fast representation is Lean's actual `UInt64`, observed through `toNat`.
Conversion admits exactly the naturals below the word size. The fast successor
checks the word boundary before using the native word addition operation.

The existing guarded-transfer and partial-realization interfaces assemble this
with an exact `Nat` fallback. Overflow therefore changes the chosen physical
representation, not the unbounded natural result. These proofs concern Lean's
word operations and the backend contract; they do not verify a CeTTa C backend
or establish a performance advantage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.NaturalBackendAdmission

open RepresentationSwitching CertifiedRepresentationPlanning

def encode? (value : Nat) : Option UInt64 :=
  if value < UInt64.size then some (UInt64.ofNat value) else none

theorem encode?_some_iff (value : Nat) (word : UInt64) :
    encode? value = some word ↔ value < UInt64.size ∧ UInt64.ofNat value = word := by
  by_cases fits : value < UInt64.size <;> simp [encode?, fits]

theorem encode?_accepted_iff (value : Nat) :
    (encode? value).isSome = true ↔ value < UInt64.size := by
  by_cases fits : value < UInt64.size <;> simp [encode?, fits]

theorem encode?_correct (value : Nat) (word : UInt64) (accepted : encode? value = some word) :
    word.toNat = value := by
  obtain ⟨fits, rfl⟩ := (encode?_some_iff value word).mp accepted
  exact UInt64.toNat_ofNat_of_lt' fits

/-- Every existing word survives decoding and checked re-encoding. -/
@[simp] theorem encode?_decode (word : UInt64) : encode? word.toNat = some word := by
  simp [encode?, word.toNat_lt_size]

def conversion : GuardedTransfer (fun value : Nat => value) UInt64.toNat where
  attempt := encode?
  correct := encode?_correct

def conversionPartial : PartialRealization (fun _ : Unit => Nat)
    (fun _ => UInt64) (fun _ => Nat) := guardedAsPartial conversion

theorem conversionPartial_admission (value : Nat) :
    conversionPartial.accepts () value = true ↔ value < UInt64.size :=
  encode?_accepted_iff value

/-- Refused conversion retains the original unbounded input. -/
theorem conversion_choose_preserves (value : Nat) :
    Sum.elim (fun value => value) UInt64.toNat (conversion.choose value) = value :=
  conversion.choose_preserves value

def maxWord : UInt64 := UInt64.ofNat (UInt64.size - 1)

@[simp] theorem maxWord_toNat : maxWord.toNat = UInt64.size - 1 :=
  UInt64.toNat_ofNat_of_lt' (by decide)

/-- The guard is a comparison on words; the successful branch uses actual
word addition, rather than computing the answer in `Nat` and re-encoding it. -/
def wordSuccessor? (word : UInt64) : Option UInt64 :=
  if word < maxWord then some (word + 1) else none

theorem wordSuccessor_guard (word : UInt64) :
    word < maxWord ↔ word.toNat + 1 < UInt64.size := by
  rw [UInt64.lt_iff_toNat_lt, maxWord_toNat]
  have sizePositive : 0 < UInt64.size := by decide
  omega

theorem wordSuccessor?_some_iff (word result : UInt64) :
    wordSuccessor? word = some result ↔
      word.toNat + 1 < UInt64.size ∧ word + 1 = result := by
  by_cases fits : word < maxWord
  · simp [wordSuccessor?, fits, ← wordSuccessor_guard]
  · simp [wordSuccessor?, fits, ← wordSuccessor_guard]

theorem wordSuccessor?_correct (word result : UInt64)
    (accepted : wordSuccessor? word = some result) :
    result.toNat = word.toNat + 1 := by
  obtain ⟨fits, rfl⟩ := (wordSuccessor?_some_iff word result).mp accepted
  rw [UInt64.toNat_add]
  change (word.toNat + 1) % UInt64.size = word.toNat + 1
  exact Nat.mod_eq_of_lt fits

def successor? (value : Nat) : Option UInt64 :=
  (encode? value).bind wordSuccessor?

theorem successor?_correct (value : Nat) (result : UInt64)
    (accepted : successor? value = some result) : result.toNat = value + 1 := by
  cases converted : encode? value with
  | none => simp [successor?, converted] at accepted
  | some word =>
    have step : wordSuccessor? word = some result := by
      simpa [successor?, converted] using accepted
    rw [wordSuccessor?_correct word result step, encode?_correct value word converted]

theorem successor?_accepted_iff (value : Nat) :
    (successor? value).isSome = true ↔ value + 1 < UInt64.size := by
  by_cases fits : value < UInt64.size
  · have wordView : (UInt64.ofNat value).toNat = value := UInt64.toNat_ofNat_of_lt' fits
    simp only [successor?, encode?, if_pos fits, Option.bind_some, wordSuccessor?]
    by_cases nextFits : UInt64.ofNat value < maxWord
    · simp only [if_pos nextFits, Option.isSome_some, true_iff]
      simpa only [wordView] using (wordSuccessor_guard _).mp nextFits
    · simp only [if_neg nextFits, Option.isSome_none, Bool.false_eq_true, false_iff]
      simpa only [wordView] using (not_congr (wordSuccessor_guard _)).mp nextFits
  · have cannot : ¬ value + 1 < UInt64.size := by omega
    simp [successor?, encode?, fits, cannot]

def successorTransfer : GuardedTransfer (fun value : Nat => value + 1) UInt64.toNat where
  attempt := successor?
  correct := successor?_correct

def successorPartial : PartialRealization (fun _ : Unit => Nat)
    (fun _ => UInt64) (fun _ => Nat) := guardedAsPartial successorTransfer

theorem successorPartial_admission (value : Nat) :
    successorPartial.accepts () value = true ↔ value + 1 < UInt64.size :=
  successor?_accepted_iff value

/-- The fallback performs exact unbounded successor. -/
def referenceSuccessor : SimpleRealization Nat Nat Nat where
  compile _ value := value + 1
  observeSource _ value := value + 1
  observeArtifact _ value := value
  adequate _ _ := rfl

/-- The selected artifact records whether execution used the finite word or
the unbounded fallback. Both branches have the same natural observation. -/
def successorBackend : SimpleRealization Nat (UInt64 ⊕ Nat) Nat :=
  successorPartial.withFallback referenceSuccessor (fun _ _ => rfl)

theorem successorBackend_exact (value : Nat) :
    Sum.elim UInt64.toNat (fun result => result) (successorBackend.compile () value) = value + 1 :=
  successorBackend.adequate () value

theorem successorBackend_uses_word (value : Nat) (fits : value + 1 < UInt64.size) :
    ∃ word, successorBackend.compile () value = .inl word ∧ word.toNat = value + 1 := by
  have accepted := (successorPartial_admission value).mpr fits
  refine ⟨successorPartial.compile () value accepted, ?_, successorPartial.adequate () value accepted⟩
  exact PartialRealization.withFallback_compile_fast _ _ _ _ _ accepted

theorem successorBackend_uses_fallback (value : Nat) (outside : UInt64.size ≤ value + 1) :
    successorBackend.compile () value = .inr (value + 1) := by
  apply PartialRealization.withFallback_compile_fallback
  intro accepted
  exact Nat.not_lt_of_ge outside ((successorPartial_admission value).mp accepted)

namespace Controls

theorem conversion_zero : encode? 0 = some 0 := by decide

theorem conversion_last_word : encode? (UInt64.size - 1) = some maxWord := by decide

theorem conversion_first_outside : encode? UInt64.size = none := by decide

theorem conversion_refusal_keeps_input : conversion.choose UInt64.size = .inl UInt64.size := by
  decide

theorem successor_small : successorBackend.compile () 40 = .inl 41 := by decide

theorem successor_last_safe :
    successorBackend.compile () (UInt64.size - 2) = .inl maxWord := by decide

theorem successor_boundary_fallback :
    successorBackend.compile () (UInt64.size - 1) = .inr UInt64.size := by decide

theorem successor_large_fallback :
    successorBackend.compile () (UInt64.size + 7) = .inr (UInt64.size + 8) := by decide

/-- Unchecked finite-word successor wraps, so it is not a realization of
unbounded natural successor on every represented input. -/
theorem unchecked_successor_wraps : maxWord + 1 = (0 : UInt64) := by decide

theorem unchecked_successor_not_natural :
    (maxWord + 1).toNat ≠ maxWord.toNat + 1 := by decide

theorem boundary_observation_exact :
    Sum.elim UInt64.toNat (fun result => result)
      (successorBackend.compile () (UInt64.size - 1)) = UInt64.size := by
  rw [successor_boundary_fallback]
  rfl

end Controls

end Mettapedia.GSLT.Dynamics.NaturalBackendAdmission
