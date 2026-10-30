import Mathlib.Tactic

/-!
# Exact compact integer literals under complete encoded cost

The logical value is always a sequence of integers. A compact literal stores
actual bounded byte values, with an explicit constructor distinct from an
ordinary integer literal. A supplied writer encodes the entire tagged literal;
the choice compares those full byte strings, not just their numeric payloads.
Native TP1/CTN1 byte correspondence is checked independently by the literal gate.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.PackedIntegerLiteral

def narrowOne (value : Int) : Option (Fin 256) :=
  if admitted : 0 ≤ value ∧ value < 256 then
    some ⟨value.toNat, by omega⟩ else none

def widenOne (byte : Fin 256) : Int := byte.val

theorem narrowOne_sound (value : Int) (byte : Fin 256)
    (found : narrowOne value = some byte) : widenOne byte = value := by
  unfold narrowOne at found
  split at found
  · rename_i admitted
    cases Option.some.inj found
    simp only [widenOne]
    omega
  · cases found

theorem narrowOne_widenOne (byte : Fin 256) : narrowOne (widenOne byte) = some byte := by
  have low : 0 ≤ widenOne byte := by simp [widenOne]
  have high : widenOne byte < 256 := by
    change (byte.val : Int) < 256
    exact_mod_cast byte.isLt
  unfold narrowOne
  rw [dif_pos ⟨low, high⟩]
  congr 1

def narrow : List Int → Option (List (Fin 256))
  | [] => some []
  | value :: rest => do
      let first ← narrowOne value
      let later ← narrow rest
      pure (first :: later)

def widen (bytes : List (Fin 256)) : List Int := bytes.map widenOne

theorem narrow_sound (values : List Int) (bytes : List (Fin 256))
    (found : narrow values = some bytes) : widen bytes = values := by
  induction values generalizing bytes with
  | nil => simp [narrow] at found; subst bytes; rfl
  | cons first rest ih =>
      cases one : narrowOne first with
      | none => simp [narrow, one] at found
      | some byte =>
          cases later : narrow rest with
          | none => simp [narrow, one, later] at found
          | some tail =>
              simp [narrow, one, later] at found
              subst bytes
              change widenOne byte :: widen tail = first :: rest
              rw [narrowOne_sound first byte one, ih tail later]

theorem narrow_widen (bytes : List (Fin 256)) : narrow (widen bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons first rest ih =>
      change narrow (widenOne first :: widen rest) = some (first :: rest)
      simp [narrow, narrowOne_widenOne, ih]

inductive Literal where
  | ordinary : List Int → Literal
  | packedU8 : List (Fin 256) → Literal
  deriving DecidableEq

def value : Literal → List Int
  | .ordinary values => values
  | .packedU8 bytes => widen bytes

def choose (encode : Literal → List UInt8) (values : List Int) : Literal :=
  match narrow values with
  | none => .ordinary values
  | some bytes =>
      if (encode (.packedU8 bytes)).length < (encode (.ordinary values)).length then
        .packedU8 bytes else .ordinary values

theorem choose_preserves (encode : Literal → List UInt8) (values : List Int) :
    value (choose encode values) = values := by
  cases narrowed : narrow values with
  | none => simp [choose, narrowed, value]
  | some bytes =>
      simp only [choose, narrowed]
      split_ifs
      · exact narrow_sound values bytes narrowed
      · rfl

theorem choose_cost (encode : Literal → List UInt8) (values : List Int) :
    (encode (choose encode values)).length ≤ (encode (.ordinary values)).length := by
  cases narrowed : narrow values with
  | none => simp [choose, narrowed]
  | some bytes =>
      simp only [choose, narrowed]
      split_ifs
      · exact Nat.le_of_lt ‹_›
      · exact Nat.le_refl _

theorem packed_choice_strictly_smaller (encode : Literal → List UInt8) (values : List Int)
    (bytes : List (Fin 256)) (chosen : choose encode values = .packedU8 bytes) :
    narrow values = some bytes ∧
      (encode (.packedU8 bytes)).length < (encode (.ordinary values)).length := by
  cases narrowed : narrow values with
  | none => simp [choose, narrowed] at chosen
  | some actual =>
      simp only [choose, narrowed] at chosen
      split_ifs at chosen
      · rename_i smaller
        cases chosen
        exact ⟨rfl, smaller⟩

theorem no_payload_only_override (encode : Literal → List UInt8) (values : List Int)
    (bytes : List (Fin 256)) (narrowed : narrow values = some bytes)
    (noGain : (encode (.ordinary values)).length ≤ (encode (.packedU8 bytes)).length) :
    choose encode values = .ordinary values := by
  simp [choose, narrowed, Nat.not_lt.mpr noGain]

namespace Controls

theorem negative_does_not_wrap : narrowOne (-1) = none := by decide

theorem large_does_not_wrap : narrowOne 256 = none := by decide

theorem upper_byte_round_trip : widen <$> narrow [0, 1, 255] = some [0, 1, 255] := by decide

def overheadWriter : Literal → List UInt8
  | .ordinary _ => [0, 0]
  | .packedU8 _ => [1, 0, 0]

theorem extra_tag_cost_can_defeat_a_small_payload :
    choose overheadWriter [1] = .ordinary [1] := by decide

end Controls

end Mettapedia.Algorithms.Compression.PackedIntegerLiteral
