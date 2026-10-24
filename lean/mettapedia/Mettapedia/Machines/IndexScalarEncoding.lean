import Mathlib.Data.UInt
import Init.Data.SInt.Lemmas
import Mathlib.Tactic

/-!
# Exact scalar observations of unsigned index words

Index buffers retain unsigned 64-bit words. Scalar inspection exposes an
ordinary signed integer atom when representable, otherwise a large integer
atom. The native callback adapter may use the signed word fast path only
below the sign boundary. The observation preserves both the integer value
and the small/large atom distinction. No floating conversion is involved.

This models the representation choice and machine-integer cast, not native
allocation, decimal parsing or the implementation of the callback itself.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IndexScalarEncoding

inductive AtomValue where
  | small (value : Int)
  | large (value : Nat)
  deriving DecidableEq

inductive Argument where
  | signedWord (word : Int64)
  | unsignedWord (word : UInt64)

def observe : Argument → AtomValue
  | .signedWord word => .small word.toInt
  | .unsignedWord word => .large word.toNat

/-- Canonical scalar inspection selects its atom class without narrowing. -/
def canonical (word : UInt64) : AtomValue :=
  if word.toNat < 2 ^ 63 then .small word.toNat else .large word.toNat

/-- The fast signed encoding is guarded; the remaining word uses the
canonical unsigned-to-large-integer path. -/
def encode (word : UInt64) : Argument :=
  if word.toNat < 2 ^ 63 then .signedWord (Int64.ofInt word.toNat)
  else .unsignedWord word

theorem signed_fast_path_exact (word : UInt64) (bounded : word.toNat < 2 ^ 63) :
    (Int64.ofInt word.toNat).toInt = (word.toNat : Int) := by
  apply Int64.toInt_ofInt_of_le
  · omega
  · exact_mod_cast bounded

/-- The independently represented callback argument has exactly the
canonical atom observation, including its small/large class. -/
theorem observation_exact (word : UInt64) : observe (encode word) = canonical word := by
  unfold encode canonical
  by_cases bounded : word.toNat < 2 ^ 63
  · rw [if_pos bounded, if_pos bounded]
    exact congrArg AtomValue.small (signed_fast_path_exact word bounded)
  · rw [if_neg bounded, if_neg bounded]
    rfl

theorem callback_observation {Result : Type*} (callback : AtomValue → Option Result)
    (word : UInt64) : callback (observe (encode word)) = callback (canonical word) := by
  rw [observation_exact]

theorem ordered_input_observations (words : List UInt64) :
    words.map (fun word => observe (encode word)) = words.map canonical := by
  simp only [observation_exact]

def integerValue : AtomValue → Int
  | .small value => value
  | .large value => value

theorem no_wrap (word : UInt64) : integerValue (observe (encode word)) = word.toNat := by
  rw [observation_exact]
  simp only [canonical]
  split <;> rfl

example : observe (encode (UInt64.ofNat (2 ^ 63 - 1))) = .small (2 ^ 63 - 1) := by
  decide +kernel

example : observe (encode (UInt64.ofNat (2 ^ 63))) = .large (2 ^ 63) := by
  decide +kernel

example : observe (encode (UInt64.ofNat (2 ^ 64 - 1))) = .large (2 ^ 64 - 1) := by
  decide +kernel

/-- The unchecked signed cast is observably wrong at the unsigned maximum. -/
example : (Int64.ofInt ((UInt64.ofNat (2 ^ 64 - 1)).toNat)).toInt = -1 := by
  decide +kernel

#print axioms signed_fast_path_exact
#print axioms observation_exact
#print axioms callback_observation
#print axioms ordered_input_observations
#print axioms no_wrap

end Mettapedia.Machines.IndexScalarEncoding
