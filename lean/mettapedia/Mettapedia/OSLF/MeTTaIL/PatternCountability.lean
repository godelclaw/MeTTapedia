import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.Data.String.Countability
import Mathlib.Tactic.DeriveCountable
import Mathlib.Data.Countable.Basic

/-!
# Countability of the complete authored pattern syntax

The independently formed mutual code replaces recursive lists with an
explicit spine. Encoding retains every constructor, index, display name,
collection kind and collection remainder. Decoding recovers the original
pattern and each ordered argument list, earning an injection into a
countable carrier without changing the authored syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternCountability

open Syntax

deriving instance Countable for CollType

mutual
inductive Code where
  | bvar : Nat → Code
  | fvar : String → Code
  | apply : String → Arguments → Code
  | lambda : Option String → Code → Code
  | multiLambda : Nat → List String → Code → Code
  | subst : Code → Code → Code
  | collection : CollType → Arguments → Option String → Code

inductive Arguments where
  | nil : Arguments
  | cons : Code → Arguments → Arguments
end

deriving instance Countable for Code, Arguments

mutual
def encode : Pattern → Code
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply name arguments => .apply name (encodeArguments arguments)
  | .lambda name body => .lambda name (encode body)
  | .multiLambda count names body => .multiLambda count names (encode body)
  | .subst body value => .subst (encode body) (encode value)
  | .collection kind values remainder => .collection kind (encodeArguments values) remainder

def encodeArguments : List Pattern → Arguments
  | [] => .nil
  | head :: tail => .cons (encode head) (encodeArguments tail)
end

mutual
def decode : Code → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply name arguments => .apply name (decodeArguments arguments)
  | .lambda name body => .lambda name (decode body)
  | .multiLambda count names body => .multiLambda count names (decode body)
  | .subst body value => .subst (decode body) (decode value)
  | .collection kind values remainder => .collection kind (decodeArguments values) remainder

def decodeArguments : Arguments → List Pattern
  | .nil => []
  | .cons head tail => decode head :: decodeArguments tail
end

mutual
theorem decode_encode : ∀ pattern : Pattern, decode (encode pattern) = pattern
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by simp only [encode, decode, decode_encodeArguments]
  | .lambda _ body => by simp only [encode, decode, decode_encode body]
  | .multiLambda _ _ body => by simp only [encode, decode, decode_encode body]
  | .subst body value => by simp only [encode, decode, decode_encode body, decode_encode value]
  | .collection _ values _ => by simp only [encode, decode, decode_encodeArguments]

theorem decode_encodeArguments : ∀ values : List Pattern, decodeArguments (encodeArguments values) = values
  | [] => rfl
  | head :: tail => by simp only [encodeArguments, decodeArguments, decode_encode,
      decode_encodeArguments]
end

theorem encode_injective : Function.Injective encode := by
  intro first second same
  exact (decode_encode first).symm.trans ((congrArg decode same).trans (decode_encode second))

instance : Countable Pattern := encode_injective.countable

theorem reordered_arguments_distinct :
    encode (.apply "pair" [.bvar 0, .bvar 1]) ≠ encode (.apply "pair" [.bvar 1, .bvar 0]) := by
  intro same
  have patterns := encode_injective same
  cases patterns

theorem collection_multiplicity_retained :
    encode (.collection .hashBag [.bvar 0, .bvar 0] none) ≠
      encode (.collection .hashBag [.bvar 0] none) := by
  intro same
  have patterns := encode_injective same
  cases patterns

end Mettapedia.OSLF.MeTTaIL.PatternCountability
