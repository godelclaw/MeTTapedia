import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mathlib.Data.W.Basic
import Mathlib.Data.Nat.Size

/-!
# Exact coding of ordered finite derivation certificates

The node payload codec includes every rule parameter. Ordered certificate trees
are represented by the standard finitely branching W type; its constructive
codec supplies an enumeration without a completeness oracle. The wire-size
bound is the bit length of this complete encoding, rather than a node count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Tree

universe u

variable {P : Presentation.{u}}

def toW : Tree P → WType (fun rule : P.Rule => Fin (P.premises rule).length)
  | .node rule children => .mk rule (fun position => toW (children position))

def fromW : WType (fun rule : P.Rule => Fin (P.premises rule).length) → Tree P
  | .mk rule children => .node rule (fun position => fromW (children position))

theorem fromW_toW (tree : Tree P) : fromW (toW tree) = tree := by
  induction tree with
  | node rule children ih =>
      change Tree.node rule (fun position => fromW (toW (children position))) =
        Tree.node rule children
      congr 1
      funext position
      exact ih position

instance [Encodable P.Rule] : Encodable (Tree P) :=
  Encodable.ofLeftInverse toW fromW fromW_toW

def wireSize [Encodable P.Rule] (tree : Tree P) : Nat :=
  Nat.size (Encodable.encode tree)

def discoveryBound (wireBits : Nat) : Nat := 2 ^ wireBits

theorem code_lt_discoveryBound [Encodable P.Rule] (tree : Tree P) :
    Encodable.encode tree < discoveryBound (wireSize tree) := Nat.lt_size_self _

theorem decode_encode [Encodable P.Rule] (tree : Tree P) :
    Encodable.decode (α := Tree P) (Encodable.encode tree) = some tree := Encodable.encodek tree

theorem distinct_codes [Encodable P.Rule] {first second : Tree P}
    (different : first ≠ second) : Encodable.encode first ≠ Encodable.encode second :=
  fun same => different (Encodable.encode_injective same)

end Mettapedia.OSLF.NativeTypes.Certificates.Tree
