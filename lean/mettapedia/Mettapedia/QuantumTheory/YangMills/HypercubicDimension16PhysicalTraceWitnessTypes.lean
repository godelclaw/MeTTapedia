import Mathlib.Data.Rat.Defs

/-!
# Finite witness types for eight-field standard trace rows

The data carried here records standard hypercubic and field-relabel actions.
Its meaning is supplied by a separate semantic decoder and kernel-checked
validity theorem.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessTypes

/-- One literal term of a trace identity, together with a standard orbit
representative witness. -/
structure EncodedOrbitCoordinateWitness where
  coefficient : Int
  representative : Nat
  permutation : Nat
  reflection : Nat
  renameForward : Array Nat
  renameBackward : Array Nat
deriving DecidableEq

/-- A selected traceless or fundamental `2 x 2` trace row.  Kind zero is a
one-letter traceless row; kind two is the six-term fundamental identity. -/
structure EncodedPhysicalTraceWitness where
  kind : Nat
  sourceCode : Array Nat
  first : Nat
  second : Nat
  third : Nat
  coordinates : Array EncodedOrbitCoordinateWitness
deriving DecidableEq

end HypercubicDimension16PhysicalTraceWitnessTypes
end YangMills
end QuantumTheory
end Mettapedia
