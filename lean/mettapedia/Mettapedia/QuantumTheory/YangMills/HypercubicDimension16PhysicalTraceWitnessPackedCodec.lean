import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessTypes
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-!
# Packed decoder for the selected physical trace witnesses

This is OUR finite-data realization of the selected standard rows.  A witness
occupies a fixed 514-bit word: the source trace code, three sites, six
fixed-width coordinate slots, and a one-bit kind tag.  The decoder is a small
transparent arithmetic map, so the existing finite replay certificates remain
kernel checks of the decoded rows.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessPackedCodec

open HypercubicDimension16PhysicalTraceWitnessTypes
open HypercubicDimension16PackedFiniteDataCodec

/-- Extract a fixed-width little-endian field from a packed witness word. -/
@[reducible] def packedField (word offset width : Nat) : Nat :=
  (word / 2 ^ offset) % (2 ^ width)

@[reducible] def sourceField (word field : Nat) : Nat :=
  packedField word (3 * field) 3

/-- The 24-letter source trace code. -/
@[reducible] def decodeSourceCode (word : Nat) : Array Nat :=
  #[sourceField word 0, sourceField word 1, sourceField word 2,
    sourceField word 3, sourceField word 4, sourceField word 5,
    sourceField word 6, sourceField word 7, sourceField word 8,
    sourceField word 9, sourceField word 10, sourceField word 11,
    sourceField word 12, sourceField word 13, sourceField word 14,
    sourceField word 15, sourceField word 16, sourceField word 17,
    sourceField word 18, sourceField word 19, sourceField word 20,
    sourceField word 21, sourceField word 22, sourceField word 23]

@[reducible] def coordinateOffset (coordinate : Nat) : Nat :=
  81 + 72 * coordinate

@[reducible] def coordinateField
    (word coordinate offset width : Nat) : Nat :=
  packedField word (coordinateOffset coordinate + offset) width

/-- Decode one of the six fixed-width coordinate slots. -/
@[reducible] def decodeCoordinate
    (word coordinate : Nat) : EncodedOrbitCoordinateWitness where
  coefficient :=
    if coordinateField word coordinate 0 1 = 0 then (-1 : Int) else 1
  representative := coordinateField word coordinate 1 14
  permutation := coordinateField word coordinate 15 5
  reflection := coordinateField word coordinate 20 4
  renameForward :=
    #[coordinateField word coordinate 24 3,
      coordinateField word coordinate 27 3,
      coordinateField word coordinate 30 3,
      coordinateField word coordinate 33 3,
      coordinateField word coordinate 36 3,
      coordinateField word coordinate 39 3,
      coordinateField word coordinate 42 3,
      coordinateField word coordinate 45 3]
  renameBackward :=
    #[coordinateField word coordinate 48 3,
      coordinateField word coordinate 51 3,
      coordinateField word coordinate 54 3,
      coordinateField word coordinate 57 3,
      coordinateField word coordinate 60 3,
      coordinateField word coordinate 63 3,
      coordinateField word coordinate 66 3,
      coordinateField word coordinate 69 3]

/-- The kind tag selects one traceless coordinate or six fundamental ones. -/
@[reducible] def decodeKind (word : Nat) : Nat :=
  if packedField word 513 1 = 0 then 0 else 2

@[reducible] def decodeCoordinates (word : Nat) : Array EncodedOrbitCoordinateWitness :=
  if decodeKind word = 0 then
    #[decodeCoordinate word 0]
  else
    #[decodeCoordinate word 0, decodeCoordinate word 1,
      decodeCoordinate word 2, decodeCoordinate word 3,
      decodeCoordinate word 4, decodeCoordinate word 5]

/-- Decode the complete finite witness carried by one packed word. -/
@[reducible] def decodePhysicalTraceWitness
    (word : Nat) : EncodedPhysicalTraceWitness where
  kind := decodeKind word
  sourceCode := decodeSourceCode word
  first := packedField word 72 3
  second := packedField word 75 3
  third := packedField word 78 3
  coordinates := decodeCoordinates word

end HypercubicDimension16PhysicalTraceWitnessPackedCodec
end YangMills
end QuantumTheory
end Mettapedia
