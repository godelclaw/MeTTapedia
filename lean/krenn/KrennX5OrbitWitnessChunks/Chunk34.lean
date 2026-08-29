import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk34

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨115, .swap34, .p021⟩, ⟨114, .swap34, .p021⟩, ⟨118, .swap34, .p021⟩, ⟨119, .swap34, .p021⟩, ⟨116, .swap34, .p021⟩, ⟨117, .swap34, .p021⟩, ⟨121, .identity, .p021⟩, ⟨120, .identity, .p021⟩, ⟨124, .identity, .p021⟩, ⟨125, .identity, .p021⟩, ⟨122, .identity, .p021⟩, ⟨123, .identity, .p021⟩,
    ⟨85, .swap34, .p021⟩, ⟨84, .swap34, .p021⟩, ⟨88, .swap34, .p021⟩, ⟨89, .swap34, .p021⟩, ⟨86, .swap34, .p021⟩, ⟨87, .swap34, .p021⟩, ⟨103, .swap34, .p021⟩, ⟨102, .swap34, .p021⟩, ⟨106, .swap34, .p021⟩, ⟨107, .swap34, .p021⟩, ⟨104, .swap34, .p021⟩, ⟨105, .swap34, .p021⟩,
    ⟨43, .swap34, .p021⟩, ⟨42, .swap34, .p021⟩, ⟨46, .swap34, .p021⟩, ⟨47, .swap34, .p021⟩, ⟨44, .swap34, .p021⟩, ⟨45, .swap34, .p021⟩, ⟨13, .swap34, .p021⟩, ⟨12, .swap34, .p021⟩, ⟨16, .swap34, .p021⟩, ⟨17, .swap34, .p021⟩, ⟨14, .swap34, .p021⟩, ⟨15, .swap34, .p021⟩,
    ⟨79, .identity, .p021⟩, ⟨78, .identity, .p021⟩, ⟨82, .identity, .p021⟩, ⟨83, .identity, .p021⟩, ⟨80, .identity, .p021⟩, ⟨81, .identity, .p021⟩, ⟨85, .identity, .p021⟩, ⟨84, .identity, .p021⟩, ⟨88, .identity, .p021⟩, ⟨89, .identity, .p021⟩, ⟨86, .identity, .p021⟩, ⟨87, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1632) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1632 ≤ case.val)
    (upper : case.val < 1680) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1671 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1679 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk34.correct

end Krenn.X5OrbitWitnessChunks.Chunk34
