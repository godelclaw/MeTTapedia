import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk33

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨55, .swap34, .p021⟩, ⟨54, .swap34, .p021⟩, ⟨58, .swap34, .p021⟩, ⟨59, .swap34, .p021⟩, ⟨56, .swap34, .p021⟩, ⟨57, .swap34, .p021⟩, ⟨25, .swap34, .p021⟩, ⟨24, .swap34, .p021⟩, ⟨28, .swap34, .p021⟩, ⟨29, .swap34, .p021⟩, ⟨26, .swap34, .p021⟩, ⟨27, .swap34, .p021⟩,
    ⟨109, .identity, .p021⟩, ⟨108, .identity, .p021⟩, ⟨112, .identity, .p021⟩, ⟨113, .identity, .p021⟩, ⟨110, .identity, .p021⟩, ⟨111, .identity, .p021⟩, ⟨115, .identity, .p021⟩, ⟨114, .identity, .p021⟩, ⟨118, .identity, .p021⟩, ⟨119, .identity, .p021⟩, ⟨116, .identity, .p021⟩, ⟨117, .identity, .p021⟩,
    ⟨79, .swap34, .p021⟩, ⟨78, .swap34, .p021⟩, ⟨82, .swap34, .p021⟩, ⟨83, .swap34, .p021⟩, ⟨80, .swap34, .p021⟩, ⟨81, .swap34, .p021⟩, ⟨97, .swap34, .p021⟩, ⟨96, .swap34, .p021⟩, ⟨100, .swap34, .p021⟩, ⟨101, .swap34, .p021⟩, ⟨98, .swap34, .p021⟩, ⟨99, .swap34, .p021⟩,
    ⟨61, .swap34, .p021⟩, ⟨60, .swap34, .p021⟩, ⟨64, .swap34, .p021⟩, ⟨65, .swap34, .p021⟩, ⟨62, .swap34, .p021⟩, ⟨63, .swap34, .p021⟩, ⟨31, .swap34, .p021⟩, ⟨30, .swap34, .p021⟩, ⟨34, .swap34, .p021⟩, ⟨35, .swap34, .p021⟩, ⟨32, .swap34, .p021⟩, ⟨33, .swap34, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1584) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1584 ≤ case.val)
    (upper : case.val < 1632) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1623 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1631 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk33.correct

end Krenn.X5OrbitWitnessChunks.Chunk33
