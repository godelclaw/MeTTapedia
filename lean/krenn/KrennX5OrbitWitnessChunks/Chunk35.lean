import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk35

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨67, .identity, .p021⟩, ⟨66, .identity, .p021⟩, ⟨70, .identity, .p021⟩, ⟨71, .identity, .p021⟩, ⟨68, .identity, .p021⟩, ⟨69, .identity, .p021⟩, ⟨73, .identity, .p021⟩, ⟨72, .identity, .p021⟩, ⟨76, .identity, .p021⟩, ⟨77, .identity, .p021⟩, ⟨74, .identity, .p021⟩, ⟨75, .identity, .p021⟩,
    ⟨49, .swap34, .p021⟩, ⟨48, .swap34, .p021⟩, ⟨52, .swap34, .p021⟩, ⟨53, .swap34, .p021⟩, ⟨50, .swap34, .p021⟩, ⟨51, .swap34, .p021⟩, ⟨19, .swap34, .p021⟩, ⟨18, .swap34, .p021⟩, ⟨22, .swap34, .p021⟩, ⟨23, .swap34, .p021⟩, ⟨20, .swap34, .p021⟩, ⟨21, .swap34, .p021⟩,
    ⟨97, .identity, .p021⟩, ⟨96, .identity, .p021⟩, ⟨100, .identity, .p021⟩, ⟨101, .identity, .p021⟩, ⟨98, .identity, .p021⟩, ⟨99, .identity, .p021⟩, ⟨103, .identity, .p021⟩, ⟨102, .identity, .p021⟩, ⟨106, .identity, .p021⟩, ⟨107, .identity, .p021⟩, ⟨104, .identity, .p021⟩, ⟨105, .identity, .p021⟩,
    ⟨73, .swap34, .p021⟩, ⟨72, .swap34, .p021⟩, ⟨76, .swap34, .p021⟩, ⟨77, .swap34, .p021⟩, ⟨74, .swap34, .p021⟩, ⟨75, .swap34, .p021⟩, ⟨91, .identity, .p021⟩, ⟨90, .identity, .p021⟩, ⟨94, .identity, .p021⟩, ⟨95, .identity, .p021⟩, ⟨92, .identity, .p021⟩, ⟨93, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1680) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1680 ≤ case.val)
    (upper : case.val < 1728) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1719 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1727 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk35.correct

end Krenn.X5OrbitWitnessChunks.Chunk35
