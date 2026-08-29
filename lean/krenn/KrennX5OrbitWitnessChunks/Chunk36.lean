import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk36

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨145, .swap24, .p021⟩, ⟨144, .swap24, .p021⟩, ⟨148, .swap24, .p021⟩, ⟨149, .swap24, .p021⟩, ⟨146, .swap24, .p021⟩, ⟨147, .swap24, .p021⟩, ⟨55, .swap24, .p021⟩, ⟨54, .swap24, .p021⟩, ⟨58, .swap24, .p021⟩, ⟨59, .swap24, .p021⟩, ⟨56, .swap24, .p021⟩, ⟨57, .swap24, .p021⟩,
    ⟨199, .swap23, .p021⟩, ⟨198, .swap23, .p021⟩, ⟨202, .swap23, .p021⟩, ⟨203, .swap23, .p021⟩, ⟨200, .swap23, .p021⟩, ⟨201, .swap23, .p021⟩, ⟨205, .swap23, .p021⟩, ⟨204, .swap23, .p021⟩, ⟨208, .swap23, .p021⟩, ⟨209, .swap23, .p021⟩, ⟨206, .swap23, .p021⟩, ⟨207, .swap23, .p021⟩,
    ⟨169, .cycle234, .p021⟩, ⟨168, .cycle234, .p021⟩, ⟨172, .cycle234, .p021⟩, ⟨173, .cycle234, .p021⟩, ⟨170, .cycle234, .p021⟩, ⟨171, .cycle234, .p021⟩, ⟨187, .cycle234, .p021⟩, ⟨186, .cycle234, .p021⟩, ⟨190, .cycle234, .p021⟩, ⟨191, .cycle234, .p021⟩, ⟨188, .cycle234, .p021⟩, ⟨189, .cycle234, .p021⟩,
    ⟨55, .cycle234, .p021⟩, ⟨54, .cycle234, .p021⟩, ⟨58, .cycle234, .p021⟩, ⟨59, .cycle234, .p021⟩, ⟨56, .cycle234, .p021⟩, ⟨57, .cycle234, .p021⟩, ⟨25, .swap24, .p021⟩, ⟨24, .swap24, .p021⟩, ⟨28, .swap24, .p021⟩, ⟨29, .swap24, .p021⟩, ⟨26, .swap24, .p021⟩, ⟨27, .swap24, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1728) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1728 ≤ case.val)
    (upper : case.val < 1776) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1767 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1775 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk36.correct

end Krenn.X5OrbitWitnessChunks.Chunk36
