import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk37

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨109, .swap23, .p021⟩, ⟨108, .swap23, .p021⟩, ⟨112, .swap23, .p021⟩, ⟨113, .swap23, .p021⟩, ⟨110, .swap23, .p021⟩, ⟨111, .swap23, .p021⟩, ⟨115, .swap23, .p021⟩, ⟨114, .swap23, .p021⟩, ⟨118, .swap23, .p021⟩, ⟨119, .swap23, .p021⟩, ⟨116, .swap23, .p021⟩, ⟨117, .swap23, .p021⟩,
    ⟨79, .cycle234, .p021⟩, ⟨78, .cycle234, .p021⟩, ⟨82, .cycle234, .p021⟩, ⟨83, .cycle234, .p021⟩, ⟨80, .cycle234, .p021⟩, ⟨81, .cycle234, .p021⟩, ⟨97, .cycle234, .p021⟩, ⟨96, .cycle234, .p021⟩, ⟨100, .cycle234, .p021⟩, ⟨101, .cycle234, .p021⟩, ⟨98, .cycle234, .p021⟩, ⟨99, .cycle234, .p021⟩,
    ⟨199, .swap24, .p021⟩, ⟨198, .swap24, .p021⟩, ⟨202, .swap24, .p021⟩, ⟨203, .swap24, .p021⟩, ⟨200, .swap24, .p021⟩, ⟨201, .swap24, .p021⟩, ⟨109, .swap24, .p021⟩, ⟨108, .swap24, .p021⟩, ⟨112, .swap24, .p021⟩, ⟨113, .swap24, .p021⟩, ⟨110, .swap24, .p021⟩, ⟨111, .swap24, .p021⟩,
    ⟨313, .identity, .p021⟩, ⟨312, .identity, .p021⟩, ⟨316, .identity, .p021⟩, ⟨317, .identity, .p021⟩, ⟨314, .identity, .p021⟩, ⟨315, .identity, .p021⟩, ⟨319, .identity, .p021⟩, ⟨318, .identity, .p021⟩, ⟨322, .identity, .p021⟩, ⟨323, .identity, .p021⟩, ⟨320, .identity, .p021⟩, ⟨321, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1776) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1776 ≤ case.val)
    (upper : case.val < 1824) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1783 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1791 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1799 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1807 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1815 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1823 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk37.correct

end Krenn.X5OrbitWitnessChunks.Chunk37
