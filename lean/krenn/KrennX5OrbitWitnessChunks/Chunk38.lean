import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk38

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨259, .swap24, .p021⟩, ⟨258, .swap24, .p021⟩, ⟨262, .swap24, .p021⟩, ⟨263, .swap24, .p021⟩, ⟨260, .swap24, .p021⟩, ⟨261, .swap24, .p021⟩, ⟨295, .swap24, .p021⟩, ⟨294, .swap24, .p021⟩, ⟨298, .swap24, .p021⟩, ⟨299, .swap24, .p021⟩, ⟨296, .swap24, .p021⟩, ⟨297, .swap24, .p021⟩,
    ⟨205, .cycle243, .p021⟩, ⟨204, .cycle243, .p021⟩, ⟨208, .cycle243, .p021⟩, ⟨209, .cycle243, .p021⟩, ⟨206, .cycle243, .p021⟩, ⟨207, .cycle243, .p021⟩, ⟨115, .cycle243, .p021⟩, ⟨114, .cycle243, .p021⟩, ⟨118, .cycle243, .p021⟩, ⟨119, .cycle243, .p021⟩, ⟨116, .cycle243, .p021⟩, ⟨117, .cycle243, .p021⟩,
    ⟨319, .swap34, .p021⟩, ⟨318, .swap34, .p021⟩, ⟨322, .swap34, .p021⟩, ⟨323, .swap34, .p021⟩, ⟨320, .swap34, .p021⟩, ⟨321, .swap34, .p021⟩, ⟨325, .identity, .p021⟩, ⟨324, .identity, .p021⟩, ⟨328, .identity, .p021⟩, ⟨329, .identity, .p021⟩, ⟨326, .identity, .p021⟩, ⟨327, .identity, .p021⟩,
    ⟨265, .cycle243, .p021⟩, ⟨264, .cycle243, .p021⟩, ⟨268, .cycle243, .p021⟩, ⟨269, .cycle243, .p021⟩, ⟨266, .cycle243, .p021⟩, ⟨267, .cycle243, .p021⟩, ⟨301, .cycle243, .p021⟩, ⟨300, .cycle243, .p021⟩, ⟨304, .cycle243, .p021⟩, ⟨305, .cycle243, .p021⟩, ⟨302, .cycle243, .p021⟩, ⟨303, .cycle243, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1824) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1824 ≤ case.val)
    (upper : case.val < 1872) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1831 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1839 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1847 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1855 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1863 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1871 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk38.correct

end Krenn.X5OrbitWitnessChunks.Chunk38
