import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk39

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨169, .swap24, .p021⟩, ⟨168, .swap24, .p021⟩, ⟨172, .swap24, .p021⟩, ⟨173, .swap24, .p021⟩, ⟨170, .swap24, .p021⟩, ⟨171, .swap24, .p021⟩, ⟨79, .swap24, .p021⟩, ⟨78, .swap24, .p021⟩, ⟨82, .swap24, .p021⟩, ⟨83, .swap24, .p021⟩, ⟨80, .swap24, .p021⟩, ⟨81, .swap24, .p021⟩,
    ⟨259, .swap23, .p021⟩, ⟨258, .swap23, .p021⟩, ⟨262, .swap23, .p021⟩, ⟨263, .swap23, .p021⟩, ⟨260, .swap23, .p021⟩, ⟨261, .swap23, .p021⟩, ⟨265, .swap23, .p021⟩, ⟨264, .swap23, .p021⟩, ⟨268, .swap23, .p021⟩, ⟨269, .swap23, .p021⟩, ⟨266, .swap23, .p021⟩, ⟨267, .swap23, .p021⟩,
    ⟨229, .swap24, .p021⟩, ⟨228, .swap24, .p021⟩, ⟨232, .swap24, .p021⟩, ⟨233, .swap24, .p021⟩, ⟨230, .swap24, .p021⟩, ⟨231, .swap24, .p021⟩, ⟨247, .cycle234, .p021⟩, ⟨246, .cycle234, .p021⟩, ⟨250, .cycle234, .p021⟩, ⟨251, .cycle234, .p021⟩, ⟨248, .cycle234, .p021⟩, ⟨249, .cycle234, .p021⟩,
    ⟨187, .swap24, .p021⟩, ⟨186, .swap24, .p021⟩, ⟨190, .swap24, .p021⟩, ⟨191, .swap24, .p021⟩, ⟨188, .swap24, .p021⟩, ⟨189, .swap24, .p021⟩, ⟨97, .swap24, .p021⟩, ⟨96, .swap24, .p021⟩, ⟨100, .swap24, .p021⟩, ⟨101, .swap24, .p021⟩, ⟨98, .swap24, .p021⟩, ⟨99, .swap24, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1872) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1872 ≤ case.val)
    (upper : case.val < 1920) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1879 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1887 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1895 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1903 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1911 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1919 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk39.correct

end Krenn.X5OrbitWitnessChunks.Chunk39
