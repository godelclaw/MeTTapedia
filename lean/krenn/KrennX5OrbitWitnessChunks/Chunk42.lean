import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk42

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨205, .swap24, .p021⟩, ⟨204, .swap24, .p021⟩, ⟨208, .swap24, .p021⟩, ⟨209, .swap24, .p021⟩, ⟨206, .swap24, .p021⟩, ⟨207, .swap24, .p021⟩, ⟨115, .swap24, .p021⟩, ⟨114, .swap24, .p021⟩, ⟨118, .swap24, .p021⟩, ⟨119, .swap24, .p021⟩, ⟨116, .swap24, .p021⟩, ⟨117, .swap24, .p021⟩,
    ⟨319, .swap24, .p021⟩, ⟨318, .swap24, .p021⟩, ⟨322, .swap24, .p021⟩, ⟨323, .swap24, .p021⟩, ⟨320, .swap24, .p021⟩, ⟨321, .swap24, .p021⟩, ⟨325, .swap23, .p021⟩, ⟨324, .swap23, .p021⟩, ⟨328, .swap23, .p021⟩, ⟨329, .swap23, .p021⟩, ⟨326, .swap23, .p021⟩, ⟨327, .swap23, .p021⟩,
    ⟨265, .swap24, .p021⟩, ⟨264, .swap24, .p021⟩, ⟨268, .swap24, .p021⟩, ⟨269, .swap24, .p021⟩, ⟨266, .swap24, .p021⟩, ⟨267, .swap24, .p021⟩, ⟨301, .swap24, .p021⟩, ⟨300, .swap24, .p021⟩, ⟨304, .swap24, .p021⟩, ⟨305, .swap24, .p021⟩, ⟨302, .swap24, .p021⟩, ⟨303, .swap24, .p021⟩,
    ⟨211, .swap24, .p021⟩, ⟨210, .swap24, .p021⟩, ⟨214, .swap24, .p021⟩, ⟨215, .swap24, .p021⟩, ⟨212, .swap24, .p021⟩, ⟨213, .swap24, .p021⟩, ⟨121, .swap24, .p021⟩, ⟨120, .swap24, .p021⟩, ⟨124, .swap24, .p021⟩, ⟨125, .swap24, .p021⟩, ⟨122, .swap24, .p021⟩, ⟨123, .swap24, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2016) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2016 ≤ case.val)
    (upper : case.val < 2064) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2023 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2031 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2039 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2047 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2055 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2063 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk42.correct

end Krenn.X5OrbitWitnessChunks.Chunk42
