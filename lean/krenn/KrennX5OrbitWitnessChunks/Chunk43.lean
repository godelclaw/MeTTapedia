import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk43

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨325, .swap24, .p021⟩, ⟨324, .swap24, .p021⟩, ⟨328, .swap24, .p021⟩, ⟨329, .swap24, .p021⟩, ⟨326, .swap24, .p021⟩, ⟨327, .swap24, .p021⟩, ⟨331, .identity, .p021⟩, ⟨330, .identity, .p021⟩, ⟨334, .identity, .p021⟩, ⟨335, .identity, .p021⟩, ⟨332, .identity, .p021⟩, ⟨333, .identity, .p021⟩,
    ⟨271, .swap24, .p021⟩, ⟨270, .swap24, .p021⟩, ⟨274, .swap24, .p021⟩, ⟨275, .swap24, .p021⟩, ⟨272, .swap24, .p021⟩, ⟨273, .swap24, .p021⟩, ⟨307, .swap24, .p021⟩, ⟨306, .swap24, .p021⟩, ⟨310, .swap24, .p021⟩, ⟨311, .swap24, .p021⟩, ⟨308, .swap24, .p021⟩, ⟨309, .swap24, .p021⟩,
    ⟨175, .swap24, .p021⟩, ⟨174, .swap24, .p021⟩, ⟨178, .swap24, .p021⟩, ⟨179, .swap24, .p021⟩, ⟨176, .swap24, .p021⟩, ⟨177, .swap24, .p021⟩, ⟨85, .swap24, .p021⟩, ⟨84, .swap24, .p021⟩, ⟨88, .swap24, .p021⟩, ⟨89, .swap24, .p021⟩, ⟨86, .swap24, .p021⟩, ⟨87, .swap24, .p021⟩,
    ⟨265, .cycle234, .p021⟩, ⟨264, .cycle234, .p021⟩, ⟨268, .cycle234, .p021⟩, ⟨269, .cycle234, .p021⟩, ⟨266, .cycle234, .p021⟩, ⟨267, .cycle234, .p021⟩, ⟨271, .swap23, .p021⟩, ⟨270, .swap23, .p021⟩, ⟨274, .swap23, .p021⟩, ⟨275, .swap23, .p021⟩, ⟨272, .swap23, .p021⟩, ⟨273, .swap23, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2064) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2064 ≤ case.val)
    (upper : case.val < 2112) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2071 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2079 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2087 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2095 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2103 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2111 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk43.correct

end Krenn.X5OrbitWitnessChunks.Chunk43
