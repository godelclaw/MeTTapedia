import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk44

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨235, .swap24, .p021⟩, ⟨234, .swap24, .p021⟩, ⟨238, .swap24, .p021⟩, ⟨239, .swap24, .p021⟩, ⟨236, .swap24, .p021⟩, ⟨237, .swap24, .p021⟩, ⟨253, .cycle234, .p021⟩, ⟨252, .cycle234, .p021⟩, ⟨256, .cycle234, .p021⟩, ⟨257, .cycle234, .p021⟩, ⟨254, .cycle234, .p021⟩, ⟨255, .cycle234, .p021⟩,
    ⟨193, .swap24, .p021⟩, ⟨192, .swap24, .p021⟩, ⟨196, .swap24, .p021⟩, ⟨197, .swap24, .p021⟩, ⟨194, .swap24, .p021⟩, ⟨195, .swap24, .p021⟩, ⟨103, .swap24, .p021⟩, ⟨102, .swap24, .p021⟩, ⟨106, .swap24, .p021⟩, ⟨107, .swap24, .p021⟩, ⟨104, .swap24, .p021⟩, ⟨105, .swap24, .p021⟩,
    ⟨301, .cycle234, .p021⟩, ⟨300, .cycle234, .p021⟩, ⟨304, .cycle234, .p021⟩, ⟨305, .cycle234, .p021⟩, ⟨302, .cycle234, .p021⟩, ⟨303, .cycle234, .p021⟩, ⟨307, .swap23, .p021⟩, ⟨306, .swap23, .p021⟩, ⟨310, .swap23, .p021⟩, ⟨311, .swap23, .p021⟩, ⟨308, .swap23, .p021⟩, ⟨309, .swap23, .p021⟩,
    ⟨253, .swap24, .p021⟩, ⟨252, .swap24, .p021⟩, ⟨256, .swap24, .p021⟩, ⟨257, .swap24, .p021⟩, ⟨254, .swap24, .p021⟩, ⟨255, .swap24, .p021⟩, ⟨289, .swap24, .p021⟩, ⟨288, .swap24, .p021⟩, ⟨292, .swap24, .p021⟩, ⟨293, .swap24, .p021⟩, ⟨290, .swap24, .p021⟩, ⟨291, .swap24, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2112) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2112 ≤ case.val)
    (upper : case.val < 2160) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2143 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2151 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2159 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk44.correct

end Krenn.X5OrbitWitnessChunks.Chunk44
