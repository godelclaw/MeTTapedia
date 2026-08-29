import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk45

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨133, .swap24, .p021⟩, ⟨132, .swap24, .p021⟩, ⟨136, .swap24, .p021⟩, ⟨137, .swap24, .p021⟩, ⟨134, .swap24, .p021⟩, ⟨135, .swap24, .p021⟩, ⟨43, .swap24, .p021⟩, ⟨42, .swap24, .p021⟩, ⟨46, .swap24, .p021⟩, ⟨47, .swap24, .p021⟩, ⟨44, .swap24, .p021⟩, ⟨45, .swap24, .p021⟩,
    ⟨169, .swap23, .p021⟩, ⟨168, .swap23, .p021⟩, ⟨172, .swap23, .p021⟩, ⟨173, .swap23, .p021⟩, ⟨170, .swap23, .p021⟩, ⟨171, .swap23, .p021⟩, ⟨175, .swap23, .p021⟩, ⟨174, .swap23, .p021⟩, ⟨178, .swap23, .p021⟩, ⟨179, .swap23, .p021⟩, ⟨176, .swap23, .p021⟩, ⟨177, .swap23, .p021⟩,
    ⟨157, .swap23, .p021⟩, ⟨156, .swap23, .p021⟩, ⟨160, .swap23, .p021⟩, ⟨161, .swap23, .p021⟩, ⟨158, .swap23, .p021⟩, ⟨159, .swap23, .p021⟩, ⟨163, .swap23, .p021⟩, ⟨162, .swap23, .p021⟩, ⟨166, .swap23, .p021⟩, ⟨167, .swap23, .p021⟩, ⟨164, .swap23, .p021⟩, ⟨165, .swap23, .p021⟩,
    ⟨43, .cycle234, .p021⟩, ⟨42, .cycle234, .p021⟩, ⟨46, .cycle234, .p021⟩, ⟨47, .cycle234, .p021⟩, ⟨44, .cycle234, .p021⟩, ⟨45, .cycle234, .p021⟩, ⟨13, .swap24, .p021⟩, ⟨12, .swap24, .p021⟩, ⟨16, .swap24, .p021⟩, ⟨17, .swap24, .p021⟩, ⟨14, .swap24, .p021⟩, ⟨15, .swap24, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2160) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2160 ≤ case.val)
    (upper : case.val < 2208) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2191 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2199 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2207 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk45.correct

end Krenn.X5OrbitWitnessChunks.Chunk45
