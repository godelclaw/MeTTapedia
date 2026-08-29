import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk46

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨79, .swap23, .p021⟩, ⟨78, .swap23, .p021⟩, ⟨82, .swap23, .p021⟩, ⟨83, .swap23, .p021⟩, ⟨80, .swap23, .p021⟩, ⟨81, .swap23, .p021⟩, ⟨85, .swap23, .p021⟩, ⟨84, .swap23, .p021⟩, ⟨88, .swap23, .p021⟩, ⟨89, .swap23, .p021⟩, ⟨86, .swap23, .p021⟩, ⟨87, .swap23, .p021⟩,
    ⟨67, .swap23, .p021⟩, ⟨66, .swap23, .p021⟩, ⟨70, .swap23, .p021⟩, ⟨71, .swap23, .p021⟩, ⟨68, .swap23, .p021⟩, ⟨69, .swap23, .p021⟩, ⟨73, .swap23, .p021⟩, ⟨72, .swap23, .p021⟩, ⟨76, .swap23, .p021⟩, ⟨77, .swap23, .p021⟩, ⟨74, .swap23, .p021⟩, ⟨75, .swap23, .p021⟩,
    ⟨169, .cycle243, .p021⟩, ⟨168, .cycle243, .p021⟩, ⟨172, .cycle243, .p021⟩, ⟨173, .cycle243, .p021⟩, ⟨170, .cycle243, .p021⟩, ⟨171, .cycle243, .p021⟩, ⟨79, .cycle243, .p021⟩, ⟨78, .cycle243, .p021⟩, ⟨82, .cycle243, .p021⟩, ⟨83, .cycle243, .p021⟩, ⟨80, .cycle243, .p021⟩, ⟨81, .cycle243, .p021⟩,
    ⟨259, .identity, .p021⟩, ⟨258, .identity, .p021⟩, ⟨262, .identity, .p021⟩, ⟨263, .identity, .p021⟩, ⟨260, .identity, .p021⟩, ⟨261, .identity, .p021⟩, ⟨265, .identity, .p021⟩, ⟨264, .identity, .p021⟩, ⟨268, .identity, .p021⟩, ⟨269, .identity, .p021⟩, ⟨266, .identity, .p021⟩, ⟨267, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2208) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2208 ≤ case.val)
    (upper : case.val < 2256) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2239 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2247 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2255 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk46.correct

end Krenn.X5OrbitWitnessChunks.Chunk46
