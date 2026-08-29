import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk47

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨229, .swap34, .p021⟩, ⟨228, .swap34, .p021⟩, ⟨232, .swap34, .p021⟩, ⟨233, .swap34, .p021⟩, ⟨230, .swap34, .p021⟩, ⟨231, .swap34, .p021⟩, ⟨247, .swap34, .p021⟩, ⟨246, .swap34, .p021⟩, ⟨250, .swap34, .p021⟩, ⟨251, .swap34, .p021⟩, ⟨248, .swap34, .p021⟩, ⟨249, .swap34, .p021⟩,
    ⟨175, .cycle243, .p021⟩, ⟨174, .cycle243, .p021⟩, ⟨178, .cycle243, .p021⟩, ⟨179, .cycle243, .p021⟩, ⟨176, .cycle243, .p021⟩, ⟨177, .cycle243, .p021⟩, ⟨85, .cycle243, .p021⟩, ⟨84, .cycle243, .p021⟩, ⟨88, .cycle243, .p021⟩, ⟨89, .cycle243, .p021⟩, ⟨86, .cycle243, .p021⟩, ⟨87, .cycle243, .p021⟩,
    ⟨265, .swap34, .p021⟩, ⟨264, .swap34, .p021⟩, ⟨268, .swap34, .p021⟩, ⟨269, .swap34, .p021⟩, ⟨266, .swap34, .p021⟩, ⟨267, .swap34, .p021⟩, ⟨271, .identity, .p021⟩, ⟨270, .identity, .p021⟩, ⟨274, .identity, .p021⟩, ⟨275, .identity, .p021⟩, ⟨272, .identity, .p021⟩, ⟨273, .identity, .p021⟩,
    ⟨235, .swap34, .p021⟩, ⟨234, .swap34, .p021⟩, ⟨238, .swap34, .p021⟩, ⟨239, .swap34, .p021⟩, ⟨236, .swap34, .p021⟩, ⟨237, .swap34, .p021⟩, ⟨253, .swap34, .p021⟩, ⟨252, .swap34, .p021⟩, ⟨256, .swap34, .p021⟩, ⟨257, .swap34, .p021⟩, ⟨254, .swap34, .p021⟩, ⟨255, .swap34, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2256) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2256 ≤ case.val)
    (upper : case.val < 2304) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2287 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2295 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2303 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk47.correct

end Krenn.X5OrbitWitnessChunks.Chunk47
