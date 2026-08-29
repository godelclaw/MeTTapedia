import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk48

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨157, .swap24, .p021⟩, ⟨156, .swap24, .p021⟩, ⟨160, .swap24, .p021⟩, ⟨161, .swap24, .p021⟩, ⟨158, .swap24, .p021⟩, ⟨159, .swap24, .p021⟩, ⟨67, .swap24, .p021⟩, ⟨66, .swap24, .p021⟩, ⟨70, .swap24, .p021⟩, ⟨71, .swap24, .p021⟩, ⟨68, .swap24, .p021⟩, ⟨69, .swap24, .p021⟩,
    ⟨229, .identity, .p021⟩, ⟨228, .identity, .p021⟩, ⟨232, .identity, .p021⟩, ⟨233, .identity, .p021⟩, ⟨230, .identity, .p021⟩, ⟨231, .identity, .p021⟩, ⟨235, .identity, .p021⟩, ⟨234, .identity, .p021⟩, ⟨238, .identity, .p021⟩, ⟨239, .identity, .p021⟩, ⟨236, .identity, .p021⟩, ⟨237, .identity, .p021⟩,
    ⟨217, .identity, .p021⟩, ⟨216, .identity, .p021⟩, ⟨220, .identity, .p021⟩, ⟨221, .identity, .p021⟩, ⟨218, .identity, .p021⟩, ⟨219, .identity, .p021⟩, ⟨223, .identity, .p021⟩, ⟨222, .identity, .p021⟩, ⟨226, .identity, .p021⟩, ⟨227, .identity, .p021⟩, ⟨224, .identity, .p021⟩, ⟨225, .identity, .p021⟩,
    ⟨163, .cycle243, .p021⟩, ⟨162, .cycle243, .p021⟩, ⟨166, .cycle243, .p021⟩, ⟨167, .cycle243, .p021⟩, ⟨164, .cycle243, .p021⟩, ⟨165, .cycle243, .p021⟩, ⟨73, .cycle243, .p021⟩, ⟨72, .cycle243, .p021⟩, ⟨76, .cycle243, .p021⟩, ⟨77, .cycle243, .p021⟩, ⟨74, .cycle243, .p021⟩, ⟨75, .cycle243, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2304) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2304 ≤ case.val)
    (upper : case.val < 2352) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2335 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2343 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2351 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk48.correct

end Krenn.X5OrbitWitnessChunks.Chunk48
