import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk49

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨247, .identity, .p021⟩, ⟨246, .identity, .p021⟩, ⟨250, .identity, .p021⟩, ⟨251, .identity, .p021⟩, ⟨248, .identity, .p021⟩, ⟨249, .identity, .p021⟩, ⟨253, .identity, .p021⟩, ⟨252, .identity, .p021⟩, ⟨256, .identity, .p021⟩, ⟨257, .identity, .p021⟩, ⟨254, .identity, .p021⟩, ⟨255, .identity, .p021⟩,
    ⟨223, .swap34, .p021⟩, ⟨222, .swap34, .p021⟩, ⟨226, .swap34, .p021⟩, ⟨227, .swap34, .p021⟩, ⟨224, .swap34, .p021⟩, ⟨225, .swap34, .p021⟩, ⟨241, .identity, .p021⟩, ⟨240, .identity, .p021⟩, ⟨244, .identity, .p021⟩, ⟨245, .identity, .p021⟩, ⟨242, .identity, .p021⟩, ⟨243, .identity, .p021⟩,
    ⟨139, .swap24, .p021⟩, ⟨138, .swap24, .p021⟩, ⟨142, .swap24, .p021⟩, ⟨143, .swap24, .p021⟩, ⟨140, .swap24, .p021⟩, ⟨141, .swap24, .p021⟩, ⟨49, .swap24, .p021⟩, ⟨48, .swap24, .p021⟩, ⟨52, .swap24, .p021⟩, ⟨53, .swap24, .p021⟩, ⟨50, .swap24, .p021⟩, ⟨51, .swap24, .p021⟩,
    ⟨187, .swap23, .p021⟩, ⟨186, .swap23, .p021⟩, ⟨190, .swap23, .p021⟩, ⟨191, .swap23, .p021⟩, ⟨188, .swap23, .p021⟩, ⟨189, .swap23, .p021⟩, ⟨193, .swap23, .p021⟩, ⟨192, .swap23, .p021⟩, ⟨196, .swap23, .p021⟩, ⟨197, .swap23, .p021⟩, ⟨194, .swap23, .p021⟩, ⟨195, .swap23, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2352) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2352 ≤ case.val)
    (upper : case.val < 2400) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2383 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2391 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2399 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk49.correct

end Krenn.X5OrbitWitnessChunks.Chunk49
