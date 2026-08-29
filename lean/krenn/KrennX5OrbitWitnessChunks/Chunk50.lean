import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk50

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨163, .cycle234, .p021⟩, ⟨162, .cycle234, .p021⟩, ⟨166, .cycle234, .p021⟩, ⟨167, .cycle234, .p021⟩, ⟨164, .cycle234, .p021⟩, ⟨165, .cycle234, .p021⟩, ⟨181, .swap23, .p021⟩, ⟨180, .swap23, .p021⟩, ⟨184, .swap23, .p021⟩, ⟨185, .swap23, .p021⟩, ⟨182, .swap23, .p021⟩, ⟨183, .swap23, .p021⟩,
    ⟨49, .cycle234, .p021⟩, ⟨48, .cycle234, .p021⟩, ⟨52, .cycle234, .p021⟩, ⟨53, .cycle234, .p021⟩, ⟨50, .cycle234, .p021⟩, ⟨51, .cycle234, .p021⟩, ⟨19, .swap24, .p021⟩, ⟨18, .swap24, .p021⟩, ⟨22, .swap24, .p021⟩, ⟨23, .swap24, .p021⟩, ⟨20, .swap24, .p021⟩, ⟨21, .swap24, .p021⟩,
    ⟨97, .swap23, .p021⟩, ⟨96, .swap23, .p021⟩, ⟨100, .swap23, .p021⟩, ⟨101, .swap23, .p021⟩, ⟨98, .swap23, .p021⟩, ⟨99, .swap23, .p021⟩, ⟨103, .swap23, .p021⟩, ⟨102, .swap23, .p021⟩, ⟨106, .swap23, .p021⟩, ⟨107, .swap23, .p021⟩, ⟨104, .swap23, .p021⟩, ⟨105, .swap23, .p021⟩,
    ⟨73, .cycle234, .p021⟩, ⟨72, .cycle234, .p021⟩, ⟨76, .cycle234, .p021⟩, ⟨77, .cycle234, .p021⟩, ⟨74, .cycle234, .p021⟩, ⟨75, .cycle234, .p021⟩, ⟨91, .swap23, .p021⟩, ⟨90, .swap23, .p021⟩, ⟨94, .swap23, .p021⟩, ⟨95, .swap23, .p021⟩, ⟨92, .swap23, .p021⟩, ⟨93, .swap23, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2400) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2400 ≤ case.val)
    (upper : case.val < 2448) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2431 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2439 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2447 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk50.correct

end Krenn.X5OrbitWitnessChunks.Chunk50
