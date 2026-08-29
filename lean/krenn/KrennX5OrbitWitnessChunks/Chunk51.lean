import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk51

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨187, .cycle243, .p021⟩, ⟨186, .cycle243, .p021⟩, ⟨190, .cycle243, .p021⟩, ⟨191, .cycle243, .p021⟩, ⟨188, .cycle243, .p021⟩, ⟨189, .cycle243, .p021⟩, ⟨97, .cycle243, .p021⟩, ⟨96, .cycle243, .p021⟩, ⟨100, .cycle243, .p021⟩, ⟨101, .cycle243, .p021⟩, ⟨98, .cycle243, .p021⟩, ⟨99, .cycle243, .p021⟩,
    ⟨295, .identity, .p021⟩, ⟨294, .identity, .p021⟩, ⟨298, .identity, .p021⟩, ⟨299, .identity, .p021⟩, ⟨296, .identity, .p021⟩, ⟨297, .identity, .p021⟩, ⟨301, .identity, .p021⟩, ⟨300, .identity, .p021⟩, ⟨304, .identity, .p021⟩, ⟨305, .identity, .p021⟩, ⟨302, .identity, .p021⟩, ⟨303, .identity, .p021⟩,
    ⟨247, .cycle243, .p021⟩, ⟨246, .cycle243, .p021⟩, ⟨250, .cycle243, .p021⟩, ⟨251, .cycle243, .p021⟩, ⟨248, .cycle243, .p021⟩, ⟨249, .cycle243, .p021⟩, ⟨283, .swap34, .p021⟩, ⟨282, .swap34, .p021⟩, ⟨286, .swap34, .p021⟩, ⟨287, .swap34, .p021⟩, ⟨284, .swap34, .p021⟩, ⟨285, .swap34, .p021⟩,
    ⟨193, .cycle243, .p021⟩, ⟨192, .cycle243, .p021⟩, ⟨196, .cycle243, .p021⟩, ⟨197, .cycle243, .p021⟩, ⟨194, .cycle243, .p021⟩, ⟨195, .cycle243, .p021⟩, ⟨103, .cycle243, .p021⟩, ⟨102, .cycle243, .p021⟩, ⟨106, .cycle243, .p021⟩, ⟨107, .cycle243, .p021⟩, ⟨104, .cycle243, .p021⟩, ⟨105, .cycle243, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2448) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2448 ≤ case.val)
    (upper : case.val < 2496) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2479 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2487 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2495 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk51.correct

end Krenn.X5OrbitWitnessChunks.Chunk51
