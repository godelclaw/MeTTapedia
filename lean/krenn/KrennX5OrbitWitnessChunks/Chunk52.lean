import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk52

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨301, .swap34, .p021⟩, ⟨300, .swap34, .p021⟩, ⟨304, .swap34, .p021⟩, ⟨305, .swap34, .p021⟩, ⟨302, .swap34, .p021⟩, ⟨303, .swap34, .p021⟩, ⟨307, .identity, .p021⟩, ⟨306, .identity, .p021⟩, ⟨310, .identity, .p021⟩, ⟨311, .identity, .p021⟩, ⟨308, .identity, .p021⟩, ⟨309, .identity, .p021⟩,
    ⟨253, .cycle243, .p021⟩, ⟨252, .cycle243, .p021⟩, ⟨256, .cycle243, .p021⟩, ⟨257, .cycle243, .p021⟩, ⟨254, .cycle243, .p021⟩, ⟨255, .cycle243, .p021⟩, ⟨289, .swap34, .p021⟩, ⟨288, .swap34, .p021⟩, ⟨292, .swap34, .p021⟩, ⟨293, .swap34, .p021⟩, ⟨290, .swap34, .p021⟩, ⟨291, .swap34, .p021⟩,
    ⟨163, .swap24, .p021⟩, ⟨162, .swap24, .p021⟩, ⟨166, .swap24, .p021⟩, ⟨167, .swap24, .p021⟩, ⟨164, .swap24, .p021⟩, ⟨165, .swap24, .p021⟩, ⟨73, .swap24, .p021⟩, ⟨72, .swap24, .p021⟩, ⟨76, .swap24, .p021⟩, ⟨77, .swap24, .p021⟩, ⟨74, .swap24, .p021⟩, ⟨75, .swap24, .p021⟩,
    ⟨247, .swap23, .p021⟩, ⟨246, .swap23, .p021⟩, ⟨250, .swap23, .p021⟩, ⟨251, .swap23, .p021⟩, ⟨248, .swap23, .p021⟩, ⟨249, .swap23, .p021⟩, ⟨253, .swap23, .p021⟩, ⟨252, .swap23, .p021⟩, ⟨256, .swap23, .p021⟩, ⟨257, .swap23, .p021⟩, ⟨254, .swap23, .p021⟩, ⟨255, .swap23, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2496) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2496 ≤ case.val)
    (upper : case.val < 2544) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2527 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2535 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2543 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk52.correct

end Krenn.X5OrbitWitnessChunks.Chunk52
