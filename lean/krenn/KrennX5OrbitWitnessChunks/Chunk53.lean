import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk53

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨223, .swap24, .p021⟩, ⟨222, .swap24, .p021⟩, ⟨226, .swap24, .p021⟩, ⟨227, .swap24, .p021⟩, ⟨224, .swap24, .p021⟩, ⟨225, .swap24, .p021⟩, ⟨241, .swap23, .p021⟩, ⟨240, .swap23, .p021⟩, ⟨244, .swap23, .p021⟩, ⟨245, .swap23, .p021⟩, ⟨242, .swap23, .p021⟩, ⟨243, .swap23, .p021⟩,
    ⟨181, .swap24, .p021⟩, ⟨180, .swap24, .p021⟩, ⟨184, .swap24, .p021⟩, ⟨185, .swap24, .p021⟩, ⟨182, .swap24, .p021⟩, ⟨183, .swap24, .p021⟩, ⟨91, .swap24, .p021⟩, ⟨90, .swap24, .p021⟩, ⟨94, .swap24, .p021⟩, ⟨95, .swap24, .p021⟩, ⟨92, .swap24, .p021⟩, ⟨93, .swap24, .p021⟩,
    ⟨283, .identity, .p021⟩, ⟨282, .identity, .p021⟩, ⟨286, .identity, .p021⟩, ⟨287, .identity, .p021⟩, ⟨284, .identity, .p021⟩, ⟨285, .identity, .p021⟩, ⟨289, .identity, .p021⟩, ⟨288, .identity, .p021⟩, ⟨292, .identity, .p021⟩, ⟨293, .identity, .p021⟩, ⟨290, .identity, .p021⟩, ⟨291, .identity, .p021⟩,
    ⟨241, .swap24, .p021⟩, ⟨240, .swap24, .p021⟩, ⟨244, .swap24, .p021⟩, ⟨245, .swap24, .p021⟩, ⟨242, .swap24, .p021⟩, ⟨243, .swap24, .p021⟩, ⟨277, .identity, .p021⟩, ⟨276, .identity, .p021⟩, ⟨280, .identity, .p021⟩, ⟨281, .identity, .p021⟩, ⟨278, .identity, .p021⟩, ⟨279, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2544) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2544 ≤ case.val)
    (upper : case.val < 2592) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2575 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2583 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2591 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk53.correct

end Krenn.X5OrbitWitnessChunks.Chunk53
