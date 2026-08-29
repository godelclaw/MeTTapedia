import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk54

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨218, .identity, .p102⟩, ⟨219, .identity, .p102⟩, ⟨216, .identity, .p102⟩, ⟨217, .identity, .p102⟩, ⟨221, .identity, .p102⟩, ⟨220, .identity, .p102⟩, ⟨224, .identity, .p102⟩, ⟨225, .identity, .p102⟩, ⟨222, .identity, .p102⟩, ⟨223, .identity, .p102⟩, ⟨227, .identity, .p102⟩, ⟨226, .identity, .p102⟩,
    ⟨68, .swap24, .p102⟩, ⟨69, .swap24, .p102⟩, ⟨66, .swap24, .p102⟩, ⟨67, .swap24, .p102⟩, ⟨71, .swap24, .p102⟩, ⟨70, .swap24, .p102⟩, ⟨158, .swap24, .p102⟩, ⟨159, .swap24, .p102⟩, ⟨156, .swap24, .p102⟩, ⟨157, .swap24, .p102⟩, ⟨161, .swap24, .p102⟩, ⟨160, .swap24, .p102⟩,
    ⟨236, .identity, .p102⟩, ⟨237, .identity, .p102⟩, ⟨234, .identity, .p102⟩, ⟨235, .identity, .p102⟩, ⟨239, .identity, .p102⟩, ⟨238, .identity, .p102⟩, ⟨230, .identity, .p102⟩, ⟨231, .identity, .p102⟩, ⟨228, .identity, .p102⟩, ⟨229, .identity, .p102⟩, ⟨233, .identity, .p102⟩, ⟨232, .identity, .p102⟩,
    ⟨224, .swap34, .p102⟩, ⟨225, .swap34, .p102⟩, ⟨222, .swap34, .p102⟩, ⟨223, .swap34, .p102⟩, ⟨227, .swap34, .p102⟩, ⟨226, .swap34, .p102⟩, ⟨242, .identity, .p102⟩, ⟨243, .identity, .p102⟩, ⟨240, .identity, .p102⟩, ⟨241, .identity, .p102⟩, ⟨245, .identity, .p102⟩, ⟨244, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2592) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2592 ≤ case.val)
    (upper : case.val < 2640) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2623 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2631 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2639 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk54.correct

end Krenn.X5OrbitWitnessChunks.Chunk54
