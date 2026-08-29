import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk55

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨74, .cycle243, .p102⟩, ⟨75, .cycle243, .p102⟩, ⟨72, .cycle243, .p102⟩, ⟨73, .cycle243, .p102⟩, ⟨77, .cycle243, .p102⟩, ⟨76, .cycle243, .p102⟩, ⟨164, .cycle243, .p102⟩, ⟨165, .cycle243, .p102⟩, ⟨162, .cycle243, .p102⟩, ⟨163, .cycle243, .p102⟩, ⟨167, .cycle243, .p102⟩, ⟨166, .cycle243, .p102⟩,
    ⟨254, .identity, .p102⟩, ⟨255, .identity, .p102⟩, ⟨252, .identity, .p102⟩, ⟨253, .identity, .p102⟩, ⟨257, .identity, .p102⟩, ⟨256, .identity, .p102⟩, ⟨248, .identity, .p102⟩, ⟨249, .identity, .p102⟩, ⟨246, .identity, .p102⟩, ⟨247, .identity, .p102⟩, ⟨251, .identity, .p102⟩, ⟨250, .identity, .p102⟩,
    ⟨68, .swap23, .p102⟩, ⟨69, .swap23, .p102⟩, ⟨66, .swap23, .p102⟩, ⟨67, .swap23, .p102⟩, ⟨71, .swap23, .p102⟩, ⟨70, .swap23, .p102⟩, ⟨74, .swap23, .p102⟩, ⟨75, .swap23, .p102⟩, ⟨72, .swap23, .p102⟩, ⟨73, .swap23, .p102⟩, ⟨77, .swap23, .p102⟩, ⟨76, .swap23, .p102⟩,
    ⟨14, .swap24, .p102⟩, ⟨15, .swap24, .p102⟩, ⟨12, .swap24, .p102⟩, ⟨13, .swap24, .p102⟩, ⟨17, .swap24, .p102⟩, ⟨16, .swap24, .p102⟩, ⟨44, .cycle234, .p102⟩, ⟨45, .cycle234, .p102⟩, ⟨42, .cycle234, .p102⟩, ⟨43, .cycle234, .p102⟩, ⟨47, .cycle234, .p102⟩, ⟨46, .cycle234, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2640) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2640 ≤ case.val)
    (upper : case.val < 2688) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2671 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2679 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2687 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk55.correct

end Krenn.X5OrbitWitnessChunks.Chunk55
