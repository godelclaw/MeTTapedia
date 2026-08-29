import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk117

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨291, .swap24, .p120⟩, ⟨290, .swap24, .p120⟩, ⟨293, .swap24, .p120⟩, ⟨292, .swap24, .p120⟩, ⟨288, .swap24, .p120⟩, ⟨289, .swap24, .p120⟩, ⟨255, .swap24, .p120⟩, ⟨254, .swap24, .p120⟩, ⟨257, .swap24, .p120⟩, ⟨256, .swap24, .p120⟩, ⟨252, .swap24, .p120⟩, ⟨253, .swap24, .p120⟩,
    ⟨309, .swap23, .p120⟩, ⟨308, .swap23, .p120⟩, ⟨311, .swap23, .p120⟩, ⟨310, .swap23, .p120⟩, ⟨306, .swap23, .p120⟩, ⟨307, .swap23, .p120⟩, ⟨303, .cycle234, .p120⟩, ⟨302, .cycle234, .p120⟩, ⟨305, .cycle234, .p120⟩, ⟨304, .cycle234, .p120⟩, ⟨300, .cycle234, .p120⟩, ⟨301, .cycle234, .p120⟩,
    ⟨105, .swap24, .p120⟩, ⟨104, .swap24, .p120⟩, ⟨107, .swap24, .p120⟩, ⟨106, .swap24, .p120⟩, ⟨102, .swap24, .p120⟩, ⟨103, .swap24, .p120⟩, ⟨195, .swap24, .p120⟩, ⟨194, .swap24, .p120⟩, ⟨197, .swap24, .p120⟩, ⟨196, .swap24, .p120⟩, ⟨192, .swap24, .p120⟩, ⟨193, .swap24, .p120⟩,
    ⟨255, .cycle234, .p120⟩, ⟨254, .cycle234, .p120⟩, ⟨257, .cycle234, .p120⟩, ⟨256, .cycle234, .p120⟩, ⟨252, .cycle234, .p120⟩, ⟨253, .cycle234, .p120⟩, ⟨237, .swap24, .p120⟩, ⟨236, .swap24, .p120⟩, ⟨239, .swap24, .p120⟩, ⟨238, .swap24, .p120⟩, ⟨234, .swap24, .p120⟩, ⟨235, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5616) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5616 ≤ case.val)
    (upper : case.val < 5664) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5623 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5631 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5663 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk117.correct

end Krenn.X5OrbitWitnessChunks.Chunk117
