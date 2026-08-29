import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk13

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨234, .swap34, .p012⟩, ⟨235, .swap34, .p012⟩, ⟨236, .swap34, .p012⟩, ⟨237, .swap34, .p012⟩, ⟨238, .swap34, .p012⟩, ⟨239, .swap34, .p012⟩, ⟨252, .swap34, .p012⟩, ⟨253, .swap34, .p012⟩, ⟨254, .swap34, .p012⟩, ⟨255, .swap34, .p012⟩, ⟨256, .swap34, .p012⟩, ⟨257, .swap34, .p012⟩,
    ⟨264, .swap34, .p012⟩, ⟨265, .swap34, .p012⟩, ⟨266, .swap34, .p012⟩, ⟨267, .swap34, .p012⟩, ⟨268, .swap34, .p012⟩, ⟨269, .swap34, .p012⟩, ⟨270, .identity, .p012⟩, ⟨271, .identity, .p012⟩, ⟨272, .identity, .p012⟩, ⟨273, .identity, .p012⟩, ⟨274, .identity, .p012⟩, ⟨275, .identity, .p012⟩,
    ⟨18, .swap24, .p012⟩, ⟨19, .swap24, .p012⟩, ⟨20, .swap24, .p012⟩, ⟨21, .swap24, .p012⟩, ⟨22, .swap24, .p012⟩, ⟨23, .swap24, .p012⟩, ⟨48, .cycle234, .p012⟩, ⟨49, .cycle234, .p012⟩, ⟨50, .cycle234, .p012⟩, ⟨51, .cycle234, .p012⟩, ⟨52, .cycle234, .p012⟩, ⟨53, .cycle234, .p012⟩,
    ⟨72, .cycle234, .p012⟩, ⟨73, .cycle234, .p012⟩, ⟨74, .cycle234, .p012⟩, ⟨75, .cycle234, .p012⟩, ⟨76, .cycle234, .p012⟩, ⟨77, .cycle234, .p012⟩, ⟨90, .swap23, .p012⟩, ⟨91, .swap23, .p012⟩, ⟨92, .swap23, .p012⟩, ⟨93, .swap23, .p012⟩, ⟨94, .swap23, .p012⟩, ⟨95, .swap23, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 624) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 624 ≤ case.val)
    (upper : case.val < 672) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (631 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (671 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk13.correct

end Krenn.X5OrbitWitnessChunks.Chunk13
