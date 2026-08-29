import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk138

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨215, .swap23, .p210⟩, ⟨214, .swap23, .p210⟩, ⟨213, .swap23, .p210⟩, ⟨212, .swap23, .p210⟩, ⟨211, .swap23, .p210⟩, ⟨210, .swap23, .p210⟩, ⟨209, .cycle234, .p210⟩, ⟨208, .cycle234, .p210⟩, ⟨207, .cycle234, .p210⟩, ⟨206, .cycle234, .p210⟩, ⟨205, .cycle234, .p210⟩, ⟨204, .cycle234, .p210⟩,
    ⟨197, .cycle234, .p210⟩, ⟨196, .cycle234, .p210⟩, ⟨195, .cycle234, .p210⟩, ⟨194, .cycle234, .p210⟩, ⟨193, .cycle234, .p210⟩, ⟨192, .cycle234, .p210⟩, ⟨179, .cycle234, .p210⟩, ⟨178, .cycle234, .p210⟩, ⟨177, .cycle234, .p210⟩, ⟨176, .cycle234, .p210⟩, ⟨175, .cycle234, .p210⟩, ⟨174, .cycle234, .p210⟩,
    ⟨155, .swap24, .p210⟩, ⟨154, .swap24, .p210⟩, ⟨153, .swap24, .p210⟩, ⟨152, .swap24, .p210⟩, ⟨151, .swap24, .p210⟩, ⟨150, .swap24, .p210⟩, ⟨65, .swap24, .p210⟩, ⟨64, .swap24, .p210⟩, ⟨63, .swap24, .p210⟩, ⟨62, .swap24, .p210⟩, ⟨61, .swap24, .p210⟩, ⟨60, .swap24, .p210⟩,
    ⟨125, .swap23, .p210⟩, ⟨124, .swap23, .p210⟩, ⟨123, .swap23, .p210⟩, ⟨122, .swap23, .p210⟩, ⟨121, .swap23, .p210⟩, ⟨120, .swap23, .p210⟩, ⟨119, .cycle234, .p210⟩, ⟨118, .cycle234, .p210⟩, ⟨117, .cycle234, .p210⟩, ⟨116, .cycle234, .p210⟩, ⟨115, .cycle234, .p210⟩, ⟨114, .cycle234, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6624) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6624 ≤ case.val)
    (upper : case.val < 6672) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6631 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6671 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk138.correct

end Krenn.X5OrbitWitnessChunks.Chunk138
