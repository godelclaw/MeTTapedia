import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk136

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨305, .swap24, .p210⟩, ⟨304, .swap24, .p210⟩, ⟨303, .swap24, .p210⟩, ⟨302, .swap24, .p210⟩, ⟨301, .swap24, .p210⟩, ⟨300, .swap24, .p210⟩, ⟨269, .swap24, .p210⟩, ⟨268, .swap24, .p210⟩, ⟨267, .swap24, .p210⟩, ⟨266, .swap24, .p210⟩, ⟨265, .swap24, .p210⟩, ⟨264, .swap24, .p210⟩,
    ⟨209, .swap24, .p210⟩, ⟨208, .swap24, .p210⟩, ⟨207, .swap24, .p210⟩, ⟨206, .swap24, .p210⟩, ⟨205, .swap24, .p210⟩, ⟨204, .swap24, .p210⟩, ⟨119, .swap24, .p210⟩, ⟨118, .swap24, .p210⟩, ⟨117, .swap24, .p210⟩, ⟨116, .swap24, .p210⟩, ⟨115, .swap24, .p210⟩, ⟨114, .swap24, .p210⟩,
    ⟨311, .swap23, .p210⟩, ⟨310, .swap23, .p210⟩, ⟨309, .swap23, .p210⟩, ⟨308, .swap23, .p210⟩, ⟨307, .swap23, .p210⟩, ⟨306, .swap23, .p210⟩, ⟨305, .cycle234, .p210⟩, ⟨304, .cycle234, .p210⟩, ⟨303, .cycle234, .p210⟩, ⟨302, .cycle234, .p210⟩, ⟨301, .cycle234, .p210⟩, ⟨300, .cycle234, .p210⟩,
    ⟨293, .swap24, .p210⟩, ⟨292, .swap24, .p210⟩, ⟨291, .swap24, .p210⟩, ⟨290, .swap24, .p210⟩, ⟨289, .swap24, .p210⟩, ⟨288, .swap24, .p210⟩, ⟨257, .swap24, .p210⟩, ⟨256, .swap24, .p210⟩, ⟨255, .swap24, .p210⟩, ⟨254, .swap24, .p210⟩, ⟨253, .swap24, .p210⟩, ⟨252, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6528) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6528 ≤ case.val)
    (upper : case.val < 6576) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6535 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6575 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk136.correct

end Krenn.X5OrbitWitnessChunks.Chunk136
