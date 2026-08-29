import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk116

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨15, .swap24, .p120⟩, ⟨14, .swap24, .p120⟩, ⟨17, .swap24, .p120⟩, ⟨16, .swap24, .p120⟩, ⟨12, .swap24, .p120⟩, ⟨13, .swap24, .p120⟩, ⟨45, .cycle234, .p120⟩, ⟨44, .cycle234, .p120⟩, ⟨47, .cycle234, .p120⟩, ⟨46, .cycle234, .p120⟩, ⟨42, .cycle234, .p120⟩, ⟨43, .cycle234, .p120⟩,
    ⟨165, .swap23, .p120⟩, ⟨164, .swap23, .p120⟩, ⟨167, .swap23, .p120⟩, ⟨166, .swap23, .p120⟩, ⟨162, .swap23, .p120⟩, ⟨163, .swap23, .p120⟩, ⟨159, .swap23, .p120⟩, ⟨158, .swap23, .p120⟩, ⟨161, .swap23, .p120⟩, ⟨160, .swap23, .p120⟩, ⟨156, .swap23, .p120⟩, ⟨157, .swap23, .p120⟩,
    ⟨177, .swap23, .p120⟩, ⟨176, .swap23, .p120⟩, ⟨179, .swap23, .p120⟩, ⟨178, .swap23, .p120⟩, ⟨174, .swap23, .p120⟩, ⟨175, .swap23, .p120⟩, ⟨171, .swap23, .p120⟩, ⟨170, .swap23, .p120⟩, ⟨173, .swap23, .p120⟩, ⟨172, .swap23, .p120⟩, ⟨168, .swap23, .p120⟩, ⟨169, .swap23, .p120⟩,
    ⟨45, .swap24, .p120⟩, ⟨44, .swap24, .p120⟩, ⟨47, .swap24, .p120⟩, ⟨46, .swap24, .p120⟩, ⟨42, .swap24, .p120⟩, ⟨43, .swap24, .p120⟩, ⟨135, .swap24, .p120⟩, ⟨134, .swap24, .p120⟩, ⟨137, .swap24, .p120⟩, ⟨136, .swap24, .p120⟩, ⟨132, .swap24, .p120⟩, ⟨133, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5568) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5568 ≤ case.val)
    (upper : case.val < 5616) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5575 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5583 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5615 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk116.correct

end Krenn.X5OrbitWitnessChunks.Chunk116
