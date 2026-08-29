import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk137

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨197, .swap24, .p210⟩, ⟨196, .swap24, .p210⟩, ⟨195, .swap24, .p210⟩, ⟨194, .swap24, .p210⟩, ⟨193, .swap24, .p210⟩, ⟨192, .swap24, .p210⟩, ⟨107, .swap24, .p210⟩, ⟨106, .swap24, .p210⟩, ⟨105, .swap24, .p210⟩, ⟨104, .swap24, .p210⟩, ⟨103, .swap24, .p210⟩, ⟨102, .swap24, .p210⟩,
    ⟨275, .swap23, .p210⟩, ⟨274, .swap23, .p210⟩, ⟨273, .swap23, .p210⟩, ⟨272, .swap23, .p210⟩, ⟨271, .swap23, .p210⟩, ⟨270, .swap23, .p210⟩, ⟨269, .cycle234, .p210⟩, ⟨268, .cycle234, .p210⟩, ⟨267, .cycle234, .p210⟩, ⟨266, .cycle234, .p210⟩, ⟨265, .cycle234, .p210⟩, ⟨264, .cycle234, .p210⟩,
    ⟨257, .cycle234, .p210⟩, ⟨256, .cycle234, .p210⟩, ⟨255, .cycle234, .p210⟩, ⟨254, .cycle234, .p210⟩, ⟨253, .cycle234, .p210⟩, ⟨252, .cycle234, .p210⟩, ⟨239, .swap24, .p210⟩, ⟨238, .swap24, .p210⟩, ⟨237, .swap24, .p210⟩, ⟨236, .swap24, .p210⟩, ⟨235, .swap24, .p210⟩, ⟨234, .swap24, .p210⟩,
    ⟨179, .swap24, .p210⟩, ⟨178, .swap24, .p210⟩, ⟨177, .swap24, .p210⟩, ⟨176, .swap24, .p210⟩, ⟨175, .swap24, .p210⟩, ⟨174, .swap24, .p210⟩, ⟨89, .swap24, .p210⟩, ⟨88, .swap24, .p210⟩, ⟨87, .swap24, .p210⟩, ⟨86, .swap24, .p210⟩, ⟨85, .swap24, .p210⟩, ⟨84, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6576) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6576 ≤ case.val)
    (upper : case.val < 6624) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6583 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6623 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk137.correct

end Krenn.X5OrbitWitnessChunks.Chunk137
