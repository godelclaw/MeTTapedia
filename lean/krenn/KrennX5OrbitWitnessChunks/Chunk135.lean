import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk135

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨335, .identity, .p210⟩, ⟨334, .identity, .p210⟩, ⟨333, .identity, .p210⟩, ⟨332, .identity, .p210⟩, ⟨331, .identity, .p210⟩, ⟨330, .identity, .p210⟩, ⟨329, .swap24, .p210⟩, ⟨328, .swap24, .p210⟩, ⟨327, .swap24, .p210⟩, ⟨326, .swap24, .p210⟩, ⟨325, .swap24, .p210⟩, ⟨324, .swap24, .p210⟩,
    ⟨311, .swap24, .p210⟩, ⟨310, .swap24, .p210⟩, ⟨309, .swap24, .p210⟩, ⟨308, .swap24, .p210⟩, ⟨307, .swap24, .p210⟩, ⟨306, .swap24, .p210⟩, ⟨275, .swap24, .p210⟩, ⟨274, .swap24, .p210⟩, ⟨273, .swap24, .p210⟩, ⟨272, .swap24, .p210⟩, ⟨271, .swap24, .p210⟩, ⟨270, .swap24, .p210⟩,
    ⟨215, .swap24, .p210⟩, ⟨214, .swap24, .p210⟩, ⟨213, .swap24, .p210⟩, ⟨212, .swap24, .p210⟩, ⟨211, .swap24, .p210⟩, ⟨210, .swap24, .p210⟩, ⟨125, .swap24, .p210⟩, ⟨124, .swap24, .p210⟩, ⟨123, .swap24, .p210⟩, ⟨122, .swap24, .p210⟩, ⟨121, .swap24, .p210⟩, ⟨120, .swap24, .p210⟩,
    ⟨329, .swap23, .p210⟩, ⟨328, .swap23, .p210⟩, ⟨327, .swap23, .p210⟩, ⟨326, .swap23, .p210⟩, ⟨325, .swap23, .p210⟩, ⟨324, .swap23, .p210⟩, ⟨323, .swap24, .p210⟩, ⟨322, .swap24, .p210⟩, ⟨321, .swap24, .p210⟩, ⟨320, .swap24, .p210⟩, ⟨319, .swap24, .p210⟩, ⟨318, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6480) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6480 ≤ case.val)
    (upper : case.val < 6528) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6487 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6527 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk135.correct

end Krenn.X5OrbitWitnessChunks.Chunk135
