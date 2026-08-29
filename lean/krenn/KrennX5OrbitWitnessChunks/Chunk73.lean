import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk73

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨104, .swap24, .p102⟩, ⟨105, .swap24, .p102⟩, ⟨102, .swap24, .p102⟩, ⟨103, .swap24, .p102⟩, ⟨107, .swap24, .p102⟩, ⟨106, .swap24, .p102⟩, ⟨194, .swap24, .p102⟩, ⟨195, .swap24, .p102⟩, ⟨192, .swap24, .p102⟩, ⟨193, .swap24, .p102⟩, ⟨197, .swap24, .p102⟩, ⟨196, .swap24, .p102⟩,
    ⟨308, .swap23, .p102⟩, ⟨309, .swap23, .p102⟩, ⟨306, .swap23, .p102⟩, ⟨307, .swap23, .p102⟩, ⟨311, .swap23, .p102⟩, ⟨310, .swap23, .p102⟩, ⟨302, .cycle234, .p102⟩, ⟨303, .cycle234, .p102⟩, ⟨300, .cycle234, .p102⟩, ⟨301, .cycle234, .p102⟩, ⟨305, .cycle234, .p102⟩, ⟨304, .cycle234, .p102⟩,
    ⟨86, .cycle234, .p102⟩, ⟨87, .cycle234, .p102⟩, ⟨84, .cycle234, .p102⟩, ⟨85, .cycle234, .p102⟩, ⟨89, .cycle234, .p102⟩, ⟨88, .cycle234, .p102⟩, ⟨104, .cycle234, .p102⟩, ⟨105, .cycle234, .p102⟩, ⟨102, .cycle234, .p102⟩, ⟨103, .cycle234, .p102⟩, ⟨107, .cycle234, .p102⟩, ⟨106, .cycle234, .p102⟩,
    ⟨32, .swap24, .p102⟩, ⟨33, .swap24, .p102⟩, ⟨30, .swap24, .p102⟩, ⟨31, .swap24, .p102⟩, ⟨35, .swap24, .p102⟩, ⟨34, .swap24, .p102⟩, ⟨62, .cycle234, .p102⟩, ⟨63, .cycle234, .p102⟩, ⟨60, .cycle234, .p102⟩, ⟨61, .cycle234, .p102⟩, ⟨65, .cycle234, .p102⟩, ⟨64, .cycle234, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3504) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3504 ≤ case.val)
    (upper : case.val < 3552) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3527 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3535 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3551 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk73.correct

end Krenn.X5OrbitWitnessChunks.Chunk73
