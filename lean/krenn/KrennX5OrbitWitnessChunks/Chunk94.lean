import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk94

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨136, .swap34, .p201⟩, ⟨137, .swap34, .p201⟩, ⟨133, .swap34, .p201⟩, ⟨132, .swap34, .p201⟩, ⟨135, .swap34, .p201⟩, ⟨134, .swap34, .p201⟩, ⟨46, .cycle243, .p201⟩, ⟨47, .cycle243, .p201⟩, ⟨43, .cycle243, .p201⟩, ⟨42, .cycle243, .p201⟩, ⟨45, .cycle243, .p201⟩, ⟨44, .cycle243, .p201⟩,
    ⟨166, .identity, .p201⟩, ⟨167, .identity, .p201⟩, ⟨163, .identity, .p201⟩, ⟨162, .identity, .p201⟩, ⟨165, .identity, .p201⟩, ⟨164, .identity, .p201⟩, ⟨160, .identity, .p201⟩, ⟨161, .identity, .p201⟩, ⟨157, .identity, .p201⟩, ⟨156, .identity, .p201⟩, ⟨159, .identity, .p201⟩, ⟨158, .identity, .p201⟩,
    ⟨112, .identity, .p201⟩, ⟨113, .identity, .p201⟩, ⟨109, .identity, .p201⟩, ⟨108, .identity, .p201⟩, ⟨111, .identity, .p201⟩, ⟨110, .identity, .p201⟩, ⟨118, .identity, .p201⟩, ⟨119, .identity, .p201⟩, ⟨115, .identity, .p201⟩, ⟨114, .identity, .p201⟩, ⟨117, .identity, .p201⟩, ⟨116, .identity, .p201⟩,
    ⟨58, .swap34, .p201⟩, ⟨59, .swap34, .p201⟩, ⟨55, .swap34, .p201⟩, ⟨54, .swap34, .p201⟩, ⟨57, .swap34, .p201⟩, ⟨56, .swap34, .p201⟩, ⟨28, .swap34, .p201⟩, ⟨29, .swap34, .p201⟩, ⟨25, .swap34, .p201⟩, ⟨24, .swap34, .p201⟩, ⟨27, .swap34, .p201⟩, ⟨26, .swap34, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4512) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4512 ≤ case.val)
    (upper : case.val < 4560) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4527 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4535 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4559 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk94.correct

end Krenn.X5OrbitWitnessChunks.Chunk94
