import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk93

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨190, .identity, .p201⟩, ⟨191, .identity, .p201⟩, ⟨187, .identity, .p201⟩, ⟨186, .identity, .p201⟩, ⟨189, .identity, .p201⟩, ⟨188, .identity, .p201⟩, ⟨196, .identity, .p201⟩, ⟨197, .identity, .p201⟩, ⟨193, .identity, .p201⟩, ⟨192, .identity, .p201⟩, ⟨195, .identity, .p201⟩, ⟨194, .identity, .p201⟩,
    ⟨142, .swap34, .p201⟩, ⟨143, .swap34, .p201⟩, ⟨139, .swap34, .p201⟩, ⟨138, .swap34, .p201⟩, ⟨141, .swap34, .p201⟩, ⟨140, .swap34, .p201⟩, ⟨52, .cycle243, .p201⟩, ⟨53, .cycle243, .p201⟩, ⟨49, .cycle243, .p201⟩, ⟨48, .cycle243, .p201⟩, ⟨51, .cycle243, .p201⟩, ⟨50, .cycle243, .p201⟩,
    ⟨184, .identity, .p201⟩, ⟨185, .identity, .p201⟩, ⟨181, .identity, .p201⟩, ⟨180, .identity, .p201⟩, ⟨183, .identity, .p201⟩, ⟨182, .identity, .p201⟩, ⟨166, .swap34, .p201⟩, ⟨167, .swap34, .p201⟩, ⟨163, .swap34, .p201⟩, ⟨162, .swap34, .p201⟩, ⟨165, .swap34, .p201⟩, ⟨164, .swap34, .p201⟩,
    ⟨172, .identity, .p201⟩, ⟨173, .identity, .p201⟩, ⟨169, .identity, .p201⟩, ⟨168, .identity, .p201⟩, ⟨171, .identity, .p201⟩, ⟨170, .identity, .p201⟩, ⟨178, .identity, .p201⟩, ⟨179, .identity, .p201⟩, ⟨175, .identity, .p201⟩, ⟨174, .identity, .p201⟩, ⟨177, .identity, .p201⟩, ⟨176, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4464) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4464 ≤ case.val)
    (upper : case.val < 4512) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4479 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4487 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4511 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk93.correct

end Krenn.X5OrbitWitnessChunks.Chunk93
