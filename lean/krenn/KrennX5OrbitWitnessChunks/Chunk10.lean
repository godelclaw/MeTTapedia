import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk10

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨156, .swap23, .p012⟩, ⟨157, .swap23, .p012⟩, ⟨158, .swap23, .p012⟩, ⟨159, .swap23, .p012⟩, ⟨160, .swap23, .p012⟩, ⟨161, .swap23, .p012⟩, ⟨162, .swap23, .p012⟩, ⟨163, .swap23, .p012⟩, ⟨164, .swap23, .p012⟩, ⟨165, .swap23, .p012⟩, ⟨166, .swap23, .p012⟩, ⟨167, .swap23, .p012⟩,
    ⟨168, .swap23, .p012⟩, ⟨169, .swap23, .p012⟩, ⟨170, .swap23, .p012⟩, ⟨171, .swap23, .p012⟩, ⟨172, .swap23, .p012⟩, ⟨173, .swap23, .p012⟩, ⟨174, .swap23, .p012⟩, ⟨175, .swap23, .p012⟩, ⟨176, .swap23, .p012⟩, ⟨177, .swap23, .p012⟩, ⟨178, .swap23, .p012⟩, ⟨179, .swap23, .p012⟩,
    ⟨66, .swap24, .p012⟩, ⟨67, .swap24, .p012⟩, ⟨68, .swap24, .p012⟩, ⟨69, .swap24, .p012⟩, ⟨70, .swap24, .p012⟩, ⟨71, .swap24, .p012⟩, ⟨156, .swap24, .p012⟩, ⟨157, .swap24, .p012⟩, ⟨158, .swap24, .p012⟩, ⟨159, .swap24, .p012⟩, ⟨160, .swap24, .p012⟩, ⟨161, .swap24, .p012⟩,
    ⟨216, .identity, .p012⟩, ⟨217, .identity, .p012⟩, ⟨218, .identity, .p012⟩, ⟨219, .identity, .p012⟩, ⟨220, .identity, .p012⟩, ⟨221, .identity, .p012⟩, ⟨222, .identity, .p012⟩, ⟨223, .identity, .p012⟩, ⟨224, .identity, .p012⟩, ⟨225, .identity, .p012⟩, ⟨226, .identity, .p012⟩, ⟨227, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 480) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 480 ≤ case.val)
    (upper : case.val < 528) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (487 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (527 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk10.correct

end Krenn.X5OrbitWitnessChunks.Chunk10
