import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk156

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨155, .identity, .p210⟩, ⟨154, .identity, .p210⟩, ⟨153, .identity, .p210⟩, ⟨152, .identity, .p210⟩, ⟨151, .identity, .p210⟩, ⟨150, .identity, .p210⟩, ⟨149, .identity, .p210⟩, ⟨148, .identity, .p210⟩, ⟨147, .identity, .p210⟩, ⟨146, .identity, .p210⟩, ⟨145, .identity, .p210⟩, ⟨144, .identity, .p210⟩,
    ⟨143, .identity, .p210⟩, ⟨142, .identity, .p210⟩, ⟨141, .identity, .p210⟩, ⟨140, .identity, .p210⟩, ⟨139, .identity, .p210⟩, ⟨138, .identity, .p210⟩, ⟨137, .identity, .p210⟩, ⟨136, .identity, .p210⟩, ⟨135, .identity, .p210⟩, ⟨134, .identity, .p210⟩, ⟨133, .identity, .p210⟩, ⟨132, .identity, .p210⟩,
    ⟨131, .identity, .p210⟩, ⟨130, .identity, .p210⟩, ⟨129, .identity, .p210⟩, ⟨128, .identity, .p210⟩, ⟨127, .identity, .p210⟩, ⟨126, .identity, .p210⟩, ⟨41, .swap24, .p210⟩, ⟨40, .swap24, .p210⟩, ⟨39, .swap24, .p210⟩, ⟨38, .swap24, .p210⟩, ⟨37, .swap24, .p210⟩, ⟨36, .swap24, .p210⟩,
    ⟨65, .swap23, .p210⟩, ⟨64, .swap23, .p210⟩, ⟨63, .swap23, .p210⟩, ⟨62, .swap23, .p210⟩, ⟨61, .swap23, .p210⟩, ⟨60, .swap23, .p210⟩, ⟨59, .swap23, .p210⟩, ⟨58, .swap23, .p210⟩, ⟨57, .swap23, .p210⟩, ⟨56, .swap23, .p210⟩, ⟨55, .swap23, .p210⟩, ⟨54, .swap23, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7488) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7488 ≤ case.val)
    (upper : case.val < 7536) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7527 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7535 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk156.correct

end Krenn.X5OrbitWitnessChunks.Chunk156
