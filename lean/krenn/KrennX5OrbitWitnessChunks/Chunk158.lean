import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk158

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨65, .swap34, .p210⟩, ⟨64, .swap34, .p210⟩, ⟨63, .swap34, .p210⟩, ⟨62, .swap34, .p210⟩, ⟨61, .swap34, .p210⟩, ⟨60, .swap34, .p210⟩, ⟨35, .swap34, .p210⟩, ⟨34, .swap34, .p210⟩, ⟨33, .swap34, .p210⟩, ⟨32, .swap34, .p210⟩, ⟨31, .swap34, .p210⟩, ⟨30, .swap34, .p210⟩,
    ⟨119, .identity, .p210⟩, ⟨118, .identity, .p210⟩, ⟨117, .identity, .p210⟩, ⟨116, .identity, .p210⟩, ⟨115, .identity, .p210⟩, ⟨114, .identity, .p210⟩, ⟨113, .identity, .p210⟩, ⟨112, .identity, .p210⟩, ⟨111, .identity, .p210⟩, ⟨110, .identity, .p210⟩, ⟨109, .identity, .p210⟩, ⟨108, .identity, .p210⟩,
    ⟨101, .swap34, .p210⟩, ⟨100, .swap34, .p210⟩, ⟨99, .swap34, .p210⟩, ⟨98, .swap34, .p210⟩, ⟨97, .swap34, .p210⟩, ⟨96, .swap34, .p210⟩, ⟨83, .swap34, .p210⟩, ⟨82, .swap34, .p210⟩, ⟨81, .swap34, .p210⟩, ⟨80, .swap34, .p210⟩, ⟨79, .swap34, .p210⟩, ⟨78, .swap34, .p210⟩,
    ⟨59, .swap34, .p210⟩, ⟨58, .swap34, .p210⟩, ⟨57, .swap34, .p210⟩, ⟨56, .swap34, .p210⟩, ⟨55, .swap34, .p210⟩, ⟨54, .swap34, .p210⟩, ⟨29, .swap34, .p210⟩, ⟨28, .swap34, .p210⟩, ⟨27, .swap34, .p210⟩, ⟨26, .swap34, .p210⟩, ⟨25, .swap34, .p210⟩, ⟨24, .swap34, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7584) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7584 ≤ case.val)
    (upper : case.val < 7632) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7623 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7631 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk158.correct

end Krenn.X5OrbitWitnessChunks.Chunk158
