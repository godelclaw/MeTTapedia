import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk96

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨58, .identity, .p201⟩, ⟨59, .identity, .p201⟩, ⟨55, .identity, .p201⟩, ⟨54, .identity, .p201⟩, ⟨57, .identity, .p201⟩, ⟨56, .identity, .p201⟩, ⟨64, .identity, .p201⟩, ⟨65, .identity, .p201⟩, ⟨61, .identity, .p201⟩, ⟨60, .identity, .p201⟩, ⟨63, .identity, .p201⟩, ⟨62, .identity, .p201⟩,
    ⟨40, .identity, .p201⟩, ⟨41, .identity, .p201⟩, ⟨37, .identity, .p201⟩, ⟨36, .identity, .p201⟩, ⟨39, .identity, .p201⟩, ⟨38, .identity, .p201⟩, ⟨10, .swap34, .p201⟩, ⟨11, .swap34, .p201⟩, ⟨7, .swap34, .p201⟩, ⟨6, .swap34, .p201⟩, ⟨9, .swap34, .p201⟩, ⟨8, .swap34, .p201⟩,
    ⟨52, .identity, .p201⟩, ⟨53, .identity, .p201⟩, ⟨49, .identity, .p201⟩, ⟨48, .identity, .p201⟩, ⟨51, .identity, .p201⟩, ⟨50, .identity, .p201⟩, ⟨46, .identity, .p201⟩, ⟨47, .identity, .p201⟩, ⟨43, .identity, .p201⟩, ⟨42, .identity, .p201⟩, ⟨45, .identity, .p201⟩, ⟨44, .identity, .p201⟩,
    ⟨28, .identity, .p201⟩, ⟨29, .identity, .p201⟩, ⟨25, .identity, .p201⟩, ⟨24, .identity, .p201⟩, ⟨27, .identity, .p201⟩, ⟨26, .identity, .p201⟩, ⟨34, .identity, .p201⟩, ⟨35, .identity, .p201⟩, ⟨31, .identity, .p201⟩, ⟨30, .identity, .p201⟩, ⟨33, .identity, .p201⟩, ⟨32, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4608) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4608 ≤ case.val)
    (upper : case.val < 4656) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4623 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4631 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4655 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk96.correct

end Krenn.X5OrbitWitnessChunks.Chunk96
