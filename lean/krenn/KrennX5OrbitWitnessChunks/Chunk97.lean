import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk97

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨10, .identity, .p201⟩, ⟨11, .identity, .p201⟩, ⟨7, .identity, .p201⟩, ⟨6, .identity, .p201⟩, ⟨9, .identity, .p201⟩, ⟨8, .identity, .p201⟩, ⟨4, .identity, .p201⟩, ⟨5, .identity, .p201⟩, ⟨1, .identity, .p201⟩, ⟨0, .identity, .p201⟩, ⟨3, .identity, .p201⟩, ⟨2, .identity, .p201⟩,
    ⟨22, .identity, .p201⟩, ⟨23, .identity, .p201⟩, ⟨19, .identity, .p201⟩, ⟨18, .identity, .p201⟩, ⟨21, .identity, .p201⟩, ⟨20, .identity, .p201⟩, ⟨16, .identity, .p201⟩, ⟨17, .identity, .p201⟩, ⟨13, .identity, .p201⟩, ⟨12, .identity, .p201⟩, ⟨15, .identity, .p201⟩, ⟨14, .identity, .p201⟩,
    ⟨100, .identity, .p201⟩, ⟨101, .identity, .p201⟩, ⟨97, .identity, .p201⟩, ⟨96, .identity, .p201⟩, ⟨99, .identity, .p201⟩, ⟨98, .identity, .p201⟩, ⟨106, .identity, .p201⟩, ⟨107, .identity, .p201⟩, ⟨103, .identity, .p201⟩, ⟨102, .identity, .p201⟩, ⟨105, .identity, .p201⟩, ⟨104, .identity, .p201⟩,
    ⟨52, .swap34, .p201⟩, ⟨53, .swap34, .p201⟩, ⟨49, .swap34, .p201⟩, ⟨48, .swap34, .p201⟩, ⟨51, .swap34, .p201⟩, ⟨50, .swap34, .p201⟩, ⟨22, .swap34, .p201⟩, ⟨23, .swap34, .p201⟩, ⟨19, .swap34, .p201⟩, ⟨18, .swap34, .p201⟩, ⟨21, .swap34, .p201⟩, ⟨20, .swap34, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4656) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4656 ≤ case.val)
    (upper : case.val < 4704) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4671 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4679 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4703 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk97.correct

end Krenn.X5OrbitWitnessChunks.Chunk97
