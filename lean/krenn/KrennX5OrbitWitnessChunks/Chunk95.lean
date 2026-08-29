import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk95

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨100, .swap34, .p201⟩, ⟨101, .swap34, .p201⟩, ⟨97, .swap34, .p201⟩, ⟨96, .swap34, .p201⟩, ⟨99, .swap34, .p201⟩, ⟨98, .swap34, .p201⟩, ⟨82, .swap34, .p201⟩, ⟨83, .swap34, .p201⟩, ⟨79, .swap34, .p201⟩, ⟨78, .swap34, .p201⟩, ⟨81, .swap34, .p201⟩, ⟨80, .swap34, .p201⟩,
    ⟨118, .swap34, .p201⟩, ⟨119, .swap34, .p201⟩, ⟨115, .swap34, .p201⟩, ⟨114, .swap34, .p201⟩, ⟨117, .swap34, .p201⟩, ⟨116, .swap34, .p201⟩, ⟨124, .identity, .p201⟩, ⟨125, .identity, .p201⟩, ⟨121, .identity, .p201⟩, ⟨120, .identity, .p201⟩, ⟨123, .identity, .p201⟩, ⟨122, .identity, .p201⟩,
    ⟨64, .swap34, .p201⟩, ⟨65, .swap34, .p201⟩, ⟨61, .swap34, .p201⟩, ⟨60, .swap34, .p201⟩, ⟨63, .swap34, .p201⟩, ⟨62, .swap34, .p201⟩, ⟨34, .swap34, .p201⟩, ⟨35, .swap34, .p201⟩, ⟨31, .swap34, .p201⟩, ⟨30, .swap34, .p201⟩, ⟨33, .swap34, .p201⟩, ⟨32, .swap34, .p201⟩,
    ⟨106, .swap34, .p201⟩, ⟨107, .swap34, .p201⟩, ⟨103, .swap34, .p201⟩, ⟨102, .swap34, .p201⟩, ⟨105, .swap34, .p201⟩, ⟨104, .swap34, .p201⟩, ⟨88, .swap34, .p201⟩, ⟨89, .swap34, .p201⟩, ⟨85, .swap34, .p201⟩, ⟨84, .swap34, .p201⟩, ⟨87, .swap34, .p201⟩, ⟨86, .swap34, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4560) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4560 ≤ case.val)
    (upper : case.val < 4608) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4575 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4583 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4607 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk95.correct

end Krenn.X5OrbitWitnessChunks.Chunk95
