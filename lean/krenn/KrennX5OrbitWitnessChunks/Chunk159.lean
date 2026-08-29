import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk159

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨107, .identity, .p210⟩, ⟨106, .identity, .p210⟩, ⟨105, .identity, .p210⟩, ⟨104, .identity, .p210⟩, ⟨103, .identity, .p210⟩, ⟨102, .identity, .p210⟩, ⟨101, .identity, .p210⟩, ⟨100, .identity, .p210⟩, ⟨99, .identity, .p210⟩, ⟨98, .identity, .p210⟩, ⟨97, .identity, .p210⟩, ⟨96, .identity, .p210⟩,
    ⟨95, .identity, .p210⟩, ⟨94, .identity, .p210⟩, ⟨93, .identity, .p210⟩, ⟨92, .identity, .p210⟩, ⟨91, .identity, .p210⟩, ⟨90, .identity, .p210⟩, ⟨77, .swap34, .p210⟩, ⟨76, .swap34, .p210⟩, ⟨75, .swap34, .p210⟩, ⟨74, .swap34, .p210⟩, ⟨73, .swap34, .p210⟩, ⟨72, .swap34, .p210⟩,
    ⟨53, .swap34, .p210⟩, ⟨52, .swap34, .p210⟩, ⟨51, .swap34, .p210⟩, ⟨50, .swap34, .p210⟩, ⟨49, .swap34, .p210⟩, ⟨48, .swap34, .p210⟩, ⟨23, .swap34, .p210⟩, ⟨22, .swap34, .p210⟩, ⟨21, .swap34, .p210⟩, ⟨20, .swap34, .p210⟩, ⟨19, .swap34, .p210⟩, ⟨18, .swap34, .p210⟩,
    ⟨89, .identity, .p210⟩, ⟨88, .identity, .p210⟩, ⟨87, .identity, .p210⟩, ⟨86, .identity, .p210⟩, ⟨85, .identity, .p210⟩, ⟨84, .identity, .p210⟩, ⟨83, .identity, .p210⟩, ⟨82, .identity, .p210⟩, ⟨81, .identity, .p210⟩, ⟨80, .identity, .p210⟩, ⟨79, .identity, .p210⟩, ⟨78, .identity, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7632) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7632 ≤ case.val)
    (upper : case.val < 7680) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7647 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7671 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7679 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk159.correct

end Krenn.X5OrbitWitnessChunks.Chunk159
