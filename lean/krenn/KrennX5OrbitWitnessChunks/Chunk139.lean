import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk139

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨107, .cycle234, .p210⟩, ⟨106, .cycle234, .p210⟩, ⟨105, .cycle234, .p210⟩, ⟨104, .cycle234, .p210⟩, ⟨103, .cycle234, .p210⟩, ⟨102, .cycle234, .p210⟩, ⟨89, .cycle234, .p210⟩, ⟨88, .cycle234, .p210⟩, ⟨87, .cycle234, .p210⟩, ⟨86, .cycle234, .p210⟩, ⟨85, .cycle234, .p210⟩, ⟨84, .cycle234, .p210⟩,
    ⟨65, .cycle234, .p210⟩, ⟨64, .cycle234, .p210⟩, ⟨63, .cycle234, .p210⟩, ⟨62, .cycle234, .p210⟩, ⟨61, .cycle234, .p210⟩, ⟨60, .cycle234, .p210⟩, ⟨35, .swap24, .p210⟩, ⟨34, .swap24, .p210⟩, ⟨33, .swap24, .p210⟩, ⟨32, .swap24, .p210⟩, ⟨31, .swap24, .p210⟩, ⟨30, .swap24, .p210⟩,
    ⟨329, .identity, .p210⟩, ⟨328, .identity, .p210⟩, ⟨327, .identity, .p210⟩, ⟨326, .identity, .p210⟩, ⟨325, .identity, .p210⟩, ⟨324, .identity, .p210⟩, ⟨323, .swap34, .p210⟩, ⟨322, .swap34, .p210⟩, ⟨321, .swap34, .p210⟩, ⟨320, .swap34, .p210⟩, ⟨319, .swap34, .p210⟩, ⟨318, .swap34, .p210⟩,
    ⟨305, .cycle243, .p210⟩, ⟨304, .cycle243, .p210⟩, ⟨303, .cycle243, .p210⟩, ⟨302, .cycle243, .p210⟩, ⟨301, .cycle243, .p210⟩, ⟨300, .cycle243, .p210⟩, ⟨269, .cycle243, .p210⟩, ⟨268, .cycle243, .p210⟩, ⟨267, .cycle243, .p210⟩, ⟨266, .cycle243, .p210⟩, ⟨265, .cycle243, .p210⟩, ⟨264, .cycle243, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6672) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6672 ≤ case.val)
    (upper : case.val < 6720) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6679 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6719 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk139.correct

end Krenn.X5OrbitWitnessChunks.Chunk139
