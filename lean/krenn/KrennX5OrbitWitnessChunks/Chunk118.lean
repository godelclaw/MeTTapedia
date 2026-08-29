import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk118

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨273, .swap23, .p120⟩, ⟨272, .swap23, .p120⟩, ⟨275, .swap23, .p120⟩, ⟨274, .swap23, .p120⟩, ⟨270, .swap23, .p120⟩, ⟨271, .swap23, .p120⟩, ⟨267, .cycle234, .p120⟩, ⟨266, .cycle234, .p120⟩, ⟨269, .cycle234, .p120⟩, ⟨268, .cycle234, .p120⟩, ⟨264, .cycle234, .p120⟩, ⟨265, .cycle234, .p120⟩,
    ⟨87, .swap24, .p120⟩, ⟨86, .swap24, .p120⟩, ⟨89, .swap24, .p120⟩, ⟨88, .swap24, .p120⟩, ⟨84, .swap24, .p120⟩, ⟨85, .swap24, .p120⟩, ⟨177, .swap24, .p120⟩, ⟨176, .swap24, .p120⟩, ⟨179, .swap24, .p120⟩, ⟨178, .swap24, .p120⟩, ⟨174, .swap24, .p120⟩, ⟨175, .swap24, .p120⟩,
    ⟨309, .swap24, .p120⟩, ⟨308, .swap24, .p120⟩, ⟨311, .swap24, .p120⟩, ⟨310, .swap24, .p120⟩, ⟨306, .swap24, .p120⟩, ⟨307, .swap24, .p120⟩, ⟨273, .swap24, .p120⟩, ⟨272, .swap24, .p120⟩, ⟨275, .swap24, .p120⟩, ⟨274, .swap24, .p120⟩, ⟨270, .swap24, .p120⟩, ⟨271, .swap24, .p120⟩,
    ⟨333, .identity, .p120⟩, ⟨332, .identity, .p120⟩, ⟨335, .identity, .p120⟩, ⟨334, .identity, .p120⟩, ⟨330, .identity, .p120⟩, ⟨331, .identity, .p120⟩, ⟨327, .swap24, .p120⟩, ⟨326, .swap24, .p120⟩, ⟨329, .swap24, .p120⟩, ⟨328, .swap24, .p120⟩, ⟨324, .swap24, .p120⟩, ⟨325, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5664) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5664 ≤ case.val)
    (upper : case.val < 5712) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5671 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5679 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5711 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk118.correct

end Krenn.X5OrbitWitnessChunks.Chunk118
