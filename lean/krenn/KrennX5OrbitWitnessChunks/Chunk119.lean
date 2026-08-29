import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk119

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨123, .swap24, .p120⟩, ⟨122, .swap24, .p120⟩, ⟨125, .swap24, .p120⟩, ⟨124, .swap24, .p120⟩, ⟨120, .swap24, .p120⟩, ⟨121, .swap24, .p120⟩, ⟨213, .swap24, .p120⟩, ⟨212, .swap24, .p120⟩, ⟨215, .swap24, .p120⟩, ⟨214, .swap24, .p120⟩, ⟨210, .swap24, .p120⟩, ⟨211, .swap24, .p120⟩,
    ⟨303, .swap24, .p120⟩, ⟨302, .swap24, .p120⟩, ⟨305, .swap24, .p120⟩, ⟨304, .swap24, .p120⟩, ⟨300, .swap24, .p120⟩, ⟨301, .swap24, .p120⟩, ⟨267, .swap24, .p120⟩, ⟨266, .swap24, .p120⟩, ⟨269, .swap24, .p120⟩, ⟨268, .swap24, .p120⟩, ⟨264, .swap24, .p120⟩, ⟨265, .swap24, .p120⟩,
    ⟨327, .swap23, .p120⟩, ⟨326, .swap23, .p120⟩, ⟨329, .swap23, .p120⟩, ⟨328, .swap23, .p120⟩, ⟨324, .swap23, .p120⟩, ⟨325, .swap23, .p120⟩, ⟨321, .swap24, .p120⟩, ⟨320, .swap24, .p120⟩, ⟨323, .swap24, .p120⟩, ⟨322, .swap24, .p120⟩, ⟨318, .swap24, .p120⟩, ⟨319, .swap24, .p120⟩,
    ⟨117, .swap24, .p120⟩, ⟨116, .swap24, .p120⟩, ⟨119, .swap24, .p120⟩, ⟨118, .swap24, .p120⟩, ⟨114, .swap24, .p120⟩, ⟨115, .swap24, .p120⟩, ⟨207, .swap24, .p120⟩, ⟨206, .swap24, .p120⟩, ⟨209, .swap24, .p120⟩, ⟨208, .swap24, .p120⟩, ⟨204, .swap24, .p120⟩, ⟨205, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5712) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5712 ≤ case.val)
    (upper : case.val < 5760) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5719 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5727 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5759 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk119.correct

end Krenn.X5OrbitWitnessChunks.Chunk119
