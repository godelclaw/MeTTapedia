import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk141

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨305, .swap23, .p210⟩, ⟨304, .swap23, .p210⟩, ⟨303, .swap23, .p210⟩, ⟨302, .swap23, .p210⟩, ⟨301, .swap23, .p210⟩, ⟨300, .swap23, .p210⟩, ⟨299, .swap23, .p210⟩, ⟨298, .swap23, .p210⟩, ⟨297, .swap23, .p210⟩, ⟨296, .swap23, .p210⟩, ⟨295, .swap23, .p210⟩, ⟨294, .swap23, .p210⟩,
    ⟨287, .swap24, .p210⟩, ⟨286, .swap24, .p210⟩, ⟨285, .swap24, .p210⟩, ⟨284, .swap24, .p210⟩, ⟨283, .swap24, .p210⟩, ⟨282, .swap24, .p210⟩, ⟨251, .swap24, .p210⟩, ⟨250, .swap24, .p210⟩, ⟨249, .swap24, .p210⟩, ⟨248, .swap24, .p210⟩, ⟨247, .swap24, .p210⟩, ⟨246, .swap24, .p210⟩,
    ⟨191, .swap24, .p210⟩, ⟨190, .swap24, .p210⟩, ⟨189, .swap24, .p210⟩, ⟨188, .swap24, .p210⟩, ⟨187, .swap24, .p210⟩, ⟨186, .swap24, .p210⟩, ⟨101, .swap24, .p210⟩, ⟨100, .swap24, .p210⟩, ⟨99, .swap24, .p210⟩, ⟨98, .swap24, .p210⟩, ⟨97, .swap24, .p210⟩, ⟨96, .swap24, .p210⟩,
    ⟨269, .swap23, .p210⟩, ⟨268, .swap23, .p210⟩, ⟨267, .swap23, .p210⟩, ⟨266, .swap23, .p210⟩, ⟨265, .swap23, .p210⟩, ⟨264, .swap23, .p210⟩, ⟨263, .swap23, .p210⟩, ⟨262, .swap23, .p210⟩, ⟨261, .swap23, .p210⟩, ⟨260, .swap23, .p210⟩, ⟨259, .swap23, .p210⟩, ⟨258, .swap23, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6768) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6768 ≤ case.val)
    (upper : case.val < 6816) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6775 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6783 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6791 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6799 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6807 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6815 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk141.correct

end Krenn.X5OrbitWitnessChunks.Chunk141
