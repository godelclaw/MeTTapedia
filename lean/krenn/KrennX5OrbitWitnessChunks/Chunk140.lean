import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk140

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨209, .cycle243, .p210⟩, ⟨208, .cycle243, .p210⟩, ⟨207, .cycle243, .p210⟩, ⟨206, .cycle243, .p210⟩, ⟨205, .cycle243, .p210⟩, ⟨204, .cycle243, .p210⟩, ⟨119, .cycle243, .p210⟩, ⟨118, .cycle243, .p210⟩, ⟨117, .cycle243, .p210⟩, ⟨116, .cycle243, .p210⟩, ⟨115, .cycle243, .p210⟩, ⟨114, .cycle243, .p210⟩,
    ⟨323, .identity, .p210⟩, ⟨322, .identity, .p210⟩, ⟨321, .identity, .p210⟩, ⟨320, .identity, .p210⟩, ⟨319, .identity, .p210⟩, ⟨318, .identity, .p210⟩, ⟨317, .identity, .p210⟩, ⟨316, .identity, .p210⟩, ⟨315, .identity, .p210⟩, ⟨314, .identity, .p210⟩, ⟨313, .identity, .p210⟩, ⟨312, .identity, .p210⟩,
    ⟨299, .swap24, .p210⟩, ⟨298, .swap24, .p210⟩, ⟨297, .swap24, .p210⟩, ⟨296, .swap24, .p210⟩, ⟨295, .swap24, .p210⟩, ⟨294, .swap24, .p210⟩, ⟨263, .swap24, .p210⟩, ⟨262, .swap24, .p210⟩, ⟨261, .swap24, .p210⟩, ⟨260, .swap24, .p210⟩, ⟨259, .swap24, .p210⟩, ⟨258, .swap24, .p210⟩,
    ⟨203, .swap24, .p210⟩, ⟨202, .swap24, .p210⟩, ⟨201, .swap24, .p210⟩, ⟨200, .swap24, .p210⟩, ⟨199, .swap24, .p210⟩, ⟨198, .swap24, .p210⟩, ⟨113, .swap24, .p210⟩, ⟨112, .swap24, .p210⟩, ⟨111, .swap24, .p210⟩, ⟨110, .swap24, .p210⟩, ⟨109, .swap24, .p210⟩, ⟨108, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6720) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6720 ≤ case.val)
    (upper : case.val < 6768) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6727 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6767 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk140.correct

end Krenn.X5OrbitWitnessChunks.Chunk140
