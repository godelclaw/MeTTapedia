import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk79

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨56, .swap24, .p102⟩, ⟨57, .swap24, .p102⟩, ⟨54, .swap24, .p102⟩, ⟨55, .swap24, .p102⟩, ⟨59, .swap24, .p102⟩, ⟨58, .swap24, .p102⟩, ⟨146, .swap24, .p102⟩, ⟨147, .swap24, .p102⟩, ⟨144, .swap24, .p102⟩, ⟨145, .swap24, .p102⟩, ⟨149, .swap24, .p102⟩, ⟨148, .swap24, .p102⟩,
    ⟨206, .swap23, .p102⟩, ⟨207, .swap23, .p102⟩, ⟨204, .swap23, .p102⟩, ⟨205, .swap23, .p102⟩, ⟨209, .swap23, .p102⟩, ⟨208, .swap23, .p102⟩, ⟨200, .swap23, .p102⟩, ⟨201, .swap23, .p102⟩, ⟨198, .swap23, .p102⟩, ⟨199, .swap23, .p102⟩, ⟨203, .swap23, .p102⟩, ⟨202, .swap23, .p102⟩,
    ⟨266, .cycle243, .p102⟩, ⟨267, .cycle243, .p102⟩, ⟨264, .cycle243, .p102⟩, ⟨265, .cycle243, .p102⟩, ⟨269, .cycle243, .p102⟩, ⟨268, .cycle243, .p102⟩, ⟨302, .cycle243, .p102⟩, ⟨303, .cycle243, .p102⟩, ⟨300, .cycle243, .p102⟩, ⟨301, .cycle243, .p102⟩, ⟨305, .cycle243, .p102⟩, ⟨304, .cycle243, .p102⟩,
    ⟨116, .cycle243, .p102⟩, ⟨117, .cycle243, .p102⟩, ⟨114, .cycle243, .p102⟩, ⟨115, .cycle243, .p102⟩, ⟨119, .cycle243, .p102⟩, ⟨118, .cycle243, .p102⟩, ⟨206, .cycle243, .p102⟩, ⟨207, .cycle243, .p102⟩, ⟨204, .cycle243, .p102⟩, ⟨205, .cycle243, .p102⟩, ⟨209, .cycle243, .p102⟩, ⟨208, .cycle243, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3792) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3792 ≤ case.val)
    (upper : case.val < 3840) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3799 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3807 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3815 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3823 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3831 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3839 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk79.correct

end Krenn.X5OrbitWitnessChunks.Chunk79
