import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk80

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨326, .identity, .p102⟩, ⟨327, .identity, .p102⟩, ⟨324, .identity, .p102⟩, ⟨325, .identity, .p102⟩, ⟨329, .identity, .p102⟩, ⟨328, .identity, .p102⟩, ⟨320, .swap34, .p102⟩, ⟨321, .swap34, .p102⟩, ⟨318, .swap34, .p102⟩, ⟨319, .swap34, .p102⟩, ⟨323, .swap34, .p102⟩, ⟨322, .swap34, .p102⟩,
    ⟨260, .swap24, .p102⟩, ⟨261, .swap24, .p102⟩, ⟨258, .swap24, .p102⟩, ⟨259, .swap24, .p102⟩, ⟨263, .swap24, .p102⟩, ⟨262, .swap24, .p102⟩, ⟨296, .swap24, .p102⟩, ⟨297, .swap24, .p102⟩, ⟨294, .swap24, .p102⟩, ⟨295, .swap24, .p102⟩, ⟨299, .swap24, .p102⟩, ⟨298, .swap24, .p102⟩,
    ⟨110, .swap24, .p102⟩, ⟨111, .swap24, .p102⟩, ⟨108, .swap24, .p102⟩, ⟨109, .swap24, .p102⟩, ⟨113, .swap24, .p102⟩, ⟨112, .swap24, .p102⟩, ⟨200, .swap24, .p102⟩, ⟨201, .swap24, .p102⟩, ⟨198, .swap24, .p102⟩, ⟨199, .swap24, .p102⟩, ⟨203, .swap24, .p102⟩, ⟨202, .swap24, .p102⟩,
    ⟨320, .identity, .p102⟩, ⟨321, .identity, .p102⟩, ⟨318, .identity, .p102⟩, ⟨319, .identity, .p102⟩, ⟨323, .identity, .p102⟩, ⟨322, .identity, .p102⟩, ⟨314, .identity, .p102⟩, ⟨315, .identity, .p102⟩, ⟨312, .identity, .p102⟩, ⟨313, .identity, .p102⟩, ⟨317, .identity, .p102⟩, ⟨316, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3840) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3840 ≤ case.val)
    (upper : case.val < 3888) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3847 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3855 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3863 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3871 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3879 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3887 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk80.correct

end Krenn.X5OrbitWitnessChunks.Chunk80
