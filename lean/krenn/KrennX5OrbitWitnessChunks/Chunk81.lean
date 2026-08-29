import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk81

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨316, .identity, .p201⟩, ⟨317, .identity, .p201⟩, ⟨313, .identity, .p201⟩, ⟨312, .identity, .p201⟩, ⟨315, .identity, .p201⟩, ⟨314, .identity, .p201⟩, ⟨322, .identity, .p201⟩, ⟨323, .identity, .p201⟩, ⟨319, .identity, .p201⟩, ⟨318, .identity, .p201⟩, ⟨321, .identity, .p201⟩, ⟨320, .identity, .p201⟩,
    ⟨202, .swap24, .p201⟩, ⟨203, .swap24, .p201⟩, ⟨199, .swap24, .p201⟩, ⟨198, .swap24, .p201⟩, ⟨201, .swap24, .p201⟩, ⟨200, .swap24, .p201⟩, ⟨112, .swap24, .p201⟩, ⟨113, .swap24, .p201⟩, ⟨109, .swap24, .p201⟩, ⟨108, .swap24, .p201⟩, ⟨111, .swap24, .p201⟩, ⟨110, .swap24, .p201⟩,
    ⟨298, .swap24, .p201⟩, ⟨299, .swap24, .p201⟩, ⟨295, .swap24, .p201⟩, ⟨294, .swap24, .p201⟩, ⟨297, .swap24, .p201⟩, ⟨296, .swap24, .p201⟩, ⟨262, .swap24, .p201⟩, ⟨263, .swap24, .p201⟩, ⟨259, .swap24, .p201⟩, ⟨258, .swap24, .p201⟩, ⟨261, .swap24, .p201⟩, ⟨260, .swap24, .p201⟩,
    ⟨322, .swap34, .p201⟩, ⟨323, .swap34, .p201⟩, ⟨319, .swap34, .p201⟩, ⟨318, .swap34, .p201⟩, ⟨321, .swap34, .p201⟩, ⟨320, .swap34, .p201⟩, ⟨328, .identity, .p201⟩, ⟨329, .identity, .p201⟩, ⟨325, .identity, .p201⟩, ⟨324, .identity, .p201⟩, ⟨327, .identity, .p201⟩, ⟨326, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3888) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3888 ≤ case.val)
    (upper : case.val < 3936) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3895 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3903 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3911 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3919 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3927 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3935 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk81.correct

end Krenn.X5OrbitWitnessChunks.Chunk81
