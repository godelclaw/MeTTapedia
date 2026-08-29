import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk144

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨311, .identity, .p210⟩, ⟨310, .identity, .p210⟩, ⟨309, .identity, .p210⟩, ⟨308, .identity, .p210⟩, ⟨307, .identity, .p210⟩, ⟨306, .identity, .p210⟩, ⟨305, .swap34, .p210⟩, ⟨304, .swap34, .p210⟩, ⟨303, .swap34, .p210⟩, ⟨302, .swap34, .p210⟩, ⟨301, .swap34, .p210⟩, ⟨300, .swap34, .p210⟩,
    ⟨293, .swap34, .p210⟩, ⟨292, .swap34, .p210⟩, ⟨291, .swap34, .p210⟩, ⟨290, .swap34, .p210⟩, ⟨289, .swap34, .p210⟩, ⟨288, .swap34, .p210⟩, ⟨257, .cycle243, .p210⟩, ⟨256, .cycle243, .p210⟩, ⟨255, .cycle243, .p210⟩, ⟨254, .cycle243, .p210⟩, ⟨253, .cycle243, .p210⟩, ⟨252, .cycle243, .p210⟩,
    ⟨197, .cycle243, .p210⟩, ⟨196, .cycle243, .p210⟩, ⟨195, .cycle243, .p210⟩, ⟨194, .cycle243, .p210⟩, ⟨193, .cycle243, .p210⟩, ⟨192, .cycle243, .p210⟩, ⟨107, .cycle243, .p210⟩, ⟨106, .cycle243, .p210⟩, ⟨105, .cycle243, .p210⟩, ⟨104, .cycle243, .p210⟩, ⟨103, .cycle243, .p210⟩, ⟨102, .cycle243, .p210⟩,
    ⟨305, .identity, .p210⟩, ⟨304, .identity, .p210⟩, ⟨303, .identity, .p210⟩, ⟨302, .identity, .p210⟩, ⟨301, .identity, .p210⟩, ⟨300, .identity, .p210⟩, ⟨299, .identity, .p210⟩, ⟨298, .identity, .p210⟩, ⟨297, .identity, .p210⟩, ⟨296, .identity, .p210⟩, ⟨295, .identity, .p210⟩, ⟨294, .identity, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6912) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6912 ≤ case.val)
    (upper : case.val < 6960) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6919 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6927 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6935 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6943 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6951 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6959 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk144.correct

end Krenn.X5OrbitWitnessChunks.Chunk144
