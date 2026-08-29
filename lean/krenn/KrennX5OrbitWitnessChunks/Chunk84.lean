import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk84

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨298, .swap23, .p201⟩, ⟨299, .swap23, .p201⟩, ⟨295, .swap23, .p201⟩, ⟨294, .swap23, .p201⟩, ⟨297, .swap23, .p201⟩, ⟨296, .swap23, .p201⟩, ⟨304, .swap23, .p201⟩, ⟨305, .swap23, .p201⟩, ⟨301, .swap23, .p201⟩, ⟨300, .swap23, .p201⟩, ⟨303, .swap23, .p201⟩, ⟨302, .swap23, .p201⟩,
    ⟨190, .swap24, .p201⟩, ⟨191, .swap24, .p201⟩, ⟨187, .swap24, .p201⟩, ⟨186, .swap24, .p201⟩, ⟨189, .swap24, .p201⟩, ⟨188, .swap24, .p201⟩, ⟨100, .swap24, .p201⟩, ⟨101, .swap24, .p201⟩, ⟨97, .swap24, .p201⟩, ⟨96, .swap24, .p201⟩, ⟨99, .swap24, .p201⟩, ⟨98, .swap24, .p201⟩,
    ⟨286, .swap24, .p201⟩, ⟨287, .swap24, .p201⟩, ⟨283, .swap24, .p201⟩, ⟨282, .swap24, .p201⟩, ⟨285, .swap24, .p201⟩, ⟨284, .swap24, .p201⟩, ⟨250, .swap24, .p201⟩, ⟨251, .swap24, .p201⟩, ⟨247, .swap24, .p201⟩, ⟨246, .swap24, .p201⟩, ⟨249, .swap24, .p201⟩, ⟨248, .swap24, .p201⟩,
    ⟨262, .swap23, .p201⟩, ⟨263, .swap23, .p201⟩, ⟨259, .swap23, .p201⟩, ⟨258, .swap23, .p201⟩, ⟨261, .swap23, .p201⟩, ⟨260, .swap23, .p201⟩, ⟨268, .swap23, .p201⟩, ⟨269, .swap23, .p201⟩, ⟨265, .swap23, .p201⟩, ⟨264, .swap23, .p201⟩, ⟨267, .swap23, .p201⟩, ⟨266, .swap23, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4032) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4032 ≤ case.val)
    (upper : case.val < 4080) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4039 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4047 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4055 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4063 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4071 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4079 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk84.correct

end Krenn.X5OrbitWitnessChunks.Chunk84
