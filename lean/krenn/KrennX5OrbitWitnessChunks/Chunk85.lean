import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk85

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨172, .swap24, .p201⟩, ⟨173, .swap24, .p201⟩, ⟨169, .swap24, .p201⟩, ⟨168, .swap24, .p201⟩, ⟨171, .swap24, .p201⟩, ⟨170, .swap24, .p201⟩, ⟨82, .swap24, .p201⟩, ⟨83, .swap24, .p201⟩, ⟨79, .swap24, .p201⟩, ⟨78, .swap24, .p201⟩, ⟨81, .swap24, .p201⟩, ⟨80, .swap24, .p201⟩,
    ⟨250, .cycle234, .p201⟩, ⟨251, .cycle234, .p201⟩, ⟨247, .cycle234, .p201⟩, ⟨246, .cycle234, .p201⟩, ⟨249, .cycle234, .p201⟩, ⟨248, .cycle234, .p201⟩, ⟨232, .swap24, .p201⟩, ⟨233, .swap24, .p201⟩, ⟨229, .swap24, .p201⟩, ⟨228, .swap24, .p201⟩, ⟨231, .swap24, .p201⟩, ⟨230, .swap24, .p201⟩,
    ⟨322, .swap24, .p201⟩, ⟨323, .swap24, .p201⟩, ⟨319, .swap24, .p201⟩, ⟨318, .swap24, .p201⟩, ⟨321, .swap24, .p201⟩, ⟨320, .swap24, .p201⟩, ⟨328, .swap23, .p201⟩, ⟨329, .swap23, .p201⟩, ⟨325, .swap23, .p201⟩, ⟨324, .swap23, .p201⟩, ⟨327, .swap23, .p201⟩, ⟨326, .swap23, .p201⟩,
    ⟨208, .swap24, .p201⟩, ⟨209, .swap24, .p201⟩, ⟨205, .swap24, .p201⟩, ⟨204, .swap24, .p201⟩, ⟨207, .swap24, .p201⟩, ⟨206, .swap24, .p201⟩, ⟨118, .swap24, .p201⟩, ⟨119, .swap24, .p201⟩, ⟨115, .swap24, .p201⟩, ⟨114, .swap24, .p201⟩, ⟨117, .swap24, .p201⟩, ⟨116, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4080) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4080 ≤ case.val)
    (upper : case.val < 4128) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4087 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4095 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4103 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4127 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk85.correct

end Krenn.X5OrbitWitnessChunks.Chunk85
