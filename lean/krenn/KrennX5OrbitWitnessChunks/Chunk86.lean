import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk86

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨304, .swap24, .p201⟩, ⟨305, .swap24, .p201⟩, ⟨301, .swap24, .p201⟩, ⟨300, .swap24, .p201⟩, ⟨303, .swap24, .p201⟩, ⟨302, .swap24, .p201⟩, ⟨268, .swap24, .p201⟩, ⟨269, .swap24, .p201⟩, ⟨265, .swap24, .p201⟩, ⟨264, .swap24, .p201⟩, ⟨267, .swap24, .p201⟩, ⟨266, .swap24, .p201⟩,
    ⟨328, .swap24, .p201⟩, ⟨329, .swap24, .p201⟩, ⟨325, .swap24, .p201⟩, ⟨324, .swap24, .p201⟩, ⟨327, .swap24, .p201⟩, ⟨326, .swap24, .p201⟩, ⟨334, .identity, .p201⟩, ⟨335, .identity, .p201⟩, ⟨331, .identity, .p201⟩, ⟨330, .identity, .p201⟩, ⟨333, .identity, .p201⟩, ⟨332, .identity, .p201⟩,
    ⟨214, .swap24, .p201⟩, ⟨215, .swap24, .p201⟩, ⟨211, .swap24, .p201⟩, ⟨210, .swap24, .p201⟩, ⟨213, .swap24, .p201⟩, ⟨212, .swap24, .p201⟩, ⟨124, .swap24, .p201⟩, ⟨125, .swap24, .p201⟩, ⟨121, .swap24, .p201⟩, ⟨120, .swap24, .p201⟩, ⟨123, .swap24, .p201⟩, ⟨122, .swap24, .p201⟩,
    ⟨310, .swap24, .p201⟩, ⟨311, .swap24, .p201⟩, ⟨307, .swap24, .p201⟩, ⟨306, .swap24, .p201⟩, ⟨309, .swap24, .p201⟩, ⟨308, .swap24, .p201⟩, ⟨274, .swap24, .p201⟩, ⟨275, .swap24, .p201⟩, ⟨271, .swap24, .p201⟩, ⟨270, .swap24, .p201⟩, ⟨273, .swap24, .p201⟩, ⟨272, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4128) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4128 ≤ case.val)
    (upper : case.val < 4176) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4143 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4151 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4175 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk86.correct

end Krenn.X5OrbitWitnessChunks.Chunk86
