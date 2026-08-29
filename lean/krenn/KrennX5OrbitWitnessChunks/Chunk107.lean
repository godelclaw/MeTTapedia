import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk107

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨244, .identity, .p201⟩, ⟨245, .identity, .p201⟩, ⟨241, .identity, .p201⟩, ⟨240, .identity, .p201⟩, ⟨243, .identity, .p201⟩, ⟨242, .identity, .p201⟩, ⟨226, .swap34, .p201⟩, ⟨227, .swap34, .p201⟩, ⟨223, .swap34, .p201⟩, ⟨222, .swap34, .p201⟩, ⟨225, .swap34, .p201⟩, ⟨224, .swap34, .p201⟩,
    ⟨232, .identity, .p201⟩, ⟨233, .identity, .p201⟩, ⟨229, .identity, .p201⟩, ⟨228, .identity, .p201⟩, ⟨231, .identity, .p201⟩, ⟨230, .identity, .p201⟩, ⟨238, .identity, .p201⟩, ⟨239, .identity, .p201⟩, ⟨235, .identity, .p201⟩, ⟨234, .identity, .p201⟩, ⟨237, .identity, .p201⟩, ⟨236, .identity, .p201⟩,
    ⟨160, .swap24, .p201⟩, ⟨161, .swap24, .p201⟩, ⟨157, .swap24, .p201⟩, ⟨156, .swap24, .p201⟩, ⟨159, .swap24, .p201⟩, ⟨158, .swap24, .p201⟩, ⟨70, .swap24, .p201⟩, ⟨71, .swap24, .p201⟩, ⟨67, .swap24, .p201⟩, ⟨66, .swap24, .p201⟩, ⟨69, .swap24, .p201⟩, ⟨68, .swap24, .p201⟩,
    ⟨226, .identity, .p201⟩, ⟨227, .identity, .p201⟩, ⟨223, .identity, .p201⟩, ⟨222, .identity, .p201⟩, ⟨225, .identity, .p201⟩, ⟨224, .identity, .p201⟩, ⟨220, .identity, .p201⟩, ⟨221, .identity, .p201⟩, ⟨217, .identity, .p201⟩, ⟨216, .identity, .p201⟩, ⟨219, .identity, .p201⟩, ⟨218, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5136) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5136 ≤ case.val)
    (upper : case.val < 5184) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5143 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5151 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5183 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk107.correct

end Krenn.X5OrbitWitnessChunks.Chunk107
