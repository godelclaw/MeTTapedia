import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk108

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨279, .identity, .p120⟩, ⟨278, .identity, .p120⟩, ⟨281, .identity, .p120⟩, ⟨280, .identity, .p120⟩, ⟨276, .identity, .p120⟩, ⟨277, .identity, .p120⟩, ⟨243, .swap24, .p120⟩, ⟨242, .swap24, .p120⟩, ⟨245, .swap24, .p120⟩, ⟨244, .swap24, .p120⟩, ⟨240, .swap24, .p120⟩, ⟨241, .swap24, .p120⟩,
    ⟨291, .identity, .p120⟩, ⟨290, .identity, .p120⟩, ⟨293, .identity, .p120⟩, ⟨292, .identity, .p120⟩, ⟨288, .identity, .p120⟩, ⟨289, .identity, .p120⟩, ⟨285, .identity, .p120⟩, ⟨284, .identity, .p120⟩, ⟨287, .identity, .p120⟩, ⟨286, .identity, .p120⟩, ⟨282, .identity, .p120⟩, ⟨283, .identity, .p120⟩,
    ⟨93, .swap24, .p120⟩, ⟨92, .swap24, .p120⟩, ⟨95, .swap24, .p120⟩, ⟨94, .swap24, .p120⟩, ⟨90, .swap24, .p120⟩, ⟨91, .swap24, .p120⟩, ⟨183, .swap24, .p120⟩, ⟨182, .swap24, .p120⟩, ⟨185, .swap24, .p120⟩, ⟨184, .swap24, .p120⟩, ⟨180, .swap24, .p120⟩, ⟨181, .swap24, .p120⟩,
    ⟨243, .swap23, .p120⟩, ⟨242, .swap23, .p120⟩, ⟨245, .swap23, .p120⟩, ⟨244, .swap23, .p120⟩, ⟨240, .swap23, .p120⟩, ⟨241, .swap23, .p120⟩, ⟨225, .swap24, .p120⟩, ⟨224, .swap24, .p120⟩, ⟨227, .swap24, .p120⟩, ⟨226, .swap24, .p120⟩, ⟨222, .swap24, .p120⟩, ⟨223, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5184) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5184 ≤ case.val)
    (upper : case.val < 5232) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5191 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5199 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5231 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk108.correct

end Krenn.X5OrbitWitnessChunks.Chunk108
