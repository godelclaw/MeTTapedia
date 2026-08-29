import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk109

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨255, .swap23, .p120⟩, ⟨254, .swap23, .p120⟩, ⟨257, .swap23, .p120⟩, ⟨256, .swap23, .p120⟩, ⟨252, .swap23, .p120⟩, ⟨253, .swap23, .p120⟩, ⟨249, .swap23, .p120⟩, ⟨248, .swap23, .p120⟩, ⟨251, .swap23, .p120⟩, ⟨250, .swap23, .p120⟩, ⟨246, .swap23, .p120⟩, ⟨247, .swap23, .p120⟩,
    ⟨75, .swap24, .p120⟩, ⟨74, .swap24, .p120⟩, ⟨77, .swap24, .p120⟩, ⟨76, .swap24, .p120⟩, ⟨72, .swap24, .p120⟩, ⟨73, .swap24, .p120⟩, ⟨165, .swap24, .p120⟩, ⟨164, .swap24, .p120⟩, ⟨167, .swap24, .p120⟩, ⟨166, .swap24, .p120⟩, ⟨162, .swap24, .p120⟩, ⟨163, .swap24, .p120⟩,
    ⟨291, .swap34, .p120⟩, ⟨290, .swap34, .p120⟩, ⟨293, .swap34, .p120⟩, ⟨292, .swap34, .p120⟩, ⟨288, .swap34, .p120⟩, ⟨289, .swap34, .p120⟩, ⟨255, .cycle243, .p120⟩, ⟨254, .cycle243, .p120⟩, ⟨257, .cycle243, .p120⟩, ⟨256, .cycle243, .p120⟩, ⟨252, .cycle243, .p120⟩, ⟨253, .cycle243, .p120⟩,
    ⟨309, .identity, .p120⟩, ⟨308, .identity, .p120⟩, ⟨311, .identity, .p120⟩, ⟨310, .identity, .p120⟩, ⟨306, .identity, .p120⟩, ⟨307, .identity, .p120⟩, ⟨303, .swap34, .p120⟩, ⟨302, .swap34, .p120⟩, ⟨305, .swap34, .p120⟩, ⟨304, .swap34, .p120⟩, ⟨300, .swap34, .p120⟩, ⟨301, .swap34, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5232) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5232 ≤ case.val)
    (upper : case.val < 5280) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5239 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5247 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5279 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk109.correct

end Krenn.X5OrbitWitnessChunks.Chunk109
