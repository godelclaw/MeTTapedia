import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk88

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨64, .cycle234, .p201⟩, ⟨65, .cycle234, .p201⟩, ⟨61, .cycle234, .p201⟩, ⟨60, .cycle234, .p201⟩, ⟨63, .cycle234, .p201⟩, ⟨62, .cycle234, .p201⟩, ⟨34, .swap24, .p201⟩, ⟨35, .swap24, .p201⟩, ⟨31, .swap24, .p201⟩, ⟨30, .swap24, .p201⟩, ⟨33, .swap24, .p201⟩, ⟨32, .swap24, .p201⟩,
    ⟨106, .cycle234, .p201⟩, ⟨107, .cycle234, .p201⟩, ⟨103, .cycle234, .p201⟩, ⟨102, .cycle234, .p201⟩, ⟨105, .cycle234, .p201⟩, ⟨104, .cycle234, .p201⟩, ⟨88, .cycle234, .p201⟩, ⟨89, .cycle234, .p201⟩, ⟨85, .cycle234, .p201⟩, ⟨84, .cycle234, .p201⟩, ⟨87, .cycle234, .p201⟩, ⟨86, .cycle234, .p201⟩,
    ⟨304, .cycle234, .p201⟩, ⟨305, .cycle234, .p201⟩, ⟨301, .cycle234, .p201⟩, ⟨300, .cycle234, .p201⟩, ⟨303, .cycle234, .p201⟩, ⟨302, .cycle234, .p201⟩, ⟨310, .swap23, .p201⟩, ⟨311, .swap23, .p201⟩, ⟨307, .swap23, .p201⟩, ⟨306, .swap23, .p201⟩, ⟨309, .swap23, .p201⟩, ⟨308, .swap23, .p201⟩,
    ⟨196, .swap24, .p201⟩, ⟨197, .swap24, .p201⟩, ⟨193, .swap24, .p201⟩, ⟨192, .swap24, .p201⟩, ⟨195, .swap24, .p201⟩, ⟨194, .swap24, .p201⟩, ⟨106, .swap24, .p201⟩, ⟨107, .swap24, .p201⟩, ⟨103, .swap24, .p201⟩, ⟨102, .swap24, .p201⟩, ⟨105, .swap24, .p201⟩, ⟨104, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4224) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4224 ≤ case.val)
    (upper : case.val < 4272) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4239 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4247 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4271 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk88.correct

end Krenn.X5OrbitWitnessChunks.Chunk88
