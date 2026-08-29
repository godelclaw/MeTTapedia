import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk89

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨292, .swap24, .p201⟩, ⟨293, .swap24, .p201⟩, ⟨289, .swap24, .p201⟩, ⟨288, .swap24, .p201⟩, ⟨291, .swap24, .p201⟩, ⟨290, .swap24, .p201⟩, ⟨256, .swap24, .p201⟩, ⟨257, .swap24, .p201⟩, ⟨253, .swap24, .p201⟩, ⟨252, .swap24, .p201⟩, ⟨255, .swap24, .p201⟩, ⟨254, .swap24, .p201⟩,
    ⟨268, .cycle234, .p201⟩, ⟨269, .cycle234, .p201⟩, ⟨265, .cycle234, .p201⟩, ⟨264, .cycle234, .p201⟩, ⟨267, .cycle234, .p201⟩, ⟨266, .cycle234, .p201⟩, ⟨274, .swap23, .p201⟩, ⟨275, .swap23, .p201⟩, ⟨271, .swap23, .p201⟩, ⟨270, .swap23, .p201⟩, ⟨273, .swap23, .p201⟩, ⟨272, .swap23, .p201⟩,
    ⟨178, .swap24, .p201⟩, ⟨179, .swap24, .p201⟩, ⟨175, .swap24, .p201⟩, ⟨174, .swap24, .p201⟩, ⟨177, .swap24, .p201⟩, ⟨176, .swap24, .p201⟩, ⟨88, .swap24, .p201⟩, ⟨89, .swap24, .p201⟩, ⟨85, .swap24, .p201⟩, ⟨84, .swap24, .p201⟩, ⟨87, .swap24, .p201⟩, ⟨86, .swap24, .p201⟩,
    ⟨256, .cycle234, .p201⟩, ⟨257, .cycle234, .p201⟩, ⟨253, .cycle234, .p201⟩, ⟨252, .cycle234, .p201⟩, ⟨255, .cycle234, .p201⟩, ⟨254, .cycle234, .p201⟩, ⟨238, .swap24, .p201⟩, ⟨239, .swap24, .p201⟩, ⟨235, .swap24, .p201⟩, ⟨234, .swap24, .p201⟩, ⟨237, .swap24, .p201⟩, ⟨236, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4272) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4272 ≤ case.val)
    (upper : case.val < 4320) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4287 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4295 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4319 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk89.correct

end Krenn.X5OrbitWitnessChunks.Chunk89
