import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk91

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨154, .swap34, .p201⟩, ⟨155, .swap34, .p201⟩, ⟨151, .swap34, .p201⟩, ⟨150, .swap34, .p201⟩, ⟨153, .swap34, .p201⟩, ⟨152, .swap34, .p201⟩, ⟨64, .cycle243, .p201⟩, ⟨65, .cycle243, .p201⟩, ⟨61, .cycle243, .p201⟩, ⟨60, .cycle243, .p201⟩, ⟨63, .cycle243, .p201⟩, ⟨62, .cycle243, .p201⟩,
    ⟨196, .swap34, .p201⟩, ⟨197, .swap34, .p201⟩, ⟨193, .swap34, .p201⟩, ⟨192, .swap34, .p201⟩, ⟨195, .swap34, .p201⟩, ⟨194, .swap34, .p201⟩, ⟨178, .swap34, .p201⟩, ⟨179, .swap34, .p201⟩, ⟨175, .swap34, .p201⟩, ⟨174, .swap34, .p201⟩, ⟨177, .swap34, .p201⟩, ⟨176, .swap34, .p201⟩,
    ⟨148, .identity, .p201⟩, ⟨149, .identity, .p201⟩, ⟨145, .identity, .p201⟩, ⟨144, .identity, .p201⟩, ⟨147, .identity, .p201⟩, ⟨146, .identity, .p201⟩, ⟨154, .identity, .p201⟩, ⟨155, .identity, .p201⟩, ⟨151, .identity, .p201⟩, ⟨150, .identity, .p201⟩, ⟨153, .identity, .p201⟩, ⟨152, .identity, .p201⟩,
    ⟨130, .identity, .p201⟩, ⟨131, .identity, .p201⟩, ⟨127, .identity, .p201⟩, ⟨126, .identity, .p201⟩, ⟨129, .identity, .p201⟩, ⟨128, .identity, .p201⟩, ⟨40, .swap24, .p201⟩, ⟨41, .swap24, .p201⟩, ⟨37, .swap24, .p201⟩, ⟨36, .swap24, .p201⟩, ⟨39, .swap24, .p201⟩, ⟨38, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4368) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4368 ≤ case.val)
    (upper : case.val < 4416) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4383 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4391 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4415 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk91.correct

end Krenn.X5OrbitWitnessChunks.Chunk91
