import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk92

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨142, .identity, .p201⟩, ⟨143, .identity, .p201⟩, ⟨139, .identity, .p201⟩, ⟨138, .identity, .p201⟩, ⟨141, .identity, .p201⟩, ⟨140, .identity, .p201⟩, ⟨136, .identity, .p201⟩, ⟨137, .identity, .p201⟩, ⟨133, .identity, .p201⟩, ⟨132, .identity, .p201⟩, ⟨135, .identity, .p201⟩, ⟨134, .identity, .p201⟩,
    ⟨58, .swap23, .p201⟩, ⟨59, .swap23, .p201⟩, ⟨55, .swap23, .p201⟩, ⟨54, .swap23, .p201⟩, ⟨57, .swap23, .p201⟩, ⟨56, .swap23, .p201⟩, ⟨64, .swap23, .p201⟩, ⟨65, .swap23, .p201⟩, ⟨61, .swap23, .p201⟩, ⟨60, .swap23, .p201⟩, ⟨63, .swap23, .p201⟩, ⟨62, .swap23, .p201⟩,
    ⟨40, .swap23, .p201⟩, ⟨41, .swap23, .p201⟩, ⟨37, .swap23, .p201⟩, ⟨36, .swap23, .p201⟩, ⟨39, .swap23, .p201⟩, ⟨38, .swap23, .p201⟩, ⟨10, .swap24, .p201⟩, ⟨11, .swap24, .p201⟩, ⟨7, .swap24, .p201⟩, ⟨6, .swap24, .p201⟩, ⟨9, .swap24, .p201⟩, ⟨8, .swap24, .p201⟩,
    ⟨52, .swap23, .p201⟩, ⟨53, .swap23, .p201⟩, ⟨49, .swap23, .p201⟩, ⟨48, .swap23, .p201⟩, ⟨51, .swap23, .p201⟩, ⟨50, .swap23, .p201⟩, ⟨46, .swap23, .p201⟩, ⟨47, .swap23, .p201⟩, ⟨43, .swap23, .p201⟩, ⟨42, .swap23, .p201⟩, ⟨45, .swap23, .p201⟩, ⟨44, .swap23, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4416) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4416 ≤ case.val)
    (upper : case.val < 4464) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4431 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4439 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4463 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk92.correct

end Krenn.X5OrbitWitnessChunks.Chunk92
