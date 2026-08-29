import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk90

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨202, .identity, .p201⟩, ⟨203, .identity, .p201⟩, ⟨199, .identity, .p201⟩, ⟨198, .identity, .p201⟩, ⟨201, .identity, .p201⟩, ⟨200, .identity, .p201⟩, ⟨208, .identity, .p201⟩, ⟨209, .identity, .p201⟩, ⟨205, .identity, .p201⟩, ⟨204, .identity, .p201⟩, ⟨207, .identity, .p201⟩, ⟨206, .identity, .p201⟩,
    ⟨148, .swap34, .p201⟩, ⟨149, .swap34, .p201⟩, ⟨145, .swap34, .p201⟩, ⟨144, .swap34, .p201⟩, ⟨147, .swap34, .p201⟩, ⟨146, .swap34, .p201⟩, ⟨58, .cycle243, .p201⟩, ⟨59, .cycle243, .p201⟩, ⟨55, .cycle243, .p201⟩, ⟨54, .cycle243, .p201⟩, ⟨57, .cycle243, .p201⟩, ⟨56, .cycle243, .p201⟩,
    ⟨190, .swap34, .p201⟩, ⟨191, .swap34, .p201⟩, ⟨187, .swap34, .p201⟩, ⟨186, .swap34, .p201⟩, ⟨189, .swap34, .p201⟩, ⟨188, .swap34, .p201⟩, ⟨172, .swap34, .p201⟩, ⟨173, .swap34, .p201⟩, ⟨169, .swap34, .p201⟩, ⟨168, .swap34, .p201⟩, ⟨171, .swap34, .p201⟩, ⟨170, .swap34, .p201⟩,
    ⟨208, .swap34, .p201⟩, ⟨209, .swap34, .p201⟩, ⟨205, .swap34, .p201⟩, ⟨204, .swap34, .p201⟩, ⟨207, .swap34, .p201⟩, ⟨206, .swap34, .p201⟩, ⟨214, .identity, .p201⟩, ⟨215, .identity, .p201⟩, ⟨211, .identity, .p201⟩, ⟨210, .identity, .p201⟩, ⟨213, .identity, .p201⟩, ⟨212, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4320) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4320 ≤ case.val)
    (upper : case.val < 4368) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4335 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4343 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4367 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk90.correct

end Krenn.X5OrbitWitnessChunks.Chunk90
