import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk7

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨162, .swap34, .p012⟩, ⟨163, .swap34, .p012⟩, ⟨164, .swap34, .p012⟩, ⟨165, .swap34, .p012⟩, ⟨166, .swap34, .p012⟩, ⟨167, .swap34, .p012⟩, ⟨180, .identity, .p012⟩, ⟨181, .identity, .p012⟩, ⟨182, .identity, .p012⟩, ⟨183, .identity, .p012⟩, ⟨184, .identity, .p012⟩, ⟨185, .identity, .p012⟩,
    ⟨186, .identity, .p012⟩, ⟨187, .identity, .p012⟩, ⟨188, .identity, .p012⟩, ⟨189, .identity, .p012⟩, ⟨190, .identity, .p012⟩, ⟨191, .identity, .p012⟩, ⟨192, .identity, .p012⟩, ⟨193, .identity, .p012⟩, ⟨194, .identity, .p012⟩, ⟨195, .identity, .p012⟩, ⟨196, .identity, .p012⟩, ⟨197, .identity, .p012⟩,
    ⟨54, .cycle243, .p012⟩, ⟨55, .cycle243, .p012⟩, ⟨56, .cycle243, .p012⟩, ⟨57, .cycle243, .p012⟩, ⟨58, .cycle243, .p012⟩, ⟨59, .cycle243, .p012⟩, ⟨144, .swap34, .p012⟩, ⟨145, .swap34, .p012⟩, ⟨146, .swap34, .p012⟩, ⟨147, .swap34, .p012⟩, ⟨148, .swap34, .p012⟩, ⟨149, .swap34, .p012⟩,
    ⟨168, .swap34, .p012⟩, ⟨169, .swap34, .p012⟩, ⟨170, .swap34, .p012⟩, ⟨171, .swap34, .p012⟩, ⟨172, .swap34, .p012⟩, ⟨173, .swap34, .p012⟩, ⟨186, .swap34, .p012⟩, ⟨187, .swap34, .p012⟩, ⟨188, .swap34, .p012⟩, ⟨189, .swap34, .p012⟩, ⟨190, .swap34, .p012⟩, ⟨191, .swap34, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 336) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 336 ≤ case.val)
    (upper : case.val < 384) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (343 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (383 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk7.correct

end Krenn.X5OrbitWitnessChunks.Chunk7
