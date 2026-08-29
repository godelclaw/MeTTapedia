import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk154

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨191, .swap34, .p210⟩, ⟨190, .swap34, .p210⟩, ⟨189, .swap34, .p210⟩, ⟨188, .swap34, .p210⟩, ⟨187, .swap34, .p210⟩, ⟨186, .swap34, .p210⟩, ⟨173, .swap34, .p210⟩, ⟨172, .swap34, .p210⟩, ⟨171, .swap34, .p210⟩, ⟨170, .swap34, .p210⟩, ⟨169, .swap34, .p210⟩, ⟨168, .swap34, .p210⟩,
    ⟨149, .swap34, .p210⟩, ⟨148, .swap34, .p210⟩, ⟨147, .swap34, .p210⟩, ⟨146, .swap34, .p210⟩, ⟨145, .swap34, .p210⟩, ⟨144, .swap34, .p210⟩, ⟨59, .cycle243, .p210⟩, ⟨58, .cycle243, .p210⟩, ⟨57, .cycle243, .p210⟩, ⟨56, .cycle243, .p210⟩, ⟨55, .cycle243, .p210⟩, ⟨54, .cycle243, .p210⟩,
    ⟨197, .identity, .p210⟩, ⟨196, .identity, .p210⟩, ⟨195, .identity, .p210⟩, ⟨194, .identity, .p210⟩, ⟨193, .identity, .p210⟩, ⟨192, .identity, .p210⟩, ⟨191, .identity, .p210⟩, ⟨190, .identity, .p210⟩, ⟨189, .identity, .p210⟩, ⟨188, .identity, .p210⟩, ⟨187, .identity, .p210⟩, ⟨186, .identity, .p210⟩,
    ⟨185, .identity, .p210⟩, ⟨184, .identity, .p210⟩, ⟨183, .identity, .p210⟩, ⟨182, .identity, .p210⟩, ⟨181, .identity, .p210⟩, ⟨180, .identity, .p210⟩, ⟨167, .swap34, .p210⟩, ⟨166, .swap34, .p210⟩, ⟨165, .swap34, .p210⟩, ⟨164, .swap34, .p210⟩, ⟨163, .swap34, .p210⟩, ⟨162, .swap34, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7392) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7392 ≤ case.val)
    (upper : case.val < 7440) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7431 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7439 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk154.correct

end Krenn.X5OrbitWitnessChunks.Chunk154
