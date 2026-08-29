import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk71

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨212, .identity, .p102⟩, ⟨213, .identity, .p102⟩, ⟨210, .identity, .p102⟩, ⟨211, .identity, .p102⟩, ⟨215, .identity, .p102⟩, ⟨214, .identity, .p102⟩, ⟨206, .swap34, .p102⟩, ⟨207, .swap34, .p102⟩, ⟨204, .swap34, .p102⟩, ⟨205, .swap34, .p102⟩, ⟨209, .swap34, .p102⟩, ⟨208, .swap34, .p102⟩,
    ⟨170, .swap34, .p102⟩, ⟨171, .swap34, .p102⟩, ⟨168, .swap34, .p102⟩, ⟨169, .swap34, .p102⟩, ⟨173, .swap34, .p102⟩, ⟨172, .swap34, .p102⟩, ⟨188, .swap34, .p102⟩, ⟨189, .swap34, .p102⟩, ⟨186, .swap34, .p102⟩, ⟨187, .swap34, .p102⟩, ⟨191, .swap34, .p102⟩, ⟨190, .swap34, .p102⟩,
    ⟨56, .cycle243, .p102⟩, ⟨57, .cycle243, .p102⟩, ⟨54, .cycle243, .p102⟩, ⟨55, .cycle243, .p102⟩, ⟨59, .cycle243, .p102⟩, ⟨58, .cycle243, .p102⟩, ⟨146, .swap34, .p102⟩, ⟨147, .swap34, .p102⟩, ⟨144, .swap34, .p102⟩, ⟨145, .swap34, .p102⟩, ⟨149, .swap34, .p102⟩, ⟨148, .swap34, .p102⟩,
    ⟨206, .identity, .p102⟩, ⟨207, .identity, .p102⟩, ⟨204, .identity, .p102⟩, ⟨205, .identity, .p102⟩, ⟨209, .identity, .p102⟩, ⟨208, .identity, .p102⟩, ⟨200, .identity, .p102⟩, ⟨201, .identity, .p102⟩, ⟨198, .identity, .p102⟩, ⟨199, .identity, .p102⟩, ⟨203, .identity, .p102⟩, ⟨202, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3408) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3408 ≤ case.val)
    (upper : case.val < 3456) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3431 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3439 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3455 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk71.correct

end Krenn.X5OrbitWitnessChunks.Chunk71
