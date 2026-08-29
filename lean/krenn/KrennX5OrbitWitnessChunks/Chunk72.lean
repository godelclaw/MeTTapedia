import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk72

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨236, .swap24, .p102⟩, ⟨237, .swap24, .p102⟩, ⟨234, .swap24, .p102⟩, ⟨235, .swap24, .p102⟩, ⟨239, .swap24, .p102⟩, ⟨238, .swap24, .p102⟩, ⟨254, .cycle234, .p102⟩, ⟨255, .cycle234, .p102⟩, ⟨252, .cycle234, .p102⟩, ⟨253, .cycle234, .p102⟩, ⟨257, .cycle234, .p102⟩, ⟨256, .cycle234, .p102⟩,
    ⟨86, .swap24, .p102⟩, ⟨87, .swap24, .p102⟩, ⟨84, .swap24, .p102⟩, ⟨85, .swap24, .p102⟩, ⟨89, .swap24, .p102⟩, ⟨88, .swap24, .p102⟩, ⟨176, .swap24, .p102⟩, ⟨177, .swap24, .p102⟩, ⟨174, .swap24, .p102⟩, ⟨175, .swap24, .p102⟩, ⟨179, .swap24, .p102⟩, ⟨178, .swap24, .p102⟩,
    ⟨272, .swap23, .p102⟩, ⟨273, .swap23, .p102⟩, ⟨270, .swap23, .p102⟩, ⟨271, .swap23, .p102⟩, ⟨275, .swap23, .p102⟩, ⟨274, .swap23, .p102⟩, ⟨266, .cycle234, .p102⟩, ⟨267, .cycle234, .p102⟩, ⟨264, .cycle234, .p102⟩, ⟨265, .cycle234, .p102⟩, ⟨269, .cycle234, .p102⟩, ⟨268, .cycle234, .p102⟩,
    ⟨254, .swap24, .p102⟩, ⟨255, .swap24, .p102⟩, ⟨252, .swap24, .p102⟩, ⟨253, .swap24, .p102⟩, ⟨257, .swap24, .p102⟩, ⟨256, .swap24, .p102⟩, ⟨290, .swap24, .p102⟩, ⟨291, .swap24, .p102⟩, ⟨288, .swap24, .p102⟩, ⟨289, .swap24, .p102⟩, ⟨293, .swap24, .p102⟩, ⟨292, .swap24, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3456) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3456 ≤ case.val)
    (upper : case.val < 3504) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3479 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3487 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3503 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk72.correct

end Krenn.X5OrbitWitnessChunks.Chunk72
