import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk70

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨38, .swap24, .p102⟩, ⟨39, .swap24, .p102⟩, ⟨36, .swap24, .p102⟩, ⟨37, .swap24, .p102⟩, ⟨41, .swap24, .p102⟩, ⟨40, .swap24, .p102⟩, ⟨128, .identity, .p102⟩, ⟨129, .identity, .p102⟩, ⟨126, .identity, .p102⟩, ⟨127, .identity, .p102⟩, ⟨131, .identity, .p102⟩, ⟨130, .identity, .p102⟩,
    ⟨152, .identity, .p102⟩, ⟨153, .identity, .p102⟩, ⟨150, .identity, .p102⟩, ⟨151, .identity, .p102⟩, ⟨155, .identity, .p102⟩, ⟨154, .identity, .p102⟩, ⟨146, .identity, .p102⟩, ⟨147, .identity, .p102⟩, ⟨144, .identity, .p102⟩, ⟨145, .identity, .p102⟩, ⟨149, .identity, .p102⟩, ⟨148, .identity, .p102⟩,
    ⟨176, .swap34, .p102⟩, ⟨177, .swap34, .p102⟩, ⟨174, .swap34, .p102⟩, ⟨175, .swap34, .p102⟩, ⟨179, .swap34, .p102⟩, ⟨178, .swap34, .p102⟩, ⟨194, .swap34, .p102⟩, ⟨195, .swap34, .p102⟩, ⟨192, .swap34, .p102⟩, ⟨193, .swap34, .p102⟩, ⟨197, .swap34, .p102⟩, ⟨196, .swap34, .p102⟩,
    ⟨62, .cycle243, .p102⟩, ⟨63, .cycle243, .p102⟩, ⟨60, .cycle243, .p102⟩, ⟨61, .cycle243, .p102⟩, ⟨65, .cycle243, .p102⟩, ⟨64, .cycle243, .p102⟩, ⟨152, .swap34, .p102⟩, ⟨153, .swap34, .p102⟩, ⟨150, .swap34, .p102⟩, ⟨151, .swap34, .p102⟩, ⟨155, .swap34, .p102⟩, ⟨154, .swap34, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3360) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3360 ≤ case.val)
    (upper : case.val < 3408) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3383 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3391 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3407 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk70.correct

end Krenn.X5OrbitWitnessChunks.Chunk70
