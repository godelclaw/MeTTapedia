import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk153

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨215, .identity, .p210⟩, ⟨214, .identity, .p210⟩, ⟨213, .identity, .p210⟩, ⟨212, .identity, .p210⟩, ⟨211, .identity, .p210⟩, ⟨210, .identity, .p210⟩, ⟨209, .swap34, .p210⟩, ⟨208, .swap34, .p210⟩, ⟨207, .swap34, .p210⟩, ⟨206, .swap34, .p210⟩, ⟨205, .swap34, .p210⟩, ⟨204, .swap34, .p210⟩,
    ⟨197, .swap34, .p210⟩, ⟨196, .swap34, .p210⟩, ⟨195, .swap34, .p210⟩, ⟨194, .swap34, .p210⟩, ⟨193, .swap34, .p210⟩, ⟨192, .swap34, .p210⟩, ⟨179, .swap34, .p210⟩, ⟨178, .swap34, .p210⟩, ⟨177, .swap34, .p210⟩, ⟨176, .swap34, .p210⟩, ⟨175, .swap34, .p210⟩, ⟨174, .swap34, .p210⟩,
    ⟨155, .swap34, .p210⟩, ⟨154, .swap34, .p210⟩, ⟨153, .swap34, .p210⟩, ⟨152, .swap34, .p210⟩, ⟨151, .swap34, .p210⟩, ⟨150, .swap34, .p210⟩, ⟨65, .cycle243, .p210⟩, ⟨64, .cycle243, .p210⟩, ⟨63, .cycle243, .p210⟩, ⟨62, .cycle243, .p210⟩, ⟨61, .cycle243, .p210⟩, ⟨60, .cycle243, .p210⟩,
    ⟨209, .identity, .p210⟩, ⟨208, .identity, .p210⟩, ⟨207, .identity, .p210⟩, ⟨206, .identity, .p210⟩, ⟨205, .identity, .p210⟩, ⟨204, .identity, .p210⟩, ⟨203, .identity, .p210⟩, ⟨202, .identity, .p210⟩, ⟨201, .identity, .p210⟩, ⟨200, .identity, .p210⟩, ⟨199, .identity, .p210⟩, ⟨198, .identity, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7344) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7344 ≤ case.val)
    (upper : case.val < 7392) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7383 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7391 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk153.correct

end Krenn.X5OrbitWitnessChunks.Chunk153
