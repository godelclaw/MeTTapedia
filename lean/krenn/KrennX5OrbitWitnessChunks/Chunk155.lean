import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk155

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨143, .swap34, .p210⟩, ⟨142, .swap34, .p210⟩, ⟨141, .swap34, .p210⟩, ⟨140, .swap34, .p210⟩, ⟨139, .swap34, .p210⟩, ⟨138, .swap34, .p210⟩, ⟨53, .cycle243, .p210⟩, ⟨52, .cycle243, .p210⟩, ⟨51, .cycle243, .p210⟩, ⟨50, .cycle243, .p210⟩, ⟨49, .cycle243, .p210⟩, ⟨48, .cycle243, .p210⟩,
    ⟨179, .identity, .p210⟩, ⟨178, .identity, .p210⟩, ⟨177, .identity, .p210⟩, ⟨176, .identity, .p210⟩, ⟨175, .identity, .p210⟩, ⟨174, .identity, .p210⟩, ⟨173, .identity, .p210⟩, ⟨172, .identity, .p210⟩, ⟨171, .identity, .p210⟩, ⟨170, .identity, .p210⟩, ⟨169, .identity, .p210⟩, ⟨168, .identity, .p210⟩,
    ⟨167, .identity, .p210⟩, ⟨166, .identity, .p210⟩, ⟨165, .identity, .p210⟩, ⟨164, .identity, .p210⟩, ⟨163, .identity, .p210⟩, ⟨162, .identity, .p210⟩, ⟨161, .identity, .p210⟩, ⟨160, .identity, .p210⟩, ⟨159, .identity, .p210⟩, ⟨158, .identity, .p210⟩, ⟨157, .identity, .p210⟩, ⟨156, .identity, .p210⟩,
    ⟨137, .swap34, .p210⟩, ⟨136, .swap34, .p210⟩, ⟨135, .swap34, .p210⟩, ⟨134, .swap34, .p210⟩, ⟨133, .swap34, .p210⟩, ⟨132, .swap34, .p210⟩, ⟨47, .cycle243, .p210⟩, ⟨46, .cycle243, .p210⟩, ⟨45, .cycle243, .p210⟩, ⟨44, .cycle243, .p210⟩, ⟨43, .cycle243, .p210⟩, ⟨42, .cycle243, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7440) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7440 ≤ case.val)
    (upper : case.val < 7488) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7479 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7487 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk155.correct

end Krenn.X5OrbitWitnessChunks.Chunk155
