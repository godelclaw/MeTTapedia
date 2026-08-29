import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk134

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨9, .swap24, .p120⟩, ⟨8, .swap24, .p120⟩, ⟨11, .swap24, .p120⟩, ⟨10, .swap24, .p120⟩, ⟨6, .swap24, .p120⟩, ⟨7, .swap24, .p120⟩, ⟨39, .swap23, .p120⟩, ⟨38, .swap23, .p120⟩, ⟨41, .swap23, .p120⟩, ⟨40, .swap23, .p120⟩, ⟨36, .swap23, .p120⟩, ⟨37, .swap23, .p120⟩,
    ⟨141, .identity, .p120⟩, ⟨140, .identity, .p120⟩, ⟨143, .identity, .p120⟩, ⟨142, .identity, .p120⟩, ⟨138, .identity, .p120⟩, ⟨139, .identity, .p120⟩, ⟨135, .identity, .p120⟩, ⟨134, .identity, .p120⟩, ⟨137, .identity, .p120⟩, ⟨136, .identity, .p120⟩, ⟨132, .identity, .p120⟩, ⟨133, .identity, .p120⟩,
    ⟨153, .identity, .p120⟩, ⟨152, .identity, .p120⟩, ⟨155, .identity, .p120⟩, ⟨154, .identity, .p120⟩, ⟨150, .identity, .p120⟩, ⟨151, .identity, .p120⟩, ⟨147, .identity, .p120⟩, ⟨146, .identity, .p120⟩, ⟨149, .identity, .p120⟩, ⟨148, .identity, .p120⟩, ⟨144, .identity, .p120⟩, ⟨145, .identity, .p120⟩,
    ⟨39, .swap24, .p120⟩, ⟨38, .swap24, .p120⟩, ⟨41, .swap24, .p120⟩, ⟨40, .swap24, .p120⟩, ⟨36, .swap24, .p120⟩, ⟨37, .swap24, .p120⟩, ⟨129, .identity, .p120⟩, ⟨128, .identity, .p120⟩, ⟨131, .identity, .p120⟩, ⟨130, .identity, .p120⟩, ⟨126, .identity, .p120⟩, ⟨127, .identity, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6432) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6432 ≤ case.val)
    (upper : case.val < 6480) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6439 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6479 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk134.correct

end Krenn.X5OrbitWitnessChunks.Chunk134
