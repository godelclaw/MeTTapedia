import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk113

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨75, .cycle243, .p120⟩, ⟨74, .cycle243, .p120⟩, ⟨77, .cycle243, .p120⟩, ⟨76, .cycle243, .p120⟩, ⟨72, .cycle243, .p120⟩, ⟨73, .cycle243, .p120⟩, ⟨165, .cycle243, .p120⟩, ⟨164, .cycle243, .p120⟩, ⟨167, .cycle243, .p120⟩, ⟨166, .cycle243, .p120⟩, ⟨162, .cycle243, .p120⟩, ⟨163, .cycle243, .p120⟩,
    ⟨225, .identity, .p120⟩, ⟨224, .identity, .p120⟩, ⟨227, .identity, .p120⟩, ⟨226, .identity, .p120⟩, ⟨222, .identity, .p120⟩, ⟨223, .identity, .p120⟩, ⟨219, .identity, .p120⟩, ⟨218, .identity, .p120⟩, ⟨221, .identity, .p120⟩, ⟨220, .identity, .p120⟩, ⟨216, .identity, .p120⟩, ⟨217, .identity, .p120⟩,
    ⟨237, .identity, .p120⟩, ⟨236, .identity, .p120⟩, ⟨239, .identity, .p120⟩, ⟨238, .identity, .p120⟩, ⟨234, .identity, .p120⟩, ⟨235, .identity, .p120⟩, ⟨231, .identity, .p120⟩, ⟨230, .identity, .p120⟩, ⟨233, .identity, .p120⟩, ⟨232, .identity, .p120⟩, ⟨228, .identity, .p120⟩, ⟨229, .identity, .p120⟩,
    ⟨69, .swap24, .p120⟩, ⟨68, .swap24, .p120⟩, ⟨71, .swap24, .p120⟩, ⟨70, .swap24, .p120⟩, ⟨66, .swap24, .p120⟩, ⟨67, .swap24, .p120⟩, ⟨159, .swap24, .p120⟩, ⟨158, .swap24, .p120⟩, ⟨161, .swap24, .p120⟩, ⟨160, .swap24, .p120⟩, ⟨156, .swap24, .p120⟩, ⟨157, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5424) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5424 ≤ case.val)
    (upper : case.val < 5472) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5431 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5439 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5471 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk113.correct

end Krenn.X5OrbitWitnessChunks.Chunk113
