import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk115

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨267, .identity, .p120⟩, ⟨266, .identity, .p120⟩, ⟨269, .identity, .p120⟩, ⟨268, .identity, .p120⟩, ⟨264, .identity, .p120⟩, ⟨265, .identity, .p120⟩, ⟨261, .identity, .p120⟩, ⟨260, .identity, .p120⟩, ⟨263, .identity, .p120⟩, ⟨262, .identity, .p120⟩, ⟨258, .identity, .p120⟩, ⟨259, .identity, .p120⟩,
    ⟨81, .cycle243, .p120⟩, ⟨80, .cycle243, .p120⟩, ⟨83, .cycle243, .p120⟩, ⟨82, .cycle243, .p120⟩, ⟨78, .cycle243, .p120⟩, ⟨79, .cycle243, .p120⟩, ⟨171, .cycle243, .p120⟩, ⟨170, .cycle243, .p120⟩, ⟨173, .cycle243, .p120⟩, ⟨172, .cycle243, .p120⟩, ⟨168, .cycle243, .p120⟩, ⟨169, .cycle243, .p120⟩,
    ⟨75, .swap23, .p120⟩, ⟨74, .swap23, .p120⟩, ⟨77, .swap23, .p120⟩, ⟨76, .swap23, .p120⟩, ⟨72, .swap23, .p120⟩, ⟨73, .swap23, .p120⟩, ⟨69, .swap23, .p120⟩, ⟨68, .swap23, .p120⟩, ⟨71, .swap23, .p120⟩, ⟨70, .swap23, .p120⟩, ⟨66, .swap23, .p120⟩, ⟨67, .swap23, .p120⟩,
    ⟨87, .swap23, .p120⟩, ⟨86, .swap23, .p120⟩, ⟨89, .swap23, .p120⟩, ⟨88, .swap23, .p120⟩, ⟨84, .swap23, .p120⟩, ⟨85, .swap23, .p120⟩, ⟨81, .swap23, .p120⟩, ⟨80, .swap23, .p120⟩, ⟨83, .swap23, .p120⟩, ⟨82, .swap23, .p120⟩, ⟨78, .swap23, .p120⟩, ⟨79, .swap23, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5520) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5520 ≤ case.val)
    (upper : case.val < 5568) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5527 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5535 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5567 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk115.correct

end Krenn.X5OrbitWitnessChunks.Chunk115
