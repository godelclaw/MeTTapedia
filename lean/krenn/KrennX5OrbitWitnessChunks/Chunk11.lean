import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk11

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨228, .identity, .p012⟩, ⟨229, .identity, .p012⟩, ⟨230, .identity, .p012⟩, ⟨231, .identity, .p012⟩, ⟨232, .identity, .p012⟩, ⟨233, .identity, .p012⟩, ⟨234, .identity, .p012⟩, ⟨235, .identity, .p012⟩, ⟨236, .identity, .p012⟩, ⟨237, .identity, .p012⟩, ⟨238, .identity, .p012⟩, ⟨239, .identity, .p012⟩,
    ⟨72, .cycle243, .p012⟩, ⟨73, .cycle243, .p012⟩, ⟨74, .cycle243, .p012⟩, ⟨75, .cycle243, .p012⟩, ⟨76, .cycle243, .p012⟩, ⟨77, .cycle243, .p012⟩, ⟨162, .cycle243, .p012⟩, ⟨163, .cycle243, .p012⟩, ⟨164, .cycle243, .p012⟩, ⟨165, .cycle243, .p012⟩, ⟨166, .cycle243, .p012⟩, ⟨167, .cycle243, .p012⟩,
    ⟨222, .swap34, .p012⟩, ⟨223, .swap34, .p012⟩, ⟨224, .swap34, .p012⟩, ⟨225, .swap34, .p012⟩, ⟨226, .swap34, .p012⟩, ⟨227, .swap34, .p012⟩, ⟨240, .identity, .p012⟩, ⟨241, .identity, .p012⟩, ⟨242, .identity, .p012⟩, ⟨243, .identity, .p012⟩, ⟨244, .identity, .p012⟩, ⟨245, .identity, .p012⟩,
    ⟨246, .identity, .p012⟩, ⟨247, .identity, .p012⟩, ⟨248, .identity, .p012⟩, ⟨249, .identity, .p012⟩, ⟨250, .identity, .p012⟩, ⟨251, .identity, .p012⟩, ⟨252, .identity, .p012⟩, ⟨253, .identity, .p012⟩, ⟨254, .identity, .p012⟩, ⟨255, .identity, .p012⟩, ⟨256, .identity, .p012⟩, ⟨257, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 528) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 528 ≤ case.val)
    (upper : case.val < 576) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (535 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (575 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk11.correct

end Krenn.X5OrbitWitnessChunks.Chunk11
