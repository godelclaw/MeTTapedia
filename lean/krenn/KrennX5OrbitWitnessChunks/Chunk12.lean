import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk12

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨78, .cycle243, .p012⟩, ⟨79, .cycle243, .p012⟩, ⟨80, .cycle243, .p012⟩, ⟨81, .cycle243, .p012⟩, ⟨82, .cycle243, .p012⟩, ⟨83, .cycle243, .p012⟩, ⟨168, .cycle243, .p012⟩, ⟨169, .cycle243, .p012⟩, ⟨170, .cycle243, .p012⟩, ⟨171, .cycle243, .p012⟩, ⟨172, .cycle243, .p012⟩, ⟨173, .cycle243, .p012⟩,
    ⟨228, .swap34, .p012⟩, ⟨229, .swap34, .p012⟩, ⟨230, .swap34, .p012⟩, ⟨231, .swap34, .p012⟩, ⟨232, .swap34, .p012⟩, ⟨233, .swap34, .p012⟩, ⟨246, .swap34, .p012⟩, ⟨247, .swap34, .p012⟩, ⟨248, .swap34, .p012⟩, ⟨249, .swap34, .p012⟩, ⟨250, .swap34, .p012⟩, ⟨251, .swap34, .p012⟩,
    ⟨258, .identity, .p012⟩, ⟨259, .identity, .p012⟩, ⟨260, .identity, .p012⟩, ⟨261, .identity, .p012⟩, ⟨262, .identity, .p012⟩, ⟨263, .identity, .p012⟩, ⟨264, .identity, .p012⟩, ⟨265, .identity, .p012⟩, ⟨266, .identity, .p012⟩, ⟨267, .identity, .p012⟩, ⟨268, .identity, .p012⟩, ⟨269, .identity, .p012⟩,
    ⟨84, .cycle243, .p012⟩, ⟨85, .cycle243, .p012⟩, ⟨86, .cycle243, .p012⟩, ⟨87, .cycle243, .p012⟩, ⟨88, .cycle243, .p012⟩, ⟨89, .cycle243, .p012⟩, ⟨174, .cycle243, .p012⟩, ⟨175, .cycle243, .p012⟩, ⟨176, .cycle243, .p012⟩, ⟨177, .cycle243, .p012⟩, ⟨178, .cycle243, .p012⟩, ⟨179, .cycle243, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 576) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 576 ≤ case.val)
    (upper : case.val < 624) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (583 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (599 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (623 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk12.correct

end Krenn.X5OrbitWitnessChunks.Chunk12
