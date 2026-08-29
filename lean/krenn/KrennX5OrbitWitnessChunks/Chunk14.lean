import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk14

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨96, .swap23, .p012⟩, ⟨97, .swap23, .p012⟩, ⟨98, .swap23, .p012⟩, ⟨99, .swap23, .p012⟩, ⟨100, .swap23, .p012⟩, ⟨101, .swap23, .p012⟩, ⟨102, .swap23, .p012⟩, ⟨103, .swap23, .p012⟩, ⟨104, .swap23, .p012⟩, ⟨105, .swap23, .p012⟩, ⟨106, .swap23, .p012⟩, ⟨107, .swap23, .p012⟩,
    ⟨48, .swap24, .p012⟩, ⟨49, .swap24, .p012⟩, ⟨50, .swap24, .p012⟩, ⟨51, .swap24, .p012⟩, ⟨52, .swap24, .p012⟩, ⟨53, .swap24, .p012⟩, ⟨138, .swap24, .p012⟩, ⟨139, .swap24, .p012⟩, ⟨140, .swap24, .p012⟩, ⟨141, .swap24, .p012⟩, ⟨142, .swap24, .p012⟩, ⟨143, .swap24, .p012⟩,
    ⟨162, .cycle234, .p012⟩, ⟨163, .cycle234, .p012⟩, ⟨164, .cycle234, .p012⟩, ⟨165, .cycle234, .p012⟩, ⟨166, .cycle234, .p012⟩, ⟨167, .cycle234, .p012⟩, ⟨180, .swap23, .p012⟩, ⟨181, .swap23, .p012⟩, ⟨182, .swap23, .p012⟩, ⟨183, .swap23, .p012⟩, ⟨184, .swap23, .p012⟩, ⟨185, .swap23, .p012⟩,
    ⟨186, .swap23, .p012⟩, ⟨187, .swap23, .p012⟩, ⟨188, .swap23, .p012⟩, ⟨189, .swap23, .p012⟩, ⟨190, .swap23, .p012⟩, ⟨191, .swap23, .p012⟩, ⟨192, .swap23, .p012⟩, ⟨193, .swap23, .p012⟩, ⟨194, .swap23, .p012⟩, ⟨195, .swap23, .p012⟩, ⟨196, .swap23, .p012⟩, ⟨197, .swap23, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 672) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 672 ≤ case.val)
    (upper : case.val < 720) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (679 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (719 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk14.correct

end Krenn.X5OrbitWitnessChunks.Chunk14
