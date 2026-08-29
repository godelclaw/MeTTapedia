import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk15

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨72, .swap24, .p012⟩, ⟨73, .swap24, .p012⟩, ⟨74, .swap24, .p012⟩, ⟨75, .swap24, .p012⟩, ⟨76, .swap24, .p012⟩, ⟨77, .swap24, .p012⟩, ⟨162, .swap24, .p012⟩, ⟨163, .swap24, .p012⟩, ⟨164, .swap24, .p012⟩, ⟨165, .swap24, .p012⟩, ⟨166, .swap24, .p012⟩, ⟨167, .swap24, .p012⟩,
    ⟨222, .swap24, .p012⟩, ⟨223, .swap24, .p012⟩, ⟨224, .swap24, .p012⟩, ⟨225, .swap24, .p012⟩, ⟨226, .swap24, .p012⟩, ⟨227, .swap24, .p012⟩, ⟨240, .swap23, .p012⟩, ⟨241, .swap23, .p012⟩, ⟨242, .swap23, .p012⟩, ⟨243, .swap23, .p012⟩, ⟨244, .swap23, .p012⟩, ⟨245, .swap23, .p012⟩,
    ⟨246, .swap23, .p012⟩, ⟨247, .swap23, .p012⟩, ⟨248, .swap23, .p012⟩, ⟨249, .swap23, .p012⟩, ⟨250, .swap23, .p012⟩, ⟨251, .swap23, .p012⟩, ⟨252, .swap23, .p012⟩, ⟨253, .swap23, .p012⟩, ⟨254, .swap23, .p012⟩, ⟨255, .swap23, .p012⟩, ⟨256, .swap23, .p012⟩, ⟨257, .swap23, .p012⟩,
    ⟨90, .swap24, .p012⟩, ⟨91, .swap24, .p012⟩, ⟨92, .swap24, .p012⟩, ⟨93, .swap24, .p012⟩, ⟨94, .swap24, .p012⟩, ⟨95, .swap24, .p012⟩, ⟨180, .swap24, .p012⟩, ⟨181, .swap24, .p012⟩, ⟨182, .swap24, .p012⟩, ⟨183, .swap24, .p012⟩, ⟨184, .swap24, .p012⟩, ⟨185, .swap24, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 720) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 720 ≤ case.val)
    (upper : case.val < 768) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (727 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (767 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk15.correct

end Krenn.X5OrbitWitnessChunks.Chunk15
