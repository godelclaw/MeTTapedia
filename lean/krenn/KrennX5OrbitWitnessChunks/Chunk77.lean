import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk77

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨266, .swap23, .p102⟩, ⟨267, .swap23, .p102⟩, ⟨264, .swap23, .p102⟩, ⟨265, .swap23, .p102⟩, ⟨269, .swap23, .p102⟩, ⟨268, .swap23, .p102⟩, ⟨260, .swap23, .p102⟩, ⟨261, .swap23, .p102⟩, ⟨258, .swap23, .p102⟩, ⟨259, .swap23, .p102⟩, ⟨263, .swap23, .p102⟩, ⟨262, .swap23, .p102⟩,
    ⟨248, .swap24, .p102⟩, ⟨249, .swap24, .p102⟩, ⟨246, .swap24, .p102⟩, ⟨247, .swap24, .p102⟩, ⟨251, .swap24, .p102⟩, ⟨250, .swap24, .p102⟩, ⟨284, .swap24, .p102⟩, ⟨285, .swap24, .p102⟩, ⟨282, .swap24, .p102⟩, ⟨283, .swap24, .p102⟩, ⟨287, .swap24, .p102⟩, ⟨286, .swap24, .p102⟩,
    ⟨98, .swap24, .p102⟩, ⟨99, .swap24, .p102⟩, ⟨96, .swap24, .p102⟩, ⟨97, .swap24, .p102⟩, ⟨101, .swap24, .p102⟩, ⟨100, .swap24, .p102⟩, ⟨188, .swap24, .p102⟩, ⟨189, .swap24, .p102⟩, ⟨186, .swap24, .p102⟩, ⟨187, .swap24, .p102⟩, ⟨191, .swap24, .p102⟩, ⟨190, .swap24, .p102⟩,
    ⟨302, .swap23, .p102⟩, ⟨303, .swap23, .p102⟩, ⟨300, .swap23, .p102⟩, ⟨301, .swap23, .p102⟩, ⟨305, .swap23, .p102⟩, ⟨304, .swap23, .p102⟩, ⟨296, .swap23, .p102⟩, ⟨297, .swap23, .p102⟩, ⟨294, .swap23, .p102⟩, ⟨295, .swap23, .p102⟩, ⟨299, .swap23, .p102⟩, ⟨298, .swap23, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3696) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3696 ≤ case.val)
    (upper : case.val < 3744) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3719 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3727 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3743 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk77.correct

end Krenn.X5OrbitWitnessChunks.Chunk77
