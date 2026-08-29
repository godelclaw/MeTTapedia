import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk75

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨272, .swap24, .p102⟩, ⟨273, .swap24, .p102⟩, ⟨270, .swap24, .p102⟩, ⟨271, .swap24, .p102⟩, ⟨275, .swap24, .p102⟩, ⟨274, .swap24, .p102⟩, ⟨308, .swap24, .p102⟩, ⟨309, .swap24, .p102⟩, ⟨306, .swap24, .p102⟩, ⟨307, .swap24, .p102⟩, ⟨311, .swap24, .p102⟩, ⟨310, .swap24, .p102⟩,
    ⟨122, .swap24, .p102⟩, ⟨123, .swap24, .p102⟩, ⟨120, .swap24, .p102⟩, ⟨121, .swap24, .p102⟩, ⟨125, .swap24, .p102⟩, ⟨124, .swap24, .p102⟩, ⟨212, .swap24, .p102⟩, ⟨213, .swap24, .p102⟩, ⟨210, .swap24, .p102⟩, ⟨211, .swap24, .p102⟩, ⟨215, .swap24, .p102⟩, ⟨214, .swap24, .p102⟩,
    ⟨332, .identity, .p102⟩, ⟨333, .identity, .p102⟩, ⟨330, .identity, .p102⟩, ⟨331, .identity, .p102⟩, ⟨335, .identity, .p102⟩, ⟨334, .identity, .p102⟩, ⟨326, .swap24, .p102⟩, ⟨327, .swap24, .p102⟩, ⟨324, .swap24, .p102⟩, ⟨325, .swap24, .p102⟩, ⟨329, .swap24, .p102⟩, ⟨328, .swap24, .p102⟩,
    ⟨266, .swap24, .p102⟩, ⟨267, .swap24, .p102⟩, ⟨264, .swap24, .p102⟩, ⟨265, .swap24, .p102⟩, ⟨269, .swap24, .p102⟩, ⟨268, .swap24, .p102⟩, ⟨302, .swap24, .p102⟩, ⟨303, .swap24, .p102⟩, ⟨300, .swap24, .p102⟩, ⟨301, .swap24, .p102⟩, ⟨305, .swap24, .p102⟩, ⟨304, .swap24, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3600) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3600 ≤ case.val)
    (upper : case.val < 3648) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3600 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3601 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3602 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3603 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3604 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3605 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3606 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3607 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3608 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3609 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3610 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3611 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3612 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3613 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3614 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3615 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3616 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3617 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3618 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3619 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3620 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3621 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3622 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3623 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3624 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3625 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3626 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3627 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3628 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3629 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3630 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3631 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3632 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3633 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3634 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3635 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3636 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3637 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3638 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3639 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3640 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3641 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3642 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3643 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3644 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3645 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3646 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3647 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk75.correct

end Krenn.X5OrbitWitnessChunks.Chunk75
