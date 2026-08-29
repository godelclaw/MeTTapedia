import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk76

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨116, .swap24, .p102⟩, ⟨117, .swap24, .p102⟩, ⟨114, .swap24, .p102⟩, ⟨115, .swap24, .p102⟩, ⟨119, .swap24, .p102⟩, ⟨118, .swap24, .p102⟩, ⟨206, .swap24, .p102⟩, ⟨207, .swap24, .p102⟩, ⟨204, .swap24, .p102⟩, ⟨205, .swap24, .p102⟩, ⟨209, .swap24, .p102⟩, ⟨208, .swap24, .p102⟩,
    ⟨326, .swap23, .p102⟩, ⟨327, .swap23, .p102⟩, ⟨324, .swap23, .p102⟩, ⟨325, .swap23, .p102⟩, ⟨329, .swap23, .p102⟩, ⟨328, .swap23, .p102⟩, ⟨320, .swap24, .p102⟩, ⟨321, .swap24, .p102⟩, ⟨318, .swap24, .p102⟩, ⟨319, .swap24, .p102⟩, ⟨323, .swap24, .p102⟩, ⟨322, .swap24, .p102⟩,
    ⟨230, .swap24, .p102⟩, ⟨231, .swap24, .p102⟩, ⟨228, .swap24, .p102⟩, ⟨229, .swap24, .p102⟩, ⟨233, .swap24, .p102⟩, ⟨232, .swap24, .p102⟩, ⟨248, .cycle234, .p102⟩, ⟨249, .cycle234, .p102⟩, ⟨246, .cycle234, .p102⟩, ⟨247, .cycle234, .p102⟩, ⟨251, .cycle234, .p102⟩, ⟨250, .cycle234, .p102⟩,
    ⟨80, .swap24, .p102⟩, ⟨81, .swap24, .p102⟩, ⟨78, .swap24, .p102⟩, ⟨79, .swap24, .p102⟩, ⟨83, .swap24, .p102⟩, ⟨82, .swap24, .p102⟩, ⟨170, .swap24, .p102⟩, ⟨171, .swap24, .p102⟩, ⟨168, .swap24, .p102⟩, ⟨169, .swap24, .p102⟩, ⟨173, .swap24, .p102⟩, ⟨172, .swap24, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3648) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3648 ≤ case.val)
    (upper : case.val < 3696) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3648 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3649 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3650 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3651 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3652 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3653 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3654 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3655 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3656 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3657 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3658 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3659 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3660 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3661 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3662 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3663 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3664 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3665 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3666 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3667 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3668 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3669 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3670 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3671 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3672 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3673 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3674 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3675 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3676 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3677 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3678 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3679 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3695 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk76.correct

end Krenn.X5OrbitWitnessChunks.Chunk76
