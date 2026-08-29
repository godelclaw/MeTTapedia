import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk78

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨80, .cycle234, .p102⟩, ⟨81, .cycle234, .p102⟩, ⟨78, .cycle234, .p102⟩, ⟨79, .cycle234, .p102⟩, ⟨83, .cycle234, .p102⟩, ⟨82, .cycle234, .p102⟩, ⟨98, .cycle234, .p102⟩, ⟨99, .cycle234, .p102⟩, ⟨96, .cycle234, .p102⟩, ⟨97, .cycle234, .p102⟩, ⟨101, .cycle234, .p102⟩, ⟨100, .cycle234, .p102⟩,
    ⟨26, .swap24, .p102⟩, ⟨27, .swap24, .p102⟩, ⟨24, .swap24, .p102⟩, ⟨25, .swap24, .p102⟩, ⟨29, .swap24, .p102⟩, ⟨28, .swap24, .p102⟩, ⟨56, .cycle234, .p102⟩, ⟨57, .cycle234, .p102⟩, ⟨54, .cycle234, .p102⟩, ⟨55, .cycle234, .p102⟩, ⟨59, .cycle234, .p102⟩, ⟨58, .cycle234, .p102⟩,
    ⟨116, .swap23, .p102⟩, ⟨117, .swap23, .p102⟩, ⟨114, .swap23, .p102⟩, ⟨115, .swap23, .p102⟩, ⟨119, .swap23, .p102⟩, ⟨118, .swap23, .p102⟩, ⟨110, .swap23, .p102⟩, ⟨111, .swap23, .p102⟩, ⟨108, .swap23, .p102⟩, ⟨109, .swap23, .p102⟩, ⟨113, .swap23, .p102⟩, ⟨112, .swap23, .p102⟩,
    ⟨170, .cycle234, .p102⟩, ⟨171, .cycle234, .p102⟩, ⟨168, .cycle234, .p102⟩, ⟨169, .cycle234, .p102⟩, ⟨173, .cycle234, .p102⟩, ⟨172, .cycle234, .p102⟩, ⟨188, .cycle234, .p102⟩, ⟨189, .cycle234, .p102⟩, ⟨186, .cycle234, .p102⟩, ⟨187, .cycle234, .p102⟩, ⟨191, .cycle234, .p102⟩, ⟨190, .cycle234, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3744) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3744 ≤ case.val)
    (upper : case.val < 3792) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3767 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3775 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3783 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3791 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk78.correct

end Krenn.X5OrbitWitnessChunks.Chunk78
