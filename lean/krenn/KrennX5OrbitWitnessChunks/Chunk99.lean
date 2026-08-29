import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk99

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨298, .identity, .p201⟩, ⟨299, .identity, .p201⟩, ⟨295, .identity, .p201⟩, ⟨294, .identity, .p201⟩, ⟨297, .identity, .p201⟩, ⟨296, .identity, .p201⟩, ⟨304, .identity, .p201⟩, ⟨305, .identity, .p201⟩, ⟨301, .identity, .p201⟩, ⟨300, .identity, .p201⟩, ⟨303, .identity, .p201⟩, ⟨302, .identity, .p201⟩,
    ⟨190, .cycle243, .p201⟩, ⟨191, .cycle243, .p201⟩, ⟨187, .cycle243, .p201⟩, ⟨186, .cycle243, .p201⟩, ⟨189, .cycle243, .p201⟩, ⟨188, .cycle243, .p201⟩, ⟨100, .cycle243, .p201⟩, ⟨101, .cycle243, .p201⟩, ⟨97, .cycle243, .p201⟩, ⟨96, .cycle243, .p201⟩, ⟨99, .cycle243, .p201⟩, ⟨98, .cycle243, .p201⟩,
    ⟨286, .swap34, .p201⟩, ⟨287, .swap34, .p201⟩, ⟨283, .swap34, .p201⟩, ⟨282, .swap34, .p201⟩, ⟨285, .swap34, .p201⟩, ⟨284, .swap34, .p201⟩, ⟨250, .cycle243, .p201⟩, ⟨251, .cycle243, .p201⟩, ⟨247, .cycle243, .p201⟩, ⟨246, .cycle243, .p201⟩, ⟨249, .cycle243, .p201⟩, ⟨248, .cycle243, .p201⟩,
    ⟨304, .swap34, .p201⟩, ⟨305, .swap34, .p201⟩, ⟨301, .swap34, .p201⟩, ⟨300, .swap34, .p201⟩, ⟨303, .swap34, .p201⟩, ⟨302, .swap34, .p201⟩, ⟨310, .identity, .p201⟩, ⟨311, .identity, .p201⟩, ⟨307, .identity, .p201⟩, ⟨306, .identity, .p201⟩, ⟨309, .identity, .p201⟩, ⟨308, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4752) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4752 ≤ case.val)
    (upper : case.val < 4800) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4767 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4775 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4783 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4791 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4799 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk99.correct

end Krenn.X5OrbitWitnessChunks.Chunk99
