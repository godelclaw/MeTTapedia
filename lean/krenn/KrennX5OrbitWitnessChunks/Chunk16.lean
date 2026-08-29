import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk16

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨240, .swap24, .p012⟩, ⟨241, .swap24, .p012⟩, ⟨242, .swap24, .p012⟩, ⟨243, .swap24, .p012⟩, ⟨244, .swap24, .p012⟩, ⟨245, .swap24, .p012⟩, ⟨276, .identity, .p012⟩, ⟨277, .identity, .p012⟩, ⟨278, .identity, .p012⟩, ⟨279, .identity, .p012⟩, ⟨280, .identity, .p012⟩, ⟨281, .identity, .p012⟩,
    ⟨282, .identity, .p012⟩, ⟨283, .identity, .p012⟩, ⟨284, .identity, .p012⟩, ⟨285, .identity, .p012⟩, ⟨286, .identity, .p012⟩, ⟨287, .identity, .p012⟩, ⟨288, .identity, .p012⟩, ⟨289, .identity, .p012⟩, ⟨290, .identity, .p012⟩, ⟨291, .identity, .p012⟩, ⟨292, .identity, .p012⟩, ⟨293, .identity, .p012⟩,
    ⟨96, .cycle243, .p012⟩, ⟨97, .cycle243, .p012⟩, ⟨98, .cycle243, .p012⟩, ⟨99, .cycle243, .p012⟩, ⟨100, .cycle243, .p012⟩, ⟨101, .cycle243, .p012⟩, ⟨186, .cycle243, .p012⟩, ⟨187, .cycle243, .p012⟩, ⟨188, .cycle243, .p012⟩, ⟨189, .cycle243, .p012⟩, ⟨190, .cycle243, .p012⟩, ⟨191, .cycle243, .p012⟩,
    ⟨246, .cycle243, .p012⟩, ⟨247, .cycle243, .p012⟩, ⟨248, .cycle243, .p012⟩, ⟨249, .cycle243, .p012⟩, ⟨250, .cycle243, .p012⟩, ⟨251, .cycle243, .p012⟩, ⟨282, .swap34, .p012⟩, ⟨283, .swap34, .p012⟩, ⟨284, .swap34, .p012⟩, ⟨285, .swap34, .p012⟩, ⟨286, .swap34, .p012⟩, ⟨287, .swap34, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 768) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 768 ≤ case.val)
    (upper : case.val < 816) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (775 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (783 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (791 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (799 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (807 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (815 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk16.correct

end Krenn.X5OrbitWitnessChunks.Chunk16
