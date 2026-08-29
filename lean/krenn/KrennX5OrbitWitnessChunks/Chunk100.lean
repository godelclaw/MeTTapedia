import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk100

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨196, .cycle243, .p201⟩, ⟨197, .cycle243, .p201⟩, ⟨193, .cycle243, .p201⟩, ⟨192, .cycle243, .p201⟩, ⟨195, .cycle243, .p201⟩, ⟨194, .cycle243, .p201⟩, ⟨106, .cycle243, .p201⟩, ⟨107, .cycle243, .p201⟩, ⟨103, .cycle243, .p201⟩, ⟨102, .cycle243, .p201⟩, ⟨105, .cycle243, .p201⟩, ⟨104, .cycle243, .p201⟩,
    ⟨292, .swap34, .p201⟩, ⟨293, .swap34, .p201⟩, ⟨289, .swap34, .p201⟩, ⟨288, .swap34, .p201⟩, ⟨291, .swap34, .p201⟩, ⟨290, .swap34, .p201⟩, ⟨256, .cycle243, .p201⟩, ⟨257, .cycle243, .p201⟩, ⟨253, .cycle243, .p201⟩, ⟨252, .cycle243, .p201⟩, ⟨255, .cycle243, .p201⟩, ⟨254, .cycle243, .p201⟩,
    ⟨190, .swap23, .p201⟩, ⟨191, .swap23, .p201⟩, ⟨187, .swap23, .p201⟩, ⟨186, .swap23, .p201⟩, ⟨189, .swap23, .p201⟩, ⟨188, .swap23, .p201⟩, ⟨196, .swap23, .p201⟩, ⟨197, .swap23, .p201⟩, ⟨193, .swap23, .p201⟩, ⟨192, .swap23, .p201⟩, ⟨195, .swap23, .p201⟩, ⟨194, .swap23, .p201⟩,
    ⟨142, .swap24, .p201⟩, ⟨143, .swap24, .p201⟩, ⟨139, .swap24, .p201⟩, ⟨138, .swap24, .p201⟩, ⟨141, .swap24, .p201⟩, ⟨140, .swap24, .p201⟩, ⟨52, .swap24, .p201⟩, ⟨53, .swap24, .p201⟩, ⟨49, .swap24, .p201⟩, ⟨48, .swap24, .p201⟩, ⟨51, .swap24, .p201⟩, ⟨50, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4800) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4800 ≤ case.val)
    (upper : case.val < 4848) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4807 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4815 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4823 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4831 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4839 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4847 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk100.correct

end Krenn.X5OrbitWitnessChunks.Chunk100
