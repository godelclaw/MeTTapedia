import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk121

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨213, .swap23, .p120⟩, ⟨212, .swap23, .p120⟩, ⟨215, .swap23, .p120⟩, ⟨214, .swap23, .p120⟩, ⟨210, .swap23, .p120⟩, ⟨211, .swap23, .p120⟩, ⟨207, .cycle234, .p120⟩, ⟨206, .cycle234, .p120⟩, ⟨209, .cycle234, .p120⟩, ⟨208, .cycle234, .p120⟩, ⟨204, .cycle234, .p120⟩, ⟨205, .cycle234, .p120⟩,
    ⟨63, .swap24, .p120⟩, ⟨62, .swap24, .p120⟩, ⟨65, .swap24, .p120⟩, ⟨64, .swap24, .p120⟩, ⟨60, .swap24, .p120⟩, ⟨61, .swap24, .p120⟩, ⟨153, .swap24, .p120⟩, ⟨152, .swap24, .p120⟩, ⟨155, .swap24, .p120⟩, ⟨154, .swap24, .p120⟩, ⟨150, .swap24, .p120⟩, ⟨151, .swap24, .p120⟩,
    ⟨285, .swap24, .p120⟩, ⟨284, .swap24, .p120⟩, ⟨287, .swap24, .p120⟩, ⟨286, .swap24, .p120⟩, ⟨282, .swap24, .p120⟩, ⟨283, .swap24, .p120⟩, ⟨249, .swap24, .p120⟩, ⟨248, .swap24, .p120⟩, ⟨251, .swap24, .p120⟩, ⟨250, .swap24, .p120⟩, ⟨246, .swap24, .p120⟩, ⟨247, .swap24, .p120⟩,
    ⟨303, .swap23, .p120⟩, ⟨302, .swap23, .p120⟩, ⟨305, .swap23, .p120⟩, ⟨304, .swap23, .p120⟩, ⟨300, .swap23, .p120⟩, ⟨301, .swap23, .p120⟩, ⟨297, .swap23, .p120⟩, ⟨296, .swap23, .p120⟩, ⟨299, .swap23, .p120⟩, ⟨298, .swap23, .p120⟩, ⟨294, .swap23, .p120⟩, ⟨295, .swap23, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5808) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5808 ≤ case.val)
    (upper : case.val < 5856) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5815 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5823 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5831 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5839 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5847 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5855 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk121.correct

end Krenn.X5OrbitWitnessChunks.Chunk121
