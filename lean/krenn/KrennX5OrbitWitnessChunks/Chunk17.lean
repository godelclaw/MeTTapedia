import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk17

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨294, .identity, .p012⟩, ⟨295, .identity, .p012⟩, ⟨296, .identity, .p012⟩, ⟨297, .identity, .p012⟩, ⟨298, .identity, .p012⟩, ⟨299, .identity, .p012⟩, ⟨300, .identity, .p012⟩, ⟨301, .identity, .p012⟩, ⟨302, .identity, .p012⟩, ⟨303, .identity, .p012⟩, ⟨304, .identity, .p012⟩, ⟨305, .identity, .p012⟩,
    ⟨102, .cycle243, .p012⟩, ⟨103, .cycle243, .p012⟩, ⟨104, .cycle243, .p012⟩, ⟨105, .cycle243, .p012⟩, ⟨106, .cycle243, .p012⟩, ⟨107, .cycle243, .p012⟩, ⟨192, .cycle243, .p012⟩, ⟨193, .cycle243, .p012⟩, ⟨194, .cycle243, .p012⟩, ⟨195, .cycle243, .p012⟩, ⟨196, .cycle243, .p012⟩, ⟨197, .cycle243, .p012⟩,
    ⟨252, .cycle243, .p012⟩, ⟨253, .cycle243, .p012⟩, ⟨254, .cycle243, .p012⟩, ⟨255, .cycle243, .p012⟩, ⟨256, .cycle243, .p012⟩, ⟨257, .cycle243, .p012⟩, ⟨288, .swap34, .p012⟩, ⟨289, .swap34, .p012⟩, ⟨290, .swap34, .p012⟩, ⟨291, .swap34, .p012⟩, ⟨292, .swap34, .p012⟩, ⟨293, .swap34, .p012⟩,
    ⟨300, .swap34, .p012⟩, ⟨301, .swap34, .p012⟩, ⟨302, .swap34, .p012⟩, ⟨303, .swap34, .p012⟩, ⟨304, .swap34, .p012⟩, ⟨305, .swap34, .p012⟩, ⟨306, .identity, .p012⟩, ⟨307, .identity, .p012⟩, ⟨308, .identity, .p012⟩, ⟨309, .identity, .p012⟩, ⟨310, .identity, .p012⟩, ⟨311, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 816) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 816 ≤ case.val)
    (upper : case.val < 864) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (823 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (831 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (839 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (847 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (855 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (863 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk17.correct

end Krenn.X5OrbitWitnessChunks.Chunk17
