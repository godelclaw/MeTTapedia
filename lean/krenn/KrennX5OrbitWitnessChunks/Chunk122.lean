import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk122

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨99, .swap24, .p120⟩, ⟨98, .swap24, .p120⟩, ⟨101, .swap24, .p120⟩, ⟨100, .swap24, .p120⟩, ⟨96, .swap24, .p120⟩, ⟨97, .swap24, .p120⟩, ⟨189, .swap24, .p120⟩, ⟨188, .swap24, .p120⟩, ⟨191, .swap24, .p120⟩, ⟨190, .swap24, .p120⟩, ⟨186, .swap24, .p120⟩, ⟨187, .swap24, .p120⟩,
    ⟨249, .cycle234, .p120⟩, ⟨248, .cycle234, .p120⟩, ⟨251, .cycle234, .p120⟩, ⟨250, .cycle234, .p120⟩, ⟨246, .cycle234, .p120⟩, ⟨247, .cycle234, .p120⟩, ⟨231, .swap24, .p120⟩, ⟨230, .swap24, .p120⟩, ⟨233, .swap24, .p120⟩, ⟨232, .swap24, .p120⟩, ⟨228, .swap24, .p120⟩, ⟨229, .swap24, .p120⟩,
    ⟨267, .swap23, .p120⟩, ⟨266, .swap23, .p120⟩, ⟨269, .swap23, .p120⟩, ⟨268, .swap23, .p120⟩, ⟨264, .swap23, .p120⟩, ⟨265, .swap23, .p120⟩, ⟨261, .swap23, .p120⟩, ⟨260, .swap23, .p120⟩, ⟨263, .swap23, .p120⟩, ⟨262, .swap23, .p120⟩, ⟨258, .swap23, .p120⟩, ⟨259, .swap23, .p120⟩,
    ⟨81, .swap24, .p120⟩, ⟨80, .swap24, .p120⟩, ⟨83, .swap24, .p120⟩, ⟨82, .swap24, .p120⟩, ⟨78, .swap24, .p120⟩, ⟨79, .swap24, .p120⟩, ⟨171, .swap24, .p120⟩, ⟨170, .swap24, .p120⟩, ⟨173, .swap24, .p120⟩, ⟨172, .swap24, .p120⟩, ⟨168, .swap24, .p120⟩, ⟨169, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5856) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5856 ≤ case.val)
    (upper : case.val < 5904) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5863 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5871 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5879 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5887 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5895 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5903 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk122.correct

end Krenn.X5OrbitWitnessChunks.Chunk122
