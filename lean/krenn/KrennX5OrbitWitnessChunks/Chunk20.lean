import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk20

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨258, .swap23, .p012⟩, ⟨259, .swap23, .p012⟩, ⟨260, .swap23, .p012⟩, ⟨261, .swap23, .p012⟩, ⟨262, .swap23, .p012⟩, ⟨263, .swap23, .p012⟩, ⟨264, .swap23, .p012⟩, ⟨265, .swap23, .p012⟩, ⟨266, .swap23, .p012⟩, ⟨267, .swap23, .p012⟩, ⟨268, .swap23, .p012⟩, ⟨269, .swap23, .p012⟩,
    ⟨96, .swap24, .p012⟩, ⟨97, .swap24, .p012⟩, ⟨98, .swap24, .p012⟩, ⟨99, .swap24, .p012⟩, ⟨100, .swap24, .p012⟩, ⟨101, .swap24, .p012⟩, ⟨186, .swap24, .p012⟩, ⟨187, .swap24, .p012⟩, ⟨188, .swap24, .p012⟩, ⟨189, .swap24, .p012⟩, ⟨190, .swap24, .p012⟩, ⟨191, .swap24, .p012⟩,
    ⟨246, .swap24, .p012⟩, ⟨247, .swap24, .p012⟩, ⟨248, .swap24, .p012⟩, ⟨249, .swap24, .p012⟩, ⟨250, .swap24, .p012⟩, ⟨251, .swap24, .p012⟩, ⟨282, .swap24, .p012⟩, ⟨283, .swap24, .p012⟩, ⟨284, .swap24, .p012⟩, ⟨285, .swap24, .p012⟩, ⟨286, .swap24, .p012⟩, ⟨287, .swap24, .p012⟩,
    ⟨294, .swap23, .p012⟩, ⟨295, .swap23, .p012⟩, ⟨296, .swap23, .p012⟩, ⟨297, .swap23, .p012⟩, ⟨298, .swap23, .p012⟩, ⟨299, .swap23, .p012⟩, ⟨300, .swap23, .p012⟩, ⟨301, .swap23, .p012⟩, ⟨302, .swap23, .p012⟩, ⟨303, .swap23, .p012⟩, ⟨304, .swap23, .p012⟩, ⟨305, .swap23, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 960) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 960 ≤ case.val)
    (upper : case.val < 1008) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (967 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (975 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (983 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (991 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (999 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1007 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk20.correct

end Krenn.X5OrbitWitnessChunks.Chunk20
