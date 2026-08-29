import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk22

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨264, .cycle243, .p012⟩, ⟨265, .cycle243, .p012⟩, ⟨266, .cycle243, .p012⟩, ⟨267, .cycle243, .p012⟩, ⟨268, .cycle243, .p012⟩, ⟨269, .cycle243, .p012⟩, ⟨300, .cycle243, .p012⟩, ⟨301, .cycle243, .p012⟩, ⟨302, .cycle243, .p012⟩, ⟨303, .cycle243, .p012⟩, ⟨304, .cycle243, .p012⟩, ⟨305, .cycle243, .p012⟩,
    ⟨318, .swap34, .p012⟩, ⟨319, .swap34, .p012⟩, ⟨320, .swap34, .p012⟩, ⟨321, .swap34, .p012⟩, ⟨322, .swap34, .p012⟩, ⟨323, .swap34, .p012⟩, ⟨324, .identity, .p012⟩, ⟨325, .identity, .p012⟩, ⟨326, .identity, .p012⟩, ⟨327, .identity, .p012⟩, ⟨328, .identity, .p012⟩, ⟨329, .identity, .p012⟩,
    ⟨30, .swap24, .p012⟩, ⟨31, .swap24, .p012⟩, ⟨32, .swap24, .p012⟩, ⟨33, .swap24, .p012⟩, ⟨34, .swap24, .p012⟩, ⟨35, .swap24, .p012⟩, ⟨60, .cycle234, .p012⟩, ⟨61, .cycle234, .p012⟩, ⟨62, .cycle234, .p012⟩, ⟨63, .cycle234, .p012⟩, ⟨64, .cycle234, .p012⟩, ⟨65, .cycle234, .p012⟩,
    ⟨84, .cycle234, .p012⟩, ⟨85, .cycle234, .p012⟩, ⟨86, .cycle234, .p012⟩, ⟨87, .cycle234, .p012⟩, ⟨88, .cycle234, .p012⟩, ⟨89, .cycle234, .p012⟩, ⟨102, .cycle234, .p012⟩, ⟨103, .cycle234, .p012⟩, ⟨104, .cycle234, .p012⟩, ⟨105, .cycle234, .p012⟩, ⟨106, .cycle234, .p012⟩, ⟨107, .cycle234, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1056) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1056 ≤ case.val)
    (upper : case.val < 1104) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1063 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1071 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1079 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1087 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1095 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1103 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk22.correct

end Krenn.X5OrbitWitnessChunks.Chunk22
