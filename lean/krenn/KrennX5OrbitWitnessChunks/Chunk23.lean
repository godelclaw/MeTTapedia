import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk23

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨114, .cycle234, .p012⟩, ⟨115, .cycle234, .p012⟩, ⟨116, .cycle234, .p012⟩, ⟨117, .cycle234, .p012⟩, ⟨118, .cycle234, .p012⟩, ⟨119, .cycle234, .p012⟩, ⟨120, .swap23, .p012⟩, ⟨121, .swap23, .p012⟩, ⟨122, .swap23, .p012⟩, ⟨123, .swap23, .p012⟩, ⟨124, .swap23, .p012⟩, ⟨125, .swap23, .p012⟩,
    ⟨60, .swap24, .p012⟩, ⟨61, .swap24, .p012⟩, ⟨62, .swap24, .p012⟩, ⟨63, .swap24, .p012⟩, ⟨64, .swap24, .p012⟩, ⟨65, .swap24, .p012⟩, ⟨150, .swap24, .p012⟩, ⟨151, .swap24, .p012⟩, ⟨152, .swap24, .p012⟩, ⟨153, .swap24, .p012⟩, ⟨154, .swap24, .p012⟩, ⟨155, .swap24, .p012⟩,
    ⟨174, .cycle234, .p012⟩, ⟨175, .cycle234, .p012⟩, ⟨176, .cycle234, .p012⟩, ⟨177, .cycle234, .p012⟩, ⟨178, .cycle234, .p012⟩, ⟨179, .cycle234, .p012⟩, ⟨192, .cycle234, .p012⟩, ⟨193, .cycle234, .p012⟩, ⟨194, .cycle234, .p012⟩, ⟨195, .cycle234, .p012⟩, ⟨196, .cycle234, .p012⟩, ⟨197, .cycle234, .p012⟩,
    ⟨204, .cycle234, .p012⟩, ⟨205, .cycle234, .p012⟩, ⟨206, .cycle234, .p012⟩, ⟨207, .cycle234, .p012⟩, ⟨208, .cycle234, .p012⟩, ⟨209, .cycle234, .p012⟩, ⟨210, .swap23, .p012⟩, ⟨211, .swap23, .p012⟩, ⟨212, .swap23, .p012⟩, ⟨213, .swap23, .p012⟩, ⟨214, .swap23, .p012⟩, ⟨215, .swap23, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1104) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1104 ≤ case.val)
    (upper : case.val < 1152) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1143 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1151 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk23.correct

end Krenn.X5OrbitWitnessChunks.Chunk23
