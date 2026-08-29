import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk24

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨84, .swap24, .p012⟩, ⟨85, .swap24, .p012⟩, ⟨86, .swap24, .p012⟩, ⟨87, .swap24, .p012⟩, ⟨88, .swap24, .p012⟩, ⟨89, .swap24, .p012⟩, ⟨174, .swap24, .p012⟩, ⟨175, .swap24, .p012⟩, ⟨176, .swap24, .p012⟩, ⟨177, .swap24, .p012⟩, ⟨178, .swap24, .p012⟩, ⟨179, .swap24, .p012⟩,
    ⟨234, .swap24, .p012⟩, ⟨235, .swap24, .p012⟩, ⟨236, .swap24, .p012⟩, ⟨237, .swap24, .p012⟩, ⟨238, .swap24, .p012⟩, ⟨239, .swap24, .p012⟩, ⟨252, .cycle234, .p012⟩, ⟨253, .cycle234, .p012⟩, ⟨254, .cycle234, .p012⟩, ⟨255, .cycle234, .p012⟩, ⟨256, .cycle234, .p012⟩, ⟨257, .cycle234, .p012⟩,
    ⟨264, .cycle234, .p012⟩, ⟨265, .cycle234, .p012⟩, ⟨266, .cycle234, .p012⟩, ⟨267, .cycle234, .p012⟩, ⟨268, .cycle234, .p012⟩, ⟨269, .cycle234, .p012⟩, ⟨270, .swap23, .p012⟩, ⟨271, .swap23, .p012⟩, ⟨272, .swap23, .p012⟩, ⟨273, .swap23, .p012⟩, ⟨274, .swap23, .p012⟩, ⟨275, .swap23, .p012⟩,
    ⟨102, .swap24, .p012⟩, ⟨103, .swap24, .p012⟩, ⟨104, .swap24, .p012⟩, ⟨105, .swap24, .p012⟩, ⟨106, .swap24, .p012⟩, ⟨107, .swap24, .p012⟩, ⟨192, .swap24, .p012⟩, ⟨193, .swap24, .p012⟩, ⟨194, .swap24, .p012⟩, ⟨195, .swap24, .p012⟩, ⟨196, .swap24, .p012⟩, ⟨197, .swap24, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1152) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1152 ≤ case.val)
    (upper : case.val < 1200) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1191 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1199 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk24.correct

end Krenn.X5OrbitWitnessChunks.Chunk24
