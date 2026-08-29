import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk25

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨252, .swap24, .p012⟩, ⟨253, .swap24, .p012⟩, ⟨254, .swap24, .p012⟩, ⟨255, .swap24, .p012⟩, ⟨256, .swap24, .p012⟩, ⟨257, .swap24, .p012⟩, ⟨288, .swap24, .p012⟩, ⟨289, .swap24, .p012⟩, ⟨290, .swap24, .p012⟩, ⟨291, .swap24, .p012⟩, ⟨292, .swap24, .p012⟩, ⟨293, .swap24, .p012⟩,
    ⟨300, .cycle234, .p012⟩, ⟨301, .cycle234, .p012⟩, ⟨302, .cycle234, .p012⟩, ⟨303, .cycle234, .p012⟩, ⟨304, .cycle234, .p012⟩, ⟨305, .cycle234, .p012⟩, ⟨306, .swap23, .p012⟩, ⟨307, .swap23, .p012⟩, ⟨308, .swap23, .p012⟩, ⟨309, .swap23, .p012⟩, ⟨310, .swap23, .p012⟩, ⟨311, .swap23, .p012⟩,
    ⟨114, .swap24, .p012⟩, ⟨115, .swap24, .p012⟩, ⟨116, .swap24, .p012⟩, ⟨117, .swap24, .p012⟩, ⟨118, .swap24, .p012⟩, ⟨119, .swap24, .p012⟩, ⟨204, .swap24, .p012⟩, ⟨205, .swap24, .p012⟩, ⟨206, .swap24, .p012⟩, ⟨207, .swap24, .p012⟩, ⟨208, .swap24, .p012⟩, ⟨209, .swap24, .p012⟩,
    ⟨264, .swap24, .p012⟩, ⟨265, .swap24, .p012⟩, ⟨266, .swap24, .p012⟩, ⟨267, .swap24, .p012⟩, ⟨268, .swap24, .p012⟩, ⟨269, .swap24, .p012⟩, ⟨300, .swap24, .p012⟩, ⟨301, .swap24, .p012⟩, ⟨302, .swap24, .p012⟩, ⟨303, .swap24, .p012⟩, ⟨304, .swap24, .p012⟩, ⟨305, .swap24, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1200) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1200 ≤ case.val)
    (upper : case.val < 1248) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1239 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1247 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk25.correct

end Krenn.X5OrbitWitnessChunks.Chunk25
