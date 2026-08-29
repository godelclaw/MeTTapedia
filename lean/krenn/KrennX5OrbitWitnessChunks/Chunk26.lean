import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk26

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨318, .swap24, .p012⟩, ⟨319, .swap24, .p012⟩, ⟨320, .swap24, .p012⟩, ⟨321, .swap24, .p012⟩, ⟨322, .swap24, .p012⟩, ⟨323, .swap24, .p012⟩, ⟨324, .swap23, .p012⟩, ⟨325, .swap23, .p012⟩, ⟨326, .swap23, .p012⟩, ⟨327, .swap23, .p012⟩, ⟨328, .swap23, .p012⟩, ⟨329, .swap23, .p012⟩,
    ⟨120, .swap24, .p012⟩, ⟨121, .swap24, .p012⟩, ⟨122, .swap24, .p012⟩, ⟨123, .swap24, .p012⟩, ⟨124, .swap24, .p012⟩, ⟨125, .swap24, .p012⟩, ⟨210, .swap24, .p012⟩, ⟨211, .swap24, .p012⟩, ⟨212, .swap24, .p012⟩, ⟨213, .swap24, .p012⟩, ⟨214, .swap24, .p012⟩, ⟨215, .swap24, .p012⟩,
    ⟨270, .swap24, .p012⟩, ⟨271, .swap24, .p012⟩, ⟨272, .swap24, .p012⟩, ⟨273, .swap24, .p012⟩, ⟨274, .swap24, .p012⟩, ⟨275, .swap24, .p012⟩, ⟨306, .swap24, .p012⟩, ⟨307, .swap24, .p012⟩, ⟨308, .swap24, .p012⟩, ⟨309, .swap24, .p012⟩, ⟨310, .swap24, .p012⟩, ⟨311, .swap24, .p012⟩,
    ⟨324, .swap24, .p012⟩, ⟨325, .swap24, .p012⟩, ⟨326, .swap24, .p012⟩, ⟨327, .swap24, .p012⟩, ⟨328, .swap24, .p012⟩, ⟨329, .swap24, .p012⟩, ⟨330, .identity, .p012⟩, ⟨331, .identity, .p012⟩, ⟨332, .identity, .p012⟩, ⟨333, .identity, .p012⟩, ⟨334, .identity, .p012⟩, ⟨335, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1248) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1248 ≤ case.val)
    (upper : case.val < 1296) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1287 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1295 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk26.correct

end Krenn.X5OrbitWitnessChunks.Chunk26
