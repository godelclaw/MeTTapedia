import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk27

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨127, .identity, .p021⟩, ⟨126, .identity, .p021⟩, ⟨130, .identity, .p021⟩, ⟨131, .identity, .p021⟩, ⟨128, .identity, .p021⟩, ⟨129, .identity, .p021⟩, ⟨37, .swap24, .p021⟩, ⟨36, .swap24, .p021⟩, ⟨40, .swap24, .p021⟩, ⟨41, .swap24, .p021⟩, ⟨38, .swap24, .p021⟩, ⟨39, .swap24, .p021⟩,
    ⟨145, .identity, .p021⟩, ⟨144, .identity, .p021⟩, ⟨148, .identity, .p021⟩, ⟨149, .identity, .p021⟩, ⟨146, .identity, .p021⟩, ⟨147, .identity, .p021⟩, ⟨151, .identity, .p021⟩, ⟨150, .identity, .p021⟩, ⟨154, .identity, .p021⟩, ⟨155, .identity, .p021⟩, ⟨152, .identity, .p021⟩, ⟨153, .identity, .p021⟩,
    ⟨133, .identity, .p021⟩, ⟨132, .identity, .p021⟩, ⟨136, .identity, .p021⟩, ⟨137, .identity, .p021⟩, ⟨134, .identity, .p021⟩, ⟨135, .identity, .p021⟩, ⟨139, .identity, .p021⟩, ⟨138, .identity, .p021⟩, ⟨142, .identity, .p021⟩, ⟨143, .identity, .p021⟩, ⟨140, .identity, .p021⟩, ⟨141, .identity, .p021⟩,
    ⟨37, .swap23, .p021⟩, ⟨36, .swap23, .p021⟩, ⟨40, .swap23, .p021⟩, ⟨41, .swap23, .p021⟩, ⟨38, .swap23, .p021⟩, ⟨39, .swap23, .p021⟩, ⟨7, .swap24, .p021⟩, ⟨6, .swap24, .p021⟩, ⟨10, .swap24, .p021⟩, ⟨11, .swap24, .p021⟩, ⟨8, .swap24, .p021⟩, ⟨9, .swap24, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1296) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1296 ≤ case.val)
    (upper : case.val < 1344) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1335 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1343 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk27.correct

end Krenn.X5OrbitWitnessChunks.Chunk27
