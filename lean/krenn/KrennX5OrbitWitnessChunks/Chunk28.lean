import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk28

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨55, .swap23, .p021⟩, ⟨54, .swap23, .p021⟩, ⟨58, .swap23, .p021⟩, ⟨59, .swap23, .p021⟩, ⟨56, .swap23, .p021⟩, ⟨57, .swap23, .p021⟩, ⟨61, .swap23, .p021⟩, ⟨60, .swap23, .p021⟩, ⟨64, .swap23, .p021⟩, ⟨65, .swap23, .p021⟩, ⟨62, .swap23, .p021⟩, ⟨63, .swap23, .p021⟩,
    ⟨43, .swap23, .p021⟩, ⟨42, .swap23, .p021⟩, ⟨46, .swap23, .p021⟩, ⟨47, .swap23, .p021⟩, ⟨44, .swap23, .p021⟩, ⟨45, .swap23, .p021⟩, ⟨49, .swap23, .p021⟩, ⟨48, .swap23, .p021⟩, ⟨52, .swap23, .p021⟩, ⟨53, .swap23, .p021⟩, ⟨50, .swap23, .p021⟩, ⟨51, .swap23, .p021⟩,
    ⟨145, .swap34, .p021⟩, ⟨144, .swap34, .p021⟩, ⟨148, .swap34, .p021⟩, ⟨149, .swap34, .p021⟩, ⟨146, .swap34, .p021⟩, ⟨147, .swap34, .p021⟩, ⟨55, .cycle243, .p021⟩, ⟨54, .cycle243, .p021⟩, ⟨58, .cycle243, .p021⟩, ⟨59, .cycle243, .p021⟩, ⟨56, .cycle243, .p021⟩, ⟨57, .cycle243, .p021⟩,
    ⟨199, .identity, .p021⟩, ⟨198, .identity, .p021⟩, ⟨202, .identity, .p021⟩, ⟨203, .identity, .p021⟩, ⟨200, .identity, .p021⟩, ⟨201, .identity, .p021⟩, ⟨205, .identity, .p021⟩, ⟨204, .identity, .p021⟩, ⟨208, .identity, .p021⟩, ⟨209, .identity, .p021⟩, ⟨206, .identity, .p021⟩, ⟨207, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1344) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1344 ≤ case.val)
    (upper : case.val < 1392) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1383 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1391 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk28.correct

end Krenn.X5OrbitWitnessChunks.Chunk28
