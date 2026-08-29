import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk29

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨169, .swap34, .p021⟩, ⟨168, .swap34, .p021⟩, ⟨172, .swap34, .p021⟩, ⟨173, .swap34, .p021⟩, ⟨170, .swap34, .p021⟩, ⟨171, .swap34, .p021⟩, ⟨187, .swap34, .p021⟩, ⟨186, .swap34, .p021⟩, ⟨190, .swap34, .p021⟩, ⟨191, .swap34, .p021⟩, ⟨188, .swap34, .p021⟩, ⟨189, .swap34, .p021⟩,
    ⟨151, .swap34, .p021⟩, ⟨150, .swap34, .p021⟩, ⟨154, .swap34, .p021⟩, ⟨155, .swap34, .p021⟩, ⟨152, .swap34, .p021⟩, ⟨153, .swap34, .p021⟩, ⟨61, .cycle243, .p021⟩, ⟨60, .cycle243, .p021⟩, ⟨64, .cycle243, .p021⟩, ⟨65, .cycle243, .p021⟩, ⟨62, .cycle243, .p021⟩, ⟨63, .cycle243, .p021⟩,
    ⟨205, .swap34, .p021⟩, ⟨204, .swap34, .p021⟩, ⟨208, .swap34, .p021⟩, ⟨209, .swap34, .p021⟩, ⟨206, .swap34, .p021⟩, ⟨207, .swap34, .p021⟩, ⟨211, .identity, .p021⟩, ⟨210, .identity, .p021⟩, ⟨214, .identity, .p021⟩, ⟨215, .identity, .p021⟩, ⟨212, .identity, .p021⟩, ⟨213, .identity, .p021⟩,
    ⟨175, .swap34, .p021⟩, ⟨174, .swap34, .p021⟩, ⟨178, .swap34, .p021⟩, ⟨179, .swap34, .p021⟩, ⟨176, .swap34, .p021⟩, ⟨177, .swap34, .p021⟩, ⟨193, .swap34, .p021⟩, ⟨192, .swap34, .p021⟩, ⟨196, .swap34, .p021⟩, ⟨197, .swap34, .p021⟩, ⟨194, .swap34, .p021⟩, ⟨195, .swap34, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1392) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1392 ≤ case.val)
    (upper : case.val < 1440) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1431 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1439 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk29.correct

end Krenn.X5OrbitWitnessChunks.Chunk29
