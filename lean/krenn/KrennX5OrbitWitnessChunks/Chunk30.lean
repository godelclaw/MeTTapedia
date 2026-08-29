import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk30

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨133, .swap34, .p021⟩, ⟨132, .swap34, .p021⟩, ⟨136, .swap34, .p021⟩, ⟨137, .swap34, .p021⟩, ⟨134, .swap34, .p021⟩, ⟨135, .swap34, .p021⟩, ⟨43, .cycle243, .p021⟩, ⟨42, .cycle243, .p021⟩, ⟨46, .cycle243, .p021⟩, ⟨47, .cycle243, .p021⟩, ⟨44, .cycle243, .p021⟩, ⟨45, .cycle243, .p021⟩,
    ⟨169, .identity, .p021⟩, ⟨168, .identity, .p021⟩, ⟨172, .identity, .p021⟩, ⟨173, .identity, .p021⟩, ⟨170, .identity, .p021⟩, ⟨171, .identity, .p021⟩, ⟨175, .identity, .p021⟩, ⟨174, .identity, .p021⟩, ⟨178, .identity, .p021⟩, ⟨179, .identity, .p021⟩, ⟨176, .identity, .p021⟩, ⟨177, .identity, .p021⟩,
    ⟨157, .identity, .p021⟩, ⟨156, .identity, .p021⟩, ⟨160, .identity, .p021⟩, ⟨161, .identity, .p021⟩, ⟨158, .identity, .p021⟩, ⟨159, .identity, .p021⟩, ⟨163, .identity, .p021⟩, ⟨162, .identity, .p021⟩, ⟨166, .identity, .p021⟩, ⟨167, .identity, .p021⟩, ⟨164, .identity, .p021⟩, ⟨165, .identity, .p021⟩,
    ⟨139, .swap34, .p021⟩, ⟨138, .swap34, .p021⟩, ⟨142, .swap34, .p021⟩, ⟨143, .swap34, .p021⟩, ⟨140, .swap34, .p021⟩, ⟨141, .swap34, .p021⟩, ⟨49, .cycle243, .p021⟩, ⟨48, .cycle243, .p021⟩, ⟨52, .cycle243, .p021⟩, ⟨53, .cycle243, .p021⟩, ⟨50, .cycle243, .p021⟩, ⟨51, .cycle243, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1440) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1440 ≤ case.val)
    (upper : case.val < 1488) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1479 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1487 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk30.correct

end Krenn.X5OrbitWitnessChunks.Chunk30
