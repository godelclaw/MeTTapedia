import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk31

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨187, .identity, .p021⟩, ⟨186, .identity, .p021⟩, ⟨190, .identity, .p021⟩, ⟨191, .identity, .p021⟩, ⟨188, .identity, .p021⟩, ⟨189, .identity, .p021⟩, ⟨193, .identity, .p021⟩, ⟨192, .identity, .p021⟩, ⟨196, .identity, .p021⟩, ⟨197, .identity, .p021⟩, ⟨194, .identity, .p021⟩, ⟨195, .identity, .p021⟩,
    ⟨163, .swap34, .p021⟩, ⟨162, .swap34, .p021⟩, ⟨166, .swap34, .p021⟩, ⟨167, .swap34, .p021⟩, ⟨164, .swap34, .p021⟩, ⟨165, .swap34, .p021⟩, ⟨181, .identity, .p021⟩, ⟨180, .identity, .p021⟩, ⟨184, .identity, .p021⟩, ⟨185, .identity, .p021⟩, ⟨182, .identity, .p021⟩, ⟨183, .identity, .p021⟩,
    ⟨37, .identity, .p021⟩, ⟨36, .identity, .p021⟩, ⟨40, .identity, .p021⟩, ⟨41, .identity, .p021⟩, ⟨38, .identity, .p021⟩, ⟨39, .identity, .p021⟩, ⟨7, .swap34, .p021⟩, ⟨6, .swap34, .p021⟩, ⟨10, .swap34, .p021⟩, ⟨11, .swap34, .p021⟩, ⟨8, .swap34, .p021⟩, ⟨9, .swap34, .p021⟩,
    ⟨55, .identity, .p021⟩, ⟨54, .identity, .p021⟩, ⟨58, .identity, .p021⟩, ⟨59, .identity, .p021⟩, ⟨56, .identity, .p021⟩, ⟨57, .identity, .p021⟩, ⟨61, .identity, .p021⟩, ⟨60, .identity, .p021⟩, ⟨64, .identity, .p021⟩, ⟨65, .identity, .p021⟩, ⟨62, .identity, .p021⟩, ⟨63, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1488) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1488 ≤ case.val)
    (upper : case.val < 1536) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1519 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1520 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1521 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1522 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1523 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1524 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1525 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1526 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1527 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1528 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1529 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1530 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1531 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1532 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1533 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1534 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1535 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk31.correct

end Krenn.X5OrbitWitnessChunks.Chunk31
