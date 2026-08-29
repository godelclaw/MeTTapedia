import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk32

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨43, .identity, .p021⟩, ⟨42, .identity, .p021⟩, ⟨46, .identity, .p021⟩, ⟨47, .identity, .p021⟩, ⟨44, .identity, .p021⟩, ⟨45, .identity, .p021⟩, ⟨49, .identity, .p021⟩, ⟨48, .identity, .p021⟩, ⟨52, .identity, .p021⟩, ⟨53, .identity, .p021⟩, ⟨50, .identity, .p021⟩, ⟨51, .identity, .p021⟩,
    ⟨7, .identity, .p021⟩, ⟨6, .identity, .p021⟩, ⟨10, .identity, .p021⟩, ⟨11, .identity, .p021⟩, ⟨8, .identity, .p021⟩, ⟨9, .identity, .p021⟩, ⟨1, .identity, .p021⟩, ⟨0, .identity, .p021⟩, ⟨4, .identity, .p021⟩, ⟨5, .identity, .p021⟩, ⟨2, .identity, .p021⟩, ⟨3, .identity, .p021⟩,
    ⟨25, .identity, .p021⟩, ⟨24, .identity, .p021⟩, ⟨28, .identity, .p021⟩, ⟨29, .identity, .p021⟩, ⟨26, .identity, .p021⟩, ⟨27, .identity, .p021⟩, ⟨31, .identity, .p021⟩, ⟨30, .identity, .p021⟩, ⟨34, .identity, .p021⟩, ⟨35, .identity, .p021⟩, ⟨32, .identity, .p021⟩, ⟨33, .identity, .p021⟩,
    ⟨13, .identity, .p021⟩, ⟨12, .identity, .p021⟩, ⟨16, .identity, .p021⟩, ⟨17, .identity, .p021⟩, ⟨14, .identity, .p021⟩, ⟨15, .identity, .p021⟩, ⟨19, .identity, .p021⟩, ⟨18, .identity, .p021⟩, ⟨22, .identity, .p021⟩, ⟨23, .identity, .p021⟩, ⟨20, .identity, .p021⟩, ⟨21, .identity, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1536) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1536 ≤ case.val)
    (upper : case.val < 1584) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1575 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1583 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk32.correct

end Krenn.X5OrbitWitnessChunks.Chunk32
