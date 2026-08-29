import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk157

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨53, .swap23, .p210⟩, ⟨52, .swap23, .p210⟩, ⟨51, .swap23, .p210⟩, ⟨50, .swap23, .p210⟩, ⟨49, .swap23, .p210⟩, ⟨48, .swap23, .p210⟩, ⟨47, .swap23, .p210⟩, ⟨46, .swap23, .p210⟩, ⟨45, .swap23, .p210⟩, ⟨44, .swap23, .p210⟩, ⟨43, .swap23, .p210⟩, ⟨42, .swap23, .p210⟩,
    ⟨41, .swap23, .p210⟩, ⟨40, .swap23, .p210⟩, ⟨39, .swap23, .p210⟩, ⟨38, .swap23, .p210⟩, ⟨37, .swap23, .p210⟩, ⟨36, .swap23, .p210⟩, ⟨11, .swap24, .p210⟩, ⟨10, .swap24, .p210⟩, ⟨9, .swap24, .p210⟩, ⟨8, .swap24, .p210⟩, ⟨7, .swap24, .p210⟩, ⟨6, .swap24, .p210⟩,
    ⟨125, .identity, .p210⟩, ⟨124, .identity, .p210⟩, ⟨123, .identity, .p210⟩, ⟨122, .identity, .p210⟩, ⟨121, .identity, .p210⟩, ⟨120, .identity, .p210⟩, ⟨119, .swap34, .p210⟩, ⟨118, .swap34, .p210⟩, ⟨117, .swap34, .p210⟩, ⟨116, .swap34, .p210⟩, ⟨115, .swap34, .p210⟩, ⟨114, .swap34, .p210⟩,
    ⟨107, .swap34, .p210⟩, ⟨106, .swap34, .p210⟩, ⟨105, .swap34, .p210⟩, ⟨104, .swap34, .p210⟩, ⟨103, .swap34, .p210⟩, ⟨102, .swap34, .p210⟩, ⟨89, .swap34, .p210⟩, ⟨88, .swap34, .p210⟩, ⟨87, .swap34, .p210⟩, ⟨86, .swap34, .p210⟩, ⟨85, .swap34, .p210⟩, ⟨84, .swap34, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7536) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7536 ≤ case.val)
    (upper : case.val < 7584) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7536 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7537 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7538 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7539 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7540 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7541 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7542 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7543 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7544 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7545 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7546 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7547 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7548 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7549 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7550 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7551 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7575 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7583 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk157.correct

end Krenn.X5OrbitWitnessChunks.Chunk157
