import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk0

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨0, .identity, .p012⟩, ⟨1, .identity, .p012⟩, ⟨2, .identity, .p012⟩, ⟨3, .identity, .p012⟩, ⟨4, .identity, .p012⟩, ⟨5, .identity, .p012⟩, ⟨6, .identity, .p012⟩, ⟨7, .identity, .p012⟩, ⟨8, .identity, .p012⟩, ⟨9, .identity, .p012⟩, ⟨10, .identity, .p012⟩, ⟨11, .identity, .p012⟩,
    ⟨12, .identity, .p012⟩, ⟨13, .identity, .p012⟩, ⟨14, .identity, .p012⟩, ⟨15, .identity, .p012⟩, ⟨16, .identity, .p012⟩, ⟨17, .identity, .p012⟩, ⟨18, .identity, .p012⟩, ⟨19, .identity, .p012⟩, ⟨20, .identity, .p012⟩, ⟨21, .identity, .p012⟩, ⟨22, .identity, .p012⟩, ⟨23, .identity, .p012⟩,
    ⟨24, .identity, .p012⟩, ⟨25, .identity, .p012⟩, ⟨26, .identity, .p012⟩, ⟨27, .identity, .p012⟩, ⟨28, .identity, .p012⟩, ⟨29, .identity, .p012⟩, ⟨30, .identity, .p012⟩, ⟨31, .identity, .p012⟩, ⟨32, .identity, .p012⟩, ⟨33, .identity, .p012⟩, ⟨34, .identity, .p012⟩, ⟨35, .identity, .p012⟩,
    ⟨6, .swap34, .p012⟩, ⟨7, .swap34, .p012⟩, ⟨8, .swap34, .p012⟩, ⟨9, .swap34, .p012⟩, ⟨10, .swap34, .p012⟩, ⟨11, .swap34, .p012⟩, ⟨36, .identity, .p012⟩, ⟨37, .identity, .p012⟩, ⟨38, .identity, .p012⟩, ⟨39, .identity, .p012⟩, ⟨40, .identity, .p012⟩, ⟨41, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 0) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 0 ≤ case.val)
    (upper : case.val < 48) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (0 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (8 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (9 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (10 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (11 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (12 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (13 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (14 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (15 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (16 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (17 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (18 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (19 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (20 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (21 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (22 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (23 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (24 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (25 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (26 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (27 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (28 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (29 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (30 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (31 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (32 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (33 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (34 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (35 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (36 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (37 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (38 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (39 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (40 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (41 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (42 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (43 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (44 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (45 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (46 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (47 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk0.correct

end Krenn.X5OrbitWitnessChunks.Chunk0
