import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk1

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨42, .identity, .p012⟩, ⟨43, .identity, .p012⟩, ⟨44, .identity, .p012⟩, ⟨45, .identity, .p012⟩, ⟨46, .identity, .p012⟩, ⟨47, .identity, .p012⟩, ⟨48, .identity, .p012⟩, ⟨49, .identity, .p012⟩, ⟨50, .identity, .p012⟩, ⟨51, .identity, .p012⟩, ⟨52, .identity, .p012⟩, ⟨53, .identity, .p012⟩,
    ⟨54, .identity, .p012⟩, ⟨55, .identity, .p012⟩, ⟨56, .identity, .p012⟩, ⟨57, .identity, .p012⟩, ⟨58, .identity, .p012⟩, ⟨59, .identity, .p012⟩, ⟨60, .identity, .p012⟩, ⟨61, .identity, .p012⟩, ⟨62, .identity, .p012⟩, ⟨63, .identity, .p012⟩, ⟨64, .identity, .p012⟩, ⟨65, .identity, .p012⟩,
    ⟨12, .swap34, .p012⟩, ⟨13, .swap34, .p012⟩, ⟨14, .swap34, .p012⟩, ⟨15, .swap34, .p012⟩, ⟨16, .swap34, .p012⟩, ⟨17, .swap34, .p012⟩, ⟨42, .swap34, .p012⟩, ⟨43, .swap34, .p012⟩, ⟨44, .swap34, .p012⟩, ⟨45, .swap34, .p012⟩, ⟨46, .swap34, .p012⟩, ⟨47, .swap34, .p012⟩,
    ⟨66, .identity, .p012⟩, ⟨67, .identity, .p012⟩, ⟨68, .identity, .p012⟩, ⟨69, .identity, .p012⟩, ⟨70, .identity, .p012⟩, ⟨71, .identity, .p012⟩, ⟨72, .identity, .p012⟩, ⟨73, .identity, .p012⟩, ⟨74, .identity, .p012⟩, ⟨75, .identity, .p012⟩, ⟨76, .identity, .p012⟩, ⟨77, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 48) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 48 ≤ case.val)
    (upper : case.val < 96) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (48 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (49 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (50 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (51 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (52 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (53 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (54 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (55 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (56 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (57 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (58 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (59 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (60 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (61 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (62 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (63 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (64 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (65 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (66 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (67 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (68 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (69 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (70 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (71 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (72 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (73 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (74 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (75 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (76 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (77 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (78 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (79 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (80 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (81 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (82 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (83 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (84 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (85 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (86 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (87 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (88 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (89 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (90 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (91 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (92 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (93 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (94 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (95 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk1.correct

end Krenn.X5OrbitWitnessChunks.Chunk1
