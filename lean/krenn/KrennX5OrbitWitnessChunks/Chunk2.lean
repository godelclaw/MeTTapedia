import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk2

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨78, .identity, .p012⟩, ⟨79, .identity, .p012⟩, ⟨80, .identity, .p012⟩, ⟨81, .identity, .p012⟩, ⟨82, .identity, .p012⟩, ⟨83, .identity, .p012⟩, ⟨84, .identity, .p012⟩, ⟨85, .identity, .p012⟩, ⟨86, .identity, .p012⟩, ⟨87, .identity, .p012⟩, ⟨88, .identity, .p012⟩, ⟨89, .identity, .p012⟩,
    ⟨18, .swap34, .p012⟩, ⟨19, .swap34, .p012⟩, ⟨20, .swap34, .p012⟩, ⟨21, .swap34, .p012⟩, ⟨22, .swap34, .p012⟩, ⟨23, .swap34, .p012⟩, ⟨48, .swap34, .p012⟩, ⟨49, .swap34, .p012⟩, ⟨50, .swap34, .p012⟩, ⟨51, .swap34, .p012⟩, ⟨52, .swap34, .p012⟩, ⟨53, .swap34, .p012⟩,
    ⟨72, .swap34, .p012⟩, ⟨73, .swap34, .p012⟩, ⟨74, .swap34, .p012⟩, ⟨75, .swap34, .p012⟩, ⟨76, .swap34, .p012⟩, ⟨77, .swap34, .p012⟩, ⟨90, .identity, .p012⟩, ⟨91, .identity, .p012⟩, ⟨92, .identity, .p012⟩, ⟨93, .identity, .p012⟩, ⟨94, .identity, .p012⟩, ⟨95, .identity, .p012⟩,
    ⟨96, .identity, .p012⟩, ⟨97, .identity, .p012⟩, ⟨98, .identity, .p012⟩, ⟨99, .identity, .p012⟩, ⟨100, .identity, .p012⟩, ⟨101, .identity, .p012⟩, ⟨102, .identity, .p012⟩, ⟨103, .identity, .p012⟩, ⟨104, .identity, .p012⟩, ⟨105, .identity, .p012⟩, ⟨106, .identity, .p012⟩, ⟨107, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 96) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 96 ≤ case.val)
    (upper : case.val < 144) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (96 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (97 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (98 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (99 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (103 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (143 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk2.correct

end Krenn.X5OrbitWitnessChunks.Chunk2
