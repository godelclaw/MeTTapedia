import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk3

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨24, .swap34, .p012⟩, ⟨25, .swap34, .p012⟩, ⟨26, .swap34, .p012⟩, ⟨27, .swap34, .p012⟩, ⟨28, .swap34, .p012⟩, ⟨29, .swap34, .p012⟩, ⟨54, .swap34, .p012⟩, ⟨55, .swap34, .p012⟩, ⟨56, .swap34, .p012⟩, ⟨57, .swap34, .p012⟩, ⟨58, .swap34, .p012⟩, ⟨59, .swap34, .p012⟩,
    ⟨78, .swap34, .p012⟩, ⟨79, .swap34, .p012⟩, ⟨80, .swap34, .p012⟩, ⟨81, .swap34, .p012⟩, ⟨82, .swap34, .p012⟩, ⟨83, .swap34, .p012⟩, ⟨96, .swap34, .p012⟩, ⟨97, .swap34, .p012⟩, ⟨98, .swap34, .p012⟩, ⟨99, .swap34, .p012⟩, ⟨100, .swap34, .p012⟩, ⟨101, .swap34, .p012⟩,
    ⟨108, .identity, .p012⟩, ⟨109, .identity, .p012⟩, ⟨110, .identity, .p012⟩, ⟨111, .identity, .p012⟩, ⟨112, .identity, .p012⟩, ⟨113, .identity, .p012⟩, ⟨114, .identity, .p012⟩, ⟨115, .identity, .p012⟩, ⟨116, .identity, .p012⟩, ⟨117, .identity, .p012⟩, ⟨118, .identity, .p012⟩, ⟨119, .identity, .p012⟩,
    ⟨30, .swap34, .p012⟩, ⟨31, .swap34, .p012⟩, ⟨32, .swap34, .p012⟩, ⟨33, .swap34, .p012⟩, ⟨34, .swap34, .p012⟩, ⟨35, .swap34, .p012⟩, ⟨60, .swap34, .p012⟩, ⟨61, .swap34, .p012⟩, ⟨62, .swap34, .p012⟩, ⟨63, .swap34, .p012⟩, ⟨64, .swap34, .p012⟩, ⟨65, .swap34, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 144) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 144 ≤ case.val)
    (upper : case.val < 192) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (151 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (191 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk3.correct

end Krenn.X5OrbitWitnessChunks.Chunk3
