import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk4

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨84, .swap34, .p012⟩, ⟨85, .swap34, .p012⟩, ⟨86, .swap34, .p012⟩, ⟨87, .swap34, .p012⟩, ⟨88, .swap34, .p012⟩, ⟨89, .swap34, .p012⟩, ⟨102, .swap34, .p012⟩, ⟨103, .swap34, .p012⟩, ⟨104, .swap34, .p012⟩, ⟨105, .swap34, .p012⟩, ⟨106, .swap34, .p012⟩, ⟨107, .swap34, .p012⟩,
    ⟨114, .swap34, .p012⟩, ⟨115, .swap34, .p012⟩, ⟨116, .swap34, .p012⟩, ⟨117, .swap34, .p012⟩, ⟨118, .swap34, .p012⟩, ⟨119, .swap34, .p012⟩, ⟨120, .identity, .p012⟩, ⟨121, .identity, .p012⟩, ⟨122, .identity, .p012⟩, ⟨123, .identity, .p012⟩, ⟨124, .identity, .p012⟩, ⟨125, .identity, .p012⟩,
    ⟨6, .swap24, .p012⟩, ⟨7, .swap24, .p012⟩, ⟨8, .swap24, .p012⟩, ⟨9, .swap24, .p012⟩, ⟨10, .swap24, .p012⟩, ⟨11, .swap24, .p012⟩, ⟨36, .swap23, .p012⟩, ⟨37, .swap23, .p012⟩, ⟨38, .swap23, .p012⟩, ⟨39, .swap23, .p012⟩, ⟨40, .swap23, .p012⟩, ⟨41, .swap23, .p012⟩,
    ⟨42, .swap23, .p012⟩, ⟨43, .swap23, .p012⟩, ⟨44, .swap23, .p012⟩, ⟨45, .swap23, .p012⟩, ⟨46, .swap23, .p012⟩, ⟨47, .swap23, .p012⟩, ⟨48, .swap23, .p012⟩, ⟨49, .swap23, .p012⟩, ⟨50, .swap23, .p012⟩, ⟨51, .swap23, .p012⟩, ⟨52, .swap23, .p012⟩, ⟨53, .swap23, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 192) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 192 ≤ case.val)
    (upper : case.val < 240) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (199 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (239 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk4.correct

end Krenn.X5OrbitWitnessChunks.Chunk4
