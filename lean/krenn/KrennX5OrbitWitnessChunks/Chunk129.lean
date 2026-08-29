import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk129

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨21, .identity, .p120⟩, ⟨20, .identity, .p120⟩, ⟨23, .identity, .p120⟩, ⟨22, .identity, .p120⟩, ⟨18, .identity, .p120⟩, ⟨19, .identity, .p120⟩, ⟨15, .identity, .p120⟩, ⟨14, .identity, .p120⟩, ⟨17, .identity, .p120⟩, ⟨16, .identity, .p120⟩, ⟨12, .identity, .p120⟩, ⟨13, .identity, .p120⟩,
    ⟨33, .identity, .p120⟩, ⟨32, .identity, .p120⟩, ⟨35, .identity, .p120⟩, ⟨34, .identity, .p120⟩, ⟨30, .identity, .p120⟩, ⟨31, .identity, .p120⟩, ⟨27, .identity, .p120⟩, ⟨26, .identity, .p120⟩, ⟨29, .identity, .p120⟩, ⟨28, .identity, .p120⟩, ⟨24, .identity, .p120⟩, ⟨25, .identity, .p120⟩,
    ⟨3, .identity, .p120⟩, ⟨2, .identity, .p120⟩, ⟨5, .identity, .p120⟩, ⟨4, .identity, .p120⟩, ⟨0, .identity, .p120⟩, ⟨1, .identity, .p120⟩, ⟨9, .identity, .p120⟩, ⟨8, .identity, .p120⟩, ⟨11, .identity, .p120⟩, ⟨10, .identity, .p120⟩, ⟨6, .identity, .p120⟩, ⟨7, .identity, .p120⟩,
    ⟨51, .identity, .p120⟩, ⟨50, .identity, .p120⟩, ⟨53, .identity, .p120⟩, ⟨52, .identity, .p120⟩, ⟨48, .identity, .p120⟩, ⟨49, .identity, .p120⟩, ⟨45, .identity, .p120⟩, ⟨44, .identity, .p120⟩, ⟨47, .identity, .p120⟩, ⟨46, .identity, .p120⟩, ⟨42, .identity, .p120⟩, ⟨43, .identity, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6192) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6192 ≤ case.val)
    (upper : case.val < 6240) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6199 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6239 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk129.correct

end Krenn.X5OrbitWitnessChunks.Chunk129
