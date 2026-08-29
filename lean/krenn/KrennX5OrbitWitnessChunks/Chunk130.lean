import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk130

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨63, .identity, .p120⟩, ⟨62, .identity, .p120⟩, ⟨65, .identity, .p120⟩, ⟨64, .identity, .p120⟩, ⟨60, .identity, .p120⟩, ⟨61, .identity, .p120⟩, ⟨57, .identity, .p120⟩, ⟨56, .identity, .p120⟩, ⟨59, .identity, .p120⟩, ⟨58, .identity, .p120⟩, ⟨54, .identity, .p120⟩, ⟨55, .identity, .p120⟩,
    ⟨9, .swap34, .p120⟩, ⟨8, .swap34, .p120⟩, ⟨11, .swap34, .p120⟩, ⟨10, .swap34, .p120⟩, ⟨6, .swap34, .p120⟩, ⟨7, .swap34, .p120⟩, ⟨39, .identity, .p120⟩, ⟨38, .identity, .p120⟩, ⟨41, .identity, .p120⟩, ⟨40, .identity, .p120⟩, ⟨36, .identity, .p120⟩, ⟨37, .identity, .p120⟩,
    ⟨183, .identity, .p120⟩, ⟨182, .identity, .p120⟩, ⟨185, .identity, .p120⟩, ⟨184, .identity, .p120⟩, ⟨180, .identity, .p120⟩, ⟨181, .identity, .p120⟩, ⟨165, .swap34, .p120⟩, ⟨164, .swap34, .p120⟩, ⟨167, .swap34, .p120⟩, ⟨166, .swap34, .p120⟩, ⟨162, .swap34, .p120⟩, ⟨163, .swap34, .p120⟩,
    ⟨195, .identity, .p120⟩, ⟨194, .identity, .p120⟩, ⟨197, .identity, .p120⟩, ⟨196, .identity, .p120⟩, ⟨192, .identity, .p120⟩, ⟨193, .identity, .p120⟩, ⟨189, .identity, .p120⟩, ⟨188, .identity, .p120⟩, ⟨191, .identity, .p120⟩, ⟨190, .identity, .p120⟩, ⟨186, .identity, .p120⟩, ⟨187, .identity, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6240) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6240 ≤ case.val)
    (upper : case.val < 6288) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6247 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6287 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk130.correct

end Krenn.X5OrbitWitnessChunks.Chunk130
