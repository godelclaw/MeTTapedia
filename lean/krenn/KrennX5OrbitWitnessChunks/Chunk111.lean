import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk111

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨93, .swap23, .p120⟩, ⟨92, .swap23, .p120⟩, ⟨95, .swap23, .p120⟩, ⟨94, .swap23, .p120⟩, ⟨90, .swap23, .p120⟩, ⟨91, .swap23, .p120⟩, ⟨75, .cycle234, .p120⟩, ⟨74, .cycle234, .p120⟩, ⟨77, .cycle234, .p120⟩, ⟨76, .cycle234, .p120⟩, ⟨72, .cycle234, .p120⟩, ⟨73, .cycle234, .p120⟩,
    ⟨105, .swap23, .p120⟩, ⟨104, .swap23, .p120⟩, ⟨107, .swap23, .p120⟩, ⟨106, .swap23, .p120⟩, ⟨102, .swap23, .p120⟩, ⟨103, .swap23, .p120⟩, ⟨99, .swap23, .p120⟩, ⟨98, .swap23, .p120⟩, ⟨101, .swap23, .p120⟩, ⟨100, .swap23, .p120⟩, ⟨96, .swap23, .p120⟩, ⟨97, .swap23, .p120⟩,
    ⟨21, .swap24, .p120⟩, ⟨20, .swap24, .p120⟩, ⟨23, .swap24, .p120⟩, ⟨22, .swap24, .p120⟩, ⟨18, .swap24, .p120⟩, ⟨19, .swap24, .p120⟩, ⟨51, .cycle234, .p120⟩, ⟨50, .cycle234, .p120⟩, ⟨53, .cycle234, .p120⟩, ⟨52, .cycle234, .p120⟩, ⟨48, .cycle234, .p120⟩, ⟨49, .cycle234, .p120⟩,
    ⟨183, .swap23, .p120⟩, ⟨182, .swap23, .p120⟩, ⟨185, .swap23, .p120⟩, ⟨184, .swap23, .p120⟩, ⟨180, .swap23, .p120⟩, ⟨181, .swap23, .p120⟩, ⟨165, .cycle234, .p120⟩, ⟨164, .cycle234, .p120⟩, ⟨167, .cycle234, .p120⟩, ⟨166, .cycle234, .p120⟩, ⟨162, .cycle234, .p120⟩, ⟨163, .cycle234, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5328) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5328 ≤ case.val)
    (upper : case.val < 5376) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5335 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5343 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5375 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk111.correct

end Krenn.X5OrbitWitnessChunks.Chunk111
