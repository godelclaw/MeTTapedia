import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk132

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨195, .swap34, .p120⟩, ⟨194, .swap34, .p120⟩, ⟨197, .swap34, .p120⟩, ⟨196, .swap34, .p120⟩, ⟨192, .swap34, .p120⟩, ⟨193, .swap34, .p120⟩, ⟨177, .swap34, .p120⟩, ⟨176, .swap34, .p120⟩, ⟨179, .swap34, .p120⟩, ⟨178, .swap34, .p120⟩, ⟨174, .swap34, .p120⟩, ⟨175, .swap34, .p120⟩,
    ⟨213, .identity, .p120⟩, ⟨212, .identity, .p120⟩, ⟨215, .identity, .p120⟩, ⟨214, .identity, .p120⟩, ⟨210, .identity, .p120⟩, ⟨211, .identity, .p120⟩, ⟨207, .swap34, .p120⟩, ⟨206, .swap34, .p120⟩, ⟨209, .swap34, .p120⟩, ⟨208, .swap34, .p120⟩, ⟨204, .swap34, .p120⟩, ⟨205, .swap34, .p120⟩,
    ⟨63, .cycle243, .p120⟩, ⟨62, .cycle243, .p120⟩, ⟨65, .cycle243, .p120⟩, ⟨64, .cycle243, .p120⟩, ⟨60, .cycle243, .p120⟩, ⟨61, .cycle243, .p120⟩, ⟨153, .swap34, .p120⟩, ⟨152, .swap34, .p120⟩, ⟨155, .swap34, .p120⟩, ⟨154, .swap34, .p120⟩, ⟨150, .swap34, .p120⟩, ⟨151, .swap34, .p120⟩,
    ⟨189, .swap34, .p120⟩, ⟨188, .swap34, .p120⟩, ⟨191, .swap34, .p120⟩, ⟨190, .swap34, .p120⟩, ⟨186, .swap34, .p120⟩, ⟨187, .swap34, .p120⟩, ⟨171, .swap34, .p120⟩, ⟨170, .swap34, .p120⟩, ⟨173, .swap34, .p120⟩, ⟨172, .swap34, .p120⟩, ⟨168, .swap34, .p120⟩, ⟨169, .swap34, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6336) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6336 ≤ case.val)
    (upper : case.val < 6384) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6343 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6359 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6360 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6361 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6362 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6363 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6364 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6365 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6366 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6367 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6368 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6369 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6370 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6371 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6372 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6373 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6374 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6375 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6383 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk132.correct

end Krenn.X5OrbitWitnessChunks.Chunk132
