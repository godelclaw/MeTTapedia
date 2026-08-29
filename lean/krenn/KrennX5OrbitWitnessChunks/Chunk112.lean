import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk112

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨195, .swap23, .p120⟩, ⟨194, .swap23, .p120⟩, ⟨197, .swap23, .p120⟩, ⟨196, .swap23, .p120⟩, ⟨192, .swap23, .p120⟩, ⟨193, .swap23, .p120⟩, ⟨189, .swap23, .p120⟩, ⟨188, .swap23, .p120⟩, ⟨191, .swap23, .p120⟩, ⟨190, .swap23, .p120⟩, ⟨186, .swap23, .p120⟩, ⟨187, .swap23, .p120⟩,
    ⟨51, .swap24, .p120⟩, ⟨50, .swap24, .p120⟩, ⟨53, .swap24, .p120⟩, ⟨52, .swap24, .p120⟩, ⟨48, .swap24, .p120⟩, ⟨49, .swap24, .p120⟩, ⟨141, .swap24, .p120⟩, ⟨140, .swap24, .p120⟩, ⟨143, .swap24, .p120⟩, ⟨142, .swap24, .p120⟩, ⟨138, .swap24, .p120⟩, ⟨139, .swap24, .p120⟩,
    ⟨243, .identity, .p120⟩, ⟨242, .identity, .p120⟩, ⟨245, .identity, .p120⟩, ⟨244, .identity, .p120⟩, ⟨240, .identity, .p120⟩, ⟨241, .identity, .p120⟩, ⟨225, .swap34, .p120⟩, ⟨224, .swap34, .p120⟩, ⟨227, .swap34, .p120⟩, ⟨226, .swap34, .p120⟩, ⟨222, .swap34, .p120⟩, ⟨223, .swap34, .p120⟩,
    ⟨255, .identity, .p120⟩, ⟨254, .identity, .p120⟩, ⟨257, .identity, .p120⟩, ⟨256, .identity, .p120⟩, ⟨252, .identity, .p120⟩, ⟨253, .identity, .p120⟩, ⟨249, .identity, .p120⟩, ⟨248, .identity, .p120⟩, ⟨251, .identity, .p120⟩, ⟨250, .identity, .p120⟩, ⟨246, .identity, .p120⟩, ⟨247, .identity, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5376) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5376 ≤ case.val)
    (upper : case.val < 5424) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5376 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5377 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5378 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5379 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5380 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5381 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5382 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5383 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5391 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5423 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk112.correct

end Krenn.X5OrbitWitnessChunks.Chunk112
