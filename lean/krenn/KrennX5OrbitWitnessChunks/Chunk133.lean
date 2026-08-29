import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk133

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨207, .identity, .p120⟩, ⟨206, .identity, .p120⟩, ⟨209, .identity, .p120⟩, ⟨208, .identity, .p120⟩, ⟨204, .identity, .p120⟩, ⟨205, .identity, .p120⟩, ⟨201, .identity, .p120⟩, ⟨200, .identity, .p120⟩, ⟨203, .identity, .p120⟩, ⟨202, .identity, .p120⟩, ⟨198, .identity, .p120⟩, ⟨199, .identity, .p120⟩,
    ⟨57, .cycle243, .p120⟩, ⟨56, .cycle243, .p120⟩, ⟨59, .cycle243, .p120⟩, ⟨58, .cycle243, .p120⟩, ⟨54, .cycle243, .p120⟩, ⟨55, .cycle243, .p120⟩, ⟨147, .swap34, .p120⟩, ⟨146, .swap34, .p120⟩, ⟨149, .swap34, .p120⟩, ⟨148, .swap34, .p120⟩, ⟨144, .swap34, .p120⟩, ⟨145, .swap34, .p120⟩,
    ⟨51, .swap23, .p120⟩, ⟨50, .swap23, .p120⟩, ⟨53, .swap23, .p120⟩, ⟨52, .swap23, .p120⟩, ⟨48, .swap23, .p120⟩, ⟨49, .swap23, .p120⟩, ⟨45, .swap23, .p120⟩, ⟨44, .swap23, .p120⟩, ⟨47, .swap23, .p120⟩, ⟨46, .swap23, .p120⟩, ⟨42, .swap23, .p120⟩, ⟨43, .swap23, .p120⟩,
    ⟨63, .swap23, .p120⟩, ⟨62, .swap23, .p120⟩, ⟨65, .swap23, .p120⟩, ⟨64, .swap23, .p120⟩, ⟨60, .swap23, .p120⟩, ⟨61, .swap23, .p120⟩, ⟨57, .swap23, .p120⟩, ⟨56, .swap23, .p120⟩, ⟨59, .swap23, .p120⟩, ⟨58, .swap23, .p120⟩, ⟨54, .swap23, .p120⟩, ⟨55, .swap23, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6384) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6384 ≤ case.val)
    (upper : case.val < 6432) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6391 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6431 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk133.correct

end Krenn.X5OrbitWitnessChunks.Chunk133
