import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk8

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨198, .identity, .p012⟩, ⟨199, .identity, .p012⟩, ⟨200, .identity, .p012⟩, ⟨201, .identity, .p012⟩, ⟨202, .identity, .p012⟩, ⟨203, .identity, .p012⟩, ⟨204, .identity, .p012⟩, ⟨205, .identity, .p012⟩, ⟨206, .identity, .p012⟩, ⟨207, .identity, .p012⟩, ⟨208, .identity, .p012⟩, ⟨209, .identity, .p012⟩,
    ⟨60, .cycle243, .p012⟩, ⟨61, .cycle243, .p012⟩, ⟨62, .cycle243, .p012⟩, ⟨63, .cycle243, .p012⟩, ⟨64, .cycle243, .p012⟩, ⟨65, .cycle243, .p012⟩, ⟨150, .swap34, .p012⟩, ⟨151, .swap34, .p012⟩, ⟨152, .swap34, .p012⟩, ⟨153, .swap34, .p012⟩, ⟨154, .swap34, .p012⟩, ⟨155, .swap34, .p012⟩,
    ⟨174, .swap34, .p012⟩, ⟨175, .swap34, .p012⟩, ⟨176, .swap34, .p012⟩, ⟨177, .swap34, .p012⟩, ⟨178, .swap34, .p012⟩, ⟨179, .swap34, .p012⟩, ⟨192, .swap34, .p012⟩, ⟨193, .swap34, .p012⟩, ⟨194, .swap34, .p012⟩, ⟨195, .swap34, .p012⟩, ⟨196, .swap34, .p012⟩, ⟨197, .swap34, .p012⟩,
    ⟨204, .swap34, .p012⟩, ⟨205, .swap34, .p012⟩, ⟨206, .swap34, .p012⟩, ⟨207, .swap34, .p012⟩, ⟨208, .swap34, .p012⟩, ⟨209, .swap34, .p012⟩, ⟨210, .identity, .p012⟩, ⟨211, .identity, .p012⟩, ⟨212, .identity, .p012⟩, ⟨213, .identity, .p012⟩, ⟨214, .identity, .p012⟩, ⟨215, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 384) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 384 ≤ case.val)
    (upper : case.val < 432) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (384 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (385 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (386 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (387 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (388 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (389 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (390 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (391 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (392 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (393 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (394 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (395 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (396 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (397 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (398 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (399 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (400 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (401 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (402 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (403 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (404 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (405 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (406 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (407 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (408 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (409 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (410 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (411 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (412 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (413 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (414 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (415 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (416 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (417 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (418 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (419 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (420 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (421 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (422 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (423 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (424 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (425 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (426 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (427 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (428 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (429 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (430 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (431 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk8.correct

end Krenn.X5OrbitWitnessChunks.Chunk8
