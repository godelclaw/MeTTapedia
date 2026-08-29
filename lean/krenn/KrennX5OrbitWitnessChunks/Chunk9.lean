import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk9

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨12, .swap24, .p012⟩, ⟨13, .swap24, .p012⟩, ⟨14, .swap24, .p012⟩, ⟨15, .swap24, .p012⟩, ⟨16, .swap24, .p012⟩, ⟨17, .swap24, .p012⟩, ⟨42, .cycle234, .p012⟩, ⟨43, .cycle234, .p012⟩, ⟨44, .cycle234, .p012⟩, ⟨45, .cycle234, .p012⟩, ⟨46, .cycle234, .p012⟩, ⟨47, .cycle234, .p012⟩,
    ⟨66, .swap23, .p012⟩, ⟨67, .swap23, .p012⟩, ⟨68, .swap23, .p012⟩, ⟨69, .swap23, .p012⟩, ⟨70, .swap23, .p012⟩, ⟨71, .swap23, .p012⟩, ⟨72, .swap23, .p012⟩, ⟨73, .swap23, .p012⟩, ⟨74, .swap23, .p012⟩, ⟨75, .swap23, .p012⟩, ⟨76, .swap23, .p012⟩, ⟨77, .swap23, .p012⟩,
    ⟨78, .swap23, .p012⟩, ⟨79, .swap23, .p012⟩, ⟨80, .swap23, .p012⟩, ⟨81, .swap23, .p012⟩, ⟨82, .swap23, .p012⟩, ⟨83, .swap23, .p012⟩, ⟨84, .swap23, .p012⟩, ⟨85, .swap23, .p012⟩, ⟨86, .swap23, .p012⟩, ⟨87, .swap23, .p012⟩, ⟨88, .swap23, .p012⟩, ⟨89, .swap23, .p012⟩,
    ⟨42, .swap24, .p012⟩, ⟨43, .swap24, .p012⟩, ⟨44, .swap24, .p012⟩, ⟨45, .swap24, .p012⟩, ⟨46, .swap24, .p012⟩, ⟨47, .swap24, .p012⟩, ⟨132, .swap24, .p012⟩, ⟨133, .swap24, .p012⟩, ⟨134, .swap24, .p012⟩, ⟨135, .swap24, .p012⟩, ⟨136, .swap24, .p012⟩, ⟨137, .swap24, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 432) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 432 ≤ case.val)
    (upper : case.val < 480) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (432 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (433 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (434 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (435 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (436 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (437 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (438 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (439 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (440 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (441 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (442 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (443 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (444 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (445 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (446 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (447 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (448 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (449 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (450 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (451 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (452 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (453 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (454 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (455 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (456 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (457 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (458 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (459 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (460 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (461 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (462 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (463 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (464 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (465 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (466 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (467 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (468 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (469 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (470 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (471 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (479 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk9.correct

end Krenn.X5OrbitWitnessChunks.Chunk9
