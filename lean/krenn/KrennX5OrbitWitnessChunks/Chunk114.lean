import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk114

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨255, .swap34, .p120⟩, ⟨254, .swap34, .p120⟩, ⟨257, .swap34, .p120⟩, ⟨256, .swap34, .p120⟩, ⟨252, .swap34, .p120⟩, ⟨253, .swap34, .p120⟩, ⟨237, .swap34, .p120⟩, ⟨236, .swap34, .p120⟩, ⟨239, .swap34, .p120⟩, ⟨238, .swap34, .p120⟩, ⟨234, .swap34, .p120⟩, ⟨235, .swap34, .p120⟩,
    ⟨273, .identity, .p120⟩, ⟨272, .identity, .p120⟩, ⟨275, .identity, .p120⟩, ⟨274, .identity, .p120⟩, ⟨270, .identity, .p120⟩, ⟨271, .identity, .p120⟩, ⟨267, .swap34, .p120⟩, ⟨266, .swap34, .p120⟩, ⟨269, .swap34, .p120⟩, ⟨268, .swap34, .p120⟩, ⟨264, .swap34, .p120⟩, ⟨265, .swap34, .p120⟩,
    ⟨87, .cycle243, .p120⟩, ⟨86, .cycle243, .p120⟩, ⟨89, .cycle243, .p120⟩, ⟨88, .cycle243, .p120⟩, ⟨84, .cycle243, .p120⟩, ⟨85, .cycle243, .p120⟩, ⟨177, .cycle243, .p120⟩, ⟨176, .cycle243, .p120⟩, ⟨179, .cycle243, .p120⟩, ⟨178, .cycle243, .p120⟩, ⟨174, .cycle243, .p120⟩, ⟨175, .cycle243, .p120⟩,
    ⟨249, .swap34, .p120⟩, ⟨248, .swap34, .p120⟩, ⟨251, .swap34, .p120⟩, ⟨250, .swap34, .p120⟩, ⟨246, .swap34, .p120⟩, ⟨247, .swap34, .p120⟩, ⟨231, .swap34, .p120⟩, ⟨230, .swap34, .p120⟩, ⟨233, .swap34, .p120⟩, ⟨232, .swap34, .p120⟩, ⟨228, .swap34, .p120⟩, ⟨229, .swap34, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5472) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5472 ≤ case.val)
    (upper : case.val < 5520) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5472 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5473 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5474 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5475 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5476 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5477 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5478 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5479 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5480 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5481 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5482 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5483 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5484 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5485 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5486 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5487 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5488 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5489 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5490 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5491 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5492 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5493 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5494 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5495 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5496 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5497 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5498 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5499 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5500 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5501 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5502 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5503 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5504 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5505 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5506 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5507 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5508 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5509 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5510 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5511 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5512 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5513 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5514 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5515 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5516 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5517 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5518 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5519 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk114.correct

end Krenn.X5OrbitWitnessChunks.Chunk114
