import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk74

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨122, .swap23, .p102⟩, ⟨123, .swap23, .p102⟩, ⟨120, .swap23, .p102⟩, ⟨121, .swap23, .p102⟩, ⟨125, .swap23, .p102⟩, ⟨124, .swap23, .p102⟩, ⟨116, .cycle234, .p102⟩, ⟨117, .cycle234, .p102⟩, ⟨114, .cycle234, .p102⟩, ⟨115, .cycle234, .p102⟩, ⟨119, .cycle234, .p102⟩, ⟨118, .cycle234, .p102⟩,
    ⟨176, .cycle234, .p102⟩, ⟨177, .cycle234, .p102⟩, ⟨174, .cycle234, .p102⟩, ⟨175, .cycle234, .p102⟩, ⟨179, .cycle234, .p102⟩, ⟨178, .cycle234, .p102⟩, ⟨194, .cycle234, .p102⟩, ⟨195, .cycle234, .p102⟩, ⟨192, .cycle234, .p102⟩, ⟨193, .cycle234, .p102⟩, ⟨197, .cycle234, .p102⟩, ⟨196, .cycle234, .p102⟩,
    ⟨62, .swap24, .p102⟩, ⟨63, .swap24, .p102⟩, ⟨60, .swap24, .p102⟩, ⟨61, .swap24, .p102⟩, ⟨65, .swap24, .p102⟩, ⟨64, .swap24, .p102⟩, ⟨152, .swap24, .p102⟩, ⟨153, .swap24, .p102⟩, ⟨150, .swap24, .p102⟩, ⟨151, .swap24, .p102⟩, ⟨155, .swap24, .p102⟩, ⟨154, .swap24, .p102⟩,
    ⟨212, .swap23, .p102⟩, ⟨213, .swap23, .p102⟩, ⟨210, .swap23, .p102⟩, ⟨211, .swap23, .p102⟩, ⟨215, .swap23, .p102⟩, ⟨214, .swap23, .p102⟩, ⟨206, .cycle234, .p102⟩, ⟨207, .cycle234, .p102⟩, ⟨204, .cycle234, .p102⟩, ⟨205, .cycle234, .p102⟩, ⟨209, .cycle234, .p102⟩, ⟨208, .cycle234, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3552) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3552 ≤ case.val)
    (upper : case.val < 3600) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3552 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3553 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3554 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3555 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3556 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3557 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3558 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3559 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3560 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3561 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3562 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3563 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3564 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3565 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3566 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3567 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3568 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3569 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3570 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3571 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3572 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3573 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3574 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3575 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3576 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3577 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3578 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3579 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3580 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3581 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3582 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3583 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3584 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3585 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3586 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3587 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3588 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3589 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3590 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3591 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3592 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3593 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3594 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3595 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3596 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3597 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3598 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3599 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk74.correct

end Krenn.X5OrbitWitnessChunks.Chunk74
