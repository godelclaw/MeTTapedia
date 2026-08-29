import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk160

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨77, .identity, .p210⟩, ⟨76, .identity, .p210⟩, ⟨75, .identity, .p210⟩, ⟨74, .identity, .p210⟩, ⟨73, .identity, .p210⟩, ⟨72, .identity, .p210⟩, ⟨71, .identity, .p210⟩, ⟨70, .identity, .p210⟩, ⟨69, .identity, .p210⟩, ⟨68, .identity, .p210⟩, ⟨67, .identity, .p210⟩, ⟨66, .identity, .p210⟩,
    ⟨47, .swap34, .p210⟩, ⟨46, .swap34, .p210⟩, ⟨45, .swap34, .p210⟩, ⟨44, .swap34, .p210⟩, ⟨43, .swap34, .p210⟩, ⟨42, .swap34, .p210⟩, ⟨17, .swap34, .p210⟩, ⟨16, .swap34, .p210⟩, ⟨15, .swap34, .p210⟩, ⟨14, .swap34, .p210⟩, ⟨13, .swap34, .p210⟩, ⟨12, .swap34, .p210⟩,
    ⟨65, .identity, .p210⟩, ⟨64, .identity, .p210⟩, ⟨63, .identity, .p210⟩, ⟨62, .identity, .p210⟩, ⟨61, .identity, .p210⟩, ⟨60, .identity, .p210⟩, ⟨59, .identity, .p210⟩, ⟨58, .identity, .p210⟩, ⟨57, .identity, .p210⟩, ⟨56, .identity, .p210⟩, ⟨55, .identity, .p210⟩, ⟨54, .identity, .p210⟩,
    ⟨53, .identity, .p210⟩, ⟨52, .identity, .p210⟩, ⟨51, .identity, .p210⟩, ⟨50, .identity, .p210⟩, ⟨49, .identity, .p210⟩, ⟨48, .identity, .p210⟩, ⟨47, .identity, .p210⟩, ⟨46, .identity, .p210⟩, ⟨45, .identity, .p210⟩, ⟨44, .identity, .p210⟩, ⟨43, .identity, .p210⟩, ⟨42, .identity, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7680) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7680 ≤ case.val)
    (upper : case.val < 7728) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7680 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7681 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7682 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7683 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7684 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7685 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7686 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7687 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7719 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7727 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk160.correct

end Krenn.X5OrbitWitnessChunks.Chunk160
