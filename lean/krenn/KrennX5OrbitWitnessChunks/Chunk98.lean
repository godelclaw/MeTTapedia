import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk98

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨94, .identity, .p201⟩, ⟨95, .identity, .p201⟩, ⟨91, .identity, .p201⟩, ⟨90, .identity, .p201⟩, ⟨93, .identity, .p201⟩, ⟨92, .identity, .p201⟩, ⟨76, .swap34, .p201⟩, ⟨77, .swap34, .p201⟩, ⟨73, .swap34, .p201⟩, ⟨72, .swap34, .p201⟩, ⟨75, .swap34, .p201⟩, ⟨74, .swap34, .p201⟩,
    ⟨82, .identity, .p201⟩, ⟨83, .identity, .p201⟩, ⟨79, .identity, .p201⟩, ⟨78, .identity, .p201⟩, ⟨81, .identity, .p201⟩, ⟨80, .identity, .p201⟩, ⟨88, .identity, .p201⟩, ⟨89, .identity, .p201⟩, ⟨85, .identity, .p201⟩, ⟨84, .identity, .p201⟩, ⟨87, .identity, .p201⟩, ⟨86, .identity, .p201⟩,
    ⟨46, .swap34, .p201⟩, ⟨47, .swap34, .p201⟩, ⟨43, .swap34, .p201⟩, ⟨42, .swap34, .p201⟩, ⟨45, .swap34, .p201⟩, ⟨44, .swap34, .p201⟩, ⟨16, .swap34, .p201⟩, ⟨17, .swap34, .p201⟩, ⟨13, .swap34, .p201⟩, ⟨12, .swap34, .p201⟩, ⟨15, .swap34, .p201⟩, ⟨14, .swap34, .p201⟩,
    ⟨76, .identity, .p201⟩, ⟨77, .identity, .p201⟩, ⟨73, .identity, .p201⟩, ⟨72, .identity, .p201⟩, ⟨75, .identity, .p201⟩, ⟨74, .identity, .p201⟩, ⟨70, .identity, .p201⟩, ⟨71, .identity, .p201⟩, ⟨67, .identity, .p201⟩, ⟨66, .identity, .p201⟩, ⟨69, .identity, .p201⟩, ⟨68, .identity, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4704) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4704 ≤ case.val)
    (upper : case.val < 4752) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4719 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4727 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4751 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk98.correct

end Krenn.X5OrbitWitnessChunks.Chunk98
