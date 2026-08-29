import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk125

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨27, .swap24, .p120⟩, ⟨26, .swap24, .p120⟩, ⟨29, .swap24, .p120⟩, ⟨28, .swap24, .p120⟩, ⟨24, .swap24, .p120⟩, ⟨25, .swap24, .p120⟩, ⟨57, .cycle234, .p120⟩, ⟨56, .cycle234, .p120⟩, ⟨59, .cycle234, .p120⟩, ⟨58, .cycle234, .p120⟩, ⟨54, .cycle234, .p120⟩, ⟨55, .cycle234, .p120⟩,
    ⟨189, .cycle234, .p120⟩, ⟨188, .cycle234, .p120⟩, ⟨191, .cycle234, .p120⟩, ⟨190, .cycle234, .p120⟩, ⟨186, .cycle234, .p120⟩, ⟨187, .cycle234, .p120⟩, ⟨171, .cycle234, .p120⟩, ⟨170, .cycle234, .p120⟩, ⟨173, .cycle234, .p120⟩, ⟨172, .cycle234, .p120⟩, ⟨168, .cycle234, .p120⟩, ⟨169, .cycle234, .p120⟩,
    ⟨207, .swap23, .p120⟩, ⟨206, .swap23, .p120⟩, ⟨209, .swap23, .p120⟩, ⟨208, .swap23, .p120⟩, ⟨204, .swap23, .p120⟩, ⟨205, .swap23, .p120⟩, ⟨201, .swap23, .p120⟩, ⟨200, .swap23, .p120⟩, ⟨203, .swap23, .p120⟩, ⟨202, .swap23, .p120⟩, ⟨198, .swap23, .p120⟩, ⟨199, .swap23, .p120⟩,
    ⟨57, .swap24, .p120⟩, ⟨56, .swap24, .p120⟩, ⟨59, .swap24, .p120⟩, ⟨58, .swap24, .p120⟩, ⟨54, .swap24, .p120⟩, ⟨55, .swap24, .p120⟩, ⟨147, .swap24, .p120⟩, ⟨146, .swap24, .p120⟩, ⟨149, .swap24, .p120⟩, ⟨148, .swap24, .p120⟩, ⟨144, .swap24, .p120⟩, ⟨145, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6000) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6000 ≤ case.val)
    (upper : case.val < 6048) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6007 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6015 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6023 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6031 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6039 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6047 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk125.correct

end Krenn.X5OrbitWitnessChunks.Chunk125
