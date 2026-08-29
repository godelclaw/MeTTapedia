import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk83

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨190, .cycle234, .p201⟩, ⟨191, .cycle234, .p201⟩, ⟨187, .cycle234, .p201⟩, ⟨186, .cycle234, .p201⟩, ⟨189, .cycle234, .p201⟩, ⟨188, .cycle234, .p201⟩, ⟨172, .cycle234, .p201⟩, ⟨173, .cycle234, .p201⟩, ⟨169, .cycle234, .p201⟩, ⟨168, .cycle234, .p201⟩, ⟨171, .cycle234, .p201⟩, ⟨170, .cycle234, .p201⟩,
    ⟨112, .swap23, .p201⟩, ⟨113, .swap23, .p201⟩, ⟨109, .swap23, .p201⟩, ⟨108, .swap23, .p201⟩, ⟨111, .swap23, .p201⟩, ⟨110, .swap23, .p201⟩, ⟨118, .swap23, .p201⟩, ⟨119, .swap23, .p201⟩, ⟨115, .swap23, .p201⟩, ⟨114, .swap23, .p201⟩, ⟨117, .swap23, .p201⟩, ⟨116, .swap23, .p201⟩,
    ⟨58, .cycle234, .p201⟩, ⟨59, .cycle234, .p201⟩, ⟨55, .cycle234, .p201⟩, ⟨54, .cycle234, .p201⟩, ⟨57, .cycle234, .p201⟩, ⟨56, .cycle234, .p201⟩, ⟨28, .swap24, .p201⟩, ⟨29, .swap24, .p201⟩, ⟨25, .swap24, .p201⟩, ⟨24, .swap24, .p201⟩, ⟨27, .swap24, .p201⟩, ⟨26, .swap24, .p201⟩,
    ⟨100, .cycle234, .p201⟩, ⟨101, .cycle234, .p201⟩, ⟨97, .cycle234, .p201⟩, ⟨96, .cycle234, .p201⟩, ⟨99, .cycle234, .p201⟩, ⟨98, .cycle234, .p201⟩, ⟨82, .cycle234, .p201⟩, ⟨83, .cycle234, .p201⟩, ⟨79, .cycle234, .p201⟩, ⟨78, .cycle234, .p201⟩, ⟨81, .cycle234, .p201⟩, ⟨80, .cycle234, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3984) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3984 ≤ case.val)
    (upper : case.val < 4032) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3991 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3999 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4007 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4015 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4023 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4031 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk83.correct

end Krenn.X5OrbitWitnessChunks.Chunk83
