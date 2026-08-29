import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk104

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨250, .swap34, .p201⟩, ⟨251, .swap34, .p201⟩, ⟨247, .swap34, .p201⟩, ⟨246, .swap34, .p201⟩, ⟨249, .swap34, .p201⟩, ⟨248, .swap34, .p201⟩, ⟨232, .swap34, .p201⟩, ⟨233, .swap34, .p201⟩, ⟨229, .swap34, .p201⟩, ⟨228, .swap34, .p201⟩, ⟨231, .swap34, .p201⟩, ⟨230, .swap34, .p201⟩,
    ⟨268, .swap34, .p201⟩, ⟨269, .swap34, .p201⟩, ⟨265, .swap34, .p201⟩, ⟨264, .swap34, .p201⟩, ⟨267, .swap34, .p201⟩, ⟨266, .swap34, .p201⟩, ⟨274, .identity, .p201⟩, ⟨275, .identity, .p201⟩, ⟨271, .identity, .p201⟩, ⟨270, .identity, .p201⟩, ⟨273, .identity, .p201⟩, ⟨272, .identity, .p201⟩,
    ⟨178, .cycle243, .p201⟩, ⟨179, .cycle243, .p201⟩, ⟨175, .cycle243, .p201⟩, ⟨174, .cycle243, .p201⟩, ⟨177, .cycle243, .p201⟩, ⟨176, .cycle243, .p201⟩, ⟨88, .cycle243, .p201⟩, ⟨89, .cycle243, .p201⟩, ⟨85, .cycle243, .p201⟩, ⟨84, .cycle243, .p201⟩, ⟨87, .cycle243, .p201⟩, ⟨86, .cycle243, .p201⟩,
    ⟨256, .swap34, .p201⟩, ⟨257, .swap34, .p201⟩, ⟨253, .swap34, .p201⟩, ⟨252, .swap34, .p201⟩, ⟨255, .swap34, .p201⟩, ⟨254, .swap34, .p201⟩, ⟨238, .swap34, .p201⟩, ⟨239, .swap34, .p201⟩, ⟨235, .swap34, .p201⟩, ⟨234, .swap34, .p201⟩, ⟨237, .swap34, .p201⟩, ⟨236, .swap34, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4992) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4992 ≤ case.val)
    (upper : case.val < 5040) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4999 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5007 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5015 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5023 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5031 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5039 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk104.correct

end Krenn.X5OrbitWitnessChunks.Chunk104
