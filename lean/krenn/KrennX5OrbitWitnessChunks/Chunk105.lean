import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk105

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨172, .swap23, .p201⟩, ⟨173, .swap23, .p201⟩, ⟨169, .swap23, .p201⟩, ⟨168, .swap23, .p201⟩, ⟨171, .swap23, .p201⟩, ⟨170, .swap23, .p201⟩, ⟨178, .swap23, .p201⟩, ⟨179, .swap23, .p201⟩, ⟨175, .swap23, .p201⟩, ⟨174, .swap23, .p201⟩, ⟨177, .swap23, .p201⟩, ⟨176, .swap23, .p201⟩,
    ⟨136, .swap24, .p201⟩, ⟨137, .swap24, .p201⟩, ⟨133, .swap24, .p201⟩, ⟨132, .swap24, .p201⟩, ⟨135, .swap24, .p201⟩, ⟨134, .swap24, .p201⟩, ⟨46, .swap24, .p201⟩, ⟨47, .swap24, .p201⟩, ⟨43, .swap24, .p201⟩, ⟨42, .swap24, .p201⟩, ⟨45, .swap24, .p201⟩, ⟨44, .swap24, .p201⟩,
    ⟨166, .swap23, .p201⟩, ⟨167, .swap23, .p201⟩, ⟨163, .swap23, .p201⟩, ⟨162, .swap23, .p201⟩, ⟨165, .swap23, .p201⟩, ⟨164, .swap23, .p201⟩, ⟨160, .swap23, .p201⟩, ⟨161, .swap23, .p201⟩, ⟨157, .swap23, .p201⟩, ⟨156, .swap23, .p201⟩, ⟨159, .swap23, .p201⟩, ⟨158, .swap23, .p201⟩,
    ⟨82, .swap23, .p201⟩, ⟨83, .swap23, .p201⟩, ⟨79, .swap23, .p201⟩, ⟨78, .swap23, .p201⟩, ⟨81, .swap23, .p201⟩, ⟨80, .swap23, .p201⟩, ⟨88, .swap23, .p201⟩, ⟨89, .swap23, .p201⟩, ⟨85, .swap23, .p201⟩, ⟨84, .swap23, .p201⟩, ⟨87, .swap23, .p201⟩, ⟨86, .swap23, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5040) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5040 ≤ case.val)
    (upper : case.val < 5088) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5047 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5055 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5063 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5071 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5079 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5087 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk105.correct

end Krenn.X5OrbitWitnessChunks.Chunk105
