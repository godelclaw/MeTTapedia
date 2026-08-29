import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk106

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨46, .cycle234, .p201⟩, ⟨47, .cycle234, .p201⟩, ⟨43, .cycle234, .p201⟩, ⟨42, .cycle234, .p201⟩, ⟨45, .cycle234, .p201⟩, ⟨44, .cycle234, .p201⟩, ⟨16, .swap24, .p201⟩, ⟨17, .swap24, .p201⟩, ⟨13, .swap24, .p201⟩, ⟨12, .swap24, .p201⟩, ⟨15, .swap24, .p201⟩, ⟨14, .swap24, .p201⟩,
    ⟨76, .swap23, .p201⟩, ⟨77, .swap23, .p201⟩, ⟨73, .swap23, .p201⟩, ⟨72, .swap23, .p201⟩, ⟨75, .swap23, .p201⟩, ⟨74, .swap23, .p201⟩, ⟨70, .swap23, .p201⟩, ⟨71, .swap23, .p201⟩, ⟨67, .swap23, .p201⟩, ⟨66, .swap23, .p201⟩, ⟨69, .swap23, .p201⟩, ⟨68, .swap23, .p201⟩,
    ⟨250, .identity, .p201⟩, ⟨251, .identity, .p201⟩, ⟨247, .identity, .p201⟩, ⟨246, .identity, .p201⟩, ⟨249, .identity, .p201⟩, ⟨248, .identity, .p201⟩, ⟨256, .identity, .p201⟩, ⟨257, .identity, .p201⟩, ⟨253, .identity, .p201⟩, ⟨252, .identity, .p201⟩, ⟨255, .identity, .p201⟩, ⟨254, .identity, .p201⟩,
    ⟨166, .cycle243, .p201⟩, ⟨167, .cycle243, .p201⟩, ⟨163, .cycle243, .p201⟩, ⟨162, .cycle243, .p201⟩, ⟨165, .cycle243, .p201⟩, ⟨164, .cycle243, .p201⟩, ⟨76, .cycle243, .p201⟩, ⟨77, .cycle243, .p201⟩, ⟨73, .cycle243, .p201⟩, ⟨72, .cycle243, .p201⟩, ⟨75, .cycle243, .p201⟩, ⟨74, .cycle243, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5088) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5088 ≤ case.val)
    (upper : case.val < 5136) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5095 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5103 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5135 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk106.correct

end Krenn.X5OrbitWitnessChunks.Chunk106
