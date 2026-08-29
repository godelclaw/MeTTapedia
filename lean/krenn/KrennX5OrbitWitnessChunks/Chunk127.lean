import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk127

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨87, .identity, .p120⟩, ⟨86, .identity, .p120⟩, ⟨89, .identity, .p120⟩, ⟨88, .identity, .p120⟩, ⟨84, .identity, .p120⟩, ⟨85, .identity, .p120⟩, ⟨81, .identity, .p120⟩, ⟨80, .identity, .p120⟩, ⟨83, .identity, .p120⟩, ⟨82, .identity, .p120⟩, ⟨78, .identity, .p120⟩, ⟨79, .identity, .p120⟩,
    ⟨15, .swap34, .p120⟩, ⟨14, .swap34, .p120⟩, ⟨17, .swap34, .p120⟩, ⟨16, .swap34, .p120⟩, ⟨12, .swap34, .p120⟩, ⟨13, .swap34, .p120⟩, ⟨45, .swap34, .p120⟩, ⟨44, .swap34, .p120⟩, ⟨47, .swap34, .p120⟩, ⟨46, .swap34, .p120⟩, ⟨42, .swap34, .p120⟩, ⟨43, .swap34, .p120⟩,
    ⟨105, .swap34, .p120⟩, ⟨104, .swap34, .p120⟩, ⟨107, .swap34, .p120⟩, ⟨106, .swap34, .p120⟩, ⟨102, .swap34, .p120⟩, ⟨103, .swap34, .p120⟩, ⟨87, .swap34, .p120⟩, ⟨86, .swap34, .p120⟩, ⟨89, .swap34, .p120⟩, ⟨88, .swap34, .p120⟩, ⟨84, .swap34, .p120⟩, ⟨85, .swap34, .p120⟩,
    ⟨123, .identity, .p120⟩, ⟨122, .identity, .p120⟩, ⟨125, .identity, .p120⟩, ⟨124, .identity, .p120⟩, ⟨120, .identity, .p120⟩, ⟨121, .identity, .p120⟩, ⟨117, .swap34, .p120⟩, ⟨116, .swap34, .p120⟩, ⟨119, .swap34, .p120⟩, ⟨118, .swap34, .p120⟩, ⟨114, .swap34, .p120⟩, ⟨115, .swap34, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6096) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6096 ≤ case.val)
    (upper : case.val < 6144) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6103 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6143 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk127.correct

end Krenn.X5OrbitWitnessChunks.Chunk127
