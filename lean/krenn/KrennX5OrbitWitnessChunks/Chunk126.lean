import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk126

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨93, .identity, .p120⟩, ⟨92, .identity, .p120⟩, ⟨95, .identity, .p120⟩, ⟨94, .identity, .p120⟩, ⟨90, .identity, .p120⟩, ⟨91, .identity, .p120⟩, ⟨75, .swap34, .p120⟩, ⟨74, .swap34, .p120⟩, ⟨77, .swap34, .p120⟩, ⟨76, .swap34, .p120⟩, ⟨72, .swap34, .p120⟩, ⟨73, .swap34, .p120⟩,
    ⟨105, .identity, .p120⟩, ⟨104, .identity, .p120⟩, ⟨107, .identity, .p120⟩, ⟨106, .identity, .p120⟩, ⟨102, .identity, .p120⟩, ⟨103, .identity, .p120⟩, ⟨99, .identity, .p120⟩, ⟨98, .identity, .p120⟩, ⟨101, .identity, .p120⟩, ⟨100, .identity, .p120⟩, ⟨96, .identity, .p120⟩, ⟨97, .identity, .p120⟩,
    ⟨21, .swap34, .p120⟩, ⟨20, .swap34, .p120⟩, ⟨23, .swap34, .p120⟩, ⟨22, .swap34, .p120⟩, ⟨18, .swap34, .p120⟩, ⟨19, .swap34, .p120⟩, ⟨51, .swap34, .p120⟩, ⟨50, .swap34, .p120⟩, ⟨53, .swap34, .p120⟩, ⟨52, .swap34, .p120⟩, ⟨48, .swap34, .p120⟩, ⟨49, .swap34, .p120⟩,
    ⟨75, .identity, .p120⟩, ⟨74, .identity, .p120⟩, ⟨77, .identity, .p120⟩, ⟨76, .identity, .p120⟩, ⟨72, .identity, .p120⟩, ⟨73, .identity, .p120⟩, ⟨69, .identity, .p120⟩, ⟨68, .identity, .p120⟩, ⟨71, .identity, .p120⟩, ⟨70, .identity, .p120⟩, ⟨66, .identity, .p120⟩, ⟨67, .identity, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6048) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6048 ≤ case.val)
    (upper : case.val < 6096) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6055 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6063 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6071 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6079 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6087 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6095 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk126.correct

end Krenn.X5OrbitWitnessChunks.Chunk126
