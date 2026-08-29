import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk147

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨197, .swap23, .p210⟩, ⟨196, .swap23, .p210⟩, ⟨195, .swap23, .p210⟩, ⟨194, .swap23, .p210⟩, ⟨193, .swap23, .p210⟩, ⟨192, .swap23, .p210⟩, ⟨191, .swap23, .p210⟩, ⟨190, .swap23, .p210⟩, ⟨189, .swap23, .p210⟩, ⟨188, .swap23, .p210⟩, ⟨187, .swap23, .p210⟩, ⟨186, .swap23, .p210⟩,
    ⟨185, .swap23, .p210⟩, ⟨184, .swap23, .p210⟩, ⟨183, .swap23, .p210⟩, ⟨182, .swap23, .p210⟩, ⟨181, .swap23, .p210⟩, ⟨180, .swap23, .p210⟩, ⟨167, .cycle234, .p210⟩, ⟨166, .cycle234, .p210⟩, ⟨165, .cycle234, .p210⟩, ⟨164, .cycle234, .p210⟩, ⟨163, .cycle234, .p210⟩, ⟨162, .cycle234, .p210⟩,
    ⟨143, .swap24, .p210⟩, ⟨142, .swap24, .p210⟩, ⟨141, .swap24, .p210⟩, ⟨140, .swap24, .p210⟩, ⟨139, .swap24, .p210⟩, ⟨138, .swap24, .p210⟩, ⟨53, .swap24, .p210⟩, ⟨52, .swap24, .p210⟩, ⟨51, .swap24, .p210⟩, ⟨50, .swap24, .p210⟩, ⟨49, .swap24, .p210⟩, ⟨48, .swap24, .p210⟩,
    ⟨107, .swap23, .p210⟩, ⟨106, .swap23, .p210⟩, ⟨105, .swap23, .p210⟩, ⟨104, .swap23, .p210⟩, ⟨103, .swap23, .p210⟩, ⟨102, .swap23, .p210⟩, ⟨101, .swap23, .p210⟩, ⟨100, .swap23, .p210⟩, ⟨99, .swap23, .p210⟩, ⟨98, .swap23, .p210⟩, ⟨97, .swap23, .p210⟩, ⟨96, .swap23, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7056) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7056 ≤ case.val)
    (upper : case.val < 7104) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7063 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7071 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7079 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7087 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7095 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7103 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk147.correct

end Krenn.X5OrbitWitnessChunks.Chunk147
