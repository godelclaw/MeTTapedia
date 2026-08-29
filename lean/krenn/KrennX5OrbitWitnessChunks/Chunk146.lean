import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk146

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨185, .swap24, .p210⟩, ⟨184, .swap24, .p210⟩, ⟨183, .swap24, .p210⟩, ⟨182, .swap24, .p210⟩, ⟨181, .swap24, .p210⟩, ⟨180, .swap24, .p210⟩, ⟨95, .swap24, .p210⟩, ⟨94, .swap24, .p210⟩, ⟨93, .swap24, .p210⟩, ⟨92, .swap24, .p210⟩, ⟨91, .swap24, .p210⟩, ⟨90, .swap24, .p210⟩,
    ⟨257, .swap23, .p210⟩, ⟨256, .swap23, .p210⟩, ⟨255, .swap23, .p210⟩, ⟨254, .swap23, .p210⟩, ⟨253, .swap23, .p210⟩, ⟨252, .swap23, .p210⟩, ⟨251, .swap23, .p210⟩, ⟨250, .swap23, .p210⟩, ⟨249, .swap23, .p210⟩, ⟨248, .swap23, .p210⟩, ⟨247, .swap23, .p210⟩, ⟨246, .swap23, .p210⟩,
    ⟨245, .swap23, .p210⟩, ⟨244, .swap23, .p210⟩, ⟨243, .swap23, .p210⟩, ⟨242, .swap23, .p210⟩, ⟨241, .swap23, .p210⟩, ⟨240, .swap23, .p210⟩, ⟨227, .swap24, .p210⟩, ⟨226, .swap24, .p210⟩, ⟨225, .swap24, .p210⟩, ⟨224, .swap24, .p210⟩, ⟨223, .swap24, .p210⟩, ⟨222, .swap24, .p210⟩,
    ⟨167, .swap24, .p210⟩, ⟨166, .swap24, .p210⟩, ⟨165, .swap24, .p210⟩, ⟨164, .swap24, .p210⟩, ⟨163, .swap24, .p210⟩, ⟨162, .swap24, .p210⟩, ⟨77, .swap24, .p210⟩, ⟨76, .swap24, .p210⟩, ⟨75, .swap24, .p210⟩, ⟨74, .swap24, .p210⟩, ⟨73, .swap24, .p210⟩, ⟨72, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7008) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7008 ≤ case.val)
    (upper : case.val < 7056) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7015 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7023 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7031 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7039 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7047 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7055 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk146.correct

end Krenn.X5OrbitWitnessChunks.Chunk146
