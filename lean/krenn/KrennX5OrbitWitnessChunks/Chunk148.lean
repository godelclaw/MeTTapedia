import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk148

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨95, .swap23, .p210⟩, ⟨94, .swap23, .p210⟩, ⟨93, .swap23, .p210⟩, ⟨92, .swap23, .p210⟩, ⟨91, .swap23, .p210⟩, ⟨90, .swap23, .p210⟩, ⟨77, .cycle234, .p210⟩, ⟨76, .cycle234, .p210⟩, ⟨75, .cycle234, .p210⟩, ⟨74, .cycle234, .p210⟩, ⟨73, .cycle234, .p210⟩, ⟨72, .cycle234, .p210⟩,
    ⟨53, .cycle234, .p210⟩, ⟨52, .cycle234, .p210⟩, ⟨51, .cycle234, .p210⟩, ⟨50, .cycle234, .p210⟩, ⟨49, .cycle234, .p210⟩, ⟨48, .cycle234, .p210⟩, ⟨23, .swap24, .p210⟩, ⟨22, .swap24, .p210⟩, ⟨21, .swap24, .p210⟩, ⟨20, .swap24, .p210⟩, ⟨19, .swap24, .p210⟩, ⟨18, .swap24, .p210⟩,
    ⟨275, .identity, .p210⟩, ⟨274, .identity, .p210⟩, ⟨273, .identity, .p210⟩, ⟨272, .identity, .p210⟩, ⟨271, .identity, .p210⟩, ⟨270, .identity, .p210⟩, ⟨269, .swap34, .p210⟩, ⟨268, .swap34, .p210⟩, ⟨267, .swap34, .p210⟩, ⟨266, .swap34, .p210⟩, ⟨265, .swap34, .p210⟩, ⟨264, .swap34, .p210⟩,
    ⟨257, .swap34, .p210⟩, ⟨256, .swap34, .p210⟩, ⟨255, .swap34, .p210⟩, ⟨254, .swap34, .p210⟩, ⟨253, .swap34, .p210⟩, ⟨252, .swap34, .p210⟩, ⟨239, .swap34, .p210⟩, ⟨238, .swap34, .p210⟩, ⟨237, .swap34, .p210⟩, ⟨236, .swap34, .p210⟩, ⟨235, .swap34, .p210⟩, ⟨234, .swap34, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7104) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7104 ≤ case.val)
    (upper : case.val < 7152) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7119 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7143 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7151 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk148.correct

end Krenn.X5OrbitWitnessChunks.Chunk148
