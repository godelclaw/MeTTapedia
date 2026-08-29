import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk149

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨179, .cycle243, .p210⟩, ⟨178, .cycle243, .p210⟩, ⟨177, .cycle243, .p210⟩, ⟨176, .cycle243, .p210⟩, ⟨175, .cycle243, .p210⟩, ⟨174, .cycle243, .p210⟩, ⟨89, .cycle243, .p210⟩, ⟨88, .cycle243, .p210⟩, ⟨87, .cycle243, .p210⟩, ⟨86, .cycle243, .p210⟩, ⟨85, .cycle243, .p210⟩, ⟨84, .cycle243, .p210⟩,
    ⟨269, .identity, .p210⟩, ⟨268, .identity, .p210⟩, ⟨267, .identity, .p210⟩, ⟨266, .identity, .p210⟩, ⟨265, .identity, .p210⟩, ⟨264, .identity, .p210⟩, ⟨263, .identity, .p210⟩, ⟨262, .identity, .p210⟩, ⟨261, .identity, .p210⟩, ⟨260, .identity, .p210⟩, ⟨259, .identity, .p210⟩, ⟨258, .identity, .p210⟩,
    ⟨251, .swap34, .p210⟩, ⟨250, .swap34, .p210⟩, ⟨249, .swap34, .p210⟩, ⟨248, .swap34, .p210⟩, ⟨247, .swap34, .p210⟩, ⟨246, .swap34, .p210⟩, ⟨233, .swap34, .p210⟩, ⟨232, .swap34, .p210⟩, ⟨231, .swap34, .p210⟩, ⟨230, .swap34, .p210⟩, ⟨229, .swap34, .p210⟩, ⟨228, .swap34, .p210⟩,
    ⟨173, .cycle243, .p210⟩, ⟨172, .cycle243, .p210⟩, ⟨171, .cycle243, .p210⟩, ⟨170, .cycle243, .p210⟩, ⟨169, .cycle243, .p210⟩, ⟨168, .cycle243, .p210⟩, ⟨83, .cycle243, .p210⟩, ⟨82, .cycle243, .p210⟩, ⟨81, .cycle243, .p210⟩, ⟨80, .cycle243, .p210⟩, ⟨79, .cycle243, .p210⟩, ⟨78, .cycle243, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7152) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7152 ≤ case.val)
    (upper : case.val < 7200) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7191 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7199 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk149.correct

end Krenn.X5OrbitWitnessChunks.Chunk149
