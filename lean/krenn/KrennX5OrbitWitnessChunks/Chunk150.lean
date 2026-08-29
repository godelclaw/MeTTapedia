import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk150

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨257, .identity, .p210⟩, ⟨256, .identity, .p210⟩, ⟨255, .identity, .p210⟩, ⟨254, .identity, .p210⟩, ⟨253, .identity, .p210⟩, ⟨252, .identity, .p210⟩, ⟨251, .identity, .p210⟩, ⟨250, .identity, .p210⟩, ⟨249, .identity, .p210⟩, ⟨248, .identity, .p210⟩, ⟨247, .identity, .p210⟩, ⟨246, .identity, .p210⟩,
    ⟨245, .identity, .p210⟩, ⟨244, .identity, .p210⟩, ⟨243, .identity, .p210⟩, ⟨242, .identity, .p210⟩, ⟨241, .identity, .p210⟩, ⟨240, .identity, .p210⟩, ⟨227, .swap34, .p210⟩, ⟨226, .swap34, .p210⟩, ⟨225, .swap34, .p210⟩, ⟨224, .swap34, .p210⟩, ⟨223, .swap34, .p210⟩, ⟨222, .swap34, .p210⟩,
    ⟨167, .cycle243, .p210⟩, ⟨166, .cycle243, .p210⟩, ⟨165, .cycle243, .p210⟩, ⟨164, .cycle243, .p210⟩, ⟨163, .cycle243, .p210⟩, ⟨162, .cycle243, .p210⟩, ⟨77, .cycle243, .p210⟩, ⟨76, .cycle243, .p210⟩, ⟨75, .cycle243, .p210⟩, ⟨74, .cycle243, .p210⟩, ⟨73, .cycle243, .p210⟩, ⟨72, .cycle243, .p210⟩,
    ⟨239, .identity, .p210⟩, ⟨238, .identity, .p210⟩, ⟨237, .identity, .p210⟩, ⟨236, .identity, .p210⟩, ⟨235, .identity, .p210⟩, ⟨234, .identity, .p210⟩, ⟨233, .identity, .p210⟩, ⟨232, .identity, .p210⟩, ⟨231, .identity, .p210⟩, ⟨230, .identity, .p210⟩, ⟨229, .identity, .p210⟩, ⟨228, .identity, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7200) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7200 ≤ case.val)
    (upper : case.val < 7248) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7239 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7247 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk150.correct

end Krenn.X5OrbitWitnessChunks.Chunk150
