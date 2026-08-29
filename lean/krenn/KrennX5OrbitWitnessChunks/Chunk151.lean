import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk151

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨227, .identity, .p210⟩, ⟨226, .identity, .p210⟩, ⟨225, .identity, .p210⟩, ⟨224, .identity, .p210⟩, ⟨223, .identity, .p210⟩, ⟨222, .identity, .p210⟩, ⟨221, .identity, .p210⟩, ⟨220, .identity, .p210⟩, ⟨219, .identity, .p210⟩, ⟨218, .identity, .p210⟩, ⟨217, .identity, .p210⟩, ⟨216, .identity, .p210⟩,
    ⟨161, .swap24, .p210⟩, ⟨160, .swap24, .p210⟩, ⟨159, .swap24, .p210⟩, ⟨158, .swap24, .p210⟩, ⟨157, .swap24, .p210⟩, ⟨156, .swap24, .p210⟩, ⟨71, .swap24, .p210⟩, ⟨70, .swap24, .p210⟩, ⟨69, .swap24, .p210⟩, ⟨68, .swap24, .p210⟩, ⟨67, .swap24, .p210⟩, ⟨66, .swap24, .p210⟩,
    ⟨179, .swap23, .p210⟩, ⟨178, .swap23, .p210⟩, ⟨177, .swap23, .p210⟩, ⟨176, .swap23, .p210⟩, ⟨175, .swap23, .p210⟩, ⟨174, .swap23, .p210⟩, ⟨173, .swap23, .p210⟩, ⟨172, .swap23, .p210⟩, ⟨171, .swap23, .p210⟩, ⟨170, .swap23, .p210⟩, ⟨169, .swap23, .p210⟩, ⟨168, .swap23, .p210⟩,
    ⟨167, .swap23, .p210⟩, ⟨166, .swap23, .p210⟩, ⟨165, .swap23, .p210⟩, ⟨164, .swap23, .p210⟩, ⟨163, .swap23, .p210⟩, ⟨162, .swap23, .p210⟩, ⟨161, .swap23, .p210⟩, ⟨160, .swap23, .p210⟩, ⟨159, .swap23, .p210⟩, ⟨158, .swap23, .p210⟩, ⟨157, .swap23, .p210⟩, ⟨156, .swap23, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7248) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7248 ≤ case.val)
    (upper : case.val < 7296) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7287 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7295 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk151.correct

end Krenn.X5OrbitWitnessChunks.Chunk151
