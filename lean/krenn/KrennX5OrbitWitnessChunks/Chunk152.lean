import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk152

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨137, .swap24, .p210⟩, ⟨136, .swap24, .p210⟩, ⟨135, .swap24, .p210⟩, ⟨134, .swap24, .p210⟩, ⟨133, .swap24, .p210⟩, ⟨132, .swap24, .p210⟩, ⟨47, .swap24, .p210⟩, ⟨46, .swap24, .p210⟩, ⟨45, .swap24, .p210⟩, ⟨44, .swap24, .p210⟩, ⟨43, .swap24, .p210⟩, ⟨42, .swap24, .p210⟩,
    ⟨89, .swap23, .p210⟩, ⟨88, .swap23, .p210⟩, ⟨87, .swap23, .p210⟩, ⟨86, .swap23, .p210⟩, ⟨85, .swap23, .p210⟩, ⟨84, .swap23, .p210⟩, ⟨83, .swap23, .p210⟩, ⟨82, .swap23, .p210⟩, ⟨81, .swap23, .p210⟩, ⟨80, .swap23, .p210⟩, ⟨79, .swap23, .p210⟩, ⟨78, .swap23, .p210⟩,
    ⟨77, .swap23, .p210⟩, ⟨76, .swap23, .p210⟩, ⟨75, .swap23, .p210⟩, ⟨74, .swap23, .p210⟩, ⟨73, .swap23, .p210⟩, ⟨72, .swap23, .p210⟩, ⟨71, .swap23, .p210⟩, ⟨70, .swap23, .p210⟩, ⟨69, .swap23, .p210⟩, ⟨68, .swap23, .p210⟩, ⟨67, .swap23, .p210⟩, ⟨66, .swap23, .p210⟩,
    ⟨47, .cycle234, .p210⟩, ⟨46, .cycle234, .p210⟩, ⟨45, .cycle234, .p210⟩, ⟨44, .cycle234, .p210⟩, ⟨43, .cycle234, .p210⟩, ⟨42, .cycle234, .p210⟩, ⟨17, .swap24, .p210⟩, ⟨16, .swap24, .p210⟩, ⟨15, .swap24, .p210⟩, ⟨14, .swap24, .p210⟩, ⟨13, .swap24, .p210⟩, ⟨12, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7296) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7296 ≤ case.val)
    (upper : case.val < 7344) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7335 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7343 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk152.correct

end Krenn.X5OrbitWitnessChunks.Chunk152
