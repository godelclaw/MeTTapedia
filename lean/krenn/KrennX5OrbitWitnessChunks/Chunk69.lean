import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk69

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨44, .swap23, .p102⟩, ⟨45, .swap23, .p102⟩, ⟨42, .swap23, .p102⟩, ⟨43, .swap23, .p102⟩, ⟨47, .swap23, .p102⟩, ⟨46, .swap23, .p102⟩, ⟨50, .swap23, .p102⟩, ⟨51, .swap23, .p102⟩, ⟨48, .swap23, .p102⟩, ⟨49, .swap23, .p102⟩, ⟨53, .swap23, .p102⟩, ⟨52, .swap23, .p102⟩,
    ⟨8, .swap24, .p102⟩, ⟨9, .swap24, .p102⟩, ⟨6, .swap24, .p102⟩, ⟨7, .swap24, .p102⟩, ⟨11, .swap24, .p102⟩, ⟨10, .swap24, .p102⟩, ⟨38, .swap23, .p102⟩, ⟨39, .swap23, .p102⟩, ⟨36, .swap23, .p102⟩, ⟨37, .swap23, .p102⟩, ⟨41, .swap23, .p102⟩, ⟨40, .swap23, .p102⟩,
    ⟨62, .swap23, .p102⟩, ⟨63, .swap23, .p102⟩, ⟨60, .swap23, .p102⟩, ⟨61, .swap23, .p102⟩, ⟨65, .swap23, .p102⟩, ⟨64, .swap23, .p102⟩, ⟨56, .swap23, .p102⟩, ⟨57, .swap23, .p102⟩, ⟨54, .swap23, .p102⟩, ⟨55, .swap23, .p102⟩, ⟨59, .swap23, .p102⟩, ⟨58, .swap23, .p102⟩,
    ⟨134, .identity, .p102⟩, ⟨135, .identity, .p102⟩, ⟨132, .identity, .p102⟩, ⟨133, .identity, .p102⟩, ⟨137, .identity, .p102⟩, ⟨136, .identity, .p102⟩, ⟨140, .identity, .p102⟩, ⟨141, .identity, .p102⟩, ⟨138, .identity, .p102⟩, ⟨139, .identity, .p102⟩, ⟨143, .identity, .p102⟩, ⟨142, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3312) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3312 ≤ case.val)
    (upper : case.val < 3360) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3335 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3336 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3337 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3338 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3339 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3340 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3341 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3342 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3343 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3344 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3345 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3346 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3347 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3348 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3349 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3350 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3351 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3352 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3353 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3354 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3355 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3356 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3357 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3358 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3359 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk69.correct

end Krenn.X5OrbitWitnessChunks.Chunk69
