import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk68

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨176, .identity, .p102⟩, ⟨177, .identity, .p102⟩, ⟨174, .identity, .p102⟩, ⟨175, .identity, .p102⟩, ⟨179, .identity, .p102⟩, ⟨178, .identity, .p102⟩, ⟨170, .identity, .p102⟩, ⟨171, .identity, .p102⟩, ⟨168, .identity, .p102⟩, ⟨169, .identity, .p102⟩, ⟨173, .identity, .p102⟩, ⟨172, .identity, .p102⟩,
    ⟨164, .swap34, .p102⟩, ⟨165, .swap34, .p102⟩, ⟨162, .swap34, .p102⟩, ⟨163, .swap34, .p102⟩, ⟨167, .swap34, .p102⟩, ⟨166, .swap34, .p102⟩, ⟨182, .identity, .p102⟩, ⟨183, .identity, .p102⟩, ⟨180, .identity, .p102⟩, ⟨181, .identity, .p102⟩, ⟨185, .identity, .p102⟩, ⟨184, .identity, .p102⟩,
    ⟨50, .cycle243, .p102⟩, ⟨51, .cycle243, .p102⟩, ⟨48, .cycle243, .p102⟩, ⟨49, .cycle243, .p102⟩, ⟨53, .cycle243, .p102⟩, ⟨52, .cycle243, .p102⟩, ⟨140, .swap34, .p102⟩, ⟨141, .swap34, .p102⟩, ⟨138, .swap34, .p102⟩, ⟨139, .swap34, .p102⟩, ⟨143, .swap34, .p102⟩, ⟨142, .swap34, .p102⟩,
    ⟨194, .identity, .p102⟩, ⟨195, .identity, .p102⟩, ⟨192, .identity, .p102⟩, ⟨193, .identity, .p102⟩, ⟨197, .identity, .p102⟩, ⟨196, .identity, .p102⟩, ⟨188, .identity, .p102⟩, ⟨189, .identity, .p102⟩, ⟨186, .identity, .p102⟩, ⟨187, .identity, .p102⟩, ⟨191, .identity, .p102⟩, ⟨190, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3264) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3264 ≤ case.val)
    (upper : case.val < 3312) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3287 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3295 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3311 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk68.correct

end Krenn.X5OrbitWitnessChunks.Chunk68
