import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk110

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨105, .cycle243, .p120⟩, ⟨104, .cycle243, .p120⟩, ⟨107, .cycle243, .p120⟩, ⟨106, .cycle243, .p120⟩, ⟨102, .cycle243, .p120⟩, ⟨103, .cycle243, .p120⟩, ⟨195, .cycle243, .p120⟩, ⟨194, .cycle243, .p120⟩, ⟨197, .cycle243, .p120⟩, ⟨196, .cycle243, .p120⟩, ⟨192, .cycle243, .p120⟩, ⟨193, .cycle243, .p120⟩,
    ⟨285, .swap34, .p120⟩, ⟨284, .swap34, .p120⟩, ⟨287, .swap34, .p120⟩, ⟨286, .swap34, .p120⟩, ⟨282, .swap34, .p120⟩, ⟨283, .swap34, .p120⟩, ⟨249, .cycle243, .p120⟩, ⟨248, .cycle243, .p120⟩, ⟨251, .cycle243, .p120⟩, ⟨250, .cycle243, .p120⟩, ⟨246, .cycle243, .p120⟩, ⟨247, .cycle243, .p120⟩,
    ⟨303, .identity, .p120⟩, ⟨302, .identity, .p120⟩, ⟨305, .identity, .p120⟩, ⟨304, .identity, .p120⟩, ⟨300, .identity, .p120⟩, ⟨301, .identity, .p120⟩, ⟨297, .identity, .p120⟩, ⟨296, .identity, .p120⟩, ⟨299, .identity, .p120⟩, ⟨298, .identity, .p120⟩, ⟨294, .identity, .p120⟩, ⟨295, .identity, .p120⟩,
    ⟨99, .cycle243, .p120⟩, ⟨98, .cycle243, .p120⟩, ⟨101, .cycle243, .p120⟩, ⟨100, .cycle243, .p120⟩, ⟨96, .cycle243, .p120⟩, ⟨97, .cycle243, .p120⟩, ⟨189, .cycle243, .p120⟩, ⟨188, .cycle243, .p120⟩, ⟨191, .cycle243, .p120⟩, ⟨190, .cycle243, .p120⟩, ⟨186, .cycle243, .p120⟩, ⟨187, .cycle243, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5280) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5280 ≤ case.val)
    (upper : case.val < 5328) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5287 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5295 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5327 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk110.correct

end Krenn.X5OrbitWitnessChunks.Chunk110
