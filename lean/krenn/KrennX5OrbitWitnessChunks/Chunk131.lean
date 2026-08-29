import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk131

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨51, .cycle243, .p120⟩, ⟨50, .cycle243, .p120⟩, ⟨53, .cycle243, .p120⟩, ⟨52, .cycle243, .p120⟩, ⟨48, .cycle243, .p120⟩, ⟨49, .cycle243, .p120⟩, ⟨141, .swap34, .p120⟩, ⟨140, .swap34, .p120⟩, ⟨143, .swap34, .p120⟩, ⟨142, .swap34, .p120⟩, ⟨138, .swap34, .p120⟩, ⟨139, .swap34, .p120⟩,
    ⟨165, .identity, .p120⟩, ⟨164, .identity, .p120⟩, ⟨167, .identity, .p120⟩, ⟨166, .identity, .p120⟩, ⟨162, .identity, .p120⟩, ⟨163, .identity, .p120⟩, ⟨159, .identity, .p120⟩, ⟨158, .identity, .p120⟩, ⟨161, .identity, .p120⟩, ⟨160, .identity, .p120⟩, ⟨156, .identity, .p120⟩, ⟨157, .identity, .p120⟩,
    ⟨177, .identity, .p120⟩, ⟨176, .identity, .p120⟩, ⟨179, .identity, .p120⟩, ⟨178, .identity, .p120⟩, ⟨174, .identity, .p120⟩, ⟨175, .identity, .p120⟩, ⟨171, .identity, .p120⟩, ⟨170, .identity, .p120⟩, ⟨173, .identity, .p120⟩, ⟨172, .identity, .p120⟩, ⟨168, .identity, .p120⟩, ⟨169, .identity, .p120⟩,
    ⟨45, .cycle243, .p120⟩, ⟨44, .cycle243, .p120⟩, ⟨47, .cycle243, .p120⟩, ⟨46, .cycle243, .p120⟩, ⟨42, .cycle243, .p120⟩, ⟨43, .cycle243, .p120⟩, ⟨135, .swap34, .p120⟩, ⟨134, .swap34, .p120⟩, ⟨137, .swap34, .p120⟩, ⟨136, .swap34, .p120⟩, ⟨132, .swap34, .p120⟩, ⟨133, .swap34, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6288) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6288 ≤ case.val)
    (upper : case.val < 6336) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6295 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6335 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk131.correct

end Krenn.X5OrbitWitnessChunks.Chunk131
