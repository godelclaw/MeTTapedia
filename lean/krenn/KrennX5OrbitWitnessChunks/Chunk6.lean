import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk6

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨42, .cycle243, .p012⟩, ⟨43, .cycle243, .p012⟩, ⟨44, .cycle243, .p012⟩, ⟨45, .cycle243, .p012⟩, ⟨46, .cycle243, .p012⟩, ⟨47, .cycle243, .p012⟩, ⟨132, .swap34, .p012⟩, ⟨133, .swap34, .p012⟩, ⟨134, .swap34, .p012⟩, ⟨135, .swap34, .p012⟩, ⟨136, .swap34, .p012⟩, ⟨137, .swap34, .p012⟩,
    ⟨156, .identity, .p012⟩, ⟨157, .identity, .p012⟩, ⟨158, .identity, .p012⟩, ⟨159, .identity, .p012⟩, ⟨160, .identity, .p012⟩, ⟨161, .identity, .p012⟩, ⟨162, .identity, .p012⟩, ⟨163, .identity, .p012⟩, ⟨164, .identity, .p012⟩, ⟨165, .identity, .p012⟩, ⟨166, .identity, .p012⟩, ⟨167, .identity, .p012⟩,
    ⟨168, .identity, .p012⟩, ⟨169, .identity, .p012⟩, ⟨170, .identity, .p012⟩, ⟨171, .identity, .p012⟩, ⟨172, .identity, .p012⟩, ⟨173, .identity, .p012⟩, ⟨174, .identity, .p012⟩, ⟨175, .identity, .p012⟩, ⟨176, .identity, .p012⟩, ⟨177, .identity, .p012⟩, ⟨178, .identity, .p012⟩, ⟨179, .identity, .p012⟩,
    ⟨48, .cycle243, .p012⟩, ⟨49, .cycle243, .p012⟩, ⟨50, .cycle243, .p012⟩, ⟨51, .cycle243, .p012⟩, ⟨52, .cycle243, .p012⟩, ⟨53, .cycle243, .p012⟩, ⟨138, .swap34, .p012⟩, ⟨139, .swap34, .p012⟩, ⟨140, .swap34, .p012⟩, ⟨141, .swap34, .p012⟩, ⟨142, .swap34, .p012⟩, ⟨143, .swap34, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 288) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 288 ≤ case.val)
    (upper : case.val < 336) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (288 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (289 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (290 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (291 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (292 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (293 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (294 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (295 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (296 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (297 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (298 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (299 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (300 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (301 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (302 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (303 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (304 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (305 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (306 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (307 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (308 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (309 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (310 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (311 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (312 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (313 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (314 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (315 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (316 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (317 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (318 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (319 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (320 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (321 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (322 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (323 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (324 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (325 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (326 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (327 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (328 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (329 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (330 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (331 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (332 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (333 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (334 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (335 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk6.correct

end Krenn.X5OrbitWitnessChunks.Chunk6
