import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk5

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨54, .swap23, .p012⟩, ⟨55, .swap23, .p012⟩, ⟨56, .swap23, .p012⟩, ⟨57, .swap23, .p012⟩, ⟨58, .swap23, .p012⟩, ⟨59, .swap23, .p012⟩, ⟨60, .swap23, .p012⟩, ⟨61, .swap23, .p012⟩, ⟨62, .swap23, .p012⟩, ⟨63, .swap23, .p012⟩, ⟨64, .swap23, .p012⟩, ⟨65, .swap23, .p012⟩,
    ⟨36, .swap24, .p012⟩, ⟨37, .swap24, .p012⟩, ⟨38, .swap24, .p012⟩, ⟨39, .swap24, .p012⟩, ⟨40, .swap24, .p012⟩, ⟨41, .swap24, .p012⟩, ⟨126, .identity, .p012⟩, ⟨127, .identity, .p012⟩, ⟨128, .identity, .p012⟩, ⟨129, .identity, .p012⟩, ⟨130, .identity, .p012⟩, ⟨131, .identity, .p012⟩,
    ⟨132, .identity, .p012⟩, ⟨133, .identity, .p012⟩, ⟨134, .identity, .p012⟩, ⟨135, .identity, .p012⟩, ⟨136, .identity, .p012⟩, ⟨137, .identity, .p012⟩, ⟨138, .identity, .p012⟩, ⟨139, .identity, .p012⟩, ⟨140, .identity, .p012⟩, ⟨141, .identity, .p012⟩, ⟨142, .identity, .p012⟩, ⟨143, .identity, .p012⟩,
    ⟨144, .identity, .p012⟩, ⟨145, .identity, .p012⟩, ⟨146, .identity, .p012⟩, ⟨147, .identity, .p012⟩, ⟨148, .identity, .p012⟩, ⟨149, .identity, .p012⟩, ⟨150, .identity, .p012⟩, ⟨151, .identity, .p012⟩, ⟨152, .identity, .p012⟩, ⟨153, .identity, .p012⟩, ⟨154, .identity, .p012⟩, ⟨155, .identity, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 240) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 240 ≤ case.val)
    (upper : case.val < 288) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (247 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (263 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (264 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (265 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (266 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (267 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (268 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (269 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (270 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (271 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (272 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (273 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (274 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (275 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (276 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (277 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (278 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (279 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (280 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (281 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (282 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (283 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (284 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (285 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (286 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (287 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk5.correct

end Krenn.X5OrbitWitnessChunks.Chunk5
