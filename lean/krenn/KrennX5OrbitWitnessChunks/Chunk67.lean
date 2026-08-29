import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk67

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨26, .swap34, .p102⟩, ⟨27, .swap34, .p102⟩, ⟨24, .swap34, .p102⟩, ⟨25, .swap34, .p102⟩, ⟨29, .swap34, .p102⟩, ⟨28, .swap34, .p102⟩, ⟨56, .swap34, .p102⟩, ⟨57, .swap34, .p102⟩, ⟨54, .swap34, .p102⟩, ⟨55, .swap34, .p102⟩, ⟨59, .swap34, .p102⟩, ⟨58, .swap34, .p102⟩,
    ⟨116, .identity, .p102⟩, ⟨117, .identity, .p102⟩, ⟨114, .identity, .p102⟩, ⟨115, .identity, .p102⟩, ⟨119, .identity, .p102⟩, ⟨118, .identity, .p102⟩, ⟨110, .identity, .p102⟩, ⟨111, .identity, .p102⟩, ⟨108, .identity, .p102⟩, ⟨109, .identity, .p102⟩, ⟨113, .identity, .p102⟩, ⟨112, .identity, .p102⟩,
    ⟨158, .identity, .p102⟩, ⟨159, .identity, .p102⟩, ⟨156, .identity, .p102⟩, ⟨157, .identity, .p102⟩, ⟨161, .identity, .p102⟩, ⟨160, .identity, .p102⟩, ⟨164, .identity, .p102⟩, ⟨165, .identity, .p102⟩, ⟨162, .identity, .p102⟩, ⟨163, .identity, .p102⟩, ⟨167, .identity, .p102⟩, ⟨166, .identity, .p102⟩,
    ⟨44, .cycle243, .p102⟩, ⟨45, .cycle243, .p102⟩, ⟨42, .cycle243, .p102⟩, ⟨43, .cycle243, .p102⟩, ⟨47, .cycle243, .p102⟩, ⟨46, .cycle243, .p102⟩, ⟨134, .swap34, .p102⟩, ⟨135, .swap34, .p102⟩, ⟨132, .swap34, .p102⟩, ⟨133, .swap34, .p102⟩, ⟨137, .swap34, .p102⟩, ⟨136, .swap34, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3216) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3216 ≤ case.val)
    (upper : case.val < 3264) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3223 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3224 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3225 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3226 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3227 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3228 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3229 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3230 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3231 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3232 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3233 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3234 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3235 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3236 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3237 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3238 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3239 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3240 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3241 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3242 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3243 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3244 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3245 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3246 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3247 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3248 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3249 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3250 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3251 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3252 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3253 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3254 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3255 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3256 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3257 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3258 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3259 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3260 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3261 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3262 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3263 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk67.correct

end Krenn.X5OrbitWitnessChunks.Chunk67
