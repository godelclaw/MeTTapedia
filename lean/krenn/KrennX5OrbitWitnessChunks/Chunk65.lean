import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk65

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨32, .identity, .p102⟩, ⟨33, .identity, .p102⟩, ⟨30, .identity, .p102⟩, ⟨31, .identity, .p102⟩, ⟨35, .identity, .p102⟩, ⟨34, .identity, .p102⟩, ⟨26, .identity, .p102⟩, ⟨27, .identity, .p102⟩, ⟨24, .identity, .p102⟩, ⟨25, .identity, .p102⟩, ⟨29, .identity, .p102⟩, ⟨28, .identity, .p102⟩,
    ⟨44, .identity, .p102⟩, ⟨45, .identity, .p102⟩, ⟨42, .identity, .p102⟩, ⟨43, .identity, .p102⟩, ⟨47, .identity, .p102⟩, ⟨46, .identity, .p102⟩, ⟨50, .identity, .p102⟩, ⟨51, .identity, .p102⟩, ⟨48, .identity, .p102⟩, ⟨49, .identity, .p102⟩, ⟨53, .identity, .p102⟩, ⟨52, .identity, .p102⟩,
    ⟨8, .swap34, .p102⟩, ⟨9, .swap34, .p102⟩, ⟨6, .swap34, .p102⟩, ⟨7, .swap34, .p102⟩, ⟨11, .swap34, .p102⟩, ⟨10, .swap34, .p102⟩, ⟨38, .identity, .p102⟩, ⟨39, .identity, .p102⟩, ⟨36, .identity, .p102⟩, ⟨37, .identity, .p102⟩, ⟨41, .identity, .p102⟩, ⟨40, .identity, .p102⟩,
    ⟨62, .identity, .p102⟩, ⟨63, .identity, .p102⟩, ⟨60, .identity, .p102⟩, ⟨61, .identity, .p102⟩, ⟨65, .identity, .p102⟩, ⟨64, .identity, .p102⟩, ⟨56, .identity, .p102⟩, ⟨57, .identity, .p102⟩, ⟨54, .identity, .p102⟩, ⟨55, .identity, .p102⟩, ⟨59, .identity, .p102⟩, ⟨58, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3120) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3120 ≤ case.val)
    (upper : case.val < 3168) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3120 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3121 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3122 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3123 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3124 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3125 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3126 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3127 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3128 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3129 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3130 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3131 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3132 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3133 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3134 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3135 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3136 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3137 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3138 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3139 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3140 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3141 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3142 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3143 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3151 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3167 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk65.correct

end Krenn.X5OrbitWitnessChunks.Chunk65
