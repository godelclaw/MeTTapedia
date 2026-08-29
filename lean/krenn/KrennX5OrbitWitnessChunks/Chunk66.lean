import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk66

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨86, .swap34, .p102⟩, ⟨87, .swap34, .p102⟩, ⟨84, .swap34, .p102⟩, ⟨85, .swap34, .p102⟩, ⟨89, .swap34, .p102⟩, ⟨88, .swap34, .p102⟩, ⟨104, .swap34, .p102⟩, ⟨105, .swap34, .p102⟩, ⟨102, .swap34, .p102⟩, ⟨103, .swap34, .p102⟩, ⟨107, .swap34, .p102⟩, ⟨106, .swap34, .p102⟩,
    ⟨32, .swap34, .p102⟩, ⟨33, .swap34, .p102⟩, ⟨30, .swap34, .p102⟩, ⟨31, .swap34, .p102⟩, ⟨35, .swap34, .p102⟩, ⟨34, .swap34, .p102⟩, ⟨62, .swap34, .p102⟩, ⟨63, .swap34, .p102⟩, ⟨60, .swap34, .p102⟩, ⟨61, .swap34, .p102⟩, ⟨65, .swap34, .p102⟩, ⟨64, .swap34, .p102⟩,
    ⟨122, .identity, .p102⟩, ⟨123, .identity, .p102⟩, ⟨120, .identity, .p102⟩, ⟨121, .identity, .p102⟩, ⟨125, .identity, .p102⟩, ⟨124, .identity, .p102⟩, ⟨116, .swap34, .p102⟩, ⟨117, .swap34, .p102⟩, ⟨114, .swap34, .p102⟩, ⟨115, .swap34, .p102⟩, ⟨119, .swap34, .p102⟩, ⟨118, .swap34, .p102⟩,
    ⟨80, .swap34, .p102⟩, ⟨81, .swap34, .p102⟩, ⟨78, .swap34, .p102⟩, ⟨79, .swap34, .p102⟩, ⟨83, .swap34, .p102⟩, ⟨82, .swap34, .p102⟩, ⟨98, .swap34, .p102⟩, ⟨99, .swap34, .p102⟩, ⟨96, .swap34, .p102⟩, ⟨97, .swap34, .p102⟩, ⟨101, .swap34, .p102⟩, ⟨100, .swap34, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3168) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3168 ≤ case.val)
    (upper : case.val < 3216) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3191 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3199 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3215 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk66.correct

end Krenn.X5OrbitWitnessChunks.Chunk66
