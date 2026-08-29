import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk63

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨68, .identity, .p102⟩, ⟨69, .identity, .p102⟩, ⟨66, .identity, .p102⟩, ⟨67, .identity, .p102⟩, ⟨71, .identity, .p102⟩, ⟨70, .identity, .p102⟩, ⟨74, .identity, .p102⟩, ⟨75, .identity, .p102⟩, ⟨72, .identity, .p102⟩, ⟨73, .identity, .p102⟩, ⟨77, .identity, .p102⟩, ⟨76, .identity, .p102⟩,
    ⟨14, .swap34, .p102⟩, ⟨15, .swap34, .p102⟩, ⟨12, .swap34, .p102⟩, ⟨13, .swap34, .p102⟩, ⟨17, .swap34, .p102⟩, ⟨16, .swap34, .p102⟩, ⟨44, .swap34, .p102⟩, ⟨45, .swap34, .p102⟩, ⟨42, .swap34, .p102⟩, ⟨43, .swap34, .p102⟩, ⟨47, .swap34, .p102⟩, ⟨46, .swap34, .p102⟩,
    ⟨86, .identity, .p102⟩, ⟨87, .identity, .p102⟩, ⟨84, .identity, .p102⟩, ⟨85, .identity, .p102⟩, ⟨89, .identity, .p102⟩, ⟨88, .identity, .p102⟩, ⟨80, .identity, .p102⟩, ⟨81, .identity, .p102⟩, ⟨78, .identity, .p102⟩, ⟨79, .identity, .p102⟩, ⟨83, .identity, .p102⟩, ⟨82, .identity, .p102⟩,
    ⟨74, .swap34, .p102⟩, ⟨75, .swap34, .p102⟩, ⟨72, .swap34, .p102⟩, ⟨73, .swap34, .p102⟩, ⟨77, .swap34, .p102⟩, ⟨76, .swap34, .p102⟩, ⟨92, .identity, .p102⟩, ⟨93, .identity, .p102⟩, ⟨90, .identity, .p102⟩, ⟨91, .identity, .p102⟩, ⟨95, .identity, .p102⟩, ⟨94, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3024) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3024 ≤ case.val)
    (upper : case.val < 3072) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3031 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3039 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3047 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3055 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3056 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3057 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3058 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3059 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3060 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3061 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3062 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3063 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3064 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3065 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3066 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3067 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3068 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3069 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3070 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3071 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk63.correct

end Krenn.X5OrbitWitnessChunks.Chunk63
