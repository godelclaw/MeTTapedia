import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk64

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨20, .swap34, .p102⟩, ⟨21, .swap34, .p102⟩, ⟨18, .swap34, .p102⟩, ⟨19, .swap34, .p102⟩, ⟨23, .swap34, .p102⟩, ⟨22, .swap34, .p102⟩, ⟨50, .swap34, .p102⟩, ⟨51, .swap34, .p102⟩, ⟨48, .swap34, .p102⟩, ⟨49, .swap34, .p102⟩, ⟨53, .swap34, .p102⟩, ⟨52, .swap34, .p102⟩,
    ⟨104, .identity, .p102⟩, ⟨105, .identity, .p102⟩, ⟨102, .identity, .p102⟩, ⟨103, .identity, .p102⟩, ⟨107, .identity, .p102⟩, ⟨106, .identity, .p102⟩, ⟨98, .identity, .p102⟩, ⟨99, .identity, .p102⟩, ⟨96, .identity, .p102⟩, ⟨97, .identity, .p102⟩, ⟨101, .identity, .p102⟩, ⟨100, .identity, .p102⟩,
    ⟨14, .identity, .p102⟩, ⟨15, .identity, .p102⟩, ⟨12, .identity, .p102⟩, ⟨13, .identity, .p102⟩, ⟨17, .identity, .p102⟩, ⟨16, .identity, .p102⟩, ⟨20, .identity, .p102⟩, ⟨21, .identity, .p102⟩, ⟨18, .identity, .p102⟩, ⟨19, .identity, .p102⟩, ⟨23, .identity, .p102⟩, ⟨22, .identity, .p102⟩,
    ⟨2, .identity, .p102⟩, ⟨3, .identity, .p102⟩, ⟨0, .identity, .p102⟩, ⟨1, .identity, .p102⟩, ⟨5, .identity, .p102⟩, ⟨4, .identity, .p102⟩, ⟨8, .identity, .p102⟩, ⟨9, .identity, .p102⟩, ⟨6, .identity, .p102⟩, ⟨7, .identity, .p102⟩, ⟨11, .identity, .p102⟩, ⟨10, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3072) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3072 ≤ case.val)
    (upper : case.val < 3120) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3072 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3073 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3074 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3075 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3076 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3077 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3078 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3079 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3080 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3081 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3082 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3083 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3084 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3085 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3086 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3087 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3088 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3089 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3090 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3091 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3092 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3093 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3094 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3095 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3096 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3097 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3098 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3099 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3100 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3101 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3102 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3103 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3104 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3105 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3106 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3107 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3108 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3109 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3110 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3111 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3112 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3113 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3114 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3115 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3116 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3117 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3118 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3119 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk64.correct

end Krenn.X5OrbitWitnessChunks.Chunk64
