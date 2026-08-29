import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk62

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨308, .identity, .p102⟩, ⟨309, .identity, .p102⟩, ⟨306, .identity, .p102⟩, ⟨307, .identity, .p102⟩, ⟨311, .identity, .p102⟩, ⟨310, .identity, .p102⟩, ⟨302, .swap34, .p102⟩, ⟨303, .swap34, .p102⟩, ⟨300, .swap34, .p102⟩, ⟨301, .swap34, .p102⟩, ⟨305, .swap34, .p102⟩, ⟨304, .swap34, .p102⟩,
    ⟨248, .cycle243, .p102⟩, ⟨249, .cycle243, .p102⟩, ⟨246, .cycle243, .p102⟩, ⟨247, .cycle243, .p102⟩, ⟨251, .cycle243, .p102⟩, ⟨250, .cycle243, .p102⟩, ⟨284, .swap34, .p102⟩, ⟨285, .swap34, .p102⟩, ⟨282, .swap34, .p102⟩, ⟨283, .swap34, .p102⟩, ⟨287, .swap34, .p102⟩, ⟨286, .swap34, .p102⟩,
    ⟨98, .cycle243, .p102⟩, ⟨99, .cycle243, .p102⟩, ⟨96, .cycle243, .p102⟩, ⟨97, .cycle243, .p102⟩, ⟨101, .cycle243, .p102⟩, ⟨100, .cycle243, .p102⟩, ⟨188, .cycle243, .p102⟩, ⟨189, .cycle243, .p102⟩, ⟨186, .cycle243, .p102⟩, ⟨187, .cycle243, .p102⟩, ⟨191, .cycle243, .p102⟩, ⟨190, .cycle243, .p102⟩,
    ⟨302, .identity, .p102⟩, ⟨303, .identity, .p102⟩, ⟨300, .identity, .p102⟩, ⟨301, .identity, .p102⟩, ⟨305, .identity, .p102⟩, ⟨304, .identity, .p102⟩, ⟨296, .identity, .p102⟩, ⟨297, .identity, .p102⟩, ⟨294, .identity, .p102⟩, ⟨295, .identity, .p102⟩, ⟨299, .identity, .p102⟩, ⟨298, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2976) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2976 ≤ case.val)
    (upper : case.val < 3024) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2983 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2991 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2999 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3007 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3015 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3023 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk62.correct

end Krenn.X5OrbitWitnessChunks.Chunk62
