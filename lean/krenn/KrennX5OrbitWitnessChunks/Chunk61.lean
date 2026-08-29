import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk61

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨50, .swap24, .p102⟩, ⟨51, .swap24, .p102⟩, ⟨48, .swap24, .p102⟩, ⟨49, .swap24, .p102⟩, ⟨53, .swap24, .p102⟩, ⟨52, .swap24, .p102⟩, ⟨140, .swap24, .p102⟩, ⟨141, .swap24, .p102⟩, ⟨138, .swap24, .p102⟩, ⟨139, .swap24, .p102⟩, ⟨143, .swap24, .p102⟩, ⟨142, .swap24, .p102⟩,
    ⟨194, .swap23, .p102⟩, ⟨195, .swap23, .p102⟩, ⟨192, .swap23, .p102⟩, ⟨193, .swap23, .p102⟩, ⟨197, .swap23, .p102⟩, ⟨196, .swap23, .p102⟩, ⟨188, .swap23, .p102⟩, ⟨189, .swap23, .p102⟩, ⟨186, .swap23, .p102⟩, ⟨187, .swap23, .p102⟩, ⟨191, .swap23, .p102⟩, ⟨190, .swap23, .p102⟩,
    ⟨254, .cycle243, .p102⟩, ⟨255, .cycle243, .p102⟩, ⟨252, .cycle243, .p102⟩, ⟨253, .cycle243, .p102⟩, ⟨257, .cycle243, .p102⟩, ⟨256, .cycle243, .p102⟩, ⟨290, .swap34, .p102⟩, ⟨291, .swap34, .p102⟩, ⟨288, .swap34, .p102⟩, ⟨289, .swap34, .p102⟩, ⟨293, .swap34, .p102⟩, ⟨292, .swap34, .p102⟩,
    ⟨104, .cycle243, .p102⟩, ⟨105, .cycle243, .p102⟩, ⟨102, .cycle243, .p102⟩, ⟨103, .cycle243, .p102⟩, ⟨107, .cycle243, .p102⟩, ⟨106, .cycle243, .p102⟩, ⟨194, .cycle243, .p102⟩, ⟨195, .cycle243, .p102⟩, ⟨192, .cycle243, .p102⟩, ⟨193, .cycle243, .p102⟩, ⟨197, .cycle243, .p102⟩, ⟨196, .cycle243, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2928) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2928 ≤ case.val)
    (upper : case.val < 2976) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2935 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2943 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2951 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2959 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2967 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2975 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk61.correct

end Krenn.X5OrbitWitnessChunks.Chunk61
