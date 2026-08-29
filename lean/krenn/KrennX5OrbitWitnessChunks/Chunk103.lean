import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk103

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨166, .swap24, .p201⟩, ⟨167, .swap24, .p201⟩, ⟨163, .swap24, .p201⟩, ⟨162, .swap24, .p201⟩, ⟨165, .swap24, .p201⟩, ⟨164, .swap24, .p201⟩, ⟨76, .swap24, .p201⟩, ⟨77, .swap24, .p201⟩, ⟨73, .swap24, .p201⟩, ⟨72, .swap24, .p201⟩, ⟨75, .swap24, .p201⟩, ⟨74, .swap24, .p201⟩,
    ⟨244, .swap23, .p201⟩, ⟨245, .swap23, .p201⟩, ⟨241, .swap23, .p201⟩, ⟨240, .swap23, .p201⟩, ⟨243, .swap23, .p201⟩, ⟨242, .swap23, .p201⟩, ⟨226, .swap24, .p201⟩, ⟨227, .swap24, .p201⟩, ⟨223, .swap24, .p201⟩, ⟨222, .swap24, .p201⟩, ⟨225, .swap24, .p201⟩, ⟨224, .swap24, .p201⟩,
    ⟨262, .identity, .p201⟩, ⟨263, .identity, .p201⟩, ⟨259, .identity, .p201⟩, ⟨258, .identity, .p201⟩, ⟨261, .identity, .p201⟩, ⟨260, .identity, .p201⟩, ⟨268, .identity, .p201⟩, ⟨269, .identity, .p201⟩, ⟨265, .identity, .p201⟩, ⟨264, .identity, .p201⟩, ⟨267, .identity, .p201⟩, ⟨266, .identity, .p201⟩,
    ⟨172, .cycle243, .p201⟩, ⟨173, .cycle243, .p201⟩, ⟨169, .cycle243, .p201⟩, ⟨168, .cycle243, .p201⟩, ⟨171, .cycle243, .p201⟩, ⟨170, .cycle243, .p201⟩, ⟨82, .cycle243, .p201⟩, ⟨83, .cycle243, .p201⟩, ⟨79, .cycle243, .p201⟩, ⟨78, .cycle243, .p201⟩, ⟨81, .cycle243, .p201⟩, ⟨80, .cycle243, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4944) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4944 ≤ case.val)
    (upper : case.val < 4992) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4951 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4959 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4967 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4975 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4983 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4991 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk103.correct

end Krenn.X5OrbitWitnessChunks.Chunk103
