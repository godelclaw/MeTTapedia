import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk82

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨208, .cycle243, .p201⟩, ⟨209, .cycle243, .p201⟩, ⟨205, .cycle243, .p201⟩, ⟨204, .cycle243, .p201⟩, ⟨207, .cycle243, .p201⟩, ⟨206, .cycle243, .p201⟩, ⟨118, .cycle243, .p201⟩, ⟨119, .cycle243, .p201⟩, ⟨115, .cycle243, .p201⟩, ⟨114, .cycle243, .p201⟩, ⟨117, .cycle243, .p201⟩, ⟨116, .cycle243, .p201⟩,
    ⟨304, .cycle243, .p201⟩, ⟨305, .cycle243, .p201⟩, ⟨301, .cycle243, .p201⟩, ⟨300, .cycle243, .p201⟩, ⟨303, .cycle243, .p201⟩, ⟨302, .cycle243, .p201⟩, ⟨268, .cycle243, .p201⟩, ⟨269, .cycle243, .p201⟩, ⟨265, .cycle243, .p201⟩, ⟨264, .cycle243, .p201⟩, ⟨267, .cycle243, .p201⟩, ⟨266, .cycle243, .p201⟩,
    ⟨202, .swap23, .p201⟩, ⟨203, .swap23, .p201⟩, ⟨199, .swap23, .p201⟩, ⟨198, .swap23, .p201⟩, ⟨201, .swap23, .p201⟩, ⟨200, .swap23, .p201⟩, ⟨208, .swap23, .p201⟩, ⟨209, .swap23, .p201⟩, ⟨205, .swap23, .p201⟩, ⟨204, .swap23, .p201⟩, ⟨207, .swap23, .p201⟩, ⟨206, .swap23, .p201⟩,
    ⟨148, .swap24, .p201⟩, ⟨149, .swap24, .p201⟩, ⟨145, .swap24, .p201⟩, ⟨144, .swap24, .p201⟩, ⟨147, .swap24, .p201⟩, ⟨146, .swap24, .p201⟩, ⟨58, .swap24, .p201⟩, ⟨59, .swap24, .p201⟩, ⟨55, .swap24, .p201⟩, ⟨54, .swap24, .p201⟩, ⟨57, .swap24, .p201⟩, ⟨56, .swap24, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 3936) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 3936 ≤ case.val)
    (upper : case.val < 3984) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (3936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3943 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3951 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3959 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3967 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3975 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (3983 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk82.correct

end Krenn.X5OrbitWitnessChunks.Chunk82
