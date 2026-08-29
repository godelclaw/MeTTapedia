import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk19

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨168, .cycle234, .p012⟩, ⟨169, .cycle234, .p012⟩, ⟨170, .cycle234, .p012⟩, ⟨171, .cycle234, .p012⟩, ⟨172, .cycle234, .p012⟩, ⟨173, .cycle234, .p012⟩, ⟨186, .cycle234, .p012⟩, ⟨187, .cycle234, .p012⟩, ⟨188, .cycle234, .p012⟩, ⟨189, .cycle234, .p012⟩, ⟨190, .cycle234, .p012⟩, ⟨191, .cycle234, .p012⟩,
    ⟨198, .swap23, .p012⟩, ⟨199, .swap23, .p012⟩, ⟨200, .swap23, .p012⟩, ⟨201, .swap23, .p012⟩, ⟨202, .swap23, .p012⟩, ⟨203, .swap23, .p012⟩, ⟨204, .swap23, .p012⟩, ⟨205, .swap23, .p012⟩, ⟨206, .swap23, .p012⟩, ⟨207, .swap23, .p012⟩, ⟨208, .swap23, .p012⟩, ⟨209, .swap23, .p012⟩,
    ⟨78, .swap24, .p012⟩, ⟨79, .swap24, .p012⟩, ⟨80, .swap24, .p012⟩, ⟨81, .swap24, .p012⟩, ⟨82, .swap24, .p012⟩, ⟨83, .swap24, .p012⟩, ⟨168, .swap24, .p012⟩, ⟨169, .swap24, .p012⟩, ⟨170, .swap24, .p012⟩, ⟨171, .swap24, .p012⟩, ⟨172, .swap24, .p012⟩, ⟨173, .swap24, .p012⟩,
    ⟨228, .swap24, .p012⟩, ⟨229, .swap24, .p012⟩, ⟨230, .swap24, .p012⟩, ⟨231, .swap24, .p012⟩, ⟨232, .swap24, .p012⟩, ⟨233, .swap24, .p012⟩, ⟨246, .cycle234, .p012⟩, ⟨247, .cycle234, .p012⟩, ⟨248, .cycle234, .p012⟩, ⟨249, .cycle234, .p012⟩, ⟨250, .cycle234, .p012⟩, ⟨251, .cycle234, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 912) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 912 ≤ case.val)
    (upper : case.val < 960) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (919 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (927 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (935 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (943 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (951 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (959 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk19.correct

end Krenn.X5OrbitWitnessChunks.Chunk19
