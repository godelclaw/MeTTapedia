import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk21

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨108, .swap24, .p012⟩, ⟨109, .swap24, .p012⟩, ⟨110, .swap24, .p012⟩, ⟨111, .swap24, .p012⟩, ⟨112, .swap24, .p012⟩, ⟨113, .swap24, .p012⟩, ⟨198, .swap24, .p012⟩, ⟨199, .swap24, .p012⟩, ⟨200, .swap24, .p012⟩, ⟨201, .swap24, .p012⟩, ⟨202, .swap24, .p012⟩, ⟨203, .swap24, .p012⟩,
    ⟨258, .swap24, .p012⟩, ⟨259, .swap24, .p012⟩, ⟨260, .swap24, .p012⟩, ⟨261, .swap24, .p012⟩, ⟨262, .swap24, .p012⟩, ⟨263, .swap24, .p012⟩, ⟨294, .swap24, .p012⟩, ⟨295, .swap24, .p012⟩, ⟨296, .swap24, .p012⟩, ⟨297, .swap24, .p012⟩, ⟨298, .swap24, .p012⟩, ⟨299, .swap24, .p012⟩,
    ⟨312, .identity, .p012⟩, ⟨313, .identity, .p012⟩, ⟨314, .identity, .p012⟩, ⟨315, .identity, .p012⟩, ⟨316, .identity, .p012⟩, ⟨317, .identity, .p012⟩, ⟨318, .identity, .p012⟩, ⟨319, .identity, .p012⟩, ⟨320, .identity, .p012⟩, ⟨321, .identity, .p012⟩, ⟨322, .identity, .p012⟩, ⟨323, .identity, .p012⟩,
    ⟨114, .cycle243, .p012⟩, ⟨115, .cycle243, .p012⟩, ⟨116, .cycle243, .p012⟩, ⟨117, .cycle243, .p012⟩, ⟨118, .cycle243, .p012⟩, ⟨119, .cycle243, .p012⟩, ⟨204, .cycle243, .p012⟩, ⟨205, .cycle243, .p012⟩, ⟨206, .cycle243, .p012⟩, ⟨207, .cycle243, .p012⟩, ⟨208, .cycle243, .p012⟩, ⟨209, .cycle243, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1008) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1008 ≤ case.val)
    (upper : case.val < 1056) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1015 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1016 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1017 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1018 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1019 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1020 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1021 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1022 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1023 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1024 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1025 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1026 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1027 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1028 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1029 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1030 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1031 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1032 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1033 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1034 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1035 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1036 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1037 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1038 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1039 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1040 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1041 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1042 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1043 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1044 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1045 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1046 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1047 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1048 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1049 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1050 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1051 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1052 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1053 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1054 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1055 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk21.correct

end Krenn.X5OrbitWitnessChunks.Chunk21
