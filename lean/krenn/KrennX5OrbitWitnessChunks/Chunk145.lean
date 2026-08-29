import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk145

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨287, .swap34, .p210⟩, ⟨286, .swap34, .p210⟩, ⟨285, .swap34, .p210⟩, ⟨284, .swap34, .p210⟩, ⟨283, .swap34, .p210⟩, ⟨282, .swap34, .p210⟩, ⟨251, .cycle243, .p210⟩, ⟨250, .cycle243, .p210⟩, ⟨249, .cycle243, .p210⟩, ⟨248, .cycle243, .p210⟩, ⟨247, .cycle243, .p210⟩, ⟨246, .cycle243, .p210⟩,
    ⟨191, .cycle243, .p210⟩, ⟨190, .cycle243, .p210⟩, ⟨189, .cycle243, .p210⟩, ⟨188, .cycle243, .p210⟩, ⟨187, .cycle243, .p210⟩, ⟨186, .cycle243, .p210⟩, ⟨101, .cycle243, .p210⟩, ⟨100, .cycle243, .p210⟩, ⟨99, .cycle243, .p210⟩, ⟨98, .cycle243, .p210⟩, ⟨97, .cycle243, .p210⟩, ⟨96, .cycle243, .p210⟩,
    ⟨293, .identity, .p210⟩, ⟨292, .identity, .p210⟩, ⟨291, .identity, .p210⟩, ⟨290, .identity, .p210⟩, ⟨289, .identity, .p210⟩, ⟨288, .identity, .p210⟩, ⟨287, .identity, .p210⟩, ⟨286, .identity, .p210⟩, ⟨285, .identity, .p210⟩, ⟨284, .identity, .p210⟩, ⟨283, .identity, .p210⟩, ⟨282, .identity, .p210⟩,
    ⟨281, .identity, .p210⟩, ⟨280, .identity, .p210⟩, ⟨279, .identity, .p210⟩, ⟨278, .identity, .p210⟩, ⟨277, .identity, .p210⟩, ⟨276, .identity, .p210⟩, ⟨245, .swap24, .p210⟩, ⟨244, .swap24, .p210⟩, ⟨243, .swap24, .p210⟩, ⟨242, .swap24, .p210⟩, ⟨241, .swap24, .p210⟩, ⟨240, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6960) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6960 ≤ case.val)
    (upper : case.val < 7008) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6967 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6975 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6983 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6991 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6999 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7007 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk145.correct

end Krenn.X5OrbitWitnessChunks.Chunk145
