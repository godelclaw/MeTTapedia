import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk124

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨321, .identity, .p120⟩, ⟨320, .identity, .p120⟩, ⟨323, .identity, .p120⟩, ⟨322, .identity, .p120⟩, ⟨318, .identity, .p120⟩, ⟨319, .identity, .p120⟩, ⟨315, .identity, .p120⟩, ⟨314, .identity, .p120⟩, ⟨317, .identity, .p120⟩, ⟨316, .identity, .p120⟩, ⟨312, .identity, .p120⟩, ⟨313, .identity, .p120⟩,
    ⟨111, .swap24, .p120⟩, ⟨110, .swap24, .p120⟩, ⟨113, .swap24, .p120⟩, ⟨112, .swap24, .p120⟩, ⟨108, .swap24, .p120⟩, ⟨109, .swap24, .p120⟩, ⟨201, .swap24, .p120⟩, ⟨200, .swap24, .p120⟩, ⟨203, .swap24, .p120⟩, ⟨202, .swap24, .p120⟩, ⟨198, .swap24, .p120⟩, ⟨199, .swap24, .p120⟩,
    ⟨99, .cycle234, .p120⟩, ⟨98, .cycle234, .p120⟩, ⟨101, .cycle234, .p120⟩, ⟨100, .cycle234, .p120⟩, ⟨96, .cycle234, .p120⟩, ⟨97, .cycle234, .p120⟩, ⟨81, .cycle234, .p120⟩, ⟨80, .cycle234, .p120⟩, ⟨83, .cycle234, .p120⟩, ⟨82, .cycle234, .p120⟩, ⟨78, .cycle234, .p120⟩, ⟨79, .cycle234, .p120⟩,
    ⟨117, .swap23, .p120⟩, ⟨116, .swap23, .p120⟩, ⟨119, .swap23, .p120⟩, ⟨118, .swap23, .p120⟩, ⟨114, .swap23, .p120⟩, ⟨115, .swap23, .p120⟩, ⟨111, .swap23, .p120⟩, ⟨110, .swap23, .p120⟩, ⟨113, .swap23, .p120⟩, ⟨112, .swap23, .p120⟩, ⟨108, .swap23, .p120⟩, ⟨109, .swap23, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5952) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5952 ≤ case.val)
    (upper : case.val < 6000) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5959 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5967 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5975 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5983 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5991 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5999 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk124.correct

end Krenn.X5OrbitWitnessChunks.Chunk124
