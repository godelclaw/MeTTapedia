import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk143

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨149, .swap24, .p210⟩, ⟨148, .swap24, .p210⟩, ⟨147, .swap24, .p210⟩, ⟨146, .swap24, .p210⟩, ⟨145, .swap24, .p210⟩, ⟨144, .swap24, .p210⟩, ⟨59, .swap24, .p210⟩, ⟨58, .swap24, .p210⟩, ⟨57, .swap24, .p210⟩, ⟨56, .swap24, .p210⟩, ⟨55, .swap24, .p210⟩, ⟨54, .swap24, .p210⟩,
    ⟨119, .swap23, .p210⟩, ⟨118, .swap23, .p210⟩, ⟨117, .swap23, .p210⟩, ⟨116, .swap23, .p210⟩, ⟨115, .swap23, .p210⟩, ⟨114, .swap23, .p210⟩, ⟨113, .swap23, .p210⟩, ⟨112, .swap23, .p210⟩, ⟨111, .swap23, .p210⟩, ⟨110, .swap23, .p210⟩, ⟨109, .swap23, .p210⟩, ⟨108, .swap23, .p210⟩,
    ⟨101, .cycle234, .p210⟩, ⟨100, .cycle234, .p210⟩, ⟨99, .cycle234, .p210⟩, ⟨98, .cycle234, .p210⟩, ⟨97, .cycle234, .p210⟩, ⟨96, .cycle234, .p210⟩, ⟨83, .cycle234, .p210⟩, ⟨82, .cycle234, .p210⟩, ⟨81, .cycle234, .p210⟩, ⟨80, .cycle234, .p210⟩, ⟨79, .cycle234, .p210⟩, ⟨78, .cycle234, .p210⟩,
    ⟨59, .cycle234, .p210⟩, ⟨58, .cycle234, .p210⟩, ⟨57, .cycle234, .p210⟩, ⟨56, .cycle234, .p210⟩, ⟨55, .cycle234, .p210⟩, ⟨54, .cycle234, .p210⟩, ⟨29, .swap24, .p210⟩, ⟨28, .swap24, .p210⟩, ⟨27, .swap24, .p210⟩, ⟨26, .swap24, .p210⟩, ⟨25, .swap24, .p210⟩, ⟨24, .swap24, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6864) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6864 ≤ case.val)
    (upper : case.val < 6912) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6871 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6879 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6887 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6895 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6903 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6911 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk143.correct

end Krenn.X5OrbitWitnessChunks.Chunk143
