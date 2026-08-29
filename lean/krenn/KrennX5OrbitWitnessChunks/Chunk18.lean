import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk18

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨24, .swap24, .p012⟩, ⟨25, .swap24, .p012⟩, ⟨26, .swap24, .p012⟩, ⟨27, .swap24, .p012⟩, ⟨28, .swap24, .p012⟩, ⟨29, .swap24, .p012⟩, ⟨54, .cycle234, .p012⟩, ⟨55, .cycle234, .p012⟩, ⟨56, .cycle234, .p012⟩, ⟨57, .cycle234, .p012⟩, ⟨58, .cycle234, .p012⟩, ⟨59, .cycle234, .p012⟩,
    ⟨78, .cycle234, .p012⟩, ⟨79, .cycle234, .p012⟩, ⟨80, .cycle234, .p012⟩, ⟨81, .cycle234, .p012⟩, ⟨82, .cycle234, .p012⟩, ⟨83, .cycle234, .p012⟩, ⟨96, .cycle234, .p012⟩, ⟨97, .cycle234, .p012⟩, ⟨98, .cycle234, .p012⟩, ⟨99, .cycle234, .p012⟩, ⟨100, .cycle234, .p012⟩, ⟨101, .cycle234, .p012⟩,
    ⟨108, .swap23, .p012⟩, ⟨109, .swap23, .p012⟩, ⟨110, .swap23, .p012⟩, ⟨111, .swap23, .p012⟩, ⟨112, .swap23, .p012⟩, ⟨113, .swap23, .p012⟩, ⟨114, .swap23, .p012⟩, ⟨115, .swap23, .p012⟩, ⟨116, .swap23, .p012⟩, ⟨117, .swap23, .p012⟩, ⟨118, .swap23, .p012⟩, ⟨119, .swap23, .p012⟩,
    ⟨54, .swap24, .p012⟩, ⟨55, .swap24, .p012⟩, ⟨56, .swap24, .p012⟩, ⟨57, .swap24, .p012⟩, ⟨58, .swap24, .p012⟩, ⟨59, .swap24, .p012⟩, ⟨144, .swap24, .p012⟩, ⟨145, .swap24, .p012⟩, ⟨146, .swap24, .p012⟩, ⟨147, .swap24, .p012⟩, ⟨148, .swap24, .p012⟩, ⟨149, .swap24, .p012⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 864) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 864 ≤ case.val)
    (upper : case.val < 912) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (871 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (879 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (887 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (895 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (903 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (911 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk18.correct

end Krenn.X5OrbitWitnessChunks.Chunk18
