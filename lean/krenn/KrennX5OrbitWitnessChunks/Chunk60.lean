import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk60

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨74, .cycle234, .p102⟩, ⟨75, .cycle234, .p102⟩, ⟨72, .cycle234, .p102⟩, ⟨73, .cycle234, .p102⟩, ⟨77, .cycle234, .p102⟩, ⟨76, .cycle234, .p102⟩, ⟨92, .swap23, .p102⟩, ⟨93, .swap23, .p102⟩, ⟨90, .swap23, .p102⟩, ⟨91, .swap23, .p102⟩, ⟨95, .swap23, .p102⟩, ⟨94, .swap23, .p102⟩,
    ⟨20, .swap24, .p102⟩, ⟨21, .swap24, .p102⟩, ⟨18, .swap24, .p102⟩, ⟨19, .swap24, .p102⟩, ⟨23, .swap24, .p102⟩, ⟨22, .swap24, .p102⟩, ⟨50, .cycle234, .p102⟩, ⟨51, .cycle234, .p102⟩, ⟨48, .cycle234, .p102⟩, ⟨49, .cycle234, .p102⟩, ⟨53, .cycle234, .p102⟩, ⟨52, .cycle234, .p102⟩,
    ⟨104, .swap23, .p102⟩, ⟨105, .swap23, .p102⟩, ⟨102, .swap23, .p102⟩, ⟨103, .swap23, .p102⟩, ⟨107, .swap23, .p102⟩, ⟨106, .swap23, .p102⟩, ⟨98, .swap23, .p102⟩, ⟨99, .swap23, .p102⟩, ⟨96, .swap23, .p102⟩, ⟨97, .swap23, .p102⟩, ⟨101, .swap23, .p102⟩, ⟨100, .swap23, .p102⟩,
    ⟨164, .cycle234, .p102⟩, ⟨165, .cycle234, .p102⟩, ⟨162, .cycle234, .p102⟩, ⟨163, .cycle234, .p102⟩, ⟨167, .cycle234, .p102⟩, ⟨166, .cycle234, .p102⟩, ⟨182, .swap23, .p102⟩, ⟨183, .swap23, .p102⟩, ⟨180, .swap23, .p102⟩, ⟨181, .swap23, .p102⟩, ⟨185, .swap23, .p102⟩, ⟨184, .swap23, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2880) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2880 ≤ case.val)
    (upper : case.val < 2928) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2887 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2895 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2903 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2911 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2919 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2927 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk60.correct

end Krenn.X5OrbitWitnessChunks.Chunk60
