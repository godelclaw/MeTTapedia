import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk123

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨303, .cycle243, .p120⟩, ⟨302, .cycle243, .p120⟩, ⟨305, .cycle243, .p120⟩, ⟨304, .cycle243, .p120⟩, ⟨300, .cycle243, .p120⟩, ⟨301, .cycle243, .p120⟩, ⟨267, .cycle243, .p120⟩, ⟨266, .cycle243, .p120⟩, ⟨269, .cycle243, .p120⟩, ⟨268, .cycle243, .p120⟩, ⟨264, .cycle243, .p120⟩, ⟨265, .cycle243, .p120⟩,
    ⟨327, .identity, .p120⟩, ⟨326, .identity, .p120⟩, ⟨329, .identity, .p120⟩, ⟨328, .identity, .p120⟩, ⟨324, .identity, .p120⟩, ⟨325, .identity, .p120⟩, ⟨321, .swap34, .p120⟩, ⟨320, .swap34, .p120⟩, ⟨323, .swap34, .p120⟩, ⟨322, .swap34, .p120⟩, ⟨318, .swap34, .p120⟩, ⟨319, .swap34, .p120⟩,
    ⟨117, .cycle243, .p120⟩, ⟨116, .cycle243, .p120⟩, ⟨119, .cycle243, .p120⟩, ⟨118, .cycle243, .p120⟩, ⟨114, .cycle243, .p120⟩, ⟨115, .cycle243, .p120⟩, ⟨207, .cycle243, .p120⟩, ⟨206, .cycle243, .p120⟩, ⟨209, .cycle243, .p120⟩, ⟨208, .cycle243, .p120⟩, ⟨204, .cycle243, .p120⟩, ⟨205, .cycle243, .p120⟩,
    ⟨297, .swap24, .p120⟩, ⟨296, .swap24, .p120⟩, ⟨299, .swap24, .p120⟩, ⟨298, .swap24, .p120⟩, ⟨294, .swap24, .p120⟩, ⟨295, .swap24, .p120⟩, ⟨261, .swap24, .p120⟩, ⟨260, .swap24, .p120⟩, ⟨263, .swap24, .p120⟩, ⟨262, .swap24, .p120⟩, ⟨258, .swap24, .p120⟩, ⟨259, .swap24, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5904) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5904 ≤ case.val)
    (upper : case.val < 5952) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5911 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5919 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5927 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5935 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5943 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5951 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk123.correct

end Krenn.X5OrbitWitnessChunks.Chunk123
