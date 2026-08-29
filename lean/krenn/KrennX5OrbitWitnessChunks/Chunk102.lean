import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk102

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨286, .identity, .p201⟩, ⟨287, .identity, .p201⟩, ⟨283, .identity, .p201⟩, ⟨282, .identity, .p201⟩, ⟨285, .identity, .p201⟩, ⟨284, .identity, .p201⟩, ⟨292, .identity, .p201⟩, ⟨293, .identity, .p201⟩, ⟨289, .identity, .p201⟩, ⟨288, .identity, .p201⟩, ⟨291, .identity, .p201⟩, ⟨290, .identity, .p201⟩,
    ⟨184, .swap24, .p201⟩, ⟨185, .swap24, .p201⟩, ⟨181, .swap24, .p201⟩, ⟨180, .swap24, .p201⟩, ⟨183, .swap24, .p201⟩, ⟨182, .swap24, .p201⟩, ⟨94, .swap24, .p201⟩, ⟨95, .swap24, .p201⟩, ⟨91, .swap24, .p201⟩, ⟨90, .swap24, .p201⟩, ⟨93, .swap24, .p201⟩, ⟨92, .swap24, .p201⟩,
    ⟨280, .identity, .p201⟩, ⟨281, .identity, .p201⟩, ⟨277, .identity, .p201⟩, ⟨276, .identity, .p201⟩, ⟨279, .identity, .p201⟩, ⟨278, .identity, .p201⟩, ⟨244, .swap24, .p201⟩, ⟨245, .swap24, .p201⟩, ⟨241, .swap24, .p201⟩, ⟨240, .swap24, .p201⟩, ⟨243, .swap24, .p201⟩, ⟨242, .swap24, .p201⟩,
    ⟨250, .swap23, .p201⟩, ⟨251, .swap23, .p201⟩, ⟨247, .swap23, .p201⟩, ⟨246, .swap23, .p201⟩, ⟨249, .swap23, .p201⟩, ⟨248, .swap23, .p201⟩, ⟨256, .swap23, .p201⟩, ⟨257, .swap23, .p201⟩, ⟨253, .swap23, .p201⟩, ⟨252, .swap23, .p201⟩, ⟨255, .swap23, .p201⟩, ⟨254, .swap23, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4896) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4896 ≤ case.val)
    (upper : case.val < 4944) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4896 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4897 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4898 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4899 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4900 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4901 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4902 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4903 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4904 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4905 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4906 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4907 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4908 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4909 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4910 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4911 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4912 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4913 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4914 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4915 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4916 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4917 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4918 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4919 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4927 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4935 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4943 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk102.correct

end Krenn.X5OrbitWitnessChunks.Chunk102
