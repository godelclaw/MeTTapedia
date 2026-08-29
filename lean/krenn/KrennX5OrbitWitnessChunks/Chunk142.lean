import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk142

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨251, .cycle234, .p210⟩, ⟨250, .cycle234, .p210⟩, ⟨249, .cycle234, .p210⟩, ⟨248, .cycle234, .p210⟩, ⟨247, .cycle234, .p210⟩, ⟨246, .cycle234, .p210⟩, ⟨233, .swap24, .p210⟩, ⟨232, .swap24, .p210⟩, ⟨231, .swap24, .p210⟩, ⟨230, .swap24, .p210⟩, ⟨229, .swap24, .p210⟩, ⟨228, .swap24, .p210⟩,
    ⟨173, .swap24, .p210⟩, ⟨172, .swap24, .p210⟩, ⟨171, .swap24, .p210⟩, ⟨170, .swap24, .p210⟩, ⟨169, .swap24, .p210⟩, ⟨168, .swap24, .p210⟩, ⟨83, .swap24, .p210⟩, ⟨82, .swap24, .p210⟩, ⟨81, .swap24, .p210⟩, ⟨80, .swap24, .p210⟩, ⟨79, .swap24, .p210⟩, ⟨78, .swap24, .p210⟩,
    ⟨209, .swap23, .p210⟩, ⟨208, .swap23, .p210⟩, ⟨207, .swap23, .p210⟩, ⟨206, .swap23, .p210⟩, ⟨205, .swap23, .p210⟩, ⟨204, .swap23, .p210⟩, ⟨203, .swap23, .p210⟩, ⟨202, .swap23, .p210⟩, ⟨201, .swap23, .p210⟩, ⟨200, .swap23, .p210⟩, ⟨199, .swap23, .p210⟩, ⟨198, .swap23, .p210⟩,
    ⟨191, .cycle234, .p210⟩, ⟨190, .cycle234, .p210⟩, ⟨189, .cycle234, .p210⟩, ⟨188, .cycle234, .p210⟩, ⟨187, .cycle234, .p210⟩, ⟨186, .cycle234, .p210⟩, ⟨173, .cycle234, .p210⟩, ⟨172, .cycle234, .p210⟩, ⟨171, .cycle234, .p210⟩, ⟨170, .cycle234, .p210⟩, ⟨169, .cycle234, .p210⟩, ⟨168, .cycle234, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6816) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6816 ≤ case.val)
    (upper : case.val < 6864) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6823 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6831 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6839 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6847 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6855 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6863 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk142.correct

end Krenn.X5OrbitWitnessChunks.Chunk142
