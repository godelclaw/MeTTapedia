import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk59

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨254, .swap23, .p102⟩, ⟨255, .swap23, .p102⟩, ⟨252, .swap23, .p102⟩, ⟨253, .swap23, .p102⟩, ⟨257, .swap23, .p102⟩, ⟨256, .swap23, .p102⟩, ⟨248, .swap23, .p102⟩, ⟨249, .swap23, .p102⟩, ⟨246, .swap23, .p102⟩, ⟨247, .swap23, .p102⟩, ⟨251, .swap23, .p102⟩, ⟨250, .swap23, .p102⟩,
    ⟨242, .swap24, .p102⟩, ⟨243, .swap24, .p102⟩, ⟨240, .swap24, .p102⟩, ⟨241, .swap24, .p102⟩, ⟨245, .swap24, .p102⟩, ⟨244, .swap24, .p102⟩, ⟨278, .identity, .p102⟩, ⟨279, .identity, .p102⟩, ⟨276, .identity, .p102⟩, ⟨277, .identity, .p102⟩, ⟨281, .identity, .p102⟩, ⟨280, .identity, .p102⟩,
    ⟨92, .swap24, .p102⟩, ⟨93, .swap24, .p102⟩, ⟨90, .swap24, .p102⟩, ⟨91, .swap24, .p102⟩, ⟨95, .swap24, .p102⟩, ⟨94, .swap24, .p102⟩, ⟨182, .swap24, .p102⟩, ⟨183, .swap24, .p102⟩, ⟨180, .swap24, .p102⟩, ⟨181, .swap24, .p102⟩, ⟨185, .swap24, .p102⟩, ⟨184, .swap24, .p102⟩,
    ⟨290, .identity, .p102⟩, ⟨291, .identity, .p102⟩, ⟨288, .identity, .p102⟩, ⟨289, .identity, .p102⟩, ⟨293, .identity, .p102⟩, ⟨292, .identity, .p102⟩, ⟨284, .identity, .p102⟩, ⟨285, .identity, .p102⟩, ⟨282, .identity, .p102⟩, ⟨283, .identity, .p102⟩, ⟨287, .identity, .p102⟩, ⟨286, .identity, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2832) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2832 ≤ case.val)
    (upper : case.val < 2880) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2832 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2833 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2834 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2835 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2836 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2837 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2838 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2839 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2840 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2841 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2842 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2843 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2844 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2845 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2846 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2847 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2855 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2863 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2871 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2879 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk59.correct

end Krenn.X5OrbitWitnessChunks.Chunk59
