import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk58

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨80, .cycle243, .p102⟩, ⟨81, .cycle243, .p102⟩, ⟨78, .cycle243, .p102⟩, ⟨79, .cycle243, .p102⟩, ⟨83, .cycle243, .p102⟩, ⟨82, .cycle243, .p102⟩, ⟨170, .cycle243, .p102⟩, ⟨171, .cycle243, .p102⟩, ⟨168, .cycle243, .p102⟩, ⟨169, .cycle243, .p102⟩, ⟨173, .cycle243, .p102⟩, ⟨172, .cycle243, .p102⟩,
    ⟨266, .identity, .p102⟩, ⟨267, .identity, .p102⟩, ⟨264, .identity, .p102⟩, ⟨265, .identity, .p102⟩, ⟨269, .identity, .p102⟩, ⟨268, .identity, .p102⟩, ⟨260, .identity, .p102⟩, ⟨261, .identity, .p102⟩, ⟨258, .identity, .p102⟩, ⟨259, .identity, .p102⟩, ⟨263, .identity, .p102⟩, ⟨262, .identity, .p102⟩,
    ⟨224, .swap24, .p102⟩, ⟨225, .swap24, .p102⟩, ⟨222, .swap24, .p102⟩, ⟨223, .swap24, .p102⟩, ⟨227, .swap24, .p102⟩, ⟨226, .swap24, .p102⟩, ⟨242, .swap23, .p102⟩, ⟨243, .swap23, .p102⟩, ⟨240, .swap23, .p102⟩, ⟨241, .swap23, .p102⟩, ⟨245, .swap23, .p102⟩, ⟨244, .swap23, .p102⟩,
    ⟨74, .swap24, .p102⟩, ⟨75, .swap24, .p102⟩, ⟨72, .swap24, .p102⟩, ⟨73, .swap24, .p102⟩, ⟨77, .swap24, .p102⟩, ⟨76, .swap24, .p102⟩, ⟨164, .swap24, .p102⟩, ⟨165, .swap24, .p102⟩, ⟨162, .swap24, .p102⟩, ⟨163, .swap24, .p102⟩, ⟨167, .swap24, .p102⟩, ⟨166, .swap24, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2784) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2784 ≤ case.val)
    (upper : case.val < 2832) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2791 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2799 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2807 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2808 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2809 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2810 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2811 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2812 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2813 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2814 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2815 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2816 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2817 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2818 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2819 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2820 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2821 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2822 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2823 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2824 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2825 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2826 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2827 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2828 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2829 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2830 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2831 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk58.correct

end Krenn.X5OrbitWitnessChunks.Chunk58
