import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk57

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨236, .swap34, .p102⟩, ⟨237, .swap34, .p102⟩, ⟨234, .swap34, .p102⟩, ⟨235, .swap34, .p102⟩, ⟨239, .swap34, .p102⟩, ⟨238, .swap34, .p102⟩, ⟨254, .swap34, .p102⟩, ⟨255, .swap34, .p102⟩, ⟨252, .swap34, .p102⟩, ⟨253, .swap34, .p102⟩, ⟨257, .swap34, .p102⟩, ⟨256, .swap34, .p102⟩,
    ⟨86, .cycle243, .p102⟩, ⟨87, .cycle243, .p102⟩, ⟨84, .cycle243, .p102⟩, ⟨85, .cycle243, .p102⟩, ⟨89, .cycle243, .p102⟩, ⟨88, .cycle243, .p102⟩, ⟨176, .cycle243, .p102⟩, ⟨177, .cycle243, .p102⟩, ⟨174, .cycle243, .p102⟩, ⟨175, .cycle243, .p102⟩, ⟨179, .cycle243, .p102⟩, ⟨178, .cycle243, .p102⟩,
    ⟨272, .identity, .p102⟩, ⟨273, .identity, .p102⟩, ⟨270, .identity, .p102⟩, ⟨271, .identity, .p102⟩, ⟨275, .identity, .p102⟩, ⟨274, .identity, .p102⟩, ⟨266, .swap34, .p102⟩, ⟨267, .swap34, .p102⟩, ⟨264, .swap34, .p102⟩, ⟨265, .swap34, .p102⟩, ⟨269, .swap34, .p102⟩, ⟨268, .swap34, .p102⟩,
    ⟨230, .swap34, .p102⟩, ⟨231, .swap34, .p102⟩, ⟨228, .swap34, .p102⟩, ⟨229, .swap34, .p102⟩, ⟨233, .swap34, .p102⟩, ⟨232, .swap34, .p102⟩, ⟨248, .swap34, .p102⟩, ⟨249, .swap34, .p102⟩, ⟨246, .swap34, .p102⟩, ⟨247, .swap34, .p102⟩, ⟨251, .swap34, .p102⟩, ⟨250, .swap34, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2736) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2736 ≤ case.val)
    (upper : case.val < 2784) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2767 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2775 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2783 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk57.correct

end Krenn.X5OrbitWitnessChunks.Chunk57
