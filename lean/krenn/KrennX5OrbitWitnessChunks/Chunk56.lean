import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk56

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨86, .swap23, .p102⟩, ⟨87, .swap23, .p102⟩, ⟨84, .swap23, .p102⟩, ⟨85, .swap23, .p102⟩, ⟨89, .swap23, .p102⟩, ⟨88, .swap23, .p102⟩, ⟨80, .swap23, .p102⟩, ⟨81, .swap23, .p102⟩, ⟨78, .swap23, .p102⟩, ⟨79, .swap23, .p102⟩, ⟨83, .swap23, .p102⟩, ⟨82, .swap23, .p102⟩,
    ⟨158, .swap23, .p102⟩, ⟨159, .swap23, .p102⟩, ⟨156, .swap23, .p102⟩, ⟨157, .swap23, .p102⟩, ⟨161, .swap23, .p102⟩, ⟨160, .swap23, .p102⟩, ⟨164, .swap23, .p102⟩, ⟨165, .swap23, .p102⟩, ⟨162, .swap23, .p102⟩, ⟨163, .swap23, .p102⟩, ⟨167, .swap23, .p102⟩, ⟨166, .swap23, .p102⟩,
    ⟨44, .swap24, .p102⟩, ⟨45, .swap24, .p102⟩, ⟨42, .swap24, .p102⟩, ⟨43, .swap24, .p102⟩, ⟨47, .swap24, .p102⟩, ⟨46, .swap24, .p102⟩, ⟨134, .swap24, .p102⟩, ⟨135, .swap24, .p102⟩, ⟨132, .swap24, .p102⟩, ⟨133, .swap24, .p102⟩, ⟨137, .swap24, .p102⟩, ⟨136, .swap24, .p102⟩,
    ⟨176, .swap23, .p102⟩, ⟨177, .swap23, .p102⟩, ⟨174, .swap23, .p102⟩, ⟨175, .swap23, .p102⟩, ⟨179, .swap23, .p102⟩, ⟨178, .swap23, .p102⟩, ⟨170, .swap23, .p102⟩, ⟨171, .swap23, .p102⟩, ⟨168, .swap23, .p102⟩, ⟨169, .swap23, .p102⟩, ⟨173, .swap23, .p102⟩, ⟨172, .swap23, .p102⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 2688) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 2688 ≤ case.val)
    (upper : case.val < 2736) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (2688 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2689 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2690 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2691 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2692 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2693 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2694 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2695 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2696 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2697 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2698 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2699 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2700 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2701 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2702 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2703 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2704 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2705 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2706 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2707 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2708 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2709 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2710 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2711 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2712 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2713 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2714 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2715 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2716 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2717 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2718 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2719 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2720 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2721 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2722 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2723 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2724 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2725 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2726 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2727 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2735 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk56.correct

end Krenn.X5OrbitWitnessChunks.Chunk56
