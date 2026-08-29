import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk161

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨41, .identity, .p210⟩, ⟨40, .identity, .p210⟩, ⟨39, .identity, .p210⟩, ⟨38, .identity, .p210⟩, ⟨37, .identity, .p210⟩, ⟨36, .identity, .p210⟩, ⟨11, .swap34, .p210⟩, ⟨10, .swap34, .p210⟩, ⟨9, .swap34, .p210⟩, ⟨8, .swap34, .p210⟩, ⟨7, .swap34, .p210⟩, ⟨6, .swap34, .p210⟩,
    ⟨35, .identity, .p210⟩, ⟨34, .identity, .p210⟩, ⟨33, .identity, .p210⟩, ⟨32, .identity, .p210⟩, ⟨31, .identity, .p210⟩, ⟨30, .identity, .p210⟩, ⟨29, .identity, .p210⟩, ⟨28, .identity, .p210⟩, ⟨27, .identity, .p210⟩, ⟨26, .identity, .p210⟩, ⟨25, .identity, .p210⟩, ⟨24, .identity, .p210⟩,
    ⟨23, .identity, .p210⟩, ⟨22, .identity, .p210⟩, ⟨21, .identity, .p210⟩, ⟨20, .identity, .p210⟩, ⟨19, .identity, .p210⟩, ⟨18, .identity, .p210⟩, ⟨17, .identity, .p210⟩, ⟨16, .identity, .p210⟩, ⟨15, .identity, .p210⟩, ⟨14, .identity, .p210⟩, ⟨13, .identity, .p210⟩, ⟨12, .identity, .p210⟩,
    ⟨11, .identity, .p210⟩, ⟨10, .identity, .p210⟩, ⟨9, .identity, .p210⟩, ⟨8, .identity, .p210⟩, ⟨7, .identity, .p210⟩, ⟨6, .identity, .p210⟩, ⟨5, .identity, .p210⟩, ⟨4, .identity, .p210⟩, ⟨3, .identity, .p210⟩, ⟨2, .identity, .p210⟩, ⟨1, .identity, .p210⟩, ⟨0, .identity, .p210⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 7728) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 7728 ≤ case.val)
    (upper : case.val < 7776) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (7728 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7729 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7730 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7731 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7732 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7733 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7734 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7735 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7736 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7737 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7738 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7739 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7740 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7741 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7742 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7743 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7744 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7745 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7746 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7747 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7748 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7749 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7750 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7751 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7752 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7753 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7754 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7755 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7756 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7757 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7758 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7759 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7767 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (7775 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk161.correct

end Krenn.X5OrbitWitnessChunks.Chunk161
