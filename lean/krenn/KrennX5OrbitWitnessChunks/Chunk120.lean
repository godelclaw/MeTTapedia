import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk120

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨105, .cycle234, .p120⟩, ⟨104, .cycle234, .p120⟩, ⟨107, .cycle234, .p120⟩, ⟨106, .cycle234, .p120⟩, ⟨102, .cycle234, .p120⟩, ⟨103, .cycle234, .p120⟩, ⟨87, .cycle234, .p120⟩, ⟨86, .cycle234, .p120⟩, ⟨89, .cycle234, .p120⟩, ⟨88, .cycle234, .p120⟩, ⟨84, .cycle234, .p120⟩, ⟨85, .cycle234, .p120⟩,
    ⟨123, .swap23, .p120⟩, ⟨122, .swap23, .p120⟩, ⟨125, .swap23, .p120⟩, ⟨124, .swap23, .p120⟩, ⟨120, .swap23, .p120⟩, ⟨121, .swap23, .p120⟩, ⟨117, .cycle234, .p120⟩, ⟨116, .cycle234, .p120⟩, ⟨119, .cycle234, .p120⟩, ⟨118, .cycle234, .p120⟩, ⟨114, .cycle234, .p120⟩, ⟨115, .cycle234, .p120⟩,
    ⟨33, .swap24, .p120⟩, ⟨32, .swap24, .p120⟩, ⟨35, .swap24, .p120⟩, ⟨34, .swap24, .p120⟩, ⟨30, .swap24, .p120⟩, ⟨31, .swap24, .p120⟩, ⟨63, .cycle234, .p120⟩, ⟨62, .cycle234, .p120⟩, ⟨65, .cycle234, .p120⟩, ⟨64, .cycle234, .p120⟩, ⟨60, .cycle234, .p120⟩, ⟨61, .cycle234, .p120⟩,
    ⟨195, .cycle234, .p120⟩, ⟨194, .cycle234, .p120⟩, ⟨197, .cycle234, .p120⟩, ⟨196, .cycle234, .p120⟩, ⟨192, .cycle234, .p120⟩, ⟨193, .cycle234, .p120⟩, ⟨177, .cycle234, .p120⟩, ⟨176, .cycle234, .p120⟩, ⟨179, .cycle234, .p120⟩, ⟨178, .cycle234, .p120⟩, ⟨174, .cycle234, .p120⟩, ⟨175, .cycle234, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 5760) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 5760 ≤ case.val)
    (upper : case.val < 5808) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (5760 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5761 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5762 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5763 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5764 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5765 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5766 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5767 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5768 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5769 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5770 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5771 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5772 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5773 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5774 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5775 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5776 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5777 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5778 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5779 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5780 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5781 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5782 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5783 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5784 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5785 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5786 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5787 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5788 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5789 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5790 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5791 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5792 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5793 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5794 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5795 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5796 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5797 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5798 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5799 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5800 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5801 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5802 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5803 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5804 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5805 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5806 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (5807 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk120.correct

end Krenn.X5OrbitWitnessChunks.Chunk120
