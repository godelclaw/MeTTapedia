import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk101

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨184, .swap23, .p201⟩, ⟨185, .swap23, .p201⟩, ⟨181, .swap23, .p201⟩, ⟨180, .swap23, .p201⟩, ⟨183, .swap23, .p201⟩, ⟨182, .swap23, .p201⟩, ⟨166, .cycle234, .p201⟩, ⟨167, .cycle234, .p201⟩, ⟨163, .cycle234, .p201⟩, ⟨162, .cycle234, .p201⟩, ⟨165, .cycle234, .p201⟩, ⟨164, .cycle234, .p201⟩,
    ⟨100, .swap23, .p201⟩, ⟨101, .swap23, .p201⟩, ⟨97, .swap23, .p201⟩, ⟨96, .swap23, .p201⟩, ⟨99, .swap23, .p201⟩, ⟨98, .swap23, .p201⟩, ⟨106, .swap23, .p201⟩, ⟨107, .swap23, .p201⟩, ⟨103, .swap23, .p201⟩, ⟨102, .swap23, .p201⟩, ⟨105, .swap23, .p201⟩, ⟨104, .swap23, .p201⟩,
    ⟨52, .cycle234, .p201⟩, ⟨53, .cycle234, .p201⟩, ⟨49, .cycle234, .p201⟩, ⟨48, .cycle234, .p201⟩, ⟨51, .cycle234, .p201⟩, ⟨50, .cycle234, .p201⟩, ⟨22, .swap24, .p201⟩, ⟨23, .swap24, .p201⟩, ⟨19, .swap24, .p201⟩, ⟨18, .swap24, .p201⟩, ⟨21, .swap24, .p201⟩, ⟨20, .swap24, .p201⟩,
    ⟨94, .swap23, .p201⟩, ⟨95, .swap23, .p201⟩, ⟨91, .swap23, .p201⟩, ⟨90, .swap23, .p201⟩, ⟨93, .swap23, .p201⟩, ⟨92, .swap23, .p201⟩, ⟨76, .cycle234, .p201⟩, ⟨77, .cycle234, .p201⟩, ⟨73, .cycle234, .p201⟩, ⟨72, .cycle234, .p201⟩, ⟨75, .cycle234, .p201⟩, ⟨74, .cycle234, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4848) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4848 ≤ case.val)
    (upper : case.val < 4896) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4848 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4849 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4850 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4851 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4852 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4853 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4854 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4855 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4856 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4857 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4858 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4859 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4860 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4861 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4862 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4863 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4864 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4865 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4866 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4867 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4868 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4869 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4870 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4871 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4872 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4873 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4874 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4875 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4876 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4877 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4878 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4879 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4880 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4881 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4882 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4883 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4884 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4885 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4886 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4887 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4888 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4889 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4890 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4891 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4892 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4893 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4894 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4895 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk101.correct

end Krenn.X5OrbitWitnessChunks.Chunk101
