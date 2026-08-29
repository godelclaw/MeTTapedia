import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk128

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨33, .swap34, .p120⟩, ⟨32, .swap34, .p120⟩, ⟨35, .swap34, .p120⟩, ⟨34, .swap34, .p120⟩, ⟨30, .swap34, .p120⟩, ⟨31, .swap34, .p120⟩, ⟨63, .swap34, .p120⟩, ⟨62, .swap34, .p120⟩, ⟨65, .swap34, .p120⟩, ⟨64, .swap34, .p120⟩, ⟨60, .swap34, .p120⟩, ⟨61, .swap34, .p120⟩,
    ⟨99, .swap34, .p120⟩, ⟨98, .swap34, .p120⟩, ⟨101, .swap34, .p120⟩, ⟨100, .swap34, .p120⟩, ⟨96, .swap34, .p120⟩, ⟨97, .swap34, .p120⟩, ⟨81, .swap34, .p120⟩, ⟨80, .swap34, .p120⟩, ⟨83, .swap34, .p120⟩, ⟨82, .swap34, .p120⟩, ⟨78, .swap34, .p120⟩, ⟨79, .swap34, .p120⟩,
    ⟨117, .identity, .p120⟩, ⟨116, .identity, .p120⟩, ⟨119, .identity, .p120⟩, ⟨118, .identity, .p120⟩, ⟨114, .identity, .p120⟩, ⟨115, .identity, .p120⟩, ⟨111, .identity, .p120⟩, ⟨110, .identity, .p120⟩, ⟨113, .identity, .p120⟩, ⟨112, .identity, .p120⟩, ⟨108, .identity, .p120⟩, ⟨109, .identity, .p120⟩,
    ⟨27, .swap34, .p120⟩, ⟨26, .swap34, .p120⟩, ⟨29, .swap34, .p120⟩, ⟨28, .swap34, .p120⟩, ⟨24, .swap34, .p120⟩, ⟨25, .swap34, .p120⟩, ⟨57, .swap34, .p120⟩, ⟨56, .swap34, .p120⟩, ⟨59, .swap34, .p120⟩, ⟨58, .swap34, .p120⟩, ⟨54, .swap34, .p120⟩, ⟨55, .swap34, .p120⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 6144) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 6144 ≤ case.val)
    (upper : case.val < 6192) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (6144 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6145 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6146 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6147 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6148 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6149 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6150 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6151 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6152 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6153 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6154 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6155 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6156 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6157 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6158 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6159 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6160 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6161 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6162 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6163 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6164 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6165 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6166 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6167 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6168 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6169 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6170 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6171 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6172 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6173 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6174 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6175 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (6191 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk128.correct

end Krenn.X5OrbitWitnessChunks.Chunk128
