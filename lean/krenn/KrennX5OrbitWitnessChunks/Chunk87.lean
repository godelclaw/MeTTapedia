import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk87

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨208, .cycle234, .p201⟩, ⟨209, .cycle234, .p201⟩, ⟨205, .cycle234, .p201⟩, ⟨204, .cycle234, .p201⟩, ⟨207, .cycle234, .p201⟩, ⟨206, .cycle234, .p201⟩, ⟨214, .swap23, .p201⟩, ⟨215, .swap23, .p201⟩, ⟨211, .swap23, .p201⟩, ⟨210, .swap23, .p201⟩, ⟨213, .swap23, .p201⟩, ⟨212, .swap23, .p201⟩,
    ⟨154, .swap24, .p201⟩, ⟨155, .swap24, .p201⟩, ⟨151, .swap24, .p201⟩, ⟨150, .swap24, .p201⟩, ⟨153, .swap24, .p201⟩, ⟨152, .swap24, .p201⟩, ⟨64, .swap24, .p201⟩, ⟨65, .swap24, .p201⟩, ⟨61, .swap24, .p201⟩, ⟨60, .swap24, .p201⟩, ⟨63, .swap24, .p201⟩, ⟨62, .swap24, .p201⟩,
    ⟨196, .cycle234, .p201⟩, ⟨197, .cycle234, .p201⟩, ⟨193, .cycle234, .p201⟩, ⟨192, .cycle234, .p201⟩, ⟨195, .cycle234, .p201⟩, ⟨194, .cycle234, .p201⟩, ⟨178, .cycle234, .p201⟩, ⟨179, .cycle234, .p201⟩, ⟨175, .cycle234, .p201⟩, ⟨174, .cycle234, .p201⟩, ⟨177, .cycle234, .p201⟩, ⟨176, .cycle234, .p201⟩,
    ⟨118, .cycle234, .p201⟩, ⟨119, .cycle234, .p201⟩, ⟨115, .cycle234, .p201⟩, ⟨114, .cycle234, .p201⟩, ⟨117, .cycle234, .p201⟩, ⟨116, .cycle234, .p201⟩, ⟨124, .swap23, .p201⟩, ⟨125, .swap23, .p201⟩, ⟨121, .swap23, .p201⟩, ⟨120, .swap23, .p201⟩, ⟨123, .swap23, .p201⟩, ⟨122, .swap23, .p201⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 4176) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 4176 ≤ case.val)
    (upper : case.val < 4224) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (4176 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4177 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4178 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4179 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4180 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4181 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4182 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4183 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4184 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4185 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4186 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4187 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4188 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4189 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4190 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4191 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4192 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4193 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4194 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4195 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4196 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4197 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4198 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4199 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4200 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4201 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4202 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4203 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4204 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4205 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4206 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4207 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4208 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4209 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4210 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4211 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4212 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4213 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4214 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4215 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4216 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4217 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4218 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4219 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4220 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4221 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4222 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (4223 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk87.correct

end Krenn.X5OrbitWitnessChunks.Chunk87
