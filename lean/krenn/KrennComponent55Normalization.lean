import KrennCollapseComponentContainmentCore
import KrennCollapseReductionReflection

/-!
Exact normalization of external minimal-prime component 55 into
zero-based Lean component row 54.  All exponent-map equalities are
rechecked by Lean below; this source is generated only for serialization.
-/

namespace Krenn.Component55Normalization

open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

noncomputable def rawPositive : Fin 18 → Fin 30 →₀ Nat := ![
  Finsupp.single 2 1 + Finsupp.single 20 1,
  Finsupp.single 29 1,
  Finsupp.single 28 1,
  Finsupp.single 26 1,
  Finsupp.single 24 1,
  Finsupp.single 23 1,
  Finsupp.single 21 1,
  Finsupp.single 19 1,
  Finsupp.single 18 1,
  Finsupp.single 17 1,
  Finsupp.single 14 1,
  Finsupp.single 13 1,
  Finsupp.single 12 1,
  Finsupp.single 6 1,
  Finsupp.single 5 1,
  Finsupp.single 4 1,
  Finsupp.single 1 1,
  Finsupp.single 0 1
]

noncomputable def rawNegative : Fin 18 → Option (Fin 30 →₀ Nat) := ![
  some (Finsupp.single 7 1 + Finsupp.single 25 1),
  none,
  some (Finsupp.single 15 1 + Finsupp.single 26 1),
  none,
  none,
  some (Finsupp.single 10 1 + Finsupp.single 21 1),
  none,
  none,
  none,
  some (Finsupp.single 16 1 + Finsupp.single 29 1),
  some (Finsupp.single 19 1),
  none,
  some (Finsupp.single 11 1 + Finsupp.single 24 1),
  none,
  some (Finsupp.single 20 1),
  some (Finsupp.single 9 1),
  none,
  some (Finsupp.single 25 1)
]

def normalizedIndex : Fin 18 → Option (Fin 78) := ![
  some 14,
  some 0,
  some 1,
  some 3,
  some 21,
  some 5,
  some 6,
  some 15,
  some 77,
  some 8,
  none,
  some 9,
  some 10,
  some 13,
  none,
  none,
  some 46,
  none
]

def selectedIndices : List (Fin 78) := [
  14, 0, 1, 3, 21, 5, 6, 15, 77, 8, 9, 10, 13, 46
]

set_option maxRecDepth 100000 in
theorem selectedIndices_exact : componentGenerators 54 = selectedIndices := by decide

noncomputable def rawGeneratorEval {R : Type*} [CommRing R]
    (values : Fin 30 → R) (index : Fin 18) : R :=
  monomial values (rawPositive index) -
    match rawNegative index with
    | none => 0
    | some negative => monomial values negative

set_option maxRecDepth 100000 in
theorem rawPositiveMap00 :
    Finsupp.mapDomain rawToReduced (rawPositive 0) = generatorPositive 14 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap00 :
    Finsupp.mapDomain rawToReduced ((rawNegative 0).getD 0) =
      (generatorNegative 14).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap01 :
    Finsupp.mapDomain rawToReduced (rawPositive 1) = generatorPositive 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap02 :
    Finsupp.mapDomain rawToReduced (rawPositive 2) = generatorPositive 1 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap02 :
    Finsupp.mapDomain rawToReduced ((rawNegative 2).getD 0) =
      (generatorNegative 1).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap03 :
    Finsupp.mapDomain rawToReduced (rawPositive 3) = generatorPositive 3 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap04 :
    Finsupp.mapDomain rawToReduced (rawPositive 4) = generatorPositive 21 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap05 :
    Finsupp.mapDomain rawToReduced (rawPositive 5) = generatorPositive 5 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap05 :
    Finsupp.mapDomain rawToReduced ((rawNegative 5).getD 0) =
      (generatorNegative 5).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap06 :
    Finsupp.mapDomain rawToReduced (rawPositive 6) = generatorPositive 6 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap07 :
    Finsupp.mapDomain rawToReduced (rawPositive 7) = generatorPositive 15 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap08 :
    Finsupp.mapDomain rawToReduced (rawPositive 8) = generatorPositive 77 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap09 :
    Finsupp.mapDomain rawToReduced (rawPositive 9) = generatorPositive 8 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap09 :
    Finsupp.mapDomain rawToReduced ((rawNegative 9).getD 0) =
      (generatorNegative 8).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap10 :
    Finsupp.mapDomain rawToReduced (rawPositive 10) =
      Finsupp.mapDomain rawToReduced ((rawNegative 10).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap11 :
    Finsupp.mapDomain rawToReduced (rawPositive 11) = generatorPositive 9 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap12 :
    Finsupp.mapDomain rawToReduced (rawPositive 12) = generatorPositive 10 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap12 :
    Finsupp.mapDomain rawToReduced ((rawNegative 12).getD 0) =
      (generatorNegative 10).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap13 :
    Finsupp.mapDomain rawToReduced (rawPositive 13) = generatorPositive 13 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap14 :
    Finsupp.mapDomain rawToReduced (rawPositive 14) =
      Finsupp.mapDomain rawToReduced ((rawNegative 14).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap15 :
    Finsupp.mapDomain rawToReduced (rawPositive 15) =
      Finsupp.mapDomain rawToReduced ((rawNegative 15).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap16 :
    Finsupp.mapDomain rawToReduced (rawPositive 16) = generatorPositive 46 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap17 :
    Finsupp.mapDomain rawToReduced (rawPositive 17) =
      Finsupp.mapDomain rawToReduced ((rawNegative 17).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawGeneratorNormalizes {R : Type*} [CommRing R]
    (values : Fin 26 → R) (index : Fin 18) :
    rawGeneratorEval (liftReduced values) index =
      match normalizedIndex index with
      | none => 0
      | some generator => generatorEval values generator := by
  fin_cases index
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 0) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 0).getD 0) =
        generatorEval values 14
    rw [monomial_mapDomain rawToReduced values (rawPositive 0),
      monomial_mapDomain rawToReduced values ((rawNegative 0).getD 0), rawPositiveMap00,
      rawNegativeMap00]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 1) - 0 =
        generatorEval values 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 1), rawPositiveMap01]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 2) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 2).getD 0) =
        generatorEval values 1
    rw [monomial_mapDomain rawToReduced values (rawPositive 2),
      monomial_mapDomain rawToReduced values ((rawNegative 2).getD 0), rawPositiveMap02,
      rawNegativeMap02]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 3) - 0 =
        generatorEval values 3
    rw [monomial_mapDomain rawToReduced values (rawPositive 3), rawPositiveMap03]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 4) - 0 =
        generatorEval values 21
    rw [monomial_mapDomain rawToReduced values (rawPositive 4), rawPositiveMap04]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 5) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 5).getD 0) =
        generatorEval values 5
    rw [monomial_mapDomain rawToReduced values (rawPositive 5),
      monomial_mapDomain rawToReduced values ((rawNegative 5).getD 0), rawPositiveMap05,
      rawNegativeMap05]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 6) - 0 =
        generatorEval values 6
    rw [monomial_mapDomain rawToReduced values (rawPositive 6), rawPositiveMap06]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 7) - 0 =
        generatorEval values 15
    rw [monomial_mapDomain rawToReduced values (rawPositive 7), rawPositiveMap07]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 8) - 0 =
        generatorEval values 77
    rw [monomial_mapDomain rawToReduced values (rawPositive 8), rawPositiveMap08]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 9) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 9).getD 0) =
        generatorEval values 8
    rw [monomial_mapDomain rawToReduced values (rawPositive 9),
      monomial_mapDomain rawToReduced values ((rawNegative 9).getD 0), rawPositiveMap09,
      rawNegativeMap09]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 10) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 10).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 10),
      monomial_mapDomain rawToReduced values ((rawNegative 10).getD 0), rawZeroMap10]
    ring
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 11) - 0 =
        generatorEval values 9
    rw [monomial_mapDomain rawToReduced values (rawPositive 11), rawPositiveMap11]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 12) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 12).getD 0) =
        generatorEval values 10
    rw [monomial_mapDomain rawToReduced values (rawPositive 12),
      monomial_mapDomain rawToReduced values ((rawNegative 12).getD 0), rawPositiveMap12,
      rawNegativeMap12]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 13) - 0 =
        generatorEval values 13
    rw [monomial_mapDomain rawToReduced values (rawPositive 13), rawPositiveMap13]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 14) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 14).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 14),
      monomial_mapDomain rawToReduced values ((rawNegative 14).getD 0), rawZeroMap14]
    ring
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 15) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 15).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 15),
      monomial_mapDomain rawToReduced values ((rawNegative 15).getD 0), rawZeroMap15]
    ring
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 16) - 0 =
        generatorEval values 46
    rw [monomial_mapDomain rawToReduced values (rawPositive 16), rawPositiveMap16]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 17) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 17).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 17),
      monomial_mapDomain rawToReduced values ((rawNegative 17).getD 0), rawZeroMap17]
    ring

set_option maxRecDepth 100000 in
theorem rawComponent55_vanishes {R : Type*} [CommRing R]
    (values : Fin 30 → R) (collapse : SatisfiesRawCollapse values)
    (selectedVanish : ∀ generator ∈ componentGenerators 54,
      generatorEval (reduceRaw values) generator = 0) :
    ∀ index, rawGeneratorEval values index = 0 := by
  have identified : values = liftReduced (reduceRaw values) :=
    raw_eq_liftReduced_reduceRaw values
      (raw_binomial_equalities_of_collapse collapse)
  rw [identified]
  intro index
  rw [rawGeneratorNormalizes]
  fin_cases index
  · exact selectedVanish 14 (by decide)
  · exact selectedVanish 0 (by decide)
  · exact selectedVanish 1 (by decide)
  · exact selectedVanish 3 (by decide)
  · exact selectedVanish 21 (by decide)
  · exact selectedVanish 5 (by decide)
  · exact selectedVanish 6 (by decide)
  · exact selectedVanish 15 (by decide)
  · exact selectedVanish 77 (by decide)
  · exact selectedVanish 8 (by decide)
  · simp [normalizedIndex]
  · exact selectedVanish 9 (by decide)
  · exact selectedVanish 10 (by decide)
  · exact selectedVanish 13 (by decide)
  · simp [normalizedIndex]
  · simp [normalizedIndex]
  · exact selectedVanish 46 (by decide)
  · simp [normalizedIndex]

end Krenn.Component55Normalization

#print axioms Krenn.Component55Normalization.rawComponent55_vanishes
