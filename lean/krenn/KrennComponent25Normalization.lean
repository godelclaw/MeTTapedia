import KrennCollapseComponentContainmentCore
import KrennCollapseReductionReflection

/-!
Exact normalization of external minimal-prime component 25 into
zero-based Lean component row 24.  All exponent-map equalities are
rechecked by Lean below; this source is generated only for serialization.
-/

namespace Krenn.Component25Normalization

open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

noncomputable def rawPositive : Fin 20 → Fin 30 →₀ Nat := ![
  Finsupp.single 18 1 + Finsupp.single 27 1,
  Finsupp.single 13 1 + Finsupp.single 22 1,
  Finsupp.single 11 1 + Finsupp.single 22 1 + Finsupp.single 25 1,
  Finsupp.single 11 1 + Finsupp.single 19 1 + Finsupp.single 25 1,
  Finsupp.single 11 1 + Finsupp.single 18 1,
  Finsupp.single 8 1 + Finsupp.single 24 1,
  Finsupp.single 29 1,
  Finsupp.single 28 1,
  Finsupp.single 23 1,
  Finsupp.single 17 1,
  Finsupp.single 15 1,
  Finsupp.single 14 1,
  Finsupp.single 12 1,
  Finsupp.single 7 1,
  Finsupp.single 6 1,
  Finsupp.single 5 1,
  Finsupp.single 4 1,
  Finsupp.single 2 1,
  Finsupp.single 1 1,
  Finsupp.single 0 1
]

noncomputable def rawNegative : Fin 20 → Option (Fin 30 →₀ Nat) := ![
  some (Finsupp.single 19 1 + Finsupp.single 25 1),
  some (Finsupp.single 19 1 + Finsupp.single 20 1),
  some (Finsupp.single 16 1 + Finsupp.single 20 1 + Finsupp.single 27 1),
  some (Finsupp.single 13 1 + Finsupp.single 16 1 + Finsupp.single 27 1),
  some (Finsupp.single 13 1 + Finsupp.single 16 1),
  some (Finsupp.single 9 1 + Finsupp.single 10 1 + Finsupp.single 21 1),
  none,
  some (Finsupp.single 15 1 + Finsupp.single 26 1),
  some (Finsupp.single 10 1 + Finsupp.single 21 1),
  some (Finsupp.single 16 1 + Finsupp.single 29 1),
  none,
  some (Finsupp.single 19 1),
  some (Finsupp.single 11 1 + Finsupp.single 24 1),
  none,
  none,
  some (Finsupp.single 20 1),
  some (Finsupp.single 9 1),
  none,
  none,
  some (Finsupp.single 25 1)
]

def normalizedIndex : Fin 20 → Option (Fin 78) := ![
  some 43,
  some 16,
  some 44,
  some 45,
  some 17,
  some 24,
  some 0,
  some 1,
  some 5,
  some 8,
  some 28,
  none,
  some 10,
  some 30,
  some 13,
  none,
  none,
  some 23,
  some 46,
  none
]

def selectedIndices : List (Fin 78) := [
  43, 16, 44, 45, 17, 24, 0, 1, 5, 8, 28, 10, 30, 13, 23, 46
]

set_option maxRecDepth 100000 in
theorem selectedIndices_exact : componentGenerators 24 = selectedIndices := by decide

noncomputable def rawGeneratorEval {R : Type*} [CommRing R]
    (values : Fin 30 → R) (index : Fin 20) : R :=
  monomial values (rawPositive index) -
    match rawNegative index with
    | none => 0
    | some negative => monomial values negative

set_option maxRecDepth 100000 in
theorem rawPositiveMap00 :
    Finsupp.mapDomain rawToReduced (rawPositive 0) = generatorPositive 43 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap00 :
    Finsupp.mapDomain rawToReduced ((rawNegative 0).getD 0) =
      (generatorNegative 43).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap01 :
    Finsupp.mapDomain rawToReduced (rawPositive 1) = generatorPositive 16 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap01 :
    Finsupp.mapDomain rawToReduced ((rawNegative 1).getD 0) =
      (generatorNegative 16).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap02 :
    Finsupp.mapDomain rawToReduced (rawPositive 2) = generatorPositive 44 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap02 :
    Finsupp.mapDomain rawToReduced ((rawNegative 2).getD 0) =
      (generatorNegative 44).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap03 :
    Finsupp.mapDomain rawToReduced (rawPositive 3) = generatorPositive 45 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap03 :
    Finsupp.mapDomain rawToReduced ((rawNegative 3).getD 0) =
      (generatorNegative 45).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap04 :
    Finsupp.mapDomain rawToReduced (rawPositive 4) = generatorPositive 17 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap04 :
    Finsupp.mapDomain rawToReduced ((rawNegative 4).getD 0) =
      (generatorNegative 17).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap05 :
    Finsupp.mapDomain rawToReduced (rawPositive 5) = generatorPositive 24 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap05 :
    Finsupp.mapDomain rawToReduced ((rawNegative 5).getD 0) =
      (generatorNegative 24).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap06 :
    Finsupp.mapDomain rawToReduced (rawPositive 6) = generatorPositive 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap07 :
    Finsupp.mapDomain rawToReduced (rawPositive 7) = generatorPositive 1 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap07 :
    Finsupp.mapDomain rawToReduced ((rawNegative 7).getD 0) =
      (generatorNegative 1).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap08 :
    Finsupp.mapDomain rawToReduced (rawPositive 8) = generatorPositive 5 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawNegativeMap08 :
    Finsupp.mapDomain rawToReduced ((rawNegative 8).getD 0) =
      (generatorNegative 5).getD 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

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
theorem rawPositiveMap10 :
    Finsupp.mapDomain rawToReduced (rawPositive 10) = generatorPositive 28 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap11 :
    Finsupp.mapDomain rawToReduced (rawPositive 11) =
      Finsupp.mapDomain rawToReduced ((rawNegative 11).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

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
    Finsupp.mapDomain rawToReduced (rawPositive 13) = generatorPositive 30 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap14 :
    Finsupp.mapDomain rawToReduced (rawPositive 14) = generatorPositive 13 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap15 :
    Finsupp.mapDomain rawToReduced (rawPositive 15) =
      Finsupp.mapDomain rawToReduced ((rawNegative 15).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap16 :
    Finsupp.mapDomain rawToReduced (rawPositive 16) =
      Finsupp.mapDomain rawToReduced ((rawNegative 16).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap17 :
    Finsupp.mapDomain rawToReduced (rawPositive 17) = generatorPositive 23 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawPositiveMap18 :
    Finsupp.mapDomain rawToReduced (rawPositive 18) = generatorPositive 46 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawZeroMap19 :
    Finsupp.mapDomain rawToReduced (rawPositive 19) =
      Finsupp.mapDomain rawToReduced ((rawNegative 19).getD 0) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rawPositive, rawNegative, rawToReduced, Finsupp.mapDomain_add, Finsupp.mapDomain_single, generatorPositive, generatorPositiveSupport, generatorNegative, generatorNegativeSupport, squarefreeExponent, Nat.testBit, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 100000 in
theorem rawGeneratorNormalizes {R : Type*} [CommRing R]
    (values : Fin 26 → R) (index : Fin 20) :
    rawGeneratorEval (liftReduced values) index =
      match normalizedIndex index with
      | none => 0
      | some generator => generatorEval values generator := by
  fin_cases index
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 0) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 0).getD 0) =
        generatorEval values 43
    rw [monomial_mapDomain rawToReduced values (rawPositive 0),
      monomial_mapDomain rawToReduced values ((rawNegative 0).getD 0), rawPositiveMap00,
      rawNegativeMap00]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 1) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 1).getD 0) =
        generatorEval values 16
    rw [monomial_mapDomain rawToReduced values (rawPositive 1),
      monomial_mapDomain rawToReduced values ((rawNegative 1).getD 0), rawPositiveMap01,
      rawNegativeMap01]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 2) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 2).getD 0) =
        generatorEval values 44
    rw [monomial_mapDomain rawToReduced values (rawPositive 2),
      monomial_mapDomain rawToReduced values ((rawNegative 2).getD 0), rawPositiveMap02,
      rawNegativeMap02]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 3) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 3).getD 0) =
        generatorEval values 45
    rw [monomial_mapDomain rawToReduced values (rawPositive 3),
      monomial_mapDomain rawToReduced values ((rawNegative 3).getD 0), rawPositiveMap03,
      rawNegativeMap03]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 4) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 4).getD 0) =
        generatorEval values 17
    rw [monomial_mapDomain rawToReduced values (rawPositive 4),
      monomial_mapDomain rawToReduced values ((rawNegative 4).getD 0), rawPositiveMap04,
      rawNegativeMap04]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 5) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 5).getD 0) =
        generatorEval values 24
    rw [monomial_mapDomain rawToReduced values (rawPositive 5),
      monomial_mapDomain rawToReduced values ((rawNegative 5).getD 0), rawPositiveMap05,
      rawNegativeMap05]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 6) - 0 =
        generatorEval values 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 6), rawPositiveMap06]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 7) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 7).getD 0) =
        generatorEval values 1
    rw [monomial_mapDomain rawToReduced values (rawPositive 7),
      monomial_mapDomain rawToReduced values ((rawNegative 7).getD 0), rawPositiveMap07,
      rawNegativeMap07]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 8) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 8).getD 0) =
        generatorEval values 5
    rw [monomial_mapDomain rawToReduced values (rawPositive 8),
      monomial_mapDomain rawToReduced values ((rawNegative 8).getD 0), rawPositiveMap08,
      rawNegativeMap08]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 9) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 9).getD 0) =
        generatorEval values 8
    rw [monomial_mapDomain rawToReduced values (rawPositive 9),
      monomial_mapDomain rawToReduced values ((rawNegative 9).getD 0), rawPositiveMap09,
      rawNegativeMap09]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 10) - 0 =
        generatorEval values 28
    rw [monomial_mapDomain rawToReduced values (rawPositive 10), rawPositiveMap10]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 11) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 11).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 11),
      monomial_mapDomain rawToReduced values ((rawNegative 11).getD 0), rawZeroMap11]
    ring
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 12) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 12).getD 0) =
        generatorEval values 10
    rw [monomial_mapDomain rawToReduced values (rawPositive 12),
      monomial_mapDomain rawToReduced values ((rawNegative 12).getD 0), rawPositiveMap12,
      rawNegativeMap12]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 13) - 0 =
        generatorEval values 30
    rw [monomial_mapDomain rawToReduced values (rawPositive 13), rawPositiveMap13]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 14) - 0 =
        generatorEval values 13
    rw [monomial_mapDomain rawToReduced values (rawPositive 14), rawPositiveMap14]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 15) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 15).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 15),
      monomial_mapDomain rawToReduced values ((rawNegative 15).getD 0), rawZeroMap15]
    ring
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 16) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 16).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 16),
      monomial_mapDomain rawToReduced values ((rawNegative 16).getD 0), rawZeroMap16]
    ring
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 17) - 0 =
        generatorEval values 23
    rw [monomial_mapDomain rawToReduced values (rawPositive 17), rawPositiveMap17]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 18) - 0 =
        generatorEval values 46
    rw [monomial_mapDomain rawToReduced values (rawPositive 18), rawPositiveMap18]
    simp [generatorEval, generatorNegative, generatorNegativeSupport]
  · change monomial (fun coordinate => values (rawToReduced coordinate)) (rawPositive 19) -
      monomial (fun coordinate => values (rawToReduced coordinate)) ((rawNegative 19).getD 0) = 0
    rw [monomial_mapDomain rawToReduced values (rawPositive 19),
      monomial_mapDomain rawToReduced values ((rawNegative 19).getD 0), rawZeroMap19]
    ring

set_option maxRecDepth 100000 in
theorem rawComponent25_vanishes {R : Type*} [CommRing R]
    (values : Fin 30 → R) (collapse : SatisfiesRawCollapse values)
    (selectedVanish : ∀ generator ∈ componentGenerators 24,
      generatorEval (reduceRaw values) generator = 0) :
    ∀ index, rawGeneratorEval values index = 0 := by
  have identified : values = liftReduced (reduceRaw values) :=
    raw_eq_liftReduced_reduceRaw values
      (raw_binomial_equalities_of_collapse collapse)
  rw [identified]
  intro index
  rw [rawGeneratorNormalizes]
  fin_cases index
  · exact selectedVanish 43 (by decide)
  · exact selectedVanish 16 (by decide)
  · exact selectedVanish 44 (by decide)
  · exact selectedVanish 45 (by decide)
  · exact selectedVanish 17 (by decide)
  · exact selectedVanish 24 (by decide)
  · exact selectedVanish 0 (by decide)
  · exact selectedVanish 1 (by decide)
  · exact selectedVanish 5 (by decide)
  · exact selectedVanish 8 (by decide)
  · exact selectedVanish 28 (by decide)
  · simp [normalizedIndex]
  · exact selectedVanish 10 (by decide)
  · exact selectedVanish 30 (by decide)
  · exact selectedVanish 13 (by decide)
  · simp [normalizedIndex]
  · simp [normalizedIndex]
  · exact selectedVanish 23 (by decide)
  · exact selectedVanish 46 (by decide)
  · simp [normalizedIndex]

end Krenn.Component25Normalization

#print axioms Krenn.Component25Normalization.rawComponent25_vanishes
