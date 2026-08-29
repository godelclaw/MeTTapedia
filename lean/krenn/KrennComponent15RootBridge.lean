import KrennComponent15Normalization
import KrennFrozenCase0CollapseLayer
import KrennFrozenCase0System
import KrennComponent15Tree

/-!
The semantic seam from a full frozen case-0 valuation through the
external component-15 linear elimination.  The generated finite data
are rechecked by Lean; source hashes below are provenance only.
-/

namespace Krenn.Component15RootBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component15Normalization

def reducedRootSystemSHA256 : String := "37ff3898ecb44803c16e5a826a457cf9604d904dd4124ae8a68ef18c70b2853b"
def reducedRootFileSHA256 : String := "5f67e26d1178c532adf803b1492b8b21988c36f4298384d66299253b1ae5b3a8"

def rootCoordinate : Fin 57 → Fin 75 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 16, 17, 19, 20, 24, 25, 26, 28, 30, 32, 33, 34, 36, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 59, 60, 61, 62, 63, 64, 67, 68, 69, 70, 71, 72, 73, 74
]

noncomputable def rootValues {R : Type*} (full : Fin 75 → R) : Fin 57 → R :=
  fun coordinate => full (rootCoordinate coordinate)

noncomputable def reconstructFull {R : Type*} [CommRing R]
    (values : Fin 57 → R) : Fin 75 → R := ![
  values 0,
  values 1,
  values 2,
  values 3,
  values 4,
  values 5,
  values 6,
  values 7,
  values 8,
  values 9,
  values 46,
  values 10,
  values 11,
  0,
  0,
  0,
  values 12,
  values 13,
  values 40,
  values 14,
  values 15,
  0,
  0,
  0,
  values 16,
  values 17,
  values 18,
  0,
  values 19,
  0,
  values 20,
  0,
  values 21,
  values 22,
  values 23,
  0,
  values 24,
  0,
  values 25,
  0,
  values 26,
  values 27,
  values 28,
  values 29,
  values 30,
  values 31,
  values 32,
  values 33,
  values 34,
  values 35,
  values 36,
  values 37,
  values 38,
  values 39,
  values 40,
  values 41,
  values 42,
  0,
  values 18 * values 41,
  values 43,
  values 44,
  values 45,
  values 46,
  values 47,
  values 48,
  0,
  values 23 * values 47,
  values 49,
  values 50,
  values 51,
  values 52,
  values 53,
  values 54,
  values 55,
  values 56
]

set_option maxRecDepth 100000 in
theorem full_eq_reconstruct_of_raw_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (rawZero : ∀ index,
      rawGeneratorEval (rawValues full) index = 0) :
    full = reconstructFull (rootValues full) := by
  have rawRelation66 : full 66 - full 34 * full 63 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 0
  have rawRelation65 : full 65 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 1
  have rawRelation58 : full 58 - full 26 * full 55 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 2
  have rawRelation57 : full 57 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 3
  have rawRelation39 : full 39 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 4
  have rawRelation37 : full 37 - full 35 * full 67 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 5
  have rawRelation35 : full 35 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 6
  have rawRelation31 : full 31 - full 39 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 7
  have rawRelation29 : full 29 - full 27 * full 59 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 8
  have rawRelation27 : full 27 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 9
  have rawRelation23 : full 23 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 10
  have rawRelation22 : full 22 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 11
  have rawRelation21 : full 21 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 12
  have rawRelation18 : full 18 - full 54 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 13
  have rawRelation15 : full 15 - full 23 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 14
  have rawRelation14 : full 14 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 15
  have rawRelation13 : full 13 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 16
  have rawRelation10 : full 10 - full 62 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 17
  have eliminated10 : full 10 = full 62 := by
    exact sub_eq_zero.mp rawRelation10
  have eliminated13 : full 13 = 0 := by
    exact sub_eq_zero.mp rawRelation13
  have eliminated14 : full 14 = 0 := by
    exact sub_eq_zero.mp rawRelation14
  have eliminated18 : full 18 = full 54 := by
    exact sub_eq_zero.mp rawRelation18
  have eliminated21 : full 21 = 0 := by
    exact sub_eq_zero.mp rawRelation21
  have eliminated22 : full 22 = 0 := by
    exact sub_eq_zero.mp rawRelation22
  have eliminated23 : full 23 = 0 := by
    exact sub_eq_zero.mp rawRelation23
  have eliminated27 : full 27 = 0 := by
    exact sub_eq_zero.mp rawRelation27
  have eliminated35 : full 35 = 0 := by
    exact sub_eq_zero.mp rawRelation35
  have eliminated39 : full 39 = 0 := by
    exact sub_eq_zero.mp rawRelation39
  have eliminated57 : full 57 = 0 := by
    exact sub_eq_zero.mp rawRelation57
  have eliminated58 : full 58 = full 26 * full 55 := by
    exact sub_eq_zero.mp rawRelation58
  have eliminated65 : full 65 = 0 := by
    exact sub_eq_zero.mp rawRelation65
  have eliminated66 : full 66 = full 34 * full 63 := by
    exact sub_eq_zero.mp rawRelation66
  have eliminated15 : full 15 = 0 := by
    calc
      full 15 = full 23 :=
        sub_eq_zero.mp rawRelation15
      _ = 0 := by
        simp [eliminated23]
  have eliminated29 : full 29 = 0 := by
    calc
      full 29 = full 27 * full 59 :=
        sub_eq_zero.mp rawRelation29
      _ = 0 := by
        simp [eliminated27]
  have eliminated31 : full 31 = 0 := by
    calc
      full 31 = full 39 :=
        sub_eq_zero.mp rawRelation31
      _ = 0 := by
        simp [eliminated39]
  have eliminated37 : full 37 = 0 := by
    calc
      full 37 = full 35 * full 67 :=
        sub_eq_zero.mp rawRelation37
      _ = 0 := by
        simp [eliminated35]
  funext coordinate
  fin_cases coordinate <;>
    simp [reconstructFull, rootValues, rootCoordinate, *]

end Krenn.Component15RootBridge

#print axioms Krenn.Component15RootBridge.full_eq_reconstruct_of_raw_component
