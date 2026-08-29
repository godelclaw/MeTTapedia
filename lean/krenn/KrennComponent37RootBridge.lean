import KrennComponent37Normalization
import KrennFrozenCase0CollapseLayer
import KrennFrozenCase0System
import KrennComponent37Tree

/-!
The semantic seam from a full frozen case-0 valuation through the
external component-37 linear elimination.  The generated finite data
are rechecked by Lean; source hashes below are provenance only.
-/

namespace Krenn.Component37RootBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component37Normalization

def reducedRootSystemSHA256 : String := "4aea56ad80fd778b4cfea8170c6dbdd0f9d591ebd5c2458f2b66e486479fe5c1"
def reducedRootFileSHA256 : String := "2ba2bac4cce6a6bfc2e284693c84d191ef356d6f2f2aab4ffcaf5cc9c89facd5"

def rootCoordinate : Fin 62 → Fin 75 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 32, 33, 34, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74
]

noncomputable def rootValues {R : Type*} (full : Fin 75 → R) : Fin 62 → R :=
  fun coordinate => full (rootCoordinate coordinate)

noncomputable def reconstructFull {R : Type*} [CommRing R]
    (values : Fin 62 → R) : Fin 75 → R := ![
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
  values 51,
  0,
  values 10,
  values 11,
  0,
  values 18,
  values 12,
  values 13,
  values 44,
  values 14,
  values 15,
  values 16,
  values 17,
  values 18,
  values 19,
  values 20,
  values 21,
  0,
  values 22,
  0,
  values 23,
  values 29,
  values 24,
  values 25,
  values 26,
  0,
  values 27,
  0,
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
  values 43,
  values 44,
  values 45,
  values 46,
  values 47,
  values 21 * values 45,
  values 48,
  values 49,
  values 50,
  values 51,
  0,
  values 52,
  values 53,
  0,
  values 54,
  values 55,
  values 56,
  values 57,
  values 58,
  values 59,
  values 60,
  values 61
]

set_option maxRecDepth 100000 in
theorem full_eq_reconstruct_of_raw_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (rawZero : ∀ index,
      rawGeneratorEval (rawValues full) index = 0) :
    full = reconstructFull (rootValues full) := by
  have rawRelation66 : full 66 - full 34 * full 63 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 7
  have rawRelation63 : full 63 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 8
  have rawRelation58 : full 58 - full 26 * full 55 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 9
  have rawRelation37 : full 37 - full 35 * full 67 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 10
  have rawRelation35 : full 35 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 11
  have rawRelation31 : full 31 - full 39 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 12
  have rawRelation29 : full 29 - full 27 * full 59 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 13
  have rawRelation27 : full 27 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 14
  have rawRelation18 : full 18 - full 54 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 15
  have rawRelation15 : full 15 - full 23 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 16
  have rawRelation14 : full 14 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 17
  have rawRelation11 : full 11 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 18
  have rawRelation10 : full 10 - full 62 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 19
  have eliminated10 : full 10 = full 62 := by
    exact sub_eq_zero.mp rawRelation10
  have eliminated11 : full 11 = 0 := by
    exact sub_eq_zero.mp rawRelation11
  have eliminated14 : full 14 = 0 := by
    exact sub_eq_zero.mp rawRelation14
  have eliminated15 : full 15 = full 23 := by
    exact sub_eq_zero.mp rawRelation15
  have eliminated18 : full 18 = full 54 := by
    exact sub_eq_zero.mp rawRelation18
  have eliminated27 : full 27 = 0 := by
    exact sub_eq_zero.mp rawRelation27
  have eliminated31 : full 31 = full 39 := by
    exact sub_eq_zero.mp rawRelation31
  have eliminated35 : full 35 = 0 := by
    exact sub_eq_zero.mp rawRelation35
  have eliminated58 : full 58 = full 26 * full 55 := by
    exact sub_eq_zero.mp rawRelation58
  have eliminated63 : full 63 = 0 := by
    exact sub_eq_zero.mp rawRelation63
  have eliminated29 : full 29 = 0 := by
    calc
      full 29 = full 27 * full 59 :=
        sub_eq_zero.mp rawRelation29
      _ = 0 := by
        simp [eliminated27]
  have eliminated37 : full 37 = 0 := by
    calc
      full 37 = full 35 * full 67 :=
        sub_eq_zero.mp rawRelation37
      _ = 0 := by
        simp [eliminated35]
  have eliminated66 : full 66 = 0 := by
    calc
      full 66 = full 34 * full 63 :=
        sub_eq_zero.mp rawRelation66
      _ = 0 := by
        simp [eliminated63]
  funext coordinate
  fin_cases coordinate <;>
    simp [reconstructFull, rootValues, rootCoordinate, *]

end Krenn.Component37RootBridge

#print axioms Krenn.Component37RootBridge.full_eq_reconstruct_of_raw_component
